package vct.rewrite

import vct.col.rewrite.{Generation, Rewriter, RewriterBuilder}
import vct.col.ast.{
  Variable,
  LocalHeapVariable,
  HeapVariable,
  DerefPointer,
  TNonNullPointer,
  Program,
  Expr,
  Statement,
  HeapLocal,
  PointerLocation,
  HeapVariableLocation,
  DerefHeapVariable,
  Block,
  Scope,
  Local,
  Location,
  HeapLocalDecl,
}
import vct.col.origin.Origin
import vct.col.util.AstBuildHelpers._
import vct.col.ref.Ref
import vct.col.util.{CurrentRewriteProgramContext, SuccessionMap}
import vct.result.VerificationError

case object LowerHeapVariables extends RewriterBuilder {
  override def key: String = "lowerHeapVariables"

  override def desc: String =
    "Lower pointer HeapVariables to plain HeapVariables and LocalHeapVariables to Variables if their address is never taken"
}

case class LowerHeapVariables[Pre <: Generation]() extends Rewriter[Pre] {
  private val localStripped
      : SuccessionMap[LocalHeapVariable[Pre], Variable[Post]] = SuccessionMap()
  private val localLowered
      : SuccessionMap[LocalHeapVariable[Pre], Variable[Post]] = SuccessionMap()
  private val globalStripped
      : SuccessionMap[HeapVariable[Pre], HeapVariable[Post]] = SuccessionMap()
  private val globalLowered
      : SuccessionMap[HeapVariable[Pre], HeapVariable[Post]] = SuccessionMap()

  override def dispatch(program: Program[Pre]): Program[Post] = {
    val dereferencedHeapLocals = program.collect {
      case DerefPointer(hl @ HeapLocal(_)) => System.identityHashCode(hl)
    }
    val nakedHeapLocals = program.collect {
      case hl @ HeapLocal(Ref(v))
          if !dereferencedHeapLocals.contains(System.identityHashCode(hl)) =>
        v
    }
    val dereferencedHeapGlobals = program.collect {
      case PointerLocation(hl @ DerefHeapVariable(_)) =>
        System.identityHashCode(hl)
      case DerefPointer(hl @ DerefHeapVariable(_)) =>
        System.identityHashCode(hl)
    }
    val nakedHeapGlobals = program.collect {
      case hl @ DerefHeapVariable(Ref(v))
          // We check for TNonNullPointer here to distinguish between PVL/Java and C/C++/LLVM (where the latter group should encode all global heap variables as TNonNullPointer
          if !dereferencedHeapGlobals.contains(System.identityHashCode(hl)) &&
            v.t.isInstanceOf[TNonNullPointer[Pre]] =>
        v
    }
    VerificationError.withContext(CurrentRewriteProgramContext(program)) {
      program.rewrite(declarations = {
        program.collect {
          case HeapLocal(Ref(v)) if !nakedHeapLocals.contains(v) => v
        }.foreach(v =>
          localStripped(v) =
            new Variable[Post](dispatch(v.t.asPointer.get.element))(v.o)
        )
        program.collect {
          case DerefHeapVariable(Ref(v))
              if !nakedHeapGlobals.contains(v) &&
                v.t.isInstanceOf[TNonNullPointer[Pre]] =>
            v
        }.foreach(v =>
          globalStripped(v) =
            new HeapVariable[Post](
              dispatch(v.t.asPointer.get.element),
              v.init.map(dispatch),
            )(v.o)
        )
        globalDeclarations.collect {
          program.declarations.foreach {
            case v: HeapVariable[Pre] if globalStripped.contains(v) =>
              globalDeclarations.succeed(v, globalStripped(v))
            case v: HeapVariable[Pre] =>
              globalLowered(v) =
                new HeapVariable[Post](dispatch(v.t), v.init.map(dispatch))(v.o)
              globalDeclarations.succeed(v, globalLowered(v))
            case decl => dispatch(decl)
          }

        }._1
      })
    }
  }

  override def dispatch(node: Statement[Pre]): Statement[Post] = {
    implicit val o: Origin = node.o
    node match {
      // Same logic as CollectLocalDeclarations
      case Scope(vars, impl) =>
        val (newVars, newImpl) = variables.collect {
          vars.foreach(dispatch)
          dispatch(impl)
        }
        Scope(newVars, newImpl)
      case HeapLocalDecl(v) =>
        if (localStripped.contains(v)) { variables.declare(localStripped(v)) }
        else {
          localLowered(v) = new Variable[Post](dispatch(v.t))(v.o)
          variables.declare(localLowered(v))
        }
        Block(Nil)
      case _ => node.rewriteDefault()
    }
  }

  override def dispatch(node: Expr[Pre]): Expr[Post] = {
    implicit val o: Origin = node.o
    node match {
      case DerefPointer(HeapLocal(Ref(v))) if localStripped.contains(v) =>
        localStripped(v).get
      case DerefPointer(deref @ DerefHeapVariable(Ref(v)))
          if globalStripped.contains(v) =>
        DerefHeapVariable[Post](globalStripped(v).ref)(deref.blame)
      case HeapLocal(Ref(v)) if localLowered.contains(v) => {
        // localLowered.contains(v) should always be true since all localStripped HeapLocals would be caught by DerefPointer(HeapLocal(Ref(v)))
        Local(localLowered.ref(v))
      }
      case _ => node.rewriteDefault()
    }
  }

  override def dispatch(loc: Location[Pre]): Location[Post] = {
    implicit val o: Origin = loc.o
    loc match {
      case PointerLocation(DerefHeapVariable(Ref(v)))
          if globalStripped.contains(v) =>
        HeapVariableLocation[Post](globalStripped(v).ref)
      case _ => loc.rewriteDefault()
    }
  }
}

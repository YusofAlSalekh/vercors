package vct.rewrite

import vct.col.ast.{
  ADTAxiom,
  ADTFunction,
  AccountedPredicate,
  AddrOf,
  AnyFunctionInvocation,
  AnyMethodInvocation,
  ApplyCoercion,
  AxiomaticDataType,
  CoercePointerArrayPointer,
  Coercion,
  ConstructorInvocation,
  ContractApplicable,
  Declaration,
  DerefPointer,
  Expr,
  FunctionInvocation,
  InlinePattern,
  InstanceFunctionInvocation,
  Invocation,
  InvocationStatement,
  InvokeConstructor,
  InvokeMethod,
  InvokeProcedure,
  InvokingNode,
  Local,
  MethodInvocation,
  Mult,
  NewPointerArray,
  Node,
  Null,
  Perm,
  PointerAdd,
  PointerArraySubscript,
  PointerBlockLength,
  PointerBlockOffset,
  PointerLength,
  PointerLocation,
  PointerSubscript,
  Procedure,
  ProcedureInvocation,
  Result,
  SplitAccountedPredicate,
  Statement,
  TAxiomatic,
  TInt,
  TNonNullPointer,
  TPointerArray,
  Type,
  UnitAccountedPredicate,
  Variable,
  WritePerm,
}
import vct.col.origin.{
  AbstractApplicable,
  Blame,
  InstanceInvocationFailure,
  InvocationFailure,
  LabelContext,
  MismatchedArrayDimension,
  MismatchedPointerSize,
  NonNullPointerNull,
  Origin,
  PanicBlame,
  PointerAddError,
  PointerBounds,
  PointerNull,
  PointerSubscriptError,
  PreBlameSplit,
  PreconditionFailed,
  TrueSatisfiable,
}
import vct.col.rewrite.EncodeArrayValues.PointerArrayCreationFailed
import vct.col.rewrite.{Generation, RewriterBuilder}
import vct.col.typerules.CoercingRewriter
import vct.col.util.AstBuildHelpers._
import vct.col.util.SuccessionMap
import vct.result.VerificationError.{Unreachable, UserError}

import scala.collection.mutable

case object EncodePointerArrays extends RewriterBuilder {
  override def key: String = "encodePointerArray"

  override def desc: String = "Encodes (multi-dimensional) C-style arrays"

  private case class PointerToArrayUnsupportedError(node: Node[_])
      extends UserError {
    override def code: String = "pointerToArrayUnsupported"

    override def text: String =
      node.o.messageInContext(
        "We currently do not support creating a pointer to a sized array, try coercing to a normal pointer first"
      )
  }

  private case class CalculatedPointerAddBlame(
      blame: Blame[PointerSubscriptError]
  ) extends Blame[PointerAddError] {
    override def blame(error: PointerAddError): Unit =
      error match {
        case PointerNull(_) =>
          PanicBlame("It should not be possible to get a nullable PointerArray")
            .blame(error)
        case bounds @ PointerBounds(_) => blame.blame(bounds)
      }
  }

  private case class MismatchedArrayDimensionBlame(
      invokingNode: InvokingNode[_],
      dimensionExpr: Expr[_],
      v: Variable[_],
      blame: Blame[InvocationFailure],
  ) extends Blame[PreconditionFailed] {
    override def blame(error: PreconditionFailed): Unit =
      blame.blame(MismatchedArrayDimension(invokingNode, dimensionExpr, v))
  }

  private case class MismatchedPointerSizeBlame(
      invokingNode: InvokingNode[_],
      v: Variable[_],
      blame: Blame[InvocationFailure],
  ) extends Blame[PreconditionFailed] {
    override def blame(error: PreconditionFailed): Unit =
      blame.blame(MismatchedPointerSize(invokingNode, v))
  }

  private val ConstructorOrigin: Origin = Origin(
    Seq(LabelContext("Pointer array constructors"))
  )
}

case class EncodePointerArrays[Pre <: Generation]()
    extends CoercingRewriter[Pre] {
  import EncodePointerArrays._

  private val constructors
      : mutable.HashMap[(Type[Pre], Int, Option[BigInt]), Procedure[Post]] =
    mutable.HashMap()
  private val arraySucc
      : SuccessionMap[(Type[Pre], Int, Option[BigInt]), AxiomaticDataType[
        Post
      ]] = SuccessionMap()
  private val pointerSucc
      : SuccessionMap[(Type[Pre], Int, Option[BigInt]), ADTFunction[Post]] =
    SuccessionMap()
  private val dimSucc
      : SuccessionMap[(Type[Pre], Int, Option[BigInt], Int), ADTFunction[
        Post
      ]] = SuccessionMap()

  override def applyCoercion(e: => Expr[Post], coercion: Coercion[Pre])(
      implicit o: Origin
  ): Expr[Post] =
    coercion match {
      case CoercePointerArrayPointer(element, dimensions, unique) =>
        adtFunctionInvocation[Post](
          pointerSucc.ref((element, dimensions, unique)),
          args = Seq(e),
        )
      case other => super.applyCoercion(e, other)
    }

  override def postCoerce(e: Expr[Pre]): Expr[Post] = {
    implicit val o: Origin = e.o;

    e match {
      case AddrOf(sub @ PointerArraySubscript(a, _)) =>
        if (a.t.asPointerArray.get.dimensions.length == 1)
          calculatePointer(sub, 0)._1
        else
          throw PointerToArrayUnsupportedError(e)
      // This is quite an ugly solution, however since we have no non-identity coercions to PointerArraySubscript, this *should* be fine...
      case AddrOf(ApplyCoercion(sub @ PointerArraySubscript(a, _), _)) =>
        if (a.t.asPointerArray.get.dimensions.length == 1)
          calculatePointer(sub, 0)._1
        else
          throw PointerToArrayUnsupportedError(e)
      case AddrOf(ApplyCoercion(inner, c)) =>
        applyCoercion(dispatch(inner), c) match {
          case PointerArraySubscript(_, _) =>
            throw Unreachable(
              "Unexpected non-identity coercions to PointerArraySubscript, missing case in EncodePointerArrays"
            )
          case _ => super.postCoerce(e)
        }
      case sub @ PointerArraySubscript(a, _)
          if a.t.asPointerArray.get.dimensions.length == 1 =>
        DerefPointer(calculatePointer(sub, 0)._1)(sub.blame)
      case sub @ PointerArraySubscript(_, _) => calculatePointer(sub, 0)._1
      case npa @ NewPointerArray(element, dimensions, unique) =>
        procedureInvocation(
          PointerArrayCreationFailed(npa, npa.blame),
          constructors.getOrElseUpdate(
            (element, dimensions.length, unique),
            createConstructor(element, dimensions.length, unique),
          ).ref,
          dimensions.map(dispatch),
        )
      case inv: Invocation[Pre] =>
        inv match {
          case inv: AnyMethodInvocation[Pre] =>
            inv match {
              case inv: ProcedureInvocation[Pre] =>
                inv.rewrite(blame =
                  rewriteBlame(inv, inv.args, inv.ref.decl.args, inv.blame)
                )
              case inv: MethodInvocation[Pre] =>
                inv.rewrite(blame =
                  rewriteBlame(inv, inv.args, inv.ref.decl.args, inv.blame)
                )
              case inv: ConstructorInvocation[Pre] =>
                inv.rewrite(blame =
                  rewriteBlame(inv, inv.args, inv.ref.decl.args, inv.blame)
                )
            }
          case inv: AnyFunctionInvocation[Pre] =>
            inv match {
              case inv: FunctionInvocation[Pre] =>
                inv.rewrite(blame =
                  rewriteBlame(inv, inv.args, inv.ref.decl.args, inv.blame)
                )
              case inv: InstanceFunctionInvocation[Pre] =>
                inv.rewrite(blame =
                  rewriteBlame(inv, inv.args, inv.ref.decl.args, inv.blame)
                )
            }
        }
      case _ => super.postCoerce(e)
    }
  }

  private def rewriteBlame[T >: InvocationFailure <: InstanceInvocationFailure](
      invokingNode: InvokingNode[Pre],
      args: Seq[Expr[Pre]],
      declArgs: Seq[Variable[Pre]],
      inBlame: Blame[T],
  ): Blame[T] =
    args.zipWithIndex.flatMap { case (v, i) => v.t.asPointerArray.map((_, i)) }
      .flatMap { case (t, i) =>
        val result = t.dimensions.filter(_.isDefined).map(d =>
          MismatchedArrayDimensionBlame(
            invokingNode,
            d.get,
            declArgs(i),
            inBlame,
          )
        )

        if (t.dimensions.forall(_.isDefined)) {
          MismatchedPointerSizeBlame(invokingNode, declArgs(i), inBlame) +:
            result
        } else { result }
      }.foldLeft(inBlame) { case (r, l) => PreBlameSplit.left(l, r) }

  override def postCoerce(s: Statement[Pre]): Statement[Post] =
    s match {
      case inv: InvocationStatement[Pre] =>
        inv match {
          case inv: InvokeProcedure[Pre] =>
            inv.rewrite(blame =
              rewriteBlame(inv, inv.args, inv.ref.decl.args, inv.blame)
            )
          case inv: InvokeConstructor[Pre] =>
            inv.rewrite(blame =
              rewriteBlame(inv, inv.args, inv.ref.decl.args, inv.blame)
            )
          case inv: InvokeMethod[Pre] =>
            inv.rewrite(blame =
              rewriteBlame(inv, inv.args, inv.ref.decl.args, inv.blame)
            )
        }
      case _ => super.postCoerce(s)
    }

  override def postCoerce(t: Type[Pre]): Type[Post] =
    t match {
      case TPointerArray(element, dimensions, unique) =>
        TAxiomatic(arraySucc.ref((element, dimensions.length, unique)), Nil)
      case _ => super.postCoerce(t)
    }

  override def postCoerce(decl: Declaration[Pre]): Unit = {
    implicit val o: Origin = decl.o
    decl match {
      case app: ContractApplicable[Pre] =>
        val requires =
          (oldRequires: AccountedPredicate[Post]) =>
            app.args.flatMap { v => v.t.asPointerArray.map((v, _)) }.flatMap {
              case (v, t) =>
                val dimensions = t.dimensions.length
                val result = t.dimensions.zipWithIndex.filter { case (d, _) =>
                  d.isDefined
                }.map { case (d, i) =>
                  UnitAccountedPredicate(
                    adtFunctionInvocation[Post](
                      dimSucc.ref((t.element, dimensions, t.unique, i)),
                      args = Seq(Local(succ(v))),
                    ) === dispatch(d.get)
                  )
                }
                if (t.dimensions.forall(_.isDefined)) {
                  UnitAccountedPredicate(
                    PointerLength[Post](adtFunctionInvocation(
                      pointerSucc.ref((t.element, dimensions, t.unique)),
                      args = Seq(Local(succ(v))),
                    ))(NonNullPointerNull) ===
                      t.dimensions.map(d => dispatch(d.get))
                        .reduce(Mult[Post](_, _))
                  ) +: result
                } else { result }
            }.foldLeft(oldRequires) { case (r, l) =>
              SplitAccountedPredicate(l, r)
            }
        allScopes.anySucceed(
          app,
          app.rewrite(contract =
            app.contract.rewrite(requires =
              requires(app.contract.requires.rewriteDefault())
            )
          ),
        )
      case _ => super.postCoerce(decl)
    }
  }

  private def calculatePointer(
      sub: PointerArraySubscript[Pre],
      depth: Int,
  ): (Expr[Post], Expr[Post], Int) = {
    implicit val o: Origin = sub.o
    val arrayT = sub.array.t.asPointerArray.get
    val (obj, index, length) =
      sub.array match {
        case inner: PointerArraySubscript[Pre] =>
          calculatePointer(inner, depth + 1)
        case other =>
          (super.dispatch(other), const[Post](0), arrayT.dimensions.length)
      }
    val newIndex =
      adtFunctionInvocation[Post](
        dimSucc
          .ref((arrayT.element, length, arrayT.unique, length - depth - 1)),
        args = Seq(obj),
      ) * index + super.dispatch(sub.index)
    if (depth == 0) {
      (
        PointerAdd(
          adtFunctionInvocation[Post](
            pointerSucc.ref((arrayT.element, length, arrayT.unique)),
            args = Seq(obj),
          ),
          newIndex,
        )(CalculatedPointerAddBlame(sub.blame)),
        newIndex,
        length,
      )
    } else { (obj, newIndex, length) }
  }

  private def createConstructor(
      element: Type[Pre],
      dimensions: Int,
      unique: Option[BigInt],
  ): Procedure[Post] = {
    implicit val o: Origin = ConstructorOrigin
    val axiomType = TAxiomatic[Post](
      arraySucc.ref((element, dimensions, unique)),
      Nil,
    )
    val dimFunctions = Seq.range(0, dimensions).map { i =>
      val f =
        new ADTFunction(
          Seq(new Variable[Post](axiomType)(o.where(name = "array"))),
          TInt(),
        )(o.where(name = s"get_dim_${i}_$element"))
      dimSucc((element, dimensions, unique, i)) = f
      f
    }
    val pointerFunction =
      new ADTFunction(
        Seq(new Variable[Post](axiomType)(o.where(name = "array"))),
        TNonNullPointer(dispatch(element), unique),
      )(o.where(name = s"get_${element}_pointer"))
    pointerSucc((element, dimensions, unique)) = pointerFunction
    val invFunction =
      new ADTFunction(
        Seq(new Variable[Post](TNonNullPointer(dispatch(element), unique))(
          o.where(name = "ptr")
        )),
        axiomType,
      )(o.where(name = s"get_${element}_pointer_inv"))
    val invAxiom =
      new ADTAxiom[Post](forall(
        axiomType,
        { term =>
          adtFunctionInvocation[Post](
            invFunction.ref,
            args = Seq(InlinePattern(
              adtFunctionInvocation(pointerFunction.ref, args = Seq(term))
            )),
          ) === term
        },
      ))
    arraySucc((element, dimensions, unique)) = globalDeclarations.declare(
      new AxiomaticDataType(
        dimFunctions ++ Seq(pointerFunction, invFunction, invAxiom),
        Nil,
      )(o.where(name = s"pointer_array_$element"))
    )
    val args = Seq.range(0, dimensions)
      .map(i => new Variable[Post](TInt())(o.where(name = s"dim_$i")))
    globalDeclarations.declare(withResult((result: Result[Post]) => {
      procedure(
        AbstractApplicable,
        TrueSatisfiable,
        axiomType,
        args = args,
        requires = UnitAccountedPredicate(foldAnd(args.map(_.get > const(0)))),
        ensures = UnitAccountedPredicate(
          PointerBlockLength(
            adtFunctionInvocation[Post](pointerFunction.ref, args = Seq(result))
          )(NonNullPointerNull) === args.map(_.get)
            .reduce((a: Expr[Post], b: Expr[Post]) => Mult(a, b)) &*
            PointerBlockOffset(adtFunctionInvocation[Post](
              pointerFunction.ref,
              args = Seq(result),
            ))(NonNullPointerNull) === const(0) &*
            foldAnd(dimFunctions.zip(args).map { case (f, a) =>
              adtFunctionInvocation[Post](f.ref, args = Seq(result)) === a.get
            }) &* starall(
              PanicBlame("This is known to be injective!"),
              TInt(),
              body = { term =>
                (const[Post](0) <= term && term < args.map(_.get)
                  .reduce[Expr[Post]] { (a, b) => a * b }) ==> Perm(
                  PointerLocation(
                    PointerAdd(
                      adtFunctionInvocation[Post](
                        pointerFunction.ref,
                        args = Seq(result),
                      ),
                      term,
                    )(PanicBlame("Must be in range!"))
                  )(NonNullPointerNull),
                  WritePerm(),
                )
              },
              triggers = { term =>
                Seq(Seq(
                  PointerSubscript(
                    adtFunctionInvocation[Post](
                      pointerFunction.ref,
                      args = Seq(result),
                    ),
                    term,
                  )(PanicBlame("Must be in range"))
                ))
              },
            )
        ),
      )(o.where(name = s"create_${element}_pointer_array_${dimensions}_dim"))
    }))
  }
}

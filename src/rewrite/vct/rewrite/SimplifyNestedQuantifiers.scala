package vct.col.rewrite

import com.google.common.collect.ImmutableList
import com.typesafe.scalalogging.LazyLogging
import org.sosy_lab.common.{NativeLibraries, ShutdownNotifier}
import org.sosy_lab.common.configuration.Configuration
import org.sosy_lab.common.log.LogManager
import org.sosy_lab.java_smt.SolverContextFactory
import org.sosy_lab.java_smt.SolverContextFactory.Solvers
import org.sosy_lab.java_smt.api.{BooleanFormula, FormulaType}
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions
import vct.col.ast.{Variable, _}
import vct.col.ast.util.ExpressionEqualityCheck.{Neg, Pos}
import vct.col.ast.util.{AnnotationVariableInfoGetter, ExpressionEqualityCheck}
import vct.col.rewrite.util.Comparison
import vct.col.origin.{
  ArrayInsufficientPermission,
  DiagnosticOrigin,
  LabelContext,
  Origin,
  PanicBlame,
  PointerBounds,
  PreferredName,
}
import vct.col.ref.Ref
import vct.col.rewrite.SimplifyNestedQuantifiers.{
  InvalidTrigger,
  InvalidTriggerVars,
  InvalidTriggerPair,
  NotAllowedInTrigger,
}
import vct.col.rewrite.{Generation, Rewriter, RewriterBuilder}
import vct.col.typerules.CoercionUtils
import vct.col.util.AstBuildHelpers._
import vct.col.util.{AstBuildHelpers, Substitute}
import vct.result.Message
import vct.result.VerificationError.{Unreachable, UserError}

import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer
import scala.annotation.nowarn
import scala.util.Using

/** This rewrite pass simplifies expressions of roughly this form: forall(i,j:
  * Int . 0 <= i < i_max && 0 <= j < j_max; xs[a*(i_max*j + i) + b]) and
  * collapses it into a single forall: forall(k: Int. b <= k <= i_max*j_max*a +
  * b && k % a == 0; xs[k])
  *
  * We also check on if a quantifier takes just a single value. E.g. forall(i,j:
  * Int; i == 5 && i < n && i <= j && j < 5; xs[j+i]) ====> 5 < n ==> forall(int
  * j; 0 <= j < 5; xs[j])
  *
  * and if a quantifier isn't in the "body" of the forall. E.g. forall(i,j: Int.
  * 1 <= i && i< n && 0 < j; xs[j]>0) ====> n > 1 ==> forall(j: Int; 0 < j;
  * xs[j] >0)
  */
case object SimplifyNestedQuantifiers extends RewriterBuilder {
  override def key: String = "simplifyNestedQuantifiers"
  override def desc: String = "Simplify nested quantifiers."

  case class NotAllowedInTrigger(e: Expr[_]) extends UserError {
    override def code: String = "notAllowedInTrigger"
    override def text: String =
      e.o.messageInContext(
        "Arithmetic and logic operators are not allowed in triggers."
      )
  }

  case class InvalidTriggerVars(
      triggers: Seq[Expr[_]],
      missing: Set[Variable[_]],
  ) extends UserError {
    override def code: String = "invalidTriggerVars"
    override def text: String =
      Message.messagesInContext(
        triggers.map(err => err.o -> s"These triggers: ")
          .appended(missing.head.o -> s"Do not mention this var. "): _*
      )
  }

  case class InvalidTrigger(e: Expr[_]) extends UserError {
    override def code: String = "invalidTrigger"
    override def text: String =
      e.o.messageInContext(
        "We did not succeed in rewriting this part of the trigger. " +
          "Only linear expressions are possible to rewrite in triggers."
      )
  }

  case class InvalidTriggerPair(e1: Expr[_], e2: Expr[_]) extends UserError {
    override def code: String = "invalidTrigger"
    override def text: String =
      e1.o.messageInContext(
        "We cannot rewrite this pair of triggers, which contain arithmetic," +
          " because the quantifier variables are not partitioned."
      )
  }
}

case class SimplifyNestedQuantifiers[Pre <: Generation]()
    extends Rewriter[Pre] with LazyLogging {

  val SimplifyNestedQuantifiersOrigin: Origin = Origin(
    Seq(PreferredName(Seq("unknown")), LabelContext("simplification"))
  )

  private def BinderOrigin(name: String): Origin =
    Origin(Seq(PreferredName(Seq(name)), LabelContext("simplification")))

  private implicit val o: Origin = SimplifyNestedQuantifiersOrigin

  private def one: IntegerValue[Pre] = IntegerValue(1)

  var equalityChecker: ExpressionEqualityCheck[Pre] = ExpressionEqualityCheck()
  var topLevel: Boolean = false
  var infoGetter: AnnotationVariableInfoGetter[Pre] =
    new AnnotationVariableInfoGetter[Pre]()

  override def dispatch(e: Expr[Pre]): Expr[Post] = {
    e match {
      // Consider elements of top level stars and ands also toplevel
      case e: Star[Pre] if topLevel =>
        val left = dispatch(e.left)
        topLevel = true
        val right = dispatch(e.right)
        topLevel = true
        Star(left, right)(e.o)
      case e: And[Pre] if topLevel =>
        val left = dispatch(e.left)
        topLevel = true
        val right = dispatch(e.right)
        topLevel = true
        And(left, right)(e.o)
      case e: Forall[Pre] =>
        topLevel = false
        equalityChecker = ExpressionEqualityCheck(Some(infoGetter.finalInfo()))
        rewriteBinder(e)
      case e: Starall[Pre] =>
        topLevel = false
        equalityChecker = ExpressionEqualityCheck(Some(infoGetter.finalInfo()))
        rewriteBinder(e)
      case other if topLevel =>
        infoGetter.addInfo(other)
        topLevel = false
        other.rewriteDefault()
      case other => other.rewriteDefault()
    }
  }

  def rewriteBinder(e: Binder[Pre]): Expr[Post] = {
    rewriteLinearArray(e) match {
      case None =>
        val res = e.rewriteDefault()
        res match {
          case Starall(_, Nil, _) =>
            val trigger = e.o.inlineContext(false).map(_.last)
              .getOrElse("unknown context")
            logger.warn(
              f"The binder `${e.o.shortPositionText}`:`${trigger} contains no triggers`"
            )
          case Forall(_, Nil, body) =>
            val trigger = e.o.inlineContext(false).map(_.last)
              .getOrElse("unknown context")
            logger.warn(
              f"The binder `${e.o.shortPositionText}`:`${trigger} contains no triggers`"
            )
          case _ =>
        }
        res
      case Some(newE) => newE
    }
  }

  override def dispatch(stat: Statement[Pre]): Statement[Post] = {
    stat match {
      case Exhale(e) =>
      case Inhale(e) =>
      case proof: FramedProof[Pre] => return checkFramedProof(proof)
      case _ => return stat.rewriteDefault()
    }
    topLevel = true
    infoGetter.setupInfo()
    val result = stat.rewriteDefault()
    topLevel = false
    equalityChecker = ExpressionEqualityCheck()
    result
  }

  def checkFramedProof(proof: FramedProof[Pre]): Statement[Post] = {
    topLevel = true
    infoGetter.setupInfo()
    val pre = dispatch(proof.pre)
    equalityChecker = ExpressionEqualityCheck()
    infoGetter.setupInfo()
    val post = dispatch(proof.post)
    topLevel = false
    equalityChecker = ExpressionEqualityCheck()

    val body = dispatch(proof.body)

    FramedProof[Post](pre, body, post)(proof.blame)(proof.o)
  }

  override def dispatch(
      p: AccountedPredicate[Pre]
  ): AccountedPredicate[Post] = {
    p match {
      case u @ UnitAccountedPredicate(pred) =>
        topLevel = true
        u.rewriteDefault()
      case s @ SplitAccountedPredicate(left, right) => s.rewriteDefault()
    }
  }

  override def dispatch(loopContract: LoopContract[Pre]): LoopContract[Post] = {
    val loopInvariant: LoopInvariant[Pre] =
      loopContract match {
        case l: LoopInvariant[Pre] => l
        case _ => return dispatch(loopContract)
      }

    topLevel = true
    infoGetter.setupInfo()
    val invariant = dispatch(loopInvariant.invariant)
    topLevel = false
    equalityChecker = ExpressionEqualityCheck()
    val decreases = loopInvariant.decreases.map(element => dispatch(element))

    LoopInvariant(invariant, decreases)(loopInvariant.blame)(loopInvariant.o)
  }

  override def dispatch(
      contract: ApplicableContract[Pre]
  ): ApplicableContract[Post] = {

    topLevel = true
    infoGetter.setupInfo()
    val contextEverywhere = dispatch(contract.contextEverywhere)
    val oldInfo = infoGetter

    // Reuse information from context everywhere
    val requires = dispatch(contract.requires)
    equalityChecker = ExpressionEqualityCheck()

    // Again reuse information from context everywhere
    infoGetter = oldInfo
    val ensures = dispatch(contract.ensures)
    equalityChecker = ExpressionEqualityCheck()
    topLevel = false

    val signals = contract.signals.map(element => dispatch(element))
    val givenArgs =
      variables.collect { contract.givenArgs.foreach(dispatch) }._1
    val yieldsArgs =
      variables.collect { contract.yieldsArgs.foreach(dispatch) }._1
    val decreases = contract.decreases
      .map(element => rewriter.dispatch(element))

    ApplicableContract(
      requires,
      ensures,
      contextEverywhere,
      signals,
      givenArgs,
      yieldsArgs,
      decreases,
    )(contract.blame)(contract.o)
  }

  def indepOfV[G](v: Variable[G], e: Expr[G]): Boolean =
    e.collectFirst { case Local(ref) if v == ref.decl => () }.isEmpty

  private def getTriggers(e: Binder[Pre]): Seq[Seq[Expr[Pre]]] =
    e match {
      case Forall(_, triggers, _) => triggers
      case Starall(_, triggers, _) => triggers
    }

  private def triggerContainVar(
      triggers: Seq[Seq[Expr[Pre]]],
      v: Variable[Pre],
  ): Boolean = {
    triggers.flatten.foreach(e =>
      if (indepOfV(v, e))
        return true
    )
    false
  }

  private def hasTriggers(e: Binder[Pre]): Boolean = getTriggers(e).nonEmpty

  def rewriteLinearArray(e: Binder[Pre]): Option[Expr[Post]] = {
    val originalBody =
      e match {
        case Forall(_, _, body) => body
        case Starall(_, _, body) => body
        case _ => return None
      }

    // We can only rewrite quantifiers that contain at least one integer binding
    if (!e.bindings.exists(_.t == TInt()))
      return None

    // We can always try to remove independent variables
    // Since they are never mentioned in the body, we can safely 'remove' them
    // since in that case they can
    val quantifierData = new RewriteQuantifierData(originalBody, e, this)
    quantifierData.setData()
    quantifierData.checkIndependentVariables()
    // We replace variables, if they only have one value
    // (e.g. (\forall int x, int y; x=5 ....) always has x=5.
    // We only do this, when the x=... is either a non quantifier-variable or a constant
    // or is not present in a trigger
    // (so it does not fundamentally change existing triggers)
    quantifierData.checkSingleValueVariables()

    // We __only__ want to further reshape quantifiers, which are explicitly marked with a trigger.
    // There should also not be other quantifiers present (complicates things too much)
    if (!hasTriggers(e) || quantifierData.checkOtherBinders()) {
      logger.debug(s"Not rewriting $e because it has no patterns")
      return quantifierData.result()
    }

    quantifierData.lookForLinearAccesses()
  }

  class RewriteQuantifierData(
      val bindings: mutable.Set[Variable[Pre]],
      var lowerBounds: mutable.Map[Variable[Pre], ArrayBuffer[Expr[Pre]]],
      var upperBounds: mutable.Map[Variable[Pre], ArrayBuffer[Expr[Pre]]],
      var upperExclusiveBounds: mutable.Map[Variable[Pre], ArrayBuffer[
        Expr[Pre]
      ]],
      var independentConditions: ArrayBuffer[Expr[Pre]],
      val dependentConditions: ArrayBuffer[Expr[Pre]],
      var constraints: ArrayBuffer[Expr[Pre]],
      var body: Expr[Pre],
      var triggers: Seq[Seq[Expr[Pre]]],
      val originalBinder: Binder[Pre],
      val mainRewriter: SimplifyNestedQuantifiers[Pre],
  ) {
    val constantVars: mutable.Map[Variable[Pre], Expr[Pre]] = mutable.Map()

    def this(
        originalBody: Expr[Pre],
        originalBinder: Binder[Pre],
        rewriter: SimplifyNestedQuantifiers[Pre],
    ) = {
      this(
        originalBinder.bindings.to(mutable.Set),
        originalBinder.bindings.map(_ -> ArrayBuffer[Expr[Pre]]())
          .to(mutable.Map),
        originalBinder.bindings.map(_ -> ArrayBuffer[Expr[Pre]]())
          .to(mutable.Map),
        originalBinder.bindings.map(_ -> ArrayBuffer[Expr[Pre]]())
          .to(mutable.Map),
        ArrayBuffer[Expr[Pre]](),
        ArrayBuffer[Expr[Pre]](),
        ArrayBuffer[Expr[Pre]](),
        originalBody,
        getTriggers(originalBinder),
        originalBinder,
        rewriter,
      )
    }

    /** Keeps track if it is already feasible to make a new quantifier */
    var newBinder = false

    def setData(): Unit = {
      val allConditions = unfoldBody(Seq(), Seq())
      // Split bounds that are independent of any binding variables
      val (newIndependentConditions, potentialBounds) = allConditions
        .partition(indepOf(bindings, _))
      independentConditions.addAll(newIndependentConditions)
      getBounds(potentialBounds)

      for (v <- bindings) {
        val vl: Local[Pre] = Local(v.ref)
        for (l <- lowerBounds(v)) {
          constraints = constraints.appended(l <= vl)
        }
        for (u <- upperExclusiveBounds(v)) {
          constraints = constraints.appended(vl < u)
        }
      }
      for (e <- dependentConditions) { constraints = constraints.appended(e) }
      constraints = constraints ++ equalityChecker.usefullConditions()
    }

    def unfoldBody(
        prevConditions: Seq[Expr[Pre]],
        scales: Seq[Expr[Pre] => Expr[Pre]],
    ): Seq[Expr[Pre]] = {
      val (allConditions, mainBody) = unfoldImplies[Pre](body)
      val newConditions = prevConditions ++ allConditions
      val (newVars, secondBody) =
        mainBody match {
          case Forall(newVars, _, secondBody) => (newVars, secondBody)
          case Starall(newVars, _, secondBody) => (newVars, secondBody)
          // Strip Scales
          case s @ Scale(scale, res) =>
            val newScales = scales :+ ((r: Expr[Pre]) => Scale(scale, r)(s.o))
            body = res
            return unfoldBody(newConditions, newScales)
          case _ =>
            // Re-aply scales from right to left
            body = scales.foldRight(mainBody)((s, b) => s(b))
            return newConditions
        }

      bindings.addAll(newVars)

      for (v <- newVars) {
        lowerBounds(v) = ArrayBuffer[Expr[Pre]]()
        upperBounds(v) = ArrayBuffer[Expr[Pre]]()
        upperExclusiveBounds(v) = ArrayBuffer[Expr[Pre]]()
      }

      body = secondBody

      unfoldBody(newConditions, scales)
    }

    def containsOtherBinders(e: Expr[Pre]): Boolean = {
      e match {
        case _: Binder[Pre] => return true
        case _ => e.collectFirst { case e: Binder[Pre] => return true }
      }
      false
    }

    /** Process the potential bounds to be either a bound or just a dependent
      * condition.
      *
      * @param potentialBounds
      *   Bounds to be processed.
      */
    def getBounds(potentialBounds: Iterable[Expr[Pre]]): Unit = {
      for (bound <- potentialBounds) { getSingleBound(bound) }
    }

    def getSingleBound(bound: Expr[Pre]): Unit =
      Comparison.of(bound) match {
        // First try to match a simple comparison
        case Some((_, Comparison.NEQ, _)) => dependentConditions.addOne(bound)
        case Some((left, comp, right)) =>
          if (indepOf(bindings, right)) {
            // x >|>=|==|<=|< 5
            left match {
              case Local(Ref(v)) if bindings.contains(v) =>
                addSingleBound(v, right, comp)
              case Plus(ll, rr) if indepOf(bindings, rr) =>
                getSingleBound(comp.make(ll, right - rr))
              case Plus(ll, rr) if indepOf(bindings, ll) =>
                getSingleBound(comp.make(rr, right - ll))
              case Minus(ll, rr) if indepOf(bindings, rr) =>
                getSingleBound(comp.make(ll, right + rr))
              case _ => dependentConditions.addOne(bound)
            }
          } else if (indepOf(bindings, left)) {
            getSingleBound(comp.flip.make(right, left))
          } else { dependentConditions.addOne(bound) }
        case None =>
          bound match {
            // If we do not have a simple comparison, we support one special case: i \in {a..b}
            case SetMember(Local(Ref(v)), RangeSet(from, to))
                if bindings.contains(v) && indepOf(bindings, from) &&
                  indepOf(bindings, to) =>
              addSingleBound(v, from, Comparison.GREATER_EQ)
              addSingleBound(v, to, Comparison.LESS)
            case SetMember(left, RangeSet(from, to)) =>
              getSingleBound(Comparison.GREATER_EQ.make(left, from))
              getSingleBound(Comparison.LESS.make(left, to))
            case SeqMember(Local(Ref(v)), Range(from, to))
                if bindings.contains(v) && indepOf(bindings, from) &&
                  indepOf(bindings, to) =>
              addSingleBound(v, from, Comparison.GREATER_EQ)
              addSingleBound(v, to, Comparison.LESS)
            case SeqMember(left, Range(from, to)) =>
              getSingleBound(Comparison.GREATER_EQ.make(left, from))
              getSingleBound(Comparison.LESS.make(left, to))
            case _ => dependentConditions.addOne(bound)
          }
      }

    /** Add a bound like v >= right.
      */
    @nowarn("msg=xhaust")
    def addSingleBound(
        v: Variable[Pre],
        right: Expr[Pre],
        comp: Comparison,
    ): Unit = {
      right match {
        // Simplify rules from simplify.pvl come up with these kind of rules (specialize_range_right_i),
        // but we want the original bounds
        case Select(Less(e1, e2), e3, e4) =>
          if (e1 == e3 && e2 == e4 || e1 == e4 && e2 == e3) {
            addSingleBound(v, e1, comp)
            addSingleBound(v, e2, comp)
            return
          }
        case _ =>
      }

      comp match {
        // v < right
        case Comparison.LESS =>
          upperExclusiveBounds(v).addOne(right)
          upperBounds(v).addOne(right - one)
        // v <= right
        case Comparison.LESS_EQ =>
          upperExclusiveBounds(v).addOne(right + one)
          upperBounds(v).addOne(right)
        // v == right
        case Comparison.EQ =>
          lowerBounds(v).addOne(right)
          upperExclusiveBounds(v).addOne(right + one)
          upperBounds(v).addOne(right)
        // v >= right
        case Comparison.GREATER_EQ => lowerBounds(v).addOne(right)
        // v > right
        case Comparison.GREATER => lowerBounds(v).addOne(right + one)
      }
    }

    def simpleExpr(e: Expr[Pre]): Boolean =
      e match {
        // Should not point to another variable from the quantifier
        case Local(ref) if !bindings.contains(ref.decl) => true
        case _: Constant[Pre] => true
        case _ => false
      }

    /** We check if there are any binding variables which resolve to just a
      * single value, which happens if it has equal lower and upper bounds. E.g.
      * forall(int i,j; i == 0 && i <= j && j < 5; xs[j+i]) ==> forall(int j; 0
      * our bounds again. We don't worry if we have something like x == 5 && x
      * <= j < 5; xs[j]) We just replace each reference to that value, and check
      * < 0, since that will resolve to 5 < 0, which equally does not work.
      */
    def checkSingleValueVariables(): Unit = {
      for (name <- bindings) {
        val equalBounds = lowerBounds(name)
          .flatMap(x => upperBounds(name).map(y => (x, y))).collectFirst {
            case (x, y) if equalityChecker.equalExpressions(x, y) =>
              if (simpleExpr(x))
                x
              else
                y
          }
        if (equalBounds.isDefined) {
          // If in trigger and result is not simple, do not substitute for now
          if (
            triggerContainVar(triggers, name) && !simpleExpr(equalBounds.get)
          ) { constantVars(name) = equalBounds.get }
          else {
            // We will put out a new quantifier
            newBinder = true
            val newValue = equalBounds.get
            val nameVar: Expr[Pre] = Local(name.ref)
            val sub = Substitute[Pre](Map(nameVar -> newValue))
            val replacer = sub.dispatch(_: Expr[Pre])
            body = replacer(body)

            // Do not quantify over name anymore
            bindings.remove(name)
            triggers = triggers.map(_.map(replacer))

            // Some dependent selects, might now have become independent or even bounds
            val oldDependentBounds = dependentConditions.map(replacer)
            dependentConditions.clear()

            val (new_independentConditions, potentialBounds) =
              oldDependentBounds.partition(indepOf(bindings, _))
            independentConditions.addAll(new_independentConditions)
            getBounds(potentialBounds)

            // Bounds for the name, have now become independent conditions
            lowerBounds(name).foreach(lb =>
              if (lb != newValue)
                independentConditions.addOne(LessEq(lb, newValue))
            )
            upperBounds(name).foreach(ub =>
              if (ub != newValue)
                independentConditions.addOne(LessEq(newValue, ub))
            )

            lowerBounds.remove(name)
            upperBounds.remove(name)
            upperExclusiveBounds.remove(name)

            // Strictly speaking, a binding variable could be newly removed, if a previous one has been found constant
            // and then the bounds deem another binding variable also constant. We check that by doing recursion.
            checkSingleValueVariables()
            return
          }
        }
      }
    }

    def checkIndependentVariables(): Unit = {
      for (name <- bindings) {
        if (indepOfV(name, body)) {
          var independent = true
          dependentConditions.foreach(s =>
            if (!indepOfV(name, s))
              independent = false
          )
          if (triggerContainVar(triggers, name))
            independent = false
          if (independent) {
            // We can freely remove this named variable
            val maxBound = extremeValue(name, maximizing = true)
            val minBound = extremeValue(name, maximizing = false)
            (maxBound, minBound) match {
              case (Some(maxBound), Some(minBound)) =>
                newBinder = true
                // Do not quantify over name anymore
                bindings.remove(name)
                lowerBounds.remove(name)
                upperBounds.remove(name)
                upperExclusiveBounds.remove(name)

                // We remove the forall variable i, but need to rewrite some expressions
                // (forall i; a <= i <= b; ...Perm(ar, x)...) ====> b>=a ==> ...Perm(ar, x*(b-a+1))...
                independentConditions.addOne(GreaterEq(maxBound, minBound))

                if (body.t == TResource()) {
                  body =
                    Scale(Plus(one, Minus(maxBound, minBound)), body)(
                      PanicBlame(
                        "Error in SimplifyNestedQuantifiers class, implication should make sure scale is" +
                          " never negative when accessed."
                      )
                    )
                }
              case _ =>
            }
          }
        }
      }
    }

    def extremeValue(
        name: Variable[Pre],
        maximizing: Boolean,
    ): Option[Expr[Pre]] = {
      if (maximizing && upperBounds(name).nonEmpty)
        Some(extremes(upperBounds(name).toSeq, maximizing))
      else if (!maximizing && lowerBounds(name).nonEmpty)
        Some(extremes(lowerBounds(name).toSeq, maximizing))
      else
        None
    }

    def extremes(xs: Seq[Expr[Pre]], maximizing: Boolean): Expr[Pre] = {
      xs match {
        case expr +: Nil => expr
        case left +: right +: tail =>
          Select(
            condition =
              if (maximizing)
                left > right
              else
                left < right,
            whenTrue = extremes(left +: tail, maximizing),
            whenFalse = extremes(right +: tail, maximizing),
          )
      }
    }

    // This allows only forall's to be rewritten, if they have at least one lower and upper bound
    def checkBounds(): Boolean = {
      for (name <- bindings) {
        // Exit when notAt least one upper && lower bound
        if (
          lowerBounds.getOrElse(name, ArrayBuffer()).isEmpty ||
          upperBounds.getOrElse(name, ArrayBuffer()).isEmpty
        ) { return false }
      }
      true
    }

    // Returns true if contains other binders, which we won't rewrite
    def checkOtherBinders(): Boolean = {
      independentConditions
        .foldLeft(containsOtherBinders(body))(_ || containsOtherBinders(_))
    }

    case class ForallSubstitute(
        varMap: Map[Variable[Pre], Variable[Post]],
        subs: Map[Variable[Pre], Expr[Post]],
        indexReplacement: Map[Expr[Pre], Expr[Post]],
    ) extends Rewriter[Pre] {
      override val allScopes = mainRewriter.allScopes

      override def dispatch(e: Expr[Pre]): Expr[Post] =
        e match {
          case expr if indexReplacement.contains(expr) => indexReplacement(expr)
          case v: Local[Pre] if subs.contains(v.ref.decl) => subs(v.ref.decl)
          case v: Local[Pre] if varMap.contains(v.ref.decl) =>
            Local[Post](varMap(v.ref.decl).ref)(v.o)
          case other => other.rewriteDefault()
        }
    }

    // We use a map to capture the original expression, for error messages
    def collectForallVars(e: Expr[Pre]): Set[Variable[Pre]] =
      e.collect { case Local(ref) if bindings.contains(ref.decl) => ref.decl }
        .toSet

    def checkTriggersSet(
        arithmethicSet: Set[Expr[Pre]],
        others: Set[Expr[Pre]],
    ): Unit = {
      // Collect all variables mentioned by non-arithmetic patterns
      val nonRewriteVars = others.toSeq.map(collectForallVars)
      val rewriteVars = arithmethicSet.toSeq.map(collectForallVars)
      // The rewriteVars should be a clean partition.
      // The nonRewriteVars should be completely separate
      // mentioned by them
      rewriteVars.zipWithIndex.foreach { case (vars, i) =>
        // Check other rewrite candidates
        rewriteVars.zipWithIndex.foreach { case (varsOther, j) =>
          if (i != j && vars.intersect(varsOther).nonEmpty) {
            // This means the rewriteVars are not a clean partition
            throw InvalidTriggerPair(
              arithmethicSet.toSeq(i),
              arithmethicSet.toSeq(j),
            )
          }
        }
        // Check non rewrite vars
        nonRewriteVars.zipWithIndex.foreach { case (varsOther, j) =>
          if (vars.intersect(varsOther).nonEmpty) {
            // This means the rewriteVars is mentioned in a non-rewrite var
            throw InvalidTriggerPair(arithmethicSet.toSeq(i), others.toSeq(j))
          }
        }
      }
    }

    def lookForLinearAccesses(): Option[Expr[Post]] = {
      val linearAccesses = new FindLinearArrayAccesses(this)
      // Each trigger set should mention all forall vars
      triggers.foreach { t =>
        val mentionedVars = t.flatMap(collectForallVars)
        val nonMentionedVars: Set[Variable[Pre]] =
          bindings.toSet -- mentionedVars
        if (nonMentionedVars.nonEmpty)
          throw InvalidTriggerVars(t, nonMentionedVars.toSet)
      }

      // We do not do elaborate rewriting for multiple trigger sets
      if (triggers.size != 1) {
        triggers.flatten.foreach(validTrigger(_, checkArithmetic = true))
        return result()
      }

      // We split the triggers in 'patterns'. E.g each function argument is a 'pattern' and the index of an array is a
      // pattern etc. We do not need duplicates, thus we put the result in a set.
      val patternSet: Set[Expr[Pre]] =
        triggers.head.flatMap(t => getPatterns(t)).toSet
      val (special, otherTriggers) = patternSet.partition(containsSpecial(_))
      // All patterns with special tokens are now filtered out, so we can get patterns which contain arithmetic
      val (arithmetic, validPatterns) = otherTriggers
        .partition(containsSpecial(_, checkArithmetic = true))
      if (arithmetic.isEmpty && special.isEmpty) { return result() }

      // We want to know which vars are already called correctly, and which need rewriting
      val mentionedVars = validPatterns.flatMap(collectForallVars)
      // nonMentionedVars need to be rewritten in the arithmetic patterns
      val nonMentionedVars: Set[Variable[Pre]] = bindings.toSet -- mentionedVars

      // There are patterns, for which we just want to introduce a new variable.
      // E.g. (\forall int i; ... {:f(i, i+1, size+3):} ...)
      // we want to rewrite towards
      // (\forall int i, j, k; j==i+1 && k==size+3 ... {:f(i, j, k):} ...)
      // These can be in the set `arithmetic`. These are exactly the patterns
      // which do not have a nonMentionedVars, since the nonMentionedVars need to be rewritten.
      var (rewriteArithmetic, introducePatterns) = arithmetic.partition(p =>
        p.collectFirst {
          case Local(ref) if nonMentionedVars.contains(ref.decl) => ()
        }.isDefined
      )
      // specials cannot have non mentioned vars
      special.foreach(p =>
        p.collectFirst {
          case Local(ref) if nonMentionedVars.contains(ref.decl) =>
            throw InvalidTrigger(p)
        }
      )
      introducePatterns = introducePatterns ++ special
      // We need to check that at the top level, these patterns do not contain extra structure. Otherwise,
      // we would remove that structure from the trigger, and this is wrong.
      introducePatterns.foreach(p =>
        if (allowedInTrigger(p, checkArithmetic = true))
          throw Unreachable(
            "We are wrongly removing structure in a trigger. " +
              "Update getPatterns in SimplifyNestedQuantifiers if this occurs."
          )
      )

      // Now some checks if the arithmetic patterns can be used
      checkTriggersSet(rewriteArithmetic, validPatterns)
      var remaining = bindings

      val results: Seq[(SubstituteForall, Variable[Post])] = rewriteArithmetic
        .toSeq.map { pattern =>
          val qvars = collectForallVars(pattern).toSeq
          // We should have vars to rewrite, this was checked before, just sanity check
          if (qvars.isEmpty)
            throw Unreachable(
              "Arithmetic rewrite patterns should mention a forall var."
            )
          remaining = remaining.filterNot(qvars.contains(_))
          mainRewriter.variables.collect {
            linearAccesses.linearExpression(pattern, qvars)
          } match {
            case (bindings, Some(substituteForall)) =>
              if (bindings.size != 1)
                throw Unreachable(
                  "Only one new variable should be declared with SimplifyNestedQuantifiers."
                )
              (substituteForall, bindings.head)
            case (_, None) => throw InvalidTrigger(arithmetic.head)
          }
        }
      val newVars =
        remaining.map { v =>
          val res = mainRewriter.variables.collect { mainRewriter.dispatch(v) }
          (v, res._1.head)
        }.toMap
      val introducedVars = introducePatterns.toSeq.map { p =>
        val res = mainRewriter.variables.collect {
          val newName = p.o.getPreferredNameOrElse().camel
          val t = mainRewriter.dispatch(p.t)
          val xNew = new Variable[Post](t)(BinderOrigin(newName))
          mainRewriter.variables.declare(xNew)
          mainRewriter.dispatch(p)
        }
        (res._1.head, res._2)
      }

      val oldVarsMap: Map[Variable[Pre], Expr[Post]] =
        results.foldLeft(Map[Variable[Pre], Expr[Post]]()) { case (l, r) =>
          r._1.substituteOldVars ++ l
        }
      // Substitute indexes, but also expressions for which we introduced vars
      val indexMap: Map[Expr[Pre], Expr[Post]] =
        results.foldLeft(Map[Expr[Pre], Expr[Post]]()) { case (l, r) =>
          l + r._1.substituteIndex
        }
      val introduceMap: Map[Expr[Pre], Expr[Post]] =
        introducePatterns.toSeq
          .zip(introducedVars.map(v => Local[Post](v._1.ref))).toMap

      val sub = ForallSubstitute(newVars, oldVarsMap, indexMap ++ introduceMap)
      var select: Seq[Expr[Post]] =
        results.foldRight(
          independentConditions.map(sub.dispatch).toSeq ++
            dependentConditions.map(sub.dispatch).toSeq
        ) { case (l, r) => l._1.newBounds +: r }
      val newBody = sub.dispatch(body)
      for (v <- remaining) {
        val vNew = Local[Post](newVars(v).ref)(v.o)
        for (l <- lowerBounds.getOrElse(v, ArrayBuffer[Expr[Pre]]()))
          select = select :+ (sub.dispatch(l) <= vNew)
        for (u <- upperExclusiveBounds.getOrElse(v, ArrayBuffer[Expr[Pre]]()))
          select = select :+ (vNew < sub.dispatch(u))
      }
      select =
        select ++ introducedVars.map { case (v, e) => Local[Post](v.ref) === e }

      val main =
        if (select.nonEmpty)
          Implies(AstBuildHelpers.foldAnd(select), newBody)
        else
          newBody
      val newTriggers = triggers.map(_.map(sub.dispatch))
      val newBinders =
        results.foldRight(newVars.values.toSeq) { case (l, r) => l._2 +: r } ++
          introducedVars.map(_._1)

      @nowarn("msg=xhaust")
      val forall: Binder[Post] =
        originalBinder match {
          case _: Forall[Pre] =>
            Forall(newBinders, newTriggers, main)(originalBinder.o)
          case originalBinder: Starall[Pre] =>
            Starall(newBinders, newTriggers, main)(originalBinder.blame)(
              originalBinder.o
            )
        }
      Some(forall)
    }

    def result(): Option[Expr[Post]] = {
      // If we changed something we always return a result, even if we could not rewrite further
      val res =
        if (newBinder) {
          val select = independentConditions
          if (bindings.isEmpty) {
            if (select.isEmpty)
              Some(body)
            else
              Some(Implies(AstBuildHelpers.foldAnd(select.toSeq), body))
          } else {
            upperExclusiveBounds.foreach {
              case (n: Variable[Pre], upperBounds: ArrayBuffer[Expr[Pre]]) =>
                val i: Expr[Pre] = Local(n.ref)
                upperBounds.foreach(upperBound => select.addOne(i < upperBound))
            }
            lowerBounds.foreach {
              case (n: Variable[Pre], lowerBounds: ArrayBuffer[Expr[Pre]]) =>
                val i: Expr[Pre] = Local(n.ref)
                lowerBounds
                  .foreach(lowerBound => select.addOne(lowerBound <= i))
            }
            // PB: In general reordering conditions is not safe, because a condintion may frame the well-formedness of a
            // subsequent expression. Heuristic: more often than not, independent conditions frame the bounds, which then
            // frame any other dependent conditions.
            select ++= dependentConditions
            val newBody =
              if (select.nonEmpty)
                Implies(AstBuildHelpers.foldAnd(select.toSeq), body)
              else
                body

            @nowarn("msg=xhaust")
            val forall: Expr[Pre] =
              originalBinder match {
                case _: Forall[Pre] =>
                  Forall(bindings.toSeq, triggers, newBody)(originalBinder.o)
                case e: Starall[Pre] =>
                  Starall(bindings.toSeq, triggers, newBody)(e.blame)(
                    originalBinder.o
                  )
              }
            Some(forall)
          }
        } else { None }

      res.map(mainRewriter.dispatch)
    }
  }

  def indepOf[G](bindings: collection.Set[Variable[G]], e: Expr[G]): Boolean =
    e.collectFirst { case Local(ref) if bindings.contains(ref.decl) => () }
      .isEmpty

  // PB/LvdH:in general all terms are allowable in patterns, *except*
  // that z3 disallows all Bool-related operators, and Viper additionally disallows all arithmetic operators. Any
  // other operators is necessarily encoded as a smt function (allowed), or banned due to being a side effect
  // (later dealt with rigorously).
  // Arithmetic can still be rewritten in this pass, so we allow that initially
  def allowedInTrigger[G](
      e: Expr[G],
      checkArithmetic: Boolean = false,
  ): Boolean =
    e match {
      case PolarityDependent(_, _) | Wand(_, _) | _: Forall[G] | _: Starall[G] |
          _: Exists[G] =>
        throw NotAllowedInTrigger(e)
      case And(_, _) | Or(_, _) | Implies(_, _) | Star(_, _) | Eq(_, _) |
          Neq(_, _) | Less(_, _) | Greater(_, _) | LessEq(_, _) |
          GreaterEq(_, _) =>
        false
      case Plus(_, _) | Minus(_, _) | Mult(_, _) | FloatDiv(_, _) |
          TruncDiv(_, _) | TruncMod(_, _) | RatDiv(_, _) | FloorDiv(_, _) |
          Mod(_, _) | UMinus(_) if checkArithmetic =>
        false
      case _ => true
    }

  def validTrigger[G](e: Expr[G], checkArithmetic: Boolean = false): Unit = {
    e.foreach {
      case n: Expr[G] if !allowedInTrigger(n, checkArithmetic) =>
        throw NotAllowedInTrigger(n); case _ =>
    }
  }

  def containsSpecial[G](
      e: Expr[G],
      checkArithmetic: Boolean = false,
  ): Boolean = {
    e.collectFirst {
      case n: Expr[G] if !allowedInTrigger(n, checkArithmetic) => ()
    }.isDefined
  }

  def getPatterns(e: Node[Pre]): Seq[Expr[Pre]] =
    e match {
      case ArrayLocation(e, subscript) =>
        getPatterns(subscript) ++ getPatterns(e)
      case ArraySubscript(e, subscript) =>
        getPatterns(subscript) ++ getPatterns(e)
      case SeqSubscript(e, subscript) =>
        getPatterns(subscript) ++ getPatterns(e)
      case PointerSubscript(e, subscript) =>
        getPatterns(subscript) ++ getPatterns(e)
      case PointerAdd(e, offset) => getPatterns(offset) ++ getPatterns(e)
      case VectorSubscript(e, offset) => getPatterns(offset) ++ getPatterns(e)
      case FunctionInvocation(_, args, Seq(), given, _) =>
        args.flatMap(getPatterns) ++ given.flatMap(g => getPatterns(g._2))
      case e: Expr[Pre] => Seq(e)
      case _ => Seq()
    }

  class FindLinearArrayAccesses(quantifierData: RewriteQuantifierData) {
    def linearExpression(
        pattern: Expr[Pre],
        quantVars: Seq[Variable[Pre]],
    ): Option[SubstituteForall] = {
      val pot = new PotentialLinearExpressions(pattern)
      pot.visit(pattern)
      pot.canRewrite(quantVars)
    }

    class PotentialLinearExpressions(val pattern: Expr[Pre]) {
      val linearExpressions: mutable.Map[Variable[Pre], Expr[Pre]] = mutable
        .Map()
      var constantExpression: Option[Expr[Pre]] = None
      var isLinear: Boolean = true
      var currentMultiplier: Option[Expr[Pre]] = None

      def visit(e: Expr[Pre]): Unit = {
        e match {
          case Plus(left, right) =>
            // if the first is constant, the second argument cannot be
            if (isConstant(left)) {
              addToConstant(left)
              visit(right)
            } else if (isConstant(right)) {
              addToConstant(right)
              visit(left)
            } else { // Both arguments contain linear information
              visit(left)
              visit(right)
            }
          case Minus(left, right) =>
            // if the first is constant, the second argument cannot be
            if (isConstant(left)) {
              addToConstant(left)
              val oldMultiplier = currentMultiplier
              multiplyMultiplier(IntegerValue(-1))
              visit(right)
              currentMultiplier = oldMultiplier
            } else if (isConstant(right)) {
              addToConstant(right, isPlus = false)
              visit(left)
            } else { // Both arguments contain linear information
              visit(left)
              val oldMultiplier = currentMultiplier
              multiplyMultiplier(IntegerValue(-1))
              visit(right)
              currentMultiplier = oldMultiplier
            }
          case Mult(left, right) =>
            if (isConstant(left)) {
              val oldMultiplier = currentMultiplier
              multiplyMultiplier(left)
              visit(right)
              currentMultiplier = oldMultiplier
            } else if (isConstant(right)) {
              val oldMultiplier = currentMultiplier
              multiplyMultiplier(right)
              visit(left)
              currentMultiplier = oldMultiplier
            } else { isLinear = false }
          // TODO: Check if division is right conceptually with an example. Take special care to think about
          //  the order of division
//            case e@FloorDiv(left, right) =>
//              if (isConstant(right)){
//                val oldMultiplier = currentMultiplier
//                multiplyMultiplier(FloorDiv(IntegerValue(1), right)(e.blame))
//                visit(left)
//                currentMultiplier = oldMultiplier
//              } else {
//                isLinear = false
//              }
          case Local(ref) =>
            if (quantifierData.bindings.contains(ref.decl)) {
              linearExpressions get ref.decl match {
                case None =>
                  linearExpressions(ref.decl) = currentMultiplier
                    .getOrElse(IntegerValue(1))
                case Some(old) =>
                  linearExpressions(ref.decl) = Plus(
                    old,
                    currentMultiplier.getOrElse(IntegerValue(1)),
                  )
              }
            } else {
              throw Unreachable(
                "We should not end up here, the precondition of \'FindLinearArrayAccesses\' was not uphold."
              )
            }
          case _ => isLinear = false
        }
      }

      def canRewrite(
          quantVars: Seq[Variable[Pre]]
      ): Option[SubstituteForall] = {
        if (!isLinear) { return None }
        // Checking the preconditions of the check_vars_list function
        for (v <- quantVars) {
          if (
            !( // Must have an a_i
              linearExpressions.contains(v) &&
                // must have lower bound
                quantifierData.upperExclusiveBounds.contains(v) &&
                quantifierData.upperExclusiveBounds(v).nonEmpty
            )
          ) { return None }
        }

        for (v <- linearExpressions.keys) {
          linearExpressions(v) = simplify(linearExpressions(v))
        }

        def sortVar(v: Variable[Pre]): BigInt =
          equalityChecker.isConstantInt(linearExpressions(v)).getOrElse(999999)
        val vars = quantVars.toList.sortBy(sortVar)

        val res = vars.permutations.map(check_vars_list).collectFirst({
          case Some(subst) => subst
        })
        res
      }

      def abs[G](
          e: Expr[G],
          sign: Option[ExpressionEqualityCheck.Sign],
      ): Expr[G] = {
        sign match {
          case Some(ExpressionEqualityCheck.Pos()) => e
          case Some(ExpressionEqualityCheck.Neg()) => -e
          case None => Select(e >= const(0), e, -e)
        }
      }

      /** This function determines if the vars in this specific order allow the
        * forall to be rewritten to one forall.
        *
        * Precondition: * At least one var in `quantifierData.bindings` *
        * linearExpressions has an expression for all `vars` *
        * quantifierData.upperExclusiveBounds has a non-empty list for all
        * `vars` * quantifierData.lowerBounds has a non-empty list for all
        * `vars`
        *
        * We are looking for patterns: /\_{0 <= i <= k} {xmin_i <= x_i < xmin_i
        * + n_i} : ... ar[Sum_{0 <= i <= k} (a_i * x_i) + b] ... and we require
        * that for i>0 a_i >= a_{i-1} * n_{i-1} 5*x + 10*y+30*z (0<= x < 2 && 0
        * <= y < 3 && 0 <= z < 4)
        *
        * Further more we require that n_i > 0 and all a_i != 0 (all a_i are or
        * all positive or all negative) We can than replace the forall with off
        * := b + Sum_{0 <= i <= k} (xmin_i * a_i) 0 <= |x_new - off| < |a_k| *
        * n_k && (x_new - off) % a_0 == 0 : ... ar[x_new] ... and each x_i gets
        * replaced by base_i / |a_i| + xmin_i where base_k -> |x_new - off|
        * base_{i-1} -> base_i % a_i
        *
        * And for each a_i where a_i > a_{i-1} * n_{i-1} (thus was not equal) We
        * additionally add base_{i-1} / a_{i-1} < n_{i-1} (derived from (x_{i-1}
        * < xmin_i + n_{i-1})
        */
      def check_vars_list(
          vars: Seq[Variable[Pre]]
      ): Option[SubstituteForall] = {
        val x0 = vars.head
        val a0 = linearExpressions(x0)
        // x_{i-1}
        var xPrev = x0
        var linLast: Expr[Pre] = IntegerValue(0)
        val sign = equalityChecker.getSign(a0)
        // a0 always must be provable non zero
        equalityChecker.isNonZero(a0).getOrElse(return None)

        val xmins: mutable.Map[Variable[Pre], Expr[Pre]] = mutable.Map()
        val remainingLowerBounds: mutable.Map[Variable[Pre], Set[Expr[Pre]]] =
          mutable.Map()
        val remainingUpperBounds: mutable.Map[Variable[Pre], Set[Expr[Pre]]] =
          mutable.Map()
        var otherNeededBounds: Set[Expr[Pre]] = Set()

        for (x <- vars.tail) {
          findSuitableBound(x, xPrev, linLast, sign) match {
            case None => return None
            case Some(
                  FoundBound(
                    lowerBounds,
                    upperBounds,
                    otherNeeded,
                    xmin,
                    linExpr,
                  )
                ) =>
              xmins(xPrev) = xmin
              remainingLowerBounds(xPrev) = lowerBounds
              remainingUpperBounds(xPrev) = upperBounds
              otherNeededBounds ++= otherNeeded
              xPrev = x
              linLast = linExpr
          }
        }
        // We found a replacement!
        // Make the variable & declaration
        val newName = vars.map(_.o.getPreferredNameOrElse().camel).mkString("_")
        val xNew = new Variable[Post](TInt())(BinderOrigin(newName))
        quantifierData.mainRewriter.variables.declare(xNew)

        val newGen: Expr[Pre] => Expr[Post] =
          quantifierData.mainRewriter.dispatch

        // Get a random lowerbound for x_i_last;
        val lowLast = quantifierData.lowerBounds(xPrev).head
        xmins(xPrev) = lowLast
        remainingLowerBounds(xPrev) =
          quantifierData.lowerBounds(xPrev).tail.toSet

        // Get a random upperbound for x_i_last;
        val upLast = quantifierData.upperExclusiveBounds(xPrev).head
        remainingUpperBounds(xPrev) =
          quantifierData.upperExclusiveBounds(xPrev).tail.toSet
        val nLast = simplifiedMinus(upLast, lowLast)

        // off := b + Sum_{0 <= i <= k} (xmin_i * a_i)
        var offset: Expr[Pre] =
          constantExpression match {
            case None => simplifiedMult(a0, xmins(x0))
            case Some(b) => simplifiedPlus(b, simplifiedMult(a0, xmins(x0)))
          }

        for (x_i <- vars.tail) {
          offset = simplifiedPlus(
            offset,
            simplifiedMult(linearExpressions(x_i), xmins(x_i)),
          )
        }

        // base_k == (x_new - off)
        val xNewVar: Expr[Post] = Local(xNew.ref)
        var base: Expr[Post] =
          if (is_value(offset, 0))
            xNewVar
          else
            Minus(xNewVar, newGen(offset))

        val replaceMap: mutable.Map[Variable[Pre], Expr[Post]] = mutable.Map()

        // (a_0>0 => 0 <= x_new - offset < a_k * n_k) &&
        // (a_0<0 => a_k * n_k < x_new <= 0)
        val aLast = linearExpressions(xPrev)
        val extent = newGen(simplifiedMult(aLast, nLast))
        val ifAPos = const[Post](0) <= base && base < extent
        val ifANeg = extent < base && base <= const(0)

        var newBounds =
          sign match {
            case Some(Pos()) => ifAPos
            case Some(Neg()) => ifANeg
            case None =>
              ((newGen(a0) > const(0)) ==> ifAPos) &&
              ((newGen(a0) < const(0)) ==> ifANeg)
          }
        base = abs(base, sign)

        // Replace the linear expression with the new variable
        val replacePattern = (pattern, xNewVar)

        // and each x_i gets replaced by
        //  x_i -> base_i / |a_i| + xmin_i
        for (x <- vars.reverse) {
          var newValue = base
          val a = linearExpressions(x)
          val xmin = xmins(x)
          if (!is_value(a, 1))
            newValue =
              FloorDiv(newValue, newGen(abs(a, sign)))(PanicBlame("a not zero"))
          if (!is_value(xmin, 0))
            newValue = Plus(newValue, newGen(xmin))
          replaceMap(x) = newValue

          // base_{i-1} -> base_i % a_i
          if (!is_value(a, 1))
            base = Mod(base, newGen(a))(PanicBlame("n not zero"))
        }
        // Add bound that we stride through our forall if a0 != 1
        // (base_1 % a_0 == 0) --> base_0 == 0
        if (!is_value(a0, 1) && !is_value(a0, -1))
          newBounds = And(newBounds, Eq(base, IntegerValue(0)))

        for (x <- vars) {
          val xNew = replaceMap(x)
          for (lowerBound <- remainingLowerBounds(x)) {
            newBounds = And(LessEq(newGen(lowerBound), xNew), newBounds)
          }
          for (upperBound <- remainingUpperBounds(x)) {
            newBounds = And(Less(xNew, newGen(upperBound)), newBounds)
          }
        }
        for (b <- otherNeededBounds) { newBounds = And(newGen(b), newBounds) }

        Some(SubstituteForall(newBounds, replaceMap.toMap, replacePattern))
      }

      case class FoundBound(
          otherLowerBounds: Set[Expr[Pre]],
          otherUpperBounds: Set[Expr[Pre]],
          otherNeededBounds: Set[Expr[Pre]],
          xMin: Expr[Pre],
          linExpr: Expr[Pre],
      )

      def isBool(e: Expr[_]): Boolean = {
        CoercionUtils.getCoercion(e.t, TBool()).isDefined
      }

      def isInt(e: Expr[_]): Boolean = {
        CoercionUtils.getCoercion(e.t, TInt()).isDefined
      }

      case class askSMTSolver(
          constraints: Iterable[Expr[Pre]],
          test: Expr[Pre],
      ) {
        def check(): Boolean = {
          val options = Configuration.builder()
            .setOption("solver.nonLinearArithmetic", "APPROXIMATE_FALLBACK");
          val config = options.build()
          val logManager = LogManager.createNullLogManager
          val shutDown = ShutdownNotifier.createDummy
          var id = 0

          Using(SolverContextFactory.createSolverContext(
            config,
            logManager,
            shutDown,
            Solvers.SMTINTERPOL,
          )) { ctx =>
            Using(ctx.newProverEnvironment()) { prover =>
              val fmgr = ctx.getFormulaManager
              val varIntMap: mutable.Map[Variable[Pre], IntegerFormula] =
                mutable.Map()
              val varBoolMap: mutable.Map[Variable[Pre], BooleanFormula] =
                mutable.Map()
              val bmgr = fmgr.getBooleanFormulaManager
              val imgr = fmgr.getIntegerFormulaManager

              def tdiv(a: Expr[Pre], b: Expr[Pre]): Expr[Pre] =
                Select(
                  a >= const(0) || a % b === const(0),
                  a / b,
                  a / b + Select(b > const(0), const(1), const(-1)),
                )

              def tmod(a: Expr[Pre], b: Expr[Pre]): Expr[Pre] =
                Select(
                  a >= const(0) || a % b === const(0),
                  a % b,
                  a % b + Select(b > const(0), b, -b),
                )

              def addConstraint(e: Expr[Pre]): Boolean = {
                addBool(e) match {
                  case Some(b1) => prover.addConstraint(b1); true
                  case None => false
                }
              }

              def addBool(e: Expr[Pre]): Option[BooleanFormula] = {
                e match {
                  case Select(c, t, f) =>
                    for {
                      c1 <- addBool(c); t1 <- addBool(t); f1 <- addBool(f)
                    } yield bmgr.ifThenElse(c1, t1, f1)
                  case SeqMember(e1, Range(from, to)) =>
                    for {
                      i1 <- addInt(e1); fromi <- addInt(from); toi <- addInt(to)
                    } yield bmgr
                      .and(imgr.lessOrEquals(fromi, i1), imgr.lessThan(i1, toi))
                  case SetMember(e1, RangeSet(from, to)) =>
                    for {
                      i1 <- addInt(e1); fromi <- addInt(from); toi <- addInt(to)
                    } yield bmgr
                      .and(imgr.lessOrEquals(fromi, i1), imgr.lessThan(i1, toi))
                  case Or(e1, e2) =>
                    for {
                      b1 <- addBool(e1); b2 <- addBool(e2)
                    } yield bmgr.or(b1, b2)
                  case And(e1, e2) =>
                    for {
                      b1 <- addBool(e1); b2 <- addBool(e2)
                    } yield bmgr.and(b1, b2)
                  case Implies(e1, e2) =>
                    for {
                      b1 <- addBool(e1); b2 <- addBool(e2)
                    } yield bmgr.implication(b1, b2)
                  case Not(e1) => for { b1 <- addBool(e1) } yield bmgr.not(b1)
                  case Eq(e1, e2) if isBool(e1) && isBool(e2) =>
                    for {
                      b1 <- addBool(e1); b2 <- addBool(e2)
                    } yield bmgr.equivalence(b1, b2)
                  case Eq(e1, e2) if isInt(e1) && isInt(e2) =>
                    for {
                      b1 <- addInt(e1); b2 <- addInt(e2)
                    } yield imgr.equal(b1, b2)
                  case Neq(e1, e2) if isInt(e1) && isInt(e2) =>
                    for {
                      b1 <- addInt(e1); b2 <- addInt(e2)
                    } yield bmgr.not(imgr.equal(b1, b2))
                  case Less(e1, e2) if isInt(e1) && isInt(e2) =>
                    for {
                      b1 <- addInt(e1); b2 <- addInt(e2)
                    } yield imgr.lessThan(b1, b2)
                  case LessEq(e1, e2) if isInt(e1) && isInt(e2) =>
                    for {
                      b1 <- addInt(e1); b2 <- addInt(e2)
                    } yield imgr.lessOrEquals(b1, b2)
                  case Greater(e1, e2) if isInt(e1) && isInt(e2) =>
                    for {
                      b1 <- addInt(e1); b2 <- addInt(e2)
                    } yield imgr.greaterThan(b1, b2)
                  case GreaterEq(e1, e2) if isInt(e1) && isInt(e2) =>
                    for {
                      b1 <- addInt(e1); b2 <- addInt(e2)
                    } yield imgr.greaterOrEquals(b1, b2)
                  case BooleanValue(b) => Some(bmgr.makeBoolean(b))
                  case Local(ref) if isBool(e) =>
                    if (varBoolMap.contains(ref.decl))
                      Some(varBoolMap(ref.decl))
                    else {
                      val x = bmgr.makeVariable(s"b$id")
                      id += 1
                      varBoolMap(ref.decl) = x
                      Some(x)
                    }
                  case _ => None
                }
              }

              def addInt(e: Expr[Pre]): Option[IntegerFormula] = {
                e match {
                  case Select(c, t, f) =>
                    for {
                      c1 <- addBool(c); t1 <- addInt(t); f1 <- addInt(f)
                    } yield bmgr.ifThenElse(c1, t1, f1)
                  case Plus(e1, e2) =>
                    for {
                      i1 <- addInt(e1); i2 <- addInt(e2)
                    } yield imgr.add(i1, i2)
                  case Minus(e1, e2) =>
                    for {
                      i1 <- addInt(e1); i2 <- addInt(e2)
                    } yield imgr.subtract(i1, i2)
                  case Mult(e1, e2) =>
                    for {
                      i1 <- addInt(e1); i2 <- addInt(e2)
                    } yield imgr.multiply(i1, i2)
                  case FloorDiv(e1, e2) =>
                    for {
                      i1 <- addInt(e1); i2 <- addInt(e2)
                    } yield imgr.divide(i1, i2)
                  // Ugly, but the SMT library does not allow us to define functions..
                  case TruncDiv(e1, e2) => addInt(tdiv(e1, e2))
                  case TruncMod(e1, e2) => addInt(tmod(e1, e2))
                  case Mod(e1, e2) =>
                    for {
                      i1 <- addInt(e1); i2 <- addInt(e2)
                    } yield imgr.modulo(i1, i2)
                  case UMinus(e1) =>
                    for { i1 <- addInt(e1) } yield imgr.negate(i1)
                  case IntegerValue(i) => Some(imgr.makeNumber(i.toInt))
                  case Local(ref) if isInt(e) =>
                    if (varIntMap.contains(ref.decl))
                      Some(varIntMap(ref.decl))
                    else {
                      val x = imgr.makeVariable(s"i$id")
                      id += 1
                      varIntMap(ref.decl) = x
                      Some(x)
                    }
                  case _ => None
                }
              }

              for (c <- constraints) {
                if (!addConstraint(c))
                  return false
              }
              if (!addConstraint(!test))
                return false
              prover.isUnsat
            }
          }
        }.get.get
      }

      // Check in the other bounds if the specific expressions is present by a bound
      def isExprUpperBounded(
          e: Expr[Pre],
          boundRequired: Expr[Pre],
      ): Boolean = {
        // We are now officially desperate, so we are going to call the help of an SMT solver
        val smt = askSMTSolver(quantifierData.constraints, e < boundRequired)
        return smt.check()
      }

      /* We try to find a bound for x_{i-1} (xPrev). Thus a 'low' and 'up': low_{i-1} <= x_{i-1} < up_{i-1}
       * where we have n_{i-1} = up_{i-1} - low_{i-1}
       * We do not need to check that n>0, cause in that case the quantifier would have an empty domain anyway.
       * (Both the original one and the resulting one)
       * So we can assume n>0 to hold.
       * We can have the following situations:
       * 1) a_i = a_{i-1} * n_{i-1}
       *
       * For the next two checks, we first need to check that a_i and a_{i-1} are either both positive or both negative.
       * (sign(a_i) == sign(a_{i-1})
       *
       * 2) |a_{i-1}| * n_{i-1} <= |a_i|
       *    This case is almost the same as 1), but x_{i-1} is 'cut' off.
       *    E.g. (forall x1=0..2, x2=0..5; ...x[3*x2 + x1]...)
       *    is equiv to (forall x1=0..3, x2=0..5; x1<2; ... x[3*x2 + x1] ...). And this we could rewrite to:
       *    (forall x1_x2=0..3*5; (x1_x2 % 3) < 2; ... x[x1_x2]);
       * 3) This check allow us to rewrite (\forall x=0..3, y=0..5, z=0..2; 3*y+x<8 => f[8*z + 3*y + x])
       *    towards (\forall x_y_z=0..2*8; 3*((x_y_z % 8)/3) + ((x_y_z % 8) % 3)<8
       *
       *    For this case, first in linExpr we have stored: a_{i-2}*(x{i-2} - low_{i-2}) + ... + a_0*(x0 - low_0)
       *    (For i=1, linExpr == 0)
       *    Now if a_i > 0 then:
       *    we check if a_{i-1}*(x{i-1} - low_{i-2}) + ... + a_0*(x0 - low_0) < a_{i} holds
       *    And if a_i < 0 then we check if
       *    a_{i} < a_{i-1}*(x{i-1} - low_{i-2}) + ... + a_0*(x0 - low_0) holds
       */
      def findSuitableBound(
          x: Variable[Pre],
          xPrev: Variable[Pre],
          linExpr: Expr[Pre],
          sign: Option[ExpressionEqualityCheck.Sign],
      ): Option[FoundBound] = {
        val a = linearExpressions(x)
        val aLast = linearExpressions(xPrev)
        val hasSameSign = equalityChecker.isSameSign(a, aLast).getOrElse(false)

        var otherUpperBounds: Set[Expr[Pre]] =
          quantifierData.upperExclusiveBounds(xPrev).toSet
        var otherLowerBounds: Set[Expr[Pre]] =
          quantifierData.lowerBounds(xPrev).toSet
        var otherNeededBounds: Set[Expr[Pre]] = Set()

        for (up <- quantifierData.upperExclusiveBounds(xPrev)) {
          for (low <- quantifierData.lowerBounds(xPrev)) {
            val nLastCandidate = simplifiedMinus(up, low)
            val n_is_pos = equalityChecker.lowerBound(nLastCandidate)
              .exists(_ > 0)

            // Check 1
            val rhs = simplifiedMult(aLast, nLastCandidate)
            val smt = askSMTSolver(quantifierData.constraints, Eq(a, rhs))
            if (equalityChecker.equalExpressions(a, rhs) || smt.check()) {
              // For this check, it doesn't matter that n could be zero.
              // But if it is possibly zero, we need to make sure the quantifier domain is empty
              if (!n_is_pos) {
                otherNeededBounds += (nLastCandidate > const(0))
              }
              otherUpperBounds = otherUpperBounds - up
              otherLowerBounds = otherLowerBounds - low

              val linLast = simplifiedPlus(
                simplifiedMult(aLast, simplifiedMinus(Local(xPrev.ref), low)),
                linExpr,
              )
              return Some(FoundBound(
                otherLowerBounds,
                otherUpperBounds,
                otherNeededBounds,
                low,
                linLast,
              ))
            }
            // |a_{i-1}| * n_{i-1} <= |a_i|
            // Check 2
            val right = simplifiedMult(abs(aLast, sign), nLastCandidate)
            val left = abs(a, sign)
            val smt2 = askSMTSolver(quantifierData.constraints, right <= left)
            if (
              hasSameSign &&
              (equalityChecker.lessThenEq(right, left).getOrElse(false) ||
                smt2.check())
            ) {
              // Same here
              if (!n_is_pos) {
                otherNeededBounds += (nLastCandidate > const(0))
              }
              // This is also valid, we take a stride of a_i, but in that case it will stop earlier
              // So we do not remove the upperbound we found
              otherLowerBounds = otherLowerBounds - low
              val linLast = simplifiedPlus(
                simplifiedMult(aLast, simplifiedMinus(Local(xPrev.ref), low)),
                linExpr,
              )
              return Some(FoundBound(
                otherLowerBounds,
                otherUpperBounds,
                otherNeededBounds,
                low,
                linLast,
              ))
            }
          }
        }

        // Check 3
        // If we have something like f[8*z + 3*y + x] and the bound 3*y+x<8, we are valid as well
        // In this case we have to check that ai is not zero
        if (
          hasSameSign && sign.isDefined &&
          equalityChecker.isNonZero(a).getOrElse(false)
        ) {
          for (low <- quantifierData.lowerBounds(xPrev)) {
            val linLast = simplifiedPlus(
              simplifiedMult(aLast, simplifiedMinus(Local(xPrev.ref), low)),
              linExpr,
            )
            if (
              (!equalityChecker.isPos(sign.get) ||
                isExprUpperBounded(linLast, a)) &&
              (equalityChecker.isPos(sign.get) ||
                isExprUpperBounded(a, linLast))
            ) {
              otherLowerBounds = otherLowerBounds - low
              return Some(FoundBound(
                otherLowerBounds,
                otherUpperBounds,
                otherNeededBounds,
                low,
                linLast,
              ))
            }
          }
        }

        None
      }

      def getPlusses(e: Expr[Pre]): (Seq[Expr[Pre]], BigInt) = {
        e match {
          case Plus(e1, e2) =>
            val (s1, i1) = getPlusses(e1)
            val (s2, i2) = getPlusses(e2)
            (s1 ++ s2, i1 + i2)
          case e =>
            equalityChecker.isConstantInt(e) match {
              case Some(i) => (Seq(), i)
              case None => (Seq(e), 0)
            }
        }
      }

      def getMults(e: Expr[Pre]): (Seq[Expr[Pre]], BigInt) = {
        e match {
          case Mult(e1, e2) =>
            val (s1, i1) = getMults(e1)
            val (s2, i2) = getMults(e2)
            (s1 ++ s2, i1 * i2)
          case e =>
            equalityChecker.isConstantInt(e) match {
              case Some(i) => (Seq(), i)
              case None => (Seq(e), 1)
            }
        }
      }

      def simplifyMult(e: Expr[Pre]): Expr[Pre] =
        getMults(e) match {
          case (Seq(), i) => IntegerValue[Pre](i)
          case (m, i) if i == 1 => m.reduce(Mult[Pre])
          case (m, i) => Mult[Pre](IntegerValue[Pre](i), m.reduce(Mult[Pre]))
        }

      def comparePlusses(
          lhs: Expr[Pre],
          rhs: Expr[Pre],
          remainingValue: BigInt,
      ): (Option[Expr[Pre]], Option[Expr[Pre]], BigInt) = {
        val (lhsP, lhsVal) = getPlusses(lhs)
        var (rhsP, rhsVal) = getPlusses(rhs)
        var remainingLeft: Seq[Expr[Pre]] = Seq()
        var i = 0;
        while (i < lhsP.size) {
          var found = false
          var j = 0
          while (j < rhsP.size && !found) {
            if (equalityChecker.equalExpressions(lhsP(i), rhsP(j))) {
              rhsP = rhsP.diff(Seq(rhsP(j)))
              found = true
            }
            j += 1
          }
          if (!found) { remainingLeft = remainingLeft ++ Seq(lhsP(i)) }
          i += 1
        }
        (
          remainingLeft.reduceOption(Plus[Pre]),
          rhsP.reduceOption(Plus[Pre]),
          remainingValue + lhsVal - rhsVal,
        )
      }

      def simplifiedMinus(
          lhsArg: Expr[Pre],
          rhsArg: Expr[Pre],
          remainingValue: BigInt = 0,
      ): Expr[Pre] = {
        val (lhs, rhs, value) =
          comparePlusses(lhsArg, rhsArg, remainingValue) match {
            case (Some(lhs), Some(rhs), value) => (lhs, rhs, value)
            case (None, Some(rhs), value) =>
              if (value != 0)
                return IntegerValue[Pre](value) - rhs
              else
                return IntegerValue[Pre](-1) * rhs
            case (Some(lhs), None, value) =>
              if (value != 0)
                return IntegerValue[Pre](value) + lhs
              else
                return lhs
            case (None, None, value) => return IntegerValue[Pre](value)
          }

        (lhs, rhs) match {
          case (Mult(l1, r1), Mult(l2, r2)) =>
            if (equalityChecker.equalExpressions(l1, l2))
              return Mult(l1, simplifiedMinus(r1, r2, value))
            else if (equalityChecker.equalExpressions(l1, r2))
              return Mult(l1, simplifiedMinus(r1, l2, value))
            else if (equalityChecker.equalExpressions(r1, l2))
              return Mult(r1, simplifiedMinus(l1, r2, value))
            else if (equalityChecker.equalExpressions(r1, r2))
              return Mult(r1, simplifiedMinus(l1, l2, value))
          case _ =>
        }

        if (value != 0)
          IntegerValue[Pre](value) + Minus(lhs, rhs)
        else
          Minus(lhs, rhs)
      }

      def simplifiedPlus(lhs: Expr[Pre], rhs: Expr[Pre]): Expr[Pre] = {
        (
          equalityChecker.isConstantInt(lhs),
          equalityChecker.isConstantInt(rhs),
        ) match {
          case (Some(l), Some(r)) => IntegerValue(l + r)
          case (_, Some(r)) if r == 0 => lhs
          case (Some(l), _) if l == 0 => rhs
          case _ => Plus(lhs, rhs)
        }
      }

      def simplifiedMult(lhs: Expr[Pre], rhs: Expr[Pre]): Expr[Pre] = {
        if (is_value(lhs, 1))
          rhs
        else if (is_value(rhs, 1))
          lhs
        else if (is_value(lhs, 0) || is_value(rhs, 0))
          const(0)
        else
          Mult(lhs, rhs)
      }

      def simplify(e: Expr[Pre]): Expr[Pre] =
        getPlusses(e) match {
          case (Seq(), i) => IntegerValue[Pre](i)
          case (plusses, i) =>
            val res = plusses.map(simplifyMult).reduce(Plus[Pre])
            if (i == 0)
              res
            else
              Plus(IntegerValue[Pre](i), res)
        }

      def isConstant(node: Expr[Pre]): Boolean =
        indepOf(quantifierData.bindings, node)

      def addToConstant(node: Expr[Pre], isPlus: Boolean = true): Unit = {
        val added_node: Expr[Pre] =
          currentMultiplier match {
            case None => node
            case Some(expr) => Mult(expr, node)
          }
        constantExpression = Some(constantExpression match {
          case None =>
            if (isPlus)
              added_node
            else
              Mult(IntegerValue(-1), added_node)
          case Some(expr) =>
            if (isPlus)
              Plus(expr, added_node)
            else
              Minus(expr, added_node)
        })
      }

      def multiplyMultiplier(node: Expr[Pre]): Unit = {
        currentMultiplier match {
          case None => currentMultiplier = Some(node);
          case Some(expr) => currentMultiplier = Some(Mult(expr, node))
        }
      }

      def is_value(e: Expr[Pre], x: Int): Boolean =
        equalityChecker.isConstantInt(e) match {
          case None => false
          case Some(y) => y == x
        }
    }
  }

  // The `newBounds`, will contain all the new equations for "select" part of the forall.
  // The `substituteOldVars` contains a map, so we can replace the old forall variables with new expressions
  // We also store the `linearExpression`, so if we ever come across it, we can replace it with the new variable.
  case class SubstituteForall(
      newBounds: Expr[Post],
      substituteOldVars: Map[Variable[Pre], Expr[Post]],
      substituteIndex: (Expr[Pre], Expr[Post]),
  )
}

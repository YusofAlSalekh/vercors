package vct.col.rewrite

import vct.col.ast._
import vct.col.origin.{Blame, Origin, PointerLocationError, TypeName}
import vct.result.VerificationError.UserError

case object DisambiguateLocation extends RewriterBuilder {

  private case class NotALocation(expr: Expr[_]) extends UserError {
    override def code: String = "notALocation"

    private def hint: Option[String] =
      expr match {
        case PointerSubscript(_, _) =>
          Some(" (Hint: perhaps you meant to prepend `&`)")
        case DerefPointer(_) =>
          Some(" (Hint: perhaps you meant to prepend `&`)")
        case _ => None
      }

    override def text: String =
      expr.o.messageInContext(
        "This expression is not a heap location." + hint.getOrElse("")
      )
  }

  private case class InvalidPatternLocation(expr: Expr[_], cls: Class[_])
      extends UserError {
    override def code: String = "byValueClassLocationPattern"

    override def text: String =
      expr.o.messageInContext(
        s"A ${cls.o.find[TypeName].map(_.name).getOrElse("class")} value (which will be expanded to permissions for every field) is not allowed in a trigger pattern"
      )
  }

  override def key: String = "disambiguateLocation"

  override def desc: String =
    "Translate ambiguous location type into concrete location type."
}

case class DisambiguateLocation[Pre <: Generation]() extends Rewriter[Pre] {
  import DisambiguateLocation._

  private def exprToLoc(expr: Expr[Pre], blame: Blame[PointerLocationError])(
      implicit o: Origin
  ): Location[Post] =
    expr match {
      case expr if expr.t.asPointer.isDefined =>
        PointerLocation(dispatch(expr))(blame)
      case expr if expr.t.asByValueClass.isDefined =>
        ByValueClassLocation(dispatch(expr))(blame)
      case DerefHeapVariable(ref) => HeapVariableLocation(succ(ref.decl))
      case Deref(obj, ref) => FieldLocation(dispatch(obj), succ(ref.decl))
      case ModelDeref(obj, ref) => ModelLocation(dispatch(obj), succ(ref.decl))
      case SilverDeref(obj, ref) =>
        SilverFieldLocation(dispatch(obj), succ(ref.decl))
      case expr @ ArraySubscript(arr, index) =>
        ArrayLocation(dispatch(arr), dispatch(index))(expr.blame)
      case PredicateApplyExpr(inv) => PredicateLocation(dispatch(inv))
      case InlinePattern(inner, pattern, group) =>
        if (inner.t.asByValueClass.isDefined) {
          throw InvalidPatternLocation(
            expr,
            inner.t.asByValueClass.get.cls.decl,
          )
        }
        InLinePatternLocation(
          exprToLoc(inner, blame),
          InlinePattern(dispatch(inner), pattern, group)(expr.o),
        )(expr.o)

      case default => throw NotALocation(default)
    }

  override def dispatch(loc: Location[Pre]): Location[Post] =
    loc match {
      case location @ AmbiguousLocation(expr) =>
        exprToLoc(expr, location.blame)(loc.o)
      case other => super.dispatch(other)
    }
}

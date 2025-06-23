package vct.col.ast.expr.heap.read

import vct.col.ast.{PointerAdd, PointerArrayType, TPointer, TPointerArray, Type}
import vct.col.print._
import vct.col.ast.ops.PointerAddOps

trait PointerAddImpl[G] extends PointerAddOps[G] {
  this: PointerAdd[G] =>
  override def t: Type[G] =
    pointer.t match {
      case a: PointerArrayType[G] => TPointer(a.element, a.unique)
      case t => t
    }

  override def precedence: Int = Precedence.ADDITIVE
  override def layout(implicit ctx: Ctx): Doc = lassoc(pointer, "+", offset)
}

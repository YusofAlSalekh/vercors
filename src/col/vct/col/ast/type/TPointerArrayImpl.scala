package vct.col.ast.`type`

import vct.col.ast.TPointerArray
import vct.col.ast.ops.TPointerArrayOps
import vct.col.print._

trait TPointerArrayImpl[G] extends TPointerArrayOps[G] {
  this: TPointerArray[G] =>
  override def layout(implicit ctx: Ctx): Doc =
    dimensions.foldLeft[Doc](element.show) { case (l, r) =>
      l <> "[" <> r <> "]"
    }
}

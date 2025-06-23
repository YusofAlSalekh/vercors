package vct.col.ast.family.coercion

import vct.col.ast.ops.CoerceConstPointerPointerArrayOps
import vct.col.ast.{CoerceConstPointerPointerArray, TConstPointerArray}

trait CoerceConstPointerPointerArrayImpl[G]
    extends CoerceConstPointerPointerArrayOps[G] {
  this: CoerceConstPointerPointerArray[G] =>
  override def target: TConstPointerArray[G] =
    TConstPointerArray(elementType, dimensions)
}

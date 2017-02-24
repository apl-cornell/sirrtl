package firrtl.passes

import firrtl._
import firrtl.ir._
import firrtl.Mappers._

// This should convert all expressions within labels to the WIR, but leave 
// actual expressions (that reside directly in statements) as they are.
object DepsToWorkingIR extends ToWorkingIRT {
  override def name = "Dep Expressions to Working IR"
  override def toLbl(l: Label): Label = l map toLblComp map toLbl
  def toLblComp(lc: LabelComp): LabelComp =
    lc map toExp map toLblComp
}

// This should resolve the kinds of expressions within labels, but leave 
// actual expressions (that reside directly in statements) as they are.
// It is particularly important that this object does not attempt to resolve 
// kinds of "actual expressions" because at this phase Next(ids) have been
// converted to references which have not yet been declared!
object DepsResolveKinds extends ResolveKindsT {
  override def name = "Resolve Kinds of Dep Expressions"
  override def resolve_lbl(kinds: KindMap)(l: Label): Label = 
    l map resolve_lbl_cmp(kinds) map resolve_lbl(kinds)
  def resolve_lbl_cmp(kinds: KindMap)(l: LabelComp): LabelComp = 
    l map resolve_lbl_cmp(kinds) map resolve_expr(kinds)
}

object DepsInferTypes extends InferTypesT {
  override def name = "Infer Types for Dependands"
  override def infer_types_l(types: TypeMap)(l: Label): Label =
    l map infer_types_lc(types) map infer_types_l(types)
  def infer_types_lc(types: TypeMap)(l: LabelComp): LabelComp =
    l map infer_types_e(types) map infer_types_lc(types)
}

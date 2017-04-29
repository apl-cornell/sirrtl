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

object DepsResolveKinds extends ResolveKindsT with PassDebug {
  override def name = "Resolve Kinds of Dep Expressions"
  override def debugThisPass = false 

  def printExprs(l: LabelComp): LabelComp = {
    def pex(e: Expression): Expression = {
      println(e.toString)
      e
    }
    l map printExprs map pex
  }

  override def resolve_lbl(kinds: KindMap)(l: Label): Label = 
    l map resolve_lbl_cmp(kinds) map resolve_lbl(kinds)
  def resolve_lbl_cmp(kinds: KindMap)(l: LabelComp): LabelComp = {
    l map resolve_lbl_cmp(kinds) map resolve_expr(kinds)
  }
}

object DepsInferTypes extends InferTypesT {
  override def name = "Infer Types for Dependands"
  override def infer_types_l(types: TypeMap)(l: Label): Label =
    l map infer_types_lc(types) map infer_types_l(types)
  def infer_types_lc(types: TypeMap)(l: LabelComp): LabelComp =
    l map infer_types_e(types) map infer_types_lc(types)
}

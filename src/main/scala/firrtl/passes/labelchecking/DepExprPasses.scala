package firrtl.passes

import firrtl._
import firrtl.ir._
import firrtl.Mappers._
import firrtl.Utils._

// This should convert all expressions within labels to the WIR, but leave 
// actual expressions (that reside directly in statements) as they are.
//
// AF: These passes no longer do any checking within bundle labels because 
// doing so is computationally expensive, and as it turns out, unnecessary; 
// these passes are only relevant for: 1) getting kinds for dependands for
// the sequence of passes that perform next-cycle transforms, 2) getting types 
// for VecTypes which is necessary to properly apply indexing expressions 
// during the apply vec labels pass
object DepsToWorkingIR extends Pass with PassDebug {
  override def name = "Dep Expressions to Working IR"
  def toLbl(l: Label): Label = l  match {
    case lx: BundleLabel => lx
    case lx => lx map toLbl map toLblComp
  }
  def toLblComp(lc: LabelComp): LabelComp = lc map toExp map toLblComp

  def toExp(e: Expression): Expression = e map toExp match {
    case ex: Reference => WRef(ex.name, ex.tpe, ex.lbl, NodeKind, UNKNOWNGENDER)
    case ex: SubField => WSubField(ex.expr, ex.name, ex.tpe, ex.lbl, UNKNOWNGENDER)
    case ex: SubIndex => WSubIndex(ex.expr, ex.value, ex.tpe, ex.lbl, UNKNOWNGENDER)
    case ex: SubAccess => WSubAccess(ex.expr, ex.index, ex.tpe, ex.lbl, UNKNOWNGENDER)
    case ex => ex // This might look like a case to use case _ => e, DO NOT!
  }

  def toExpL(e: Expression): Expression =
    toExp(e) map toExpL map toLbl

  def toStmt(s: Statement): Statement = s map toExpL map toLbl match {
    case sx: DefInstance => WDefInstance(sx.info, sx.name, sx.module, UnknownType, UnknownLabel)
    case sx => sx map toStmt
  }

  def run (c:Circuit): Circuit =
    c copy (modules = c.modules map (_ map toStmt))
}

object DepsResolveKinds extends ResolveKindsT {
  override def name = "Resolve Kinds of Dep Expressions"
  override def debugThisPass = false

  def printExprs(l: LabelComp): LabelComp = {
    
    def pex(e: Expression): Expression = {
      dprint(e.serialize)
      dprint(s"kind: ${kind(e)}")
      e
    }
    l map printExprs map pex
  }

  override def resolve_lbl(kinds: KindMap)(l: Label): Label =
    l match {
      case lx: BundleLabel => lx
      case lx => lx map resolve_lbl(kinds) map resolve_lbl_cmp(kinds)
    }
  def resolve_lbl_cmp(kinds: KindMap)(l: LabelComp): LabelComp = {
    l map resolve_expr(kinds) map resolve_lbl_cmp(kinds)
  }
}

object DepsInferTypes extends InferTypesT {
  override def name = "Infer Types for Dependands"
  override def infer_types_l(types: TypeMap)(l: Label): Label =
    l match {
      case lx: BundleLabel => lx
      case lx => lx map infer_types_l(types) map infer_types_lc(types)
    }
  def infer_types_lc(types: TypeMap)(l: LabelComp): LabelComp =
    l map infer_types_e(types) map infer_types_lc(types)
}

package firrtl.passes

import firrtl._
import firrtl.ir._
import firrtl.Mappers._

// This code is now vestigial, but I will add it into the commit history since 
// it may be useful in the future

// This should convert all expressions within labels to the WIR, but leave 
// actual expressions (that reside directly in statements) as they are.
object DepsToWorkingIR extends ToWorkingIRT {
  override def name = "Dep Expressions to Working IR"
  override def toLbl(l: Label): Label = l map toExp map toLbl

  override def toStmt(s: Statement): Statement =
    s mapExpr { _ mapLabel toLbl } map toLbl

}

// This should resolve the kinds of expressions within labels, but leave 
// actual expressions (that reside directly in statements) as they are.
// It is particularly important that this object does not attempt to resolve 
// kinds of "actual expressions" because at this phase Next(ids) have been
// converted to references which have not yet been declared!
object DepsResolveKinds extends ResolveKindsT {
  override def name = "Resolve Kinds of Dep Expressions"
 
  override def resolve_lbl(kinds: KindMap)(l: Label): Label = 
    l map resolve_expr_(kinds) map resolve_lbl(kinds)

  // This is called on expressions which are rooted in labels. It should appear 
  // identical to resolve_expr_. Simply using super.resolve_expr in the body of 
  // resolve_lbl would not suffice, because it would not recurse as desired 
  // since the recursive calls would use DepResolveKinds.resolve_expr which is 
  // meant to leave expressions untouched.
  def resolve_expr_(kinds: KindMap)(e: Expression): Expression = 
    e map resolve_lbl(kinds) match {
    case ex: WRef => ex copy (kind = kinds(ex.name))
    case _ => e map resolve_expr_(kinds)
  }

  override def resolve_expr(kinds: KindMap)(e: Expression): Expression =
    e map resolve_lbl(kinds)

  override def resolve_stmt(kinds: KindMap)(s: Statement): Statement =
    s map resolve_stmt(kinds) map resolve_expr(kinds) map resolve_lbl(kinds)

}

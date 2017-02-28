package firrtl
import firrtl.ir._

// These statements are similar to their non-PC counterparts, except that they 
// include a PC label. These were added to avoid changing uses of case classes 
// all over the code.

case class PartialConnectPC(info: Info, loc: Expression, expr: Expression, pc: Label) extends Statement with HasInfo {
  def serialize: String =  s"[${pc.serialize}] ${loc.serialize} <- ${expr.serialize}" + info.serialize
  def mapStmt(f: Statement => Statement): Statement = this
  def mapExpr(f: Expression => Expression): Statement = PartialConnectPC(info, f(loc), f(expr), pc)
  def mapType(f: Type => Type): Statement = this
  def mapString(f: String => String): Statement = this
  def mapLabel(f: Label => Label): Statement = this
}

case class ConnectPC(info: Info, loc: Expression, expr: Expression, pc: Label) extends Statement with HasInfo {
  // def serialize: String =  s"${loc.serialize} <= ${expr.serialize}" + info.serialize
  def serialize: String = {
    val lbl_l = loc.lbl match { case UnknownLabel => ""; case _ => s" {${loc.lbl.serialize}}" }
    val lbl_r = expr.lbl match { case UnknownLabel => ""; case _ => s" {${expr.lbl.serialize}}" }
    s"[${pc.serialize}] ${loc.serialize}${lbl_l} <= ${expr.serialize}${lbl_r}" + info.serialize
  }
  def mapStmt(f: Statement => Statement): Statement = this
  def mapExpr(f: Expression => Expression): Statement = ConnectPC(info, f(loc), f(expr), pc)
  def mapType(f: Type => Type): Statement = this
  def mapString(f: String => String): Statement = this
  def mapLabel(f: Label => Label): Statement = this
}

case class DefNodePC(info: Info, name: String, value: Expression, pc: Label) extends Statement with IsDeclaration {
  def serialize: String = s"[${pc.serialize}] node $name = ${value.serialize}" + info.serialize
  def mapStmt(f: Statement => Statement): Statement = this
  def mapExpr(f: Expression => Expression): Statement = DefNodePC(info, name, f(value), pc)
  def mapType(f: Type => Type): Statement = this
  def mapString(f: String => String): Statement = DefNodePC(info, f(name), value, pc)
  def mapLabel(f: Label => Label): Statement = this
}

package firrtl
import firrtl.ir._
import Utils.indent

// These statements are similar to their non-PC counterparts, except that they 
// include a PC label. These were added to avoid changing uses of case classes 
// all over the code.

case class PartialConnectPC(info: Info, loc: Expression, expr: Expression, pc: Label) extends Statement with HasInfo {
  def serialize: String = {
    val lbl_l = loc.lbl match { case UnknownLabel => ""; case _ => s" {${loc.lbl.serialize}}" }
    val lbl_r = expr.lbl match { case UnknownLabel => ""; case _ => s" {${expr.lbl.serialize}}" }
    s"[${pc.serialize}] ${loc.serialize}${lbl_l} <= ${expr.serialize}${lbl_r}" + info.serialize
  }
  def mapStmt(f: Statement => Statement): Statement = this
  def mapExpr(f: Expression => Expression): Statement = PartialConnectPC(info, f(loc), f(expr), pc)
  def mapType(f: Type => Type): Statement = this
  def mapString(f: String => String): Statement = this
  def mapLabel(f: Label => Label): Statement = this.copy(pc = f(pc))
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
  def mapLabel(f: Label => Label): Statement = this.copy(pc = f(pc))
}

case class DefNodePC(info: Info, name: String, value: Expression, lbl: Label, pc: Label) extends Statement with IsDeclaration {
  val lbl_s = lbl match {case UnknownLabel => ""; case _ => s"{${lbl.serialize}} "}
  def serialize: String = s"[${pc.serialize}] node $name ${lbl_s}= ${value.serialize}" + info.serialize
  def mapStmt(f: Statement => Statement): Statement = this
  def mapExpr(f: Expression => Expression): Statement = this.copy(value = f(value))
  def mapType(f: Type => Type): Statement = this
  def mapString(f: String => String): Statement = this.copy(name = f(name))
  def mapLabel(f: Label => Label): Statement = this.copy(pc = f(pc), lbl = f(lbl))
}

case class ConditionallyPC(
    info: Info,
    pred: Expression,
    conseq: Statement,
    alt: Statement,
    pc: Label) extends Statement with HasInfo {
  def serialize: String =
    s"when ${pred.serialize} :" + info.serialize +
    indent("\n" + conseq.serialize) +
    (if (alt == EmptyStmt) ""
    else "\nelse :" + indent("\n" + alt.serialize))
  def mapStmt(f: Statement => Statement): Statement = Conditionally(info, pred, f(conseq), f(alt))
  def mapExpr(f: Expression => Expression): Statement = Conditionally(info, f(pred), conseq, alt)
  def mapType(f: Type => Type): Statement = this
  def mapString(f: String => String): Statement = this
  def mapLabel(f: Label => Label): Statement = this.copy(pc = f(pc))
}

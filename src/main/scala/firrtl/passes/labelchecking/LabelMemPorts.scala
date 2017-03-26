package firrtl.passes

import firrtl._
import firrtl.ir._
import firrtl.Utils._
import firrtl.Mappers._

// Label memory ports in the CHIRRTL phase since memories in this form are 
// actually easier to think about...
object LabelMPorts extends Pass with PassDebug {
  def name = "Determine memory port labels"
  override def debugThisPass = false
  type LabelMap = collection.mutable.LinkedHashMap[String, Label]

  val bot = ProdLabel(PolicyHolder.bottom, PolicyHolder.top)
  val top = ProdLabel(PolicyHolder.top, PolicyHolder.bottom)

  class UndeclaredException(info: Info, name: String) extends PassException(
    s"$info: [declaration $name] does not have a declared label")
  class UnknownLabelException(info: Info, name: String) extends PassException(
    s"$info: a label could not be determined for [$name]")
  val errors = new Errors()

  def label_is_known(l: Label): Boolean = LabelExprs.label_is_known(l)

  def checkDeclared(l: Label, i: Info, n: String) = 
    if(!label_is_known(l))
      errors.append(new UndeclaredException(i, n))

  def label_mports_s(labels: LabelMap)(s: Statement): Statement = s match {
    case sx: CDefMemory => 
      checkDeclared(sx.lbl, sx.info, sx.name)
      labels(sx.name) = sx.lbl
      sx
    case sx: CDefMPort =>
      val lb = labels getOrElse(sx.mem, UnknownLabel)
      checkDeclared(lb, sx.info, sx.mem)
      sx copy (lbl = lb)
    case sx => sx map label_mports_s(labels)
  }

  def label_mports(m: DefModule): DefModule = {
    m map label_mports_s(new LabelMap)
  }

  def run(c: Circuit) = {
    bannerprintb(name)
    dprint(c.serialize)

    val cprime = c copy (modules = c.modules map label_mports)

    bannerprintb(s"after $name")
    dprint(cprime.serialize)
 
    errors.trigger()
    cprime
  }


}

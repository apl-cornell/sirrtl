package firrtl.passes

import firrtl._
import firrtl.ir._
import firrtl.Utils._
import firrtl.Mappers._
import firrtl.Driver._

object CheckDepKinds extends Pass with PassDebug {
  def name = "Check Dep Expr Kinds"
  override def debugThisPass = true

  class NonSeqDepException(info: Info, name: String) extends PassException(
    s"$info: Something other than a sequential variable ($name) was used in a dependent type. This is not supported")
  val errors = new Errors()

  // Note that this function is only ever called on expressions appearing 
  // within labels
  def check_dep_kinds_le(info: Info)(e: Expression) : Expression =
    e map check_dep_kinds_le(info) match {
      case ex: WRef =>
        dprint(ex.toString)
        if( ex.kind != RegKind)
          errors.append( new NonSeqDepException(info, ex.name) )
        ex
      case ex =>
        dprint(ex.toString)
          errors.append( new NonSeqDepException(info, ex.serialize) )
          ex
  }

  def check_dep_kinds_l(info: Info)(l: Label) : Label = {
    dprint(l.toString)
    l map check_dep_kinds_l(info) map check_dep_kinds_le(info)
  }

  def check_dep_kinds_s(s: Statement) : Statement =
    s map check_dep_kinds_s map check_dep_kinds_l(s.info)

  def check_dep_kinds(m: DefModule) : DefModule =
    m map check_dep_kinds_s

  def run(c: Circuit): Circuit = {
    bannerprintb(name)
    dprint(c.serialize)

    val cprime = c copy (modules =
      c.modules map check_dep_kinds)

    bannerprintb(s"after $name")
    dprint(cprime.serialize)
    
    errors.trigger()
    cprime
  }
}

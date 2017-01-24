package firrtl.passes

import firrtl._
import firrtl.ir._
import firrtl.Utils._
import firrtl.Mappers._
import firrtl.Driver._


// This pass replaces all expressions of the form next(id) with a reference to 
// the next-cycle updated version of the id.
object PullNexts extends Pass with PassDebug {
  def name = "Pull Nexts"
  override def debugThisPass = true

  def next_ident(n: String) = NextCycleTransform.next_ident(n)

  class FemaleNextException(info: Info, name: String) extends PassException(
    s"$info: an attempt was made to assign to next-value next($name)")
  class IllegalNextException(info: Info, name: String) extends PassException(
    s"$info: Illegal next expression: next($name). Are you sure that $name is sequential?")
  val errors = new Errors()

  type NextCtx = collection.mutable.HashMap[String,DefRegister]

  def pull_next_e(nctx: NextCtx, info: Info)(e: Expression): Expression = e
  /*
    e map pull_next_e(nctx, info) match {
      case Next(ne, tpe, lbl, MALE) => 
        if(!nctx.contains(id)) {
          errors.append(new IllegalNextException(info, id))
          Next(id, tpe, lbl, MALE)
        } else
          WRef(next_ident(id), tpe, lbl, RegKind, MALE)
      case Next(id, tpe, lbl, FEMALE) =>
        errors.append(new FemaleNextException(info, id))
        Next(id, tpe, lbl, FEMALE)
      case ex => ex
    }
    */

  def pull_next_s(nctx: NextCtx)(s: Statement): Statement =
    s map pull_next_s(nctx) map pull_next_e(nctx, s.info) match {
      case sx : DefRegister => nctx += (sx.name -> sx); sx
      case sx => sx
    }

  def pull_next(m: DefModule): DefModule =
    m map pull_next_s(new NextCtx)

  def run(c: Circuit): Circuit = {
    bannerprintb(name)
    dprint(c.serialize)

    val cprime = c copy (modules =
      c.modules map pull_next)
    
    bannerprintb(s"after $name")
    dprint(cprime.serialize)
    
    errors.trigger()
    cprime
  }


}

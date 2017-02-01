package firrtl.passes
import firrtl._
import firrtl.ir._
import firrtl.Utils._
import firrtl.Mappers._
import firrtl.Driver._

//-----------------------------------------------------------------------------
// SeqPortGenNext
//-----------------------------------------------------------------------------
// Auto-generate the connection for next-cycle output ports
// Does not check that next-cycle output ports are not assigned by the 
// programmer, just assumes the programmer is well-behaved enough not to.
object SeqPortGenNext extends Pass with PassDebug {
  def name = "SeqPortGenNext"
  override def debugThisPass = false

  type Exprs = scala.collection.mutable.HashSet[Expression]

  // Methods borrowed from other passes
  def collect_seq_out(m: DefModule): Exprs = SeqPortCheck.collect_seq_out(m)
  def next_exp(e: Expression) : Expression = PullNexts.next_exp(e)
 
  def sp_gen_next(m: DefModule) : DefModule = m match {
    case mx : Module =>
      val so = collect_seq_out(mx)
      val mprime = (mx map sp_gen_next_s(so)).asInstanceOf[Module]
      mprime copy (body = flatten_s(mprime.body))
    case mx => mx
  }

  def sp_gen_next_s(so: Exprs)(s: Statement) : Statement = 
    s map sp_gen_next_s(so) match {
      case sx : Connect if so.contains(sx.loc) =>
        Block(Seq(Connect(sx.info, next_exp(sx.loc), next_exp(sx.expr)), sx))
      case sx => sx
    }

  def run(c: Circuit) = {
    bannerprintb(s"before $name")
    dprint(c.serialize)
    val cprime = c copy(modules = c.modules map sp_gen_next)
    bannerprintb(s"after $name")
    dprint(cprime.serialize)
    cprime
  }

}

package firrtl.passes
import firrtl._
import firrtl.ir._
import firrtl.Utils._
import firrtl.Mappers._
import firrtl.Driver._

//-----------------------------------------------------------------------------
// SeqPortGenNext
//-----------------------------------------------------------------------------
// Auto-generate the connection and declaration for next-cycle output ports
// Does not check that next-cycle output ports are not assigned by the 
// programmer, just assumes the programmer is well-behaved enough not to.
object SeqPortGenNext extends Pass with PassDebug {
  def name = "SeqPortGenNext"
  override def debugThisPass = false

  type Exprs = scala.collection.mutable.HashSet[Expression]

  // Methods borrowed from other passes
  def collect_seq_out(m: DefModule): Exprs = SeqPortCheck.collect_seq_out(m)
  def next_exp(e: Expression) : Expression = RipNexts.next_exp(e)
 
  def sp_gen_next(m: DefModule) : DefModule = m match {
    case mx : Module =>
      val so = collect_seq_out(mx)
      val pPrime = mx.ports map sp_gen_next_p
      val mprime = (mx map sp_gen_next_s(so)).asInstanceOf[Module]
      mprime copy (body = flatten_s(mprime.body), ports = pPrime)
    case mx => mx
  }

  def sp_gen_next_f(f: Field) : Seq[Field] = {
    val ntp = f.tpe match {
      case tp: BundleType =>
       BundleType(tp.fields flatMap sp_gen_next_f)
      case _ =>
        f.tpe
    }
    val nf = f copy(tpe = ntp)
    if (nf.isSeq) {
      Seq(nf)
    } else {
      Seq(nf)
    }
  }
  def sp_gen_next_p(p: Port) : Port = {
    val ptype = p.tpe match {
      case bt: BundleType => BundleType(bt.fields flatMap sp_gen_next_f)
      case _ => p.tpe
    }
    p copy(tpe = ptype)
  }

  def sp_gen_next_s(so: Exprs)(s: Statement) : Statement = 
    s map sp_gen_next_s(so) match {
      case sx : ConnectPC if so.contains(sx.loc) =>
        Block(Seq(ConnectPC(sx.info, next_exp(sx.loc), next_exp(sx.expr), sx.pc), sx))
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

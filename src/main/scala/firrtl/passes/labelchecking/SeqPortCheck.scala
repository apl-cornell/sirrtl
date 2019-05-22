package firrtl.passes
import firrtl._
import firrtl.ir._
import firrtl.Utils._
import firrtl.Mappers._
import firrtl.Driver._

//-----------------------------------------------------------------------------
// SeqPortCheck
//-----------------------------------------------------------------------------
// Check that port fields declared sequential are in fact sequential.
// This is done by checking that in the Connection Environment, the port is 
// mapped exactly to an atom which represents either: a sequential port which is
// an input, or a register

// TODO mems are sequential too!!

object SeqPortCheck extends LabelPass with LabelPassDebug {
  def name = "SeqPortCheck"
  override def debugThisPass = false
  var conGen : ConstraintGenerator = BVConstraintGen

  // TODO for better error keep info with seq outs
  class BadSeqOutConException( l: Constraint, r: Constraint) extends PassException(
      s"seq out connected to something other than seq loc: ${l.serialize} <- ${r.serialize}")
  class NoSeqOutConException( l: Constraint) extends PassException(
      s"seq out not defined: ${l.serialize}")
  val errors = new Errors()

  //-----------------------------------------------------------------------------
  // Collect Sequential Outputs
  //-----------------------------------------------------------------------------
  type Exprs = scala.collection.mutable.HashSet[Expression]
  def collect_seq_out(m: DefModule) : Exprs = { 
    val sa = new Exprs
    m map collect_seq_out_s(sa)
    sa
  }

  def collect_seq_out_s(sa: Exprs)(s: Statement) : Statement =
    s map collect_seq_out_e(sa) map collect_seq_out_s(sa)

  def collect_seq_out_e(sa: Exprs)(e: Expression) : Expression =
    e map collect_seq_out_e(sa) match {
      case ex : WSubField if kind(ex) == PortKind && gender(ex) == FEMALE
        && field_seq(ex.exp.tpe, ex.name) => sa += ex; ex
      case ex => ex
    }

  //-----------------------------------------------------------------------------
  // Collect Sequential Locations
  //-----------------------------------------------------------------------------
  // Collect defined registers
  // Collect module inputs which are sequential
  def collect_seq_loc(m: DefModule) : Exprs = {
      val sa = new Exprs
      m map collect_seq_loc_s(sa)
      sa
  }

  def collect_seq_loc_s(sa: Exprs)(s: Statement) : Statement = 
    s map collect_seq_loc_e(sa) map collect_seq_loc_s(sa) 

  def collect_seq_loc_e(sa: Exprs)(e: Expression) : Expression =
    e map collect_seq_loc_e(sa) match {
      case ex : WRef if kind(ex) == RegKind && gender(ex) == MALE =>
        sa += ex
        ex
      case ex : WSubField if (kind(ex) == PortKind || kind(ex) == InstanceKind) && gender(ex) == MALE
        && field_seq(ex.exp.tpe, ex.name) =>
          sa += ex
          ex
      case ex : DoPrim => ex.op match {
        case PrimOps.Bits =>
          collect_seq_loc_e(sa)(ex.args(0))
          if (sa.contains(ex.args(0))) { sa += ex }
          ex
        case _ =>
           ex
      }
      case Next(nex, _, _, _) => collect_seq_loc_e(sa)(nex)
      case ex => ex
    }

  //-----------------------------------------------------------------------------
  // Check connections to sequential outputs
  //-----------------------------------------------------------------------------
  // Particularly, that they are connected exactly to atoms that are sequential 
  // locations
  def check_seq_out(m: DefModule, conEnv: ConnectionEnv) : Unit = {
    val seq_loc = (collect_seq_loc(m) map {
      e => conGen.exprToCons(e)
    }).toSet[Constraint]
    collect_seq_out(m) foreach { e =>
        val a = conGen.exprToCons(e)
        if(!conEnv.contains(a)) errors.append(new NoSeqOutConException(a))
        else if(!seq_loc.contains(conEnv(a)._1))
            errors.append(new BadSeqOutConException(a, conEnv(a)._1))
    }
  }
  
  def run(m: DefModule, conEnv: ConnectionEnv,
    cg: ConstraintGenerator) : (DefModule, ConnectionEnv) = {
    conGen = cg
    bannerprintb(s"before $name")
    dprint(m.serialize)
    dprintConEnv(conEnv)
    val mprime = m
    val conEnvPrime = conEnv
    dprintb(s"sequential outputs:")
    dprintb(collect_seq_out(m).toString)
    dprintb(s"sequential locations:")
    dprintb(collect_seq_loc(m).toString)
    check_seq_out(m, conEnv)
    bannerprintb(s"after $name")
    dprint(m.serialize)
    dprintConEnv(conEnvPrime)
    if(debugThisPass) dprintb(s"Got errors: ${errors.errors.toString}")
    else errors.trigger()
    (m, conEnvPrime)
  }
}

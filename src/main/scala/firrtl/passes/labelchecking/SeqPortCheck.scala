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
  // Collect Atoms representing sequential output ports
  // Declared as Set[Constraint] so we can check if an object in range of ConEnv 
  // is a member of the set.
  type SeqAtoms = scala.collection.mutable.HashSet[Constraint]
  def collect_seq_out(m: DefModule) : SeqAtoms = { 
    val sa = new SeqAtoms
    m map collect_seq_out_p(sa)
    sa
  }

  def collect_seq_out_p(sa: SeqAtoms)(p: Port) : Port = p.tpe match {
    case BundleType(fields) => fields map { f: Field =>
        // Get the representation of a field from conGen
        val pr = WRef(p.name,UnknownType,p.lbl,PortKind,UNKNOWNGENDER)
        val sf = WSubField(pr,f.name,f.tpe,f.lbl,UNKNOWNGENDER)
        val atom = CAtom(conGen.refToIdent(sf))

        // if f is a seq output, add it to the set
        if(f.isSeq && f.flip == to_flip(p.direction)) sa += atom
      }; p
    case _ => p
      // The only way to mark a port sequential is by a field.
  }
  
  //-----------------------------------------------------------------------------
  // Collect Sequential Locations
  //-----------------------------------------------------------------------------
  // Collect defined registers
  // Collect module inputs which are sequential
  def collect_seq_loc(m: DefModule) : SeqAtoms = {
      val sa = new SeqAtoms
      m map collect_seq_in_p(sa) map
        collect_seq_loc_s(sa)
      sa
  }

  def collect_seq_in_p(sa: SeqAtoms)(p: Port) : Port = p.tpe match {
    case BundleType(fields) => fields map { f: Field =>
        // Get the representation of a field from conGen
        val pr = WRef(p.name,UnknownType,p.lbl,PortKind,UNKNOWNGENDER)
        val sf = WSubField(pr,f.name,f.tpe,f.lbl,UNKNOWNGENDER)
        val atom = CAtom(conGen.refToIdent(sf))

        // if f is a seq input, add it to the set
        if(f.isSeq && f.flip != to_flip(p.direction)) sa += atom
      }; p
    case _ => p
      // The only way to mark a port sequential is by a field.
  }

  def collect_seq_loc_s(sa: SeqAtoms)(s: Statement) : Statement = 
    s map collect_seq_loc_s(sa) match {
        case s : DefRegister => 
            val ref = WRef(s.name,s.tpe,s.lbl,RegKind,UNKNOWNGENDER)
            sa += CAtom(conGen.refToIdent(ref))
            s
        case _ => s
  }

  //-----------------------------------------------------------------------------
  // Check connections to sequential outputs
  //-----------------------------------------------------------------------------
  // Particularly, that they are connected exactly to atoms that are sequential 
  // locations
  def check_seq_out(m: DefModule, conEnv: ConnectionEnv) : Unit = { 
      val seq_loc = collect_seq_loc(m)
      collect_seq_out(m) foreach { a =>
          if(!conEnv.contains(a)) errors.append(new NoSeqOutConException(a))
          else if(!seq_loc.contains(conEnv(a)))
              errors.append(new BadSeqOutConException(a, conEnv(a)))
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

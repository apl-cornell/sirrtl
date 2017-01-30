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
// mapped exactly to an Atom which represents either: a sequential port which is
// an input, or a register

object SeqPortCheck extends LabelPass with LabelPassDebug {
  def name = "SeqPortCheck"
  override def debugThisPass = true
  var conGen : ConstraintGenerator = BVConstraintGen

  // collect set of atoms representing sequential output ports
  // collect set of atoms representing valid sequential sources
  // check that all seq outputs <- seq sources in conEnv
 
  //-----------------------------------------------------------------------------
  // Collect Sequential Outputs
  //-----------------------------------------------------------------------------
  // Collect Atoms representing sequential output ports
  type SeqAtoms = scala.collection.mutable.HashSet[CAtom]
  def collect_seq(m: DefModule) : SeqAtoms = { 
    val sa = new SeqAtoms
    m map collect_seq_p(sa)
    sa
  }

  def collect_seq_p(sa: SeqAtoms)(p: Port) : Port = p.tpe match {
    case BundleType(fields) => fields map { f: Field =>
        val pr = WRef(p.name,UnknownType,p.lbl,PortKind,UNKNOWNGENDER)
        val sf = WSubField(pr,f.name,f.tpe,f.lbl,UNKNOWNGENDER)
        // if f is a seq output, add it to the set
        if(f.isSeq && f.flip == to_flip(p.direction))
          sa += CAtom(conGen.refToIdent(sf))
        dprintb(sa.toString)
      }; p
    case _ => p
      // The only way to mark a port sequential is by a field.
  }
  
  //-----------------------------------------------------------------------------
  // Collect Sequential Inputs
  //-----------------------------------------------------------------------------
  

  def run(m: DefModule, conEnv: ConnectionEnv,
    cg: ConstraintGenerator) : (DefModule, ConnectionEnv) = {
    conGen = cg
    bannerprintb(s"before $name")
    dprint(m.serialize)
    dprintConEnv(conEnv)
    val mprime = m
    val conEnvPrime = conEnv
    dprintb(s"sequential outputs:")
    dprintb(collect_seq(m).toString)
    bannerprintb(s"after $name")
    dprint(mprime.serialize)
    dprintConEnv(conEnvPrime)
    (mprime, conEnvPrime)
  }
}

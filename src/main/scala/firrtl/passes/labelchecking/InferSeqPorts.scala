package firrtl.passes
import firrtl._
import firrtl.ir._
import firrtl.Utils._
import firrtl.Mappers._

//-----------------------------------------------------------------------------
// Infer Seq Ports
// This will add the 'seq' identifier to any Fields which can be inferred as
// 'sequential' (i.e. are driven by a sequential source such as another seq field
// or a register).
//-----------------------------------------------------------------------------
object InferSeqPorts extends Pass with PassDebug {
  override def name = "InferSeqPorts"
  override def debugThisPass = false
  var conGen : ConstraintGenerator = BVConstraintGen

  type Refs = scala.collection.mutable.HashSet[String]
  type Exprs = scala.collection.mutable.HashSet[Expression]
  // Methods borrowed from other passes
  def collect_seq_loc(m: DefModule): Exprs = SeqPortCheck.collect_seq_loc(m)

  def infer_seq_e(cons: ConnectionEnv, seqLocs: Set[Constraint],  seqOuts: Refs)(e: Expression) : Expression =
    e map infer_seq_e(cons,seqLocs, seqOuts) match {
      case ex : WSubField if kind(ex) == PortKind && gender(ex) == FEMALE =>
        val a = conGen.exprToCons(ex)
        if (cons.contains(a) && seqLocs.contains(cons(a)._1)) {
          seqOuts += ex.serialize
        }
        ex
      case ex => ex
    }

  def infer_seq_s(cons: ConnectionEnv, seqLocs: Set[Constraint], seqOuts: Refs)(s: Statement) : Statement =
    s map infer_seq_e(cons,seqLocs, seqOuts) map infer_seq_s(cons,seqLocs, seqOuts)

  def infer_types_f(seqOuts: Refs, parent: String)(f: Field): Field = {
    val refName = parent + "." + f.name
    val ftype = f.tpe match {
      case bt: BundleType => BundleType(bt.fields map infer_types_f(seqOuts, refName))
      case _ => f.tpe
    }
    Field(f.name, f.flip, ftype, f.lbl, seqOuts.contains(refName))
  }

  def infer_types_p(seqOuts: Refs)(p: Port): Field = {
    val ptype = p.tpe match {
      case bt: BundleType => BundleType(bt.fields map infer_types_f(seqOuts, p.name))
      case _ => p.tpe
    }
    Field(p.name, to_flip(p.direction), ptype, p.lbl, false)
  }

  def infer_types_port(p: Port): Port = {
   p copy (tpe = infer_types_p(seq_out)(p).tpe)
  }

   def infer_types_m(m: DefModule) : Type = {
    val conEnv = new ConnectionEnv
    val whenEnv = new WhenEnv
    conGen.gen_cons(conEnv, whenEnv)(m)
    val seq_loc = (collect_seq_loc(m) map {
     e => conGen.exprToCons(e)
    }).toSet[Constraint]
    m map infer_seq_s(conEnv,seq_loc, seq_out)
    BundleType(m.ports map infer_types_p(seq_out))
  }

  def infer_types_top(m: DefModule) : DefModule = {
    infer_types_m(m)
    m map infer_types_port
  }

  val seq_out = new Refs
  override def run(c: Circuit) = {
    bannerprintb(s"before $name")
    dprint(c.serialize)
    val cprime = c copy (modules = c.modules map infer_types_top)
    bannerprintb(s"after $name")
    dprint(cprime.serialize)
    cprime
  }

}

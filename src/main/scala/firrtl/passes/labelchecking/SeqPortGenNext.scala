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
//
// This pass is simplified by the fact that it only considers modules that will 
// not generate errors during SeqPortCheck. Namely, It can consider the 
// first connection to the sequential output port to be the only connection to 
// that port
//
// TODO it might be better to wrap this in a LabelPass and run it after 
// SeqPortCheck??
object SeqPortGenNext extends Pass with PassDebug {
  def name = "SeqPortGenNext"
  override def debugThisPass = true

  //-----------------------------------------------------------------------------
  // Collect Next-Cycle Fields
  //-----------------------------------------------------------------------------
  // NextRefs is set of (Port,Field) pairs representing sequential out ports 
  type NextRefs = scala.collection.mutable.HashSet[(Port,Field)]
  def collect_seq_out(m: DefModule) : NextRefs = {
    val nr = new NextRefs
    m map collect_seq_out_p(nr)
    nr
  }

  def collect_seq_out_p(nr: NextRefs)(p: Port) : Port = p.tpe match {
    case BundleType(fields) => fields map { f: Field =>
        // if f is a seq output, add it to the set
        // TODO check if n_sf is declared in BundleType(fields)
        if(f.isSeq && f.flip == to_flip(p.direction)) nr  += ((p, f))
      }; p
    case _ => p
      // The only way to mark a port sequential is by a field.
  }
  
  //-----------------------------------------------------------------------------
  // Collect Locs Assigned to SeqPorts
  //-----------------------------------------------------------------------------
  // Generate a mapping from nextified seq output ports to the nextified 
  // versions of locations from which they are assigned
  type SeqConEnv = scala.collection.mutable.HashMap[WSubField, Expression] 

  def collect_seq_locs(sc: SeqConEnv, nr: NextRefs)(m: DefModule) =
    m map collect_seq_locs_s(sc, nr)

  def collect_seq_locs_s(sc: SeqConEnv, nr: NextRefs)(s: Statement) : Statement =
    s map collect_seq_locs_s(sc, nr) match {
      case sx : Connect => collect_seq_locs_e(sc, nr)(sx.loc,sx.expr); s
      case sx : PartialConnect => collect_seq_locs_e(sc, nr)(sx.loc,sx.expr); s
      case _ => s
    }

  def next_refs_match(nr: NextRefs, pname: String, fname: String) : Option[(Port,Field)] = {
    nr.foreach{ case (p: Port, f: Field) =>
      if(p.name == pname && f.name == fname) return Some(p,f)
    }
    return None
  }

  def collect_seq_locs_e(sc: SeqConEnv, nr: NextRefs)(l: Expression, r: Expression) =
    l match {
      case e: WSubField => e.exp match {
        case ex: WRef => 
          next_refs_match(nr,ex.name,e.name) match {
            // The use of next_exp is dangerous; it could cause a MatchError 
            case Some((p,f)) => sc += (nr_to_wsubf(p,f) -> PullNexts.next_exp(r))
            case None =>
          }
        case _ =>
      }
      case _ =>
    }
  
  def nr_to_wsubf(p: Port, f: Field) : WSubField = {
    // Make a female reference to sequential output ports
    val pr = WRef(p.name,p.tpe,p.lbl,PortKind,FEMALE)
    val sf = WSubField(pr,f.name,f.tpe,f.lbl,FEMALE)
    // then nextify it (at time of writing adds next_ before name)
    PullNexts.next_exp(sf).asInstanceOf[WSubField]
  }

  //-----------------------------------------------------------------------------
  // Connection Generation
  //-----------------------------------------------------------------------------
  def gen_connections(sc: SeqConEnv)(m: DefModule) : DefModule = m match {
    case mx : Module => 
      val newBlock = Block((sc map { case (w: WSubField,e: Expression) =>
        Connect(NoInfo,w,e) 
      }).to[collection.immutable.Seq])
      // Keep the body flattened to be polite!
      val newBody = flatten_s(Block(Seq(mx.body, newBlock)))
      mx copy(body = newBody)
    case _ => m
  }

  def run(c: Circuit) = {
    bannerprintb(s"before $name")
    dprint(c.serialize)
    val cprime = c copy(modules = c.modules map { m =>
      val nr = collect_seq_out(m)
      dprintb(s"${m.name} next_refs:")
      nr.foreach{ case (p: Port, f: Field) =>
        dprintb(s"(${p.serialize}, ${f.serialize})") }
      dprintb(s"${m.name} SeqConEnv:")
      val sc = new SeqConEnv
      collect_seq_locs(sc, nr)(m)
      sc.foreach{ case (w: WSubField, e: Expression) =>
        dprintb(s"(${w.serialize}, ${e.serialize})") }
      gen_connections(sc)(m)
    })
    bannerprintb(s"after $name")
    dprint(cprime.serialize)
    cprime
  }

}

package firrtl.passes

import firrtl._
import firrtl.ir._
import firrtl.Utils._
import firrtl.Mappers._
import firrtl.Driver._
import firrtl.passes.NextCycleTransform.next_exp

// TODO mems are sequential too!!!!

// This pass checks that all expressions of form next(e) are valid, and 
// replaces them with a unique compiler-mangled WIR expression. Valid next 
// expressions are always female since they represent the compiler-defined 
// next-cycle value of an expression and should not be defined by user code. 
// Valid next expressions should either be references to registers or subfields 
// pointing to sequential ports.
object PullNexts extends Pass with PassDebug {
  def name = "Pull Nexts"
  override def debugThisPass = false

  class FemaleNextException(info: Info, exp: Expression) extends PassException(
    s"$info: an attempt was made to assign to next-value next(${exp.serialize})")
  class IllegalNextException(info: Info, exp: Expression) extends PassException(
    s"$info: Illegal next expression: next(${exp.serialize}). Are you sure that ${exp.serialize} is sequential?")
  class NoNextPException(info: Info, exp: Expression) extends PassException(
    s"$info: Next port unavailable: next(${exp.serialize}). Is the next_[.] port needed for ${exp.serialize} declared?")
  val errors = new Errors()
  
  def next_ident(n: String): String =  "$" + n

  def next_lbl(l: Label) : Label =
    l map next_lbl map next_lc

  def next_lc(l: LabelComp): LabelComp =
    l map next_lc map next_lc_exp

  // This function is only called on expressions appearing in dependant types.
  // Replace sequential dependands with the next-cycle version of the
  // dependand. It swaps regardless of gender
  //TODO don't throw exceptions, refactor so they are handled like other errors
  def next_lc_exp(e: Expression) : Expression = {
    e map next_lc_exp match {
      case ex: WRef if ex.kind == RegKind => next_exp(ex)
    //  case ex: WRef if ex.kind == PortKind || ex.kind == InstanceKind => ex
      case ex: WSubField => next_exp(ex)
    //  case ex: Literal => ex
      case ex => ex
    }
  }

  def next_exp(e: Expression): Expression = e match {
    case ex : WRef => ex copy (name = next_ident(ex.name), lbl = next_lbl(ex.lbl))
    case ex: WSubField if is_simple_p_subf(ex) => ex copy (name = next_ident(ex.name), lbl = next_lbl(ex.lbl))
    case ex: DoPrim => ex.op match {
      case PrimOps.Bits =>
        val next_args = ex.args map {a => next_exp(a)}
      DoPrim(PrimOps.Bits, next_args, ex.consts, ex.tpe, next_lbl(ex.lbl))
    }
    case ex => ex
  }

  def is_simple_p_subf(e: WSubField) : Boolean = e.exp match {
    case ex: WRef => ex.kind == PortKind || ex.kind == InstanceKind
    case ex: WSubField => is_simple_p_subf(ex)
    case _ => false
  }

  def next_p_declared(e: WSubField) = e.exp.tpe match {
    case t: BundleType => t.fields find (_.name == "next_" + e.name) match {
      case Some(f) => true; case None => false
    }
    case _ => false
  }

  type NextCtx = collection.mutable.HashMap[String,DefRegister]

  def pull_next_e(nctx: NextCtx, info: Info)(e: Expression): Expression = 
    e map pull_next_e(nctx, info) match {
      case Next(en, tpe, lbl, MALE) => en match {
        case enx: WRef =>
          if(!nctx.contains(enx.name))
            errors.append(new IllegalNextException(info, enx))
          next_exp(enx)
        case enx: WSubField =>
          if(!is_simple_p_subf(enx)) 
            errors.append(new IllegalNextException(info, enx))
          if(!field_seq(enx.exp.tpe, enx.name))
            errors.append(new IllegalNextException(info, enx))
          if(!next_p_declared(enx)) 
            errors.append(new NoNextPException(info, enx))
          next_exp(enx)
        case enx => 
            errors.append(new IllegalNextException(info, enx))
            enx
      }
      case Next(en, tpe, lbl, FEMALE) =>
        errors.append(new FemaleNextException(info, en))
        Next(en, tpe, lbl, FEMALE)
      case ex => ex
    }

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

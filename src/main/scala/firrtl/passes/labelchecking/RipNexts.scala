package firrtl.passes

import firrtl._
import firrtl.ir._
import firrtl.Utils._
import firrtl.Mappers._
import firrtl.Driver._
import firrtl.passes.NextCycleTransform.next_exp

// TODO mems are sequential too!!!!

//This pass removes all of the Next(e)
//expressions that were generated to assist in constraint generation

object RipNexts extends Pass with PassDebug {
  def name = "Pull Nexts"
  override def debugThisPass = false

  class FemaleNextException(info: Info, exp: Expression) extends PassException(
    s"$info: an attempt was made to assign to next-value next(${exp.serialize})")
  class IllegalNextException(info: Info, exp: Expression) extends PassException(
    s"$info: Illegal next expression: next(${exp.serialize}). Are you sure that ${exp.serialize} is sequential?")
  class NoNextPException(info: Info, exp: Expression) extends PassException(
    s"$info: Next port unavailable: next(${exp.serialize}). Is the next_[.] port needed for ${exp.serialize} declared?")
  val errors = new Errors()
  
  def next_ident(n: String) = "_next_" + n

  def next_lbl(l: Label) : Label =
    l map next_lbl map next_lc

  def next_lc(l: LabelComp): LabelComp =
    l map next_lc map next_lc_exp

  // This function is only called on expressions appearing in dependant types.
  // Replace sequential dependands with the next-cycle version of the
  // dependand. It swaps regardless of gender
  //TODO don't throw exceptions, refactor so they are handled like other errors
  def next_lc_exp(e: Expression) : Expression = {
    e match {
      case ex: WRef if ex.kind == RegKind => next_exp(ex)
      case ex: WSubField => next_exp(ex)
      case ex => ex
    }
  }

  def next_exp(e: Expression): Expression = e match {
    case ex : WRef => Next(ex, ex.tpe, next_lbl(ex.lbl), ex.gender)
    case ex: WSubField if is_simple_p_subf(ex) => ex copy(exp = next_exp(ex.exp))
    case ex: DoPrim => ex.op match {
      case PrimOps.Bits =>
        val next_args = ex.args map {a => next_exp(a)}
      DoPrim(PrimOps.Bits, next_args, ex.consts, ex.tpe, next_lbl(ex.lbl))
      case _ => throw new IllegalNextException(NoInfo, e)
    }
    case ex => throw new IllegalNextException(NoInfo, e)
  }

  def is_simple_p_subf(e: WSubField) : Boolean = e.exp match {
    case ex: WRef => true
    case ex: WSubField => is_simple_p_subf(ex)
    case _ => false
  }

  def next_p_declared(e: WSubField) = e.exp.tpe match {
    case t: BundleType => t.fields find (_.name == "next_" + e.name) match {
      case Some(f) => true; case None => false
    }
    case _ => false
  }

  def pull_next_e(info: Info)(e: Expression): Expression =
    e map pull_next_e(info) match {
      case Next(en, _, _, _) => en
      case ex => ex
    }

  def pull_next_s(s: Statement): Statement =
    s map pull_next_s map pull_next_e(s.info)

  def pull_next(m: DefModule): DefModule =
    m map pull_next_s

  def run(c: Circuit): Circuit = {
    bannerprintb(name)
    dprint(c.serialize)

    val cprime = c copy (modules =
      c.modules map pull_next)
    bannerprintb(s"after $name")
    dprint(cprime.serialize)
    cprime
  }


}

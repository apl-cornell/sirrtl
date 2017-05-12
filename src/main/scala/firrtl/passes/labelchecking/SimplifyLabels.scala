package firrtl.passes
import firrtl._
import firrtl.ir._
import firrtl.Mappers._

object SimplifyLabels extends Pass with PassDebug {
  def name = "SimplifyLabels"
  override def debugThisPass = false 

  val bot = PolicyHolder.bottom
  val top = PolicyHolder.top

  type CompSet = scala.collection.mutable.HashSet[LabelComp]

  def simplify_mt(cmps: CompSet)(l: LabelComp): LabelComp =
    l match {
      case lx: MeetLabelComp => lx map simplify_mt(cmps)
      case lx => cmps += lx; lx
    }

  def simplify_jn(cmps: CompSet)(l: LabelComp): LabelComp =
    l match {
      case lx: JoinLabelComp => lx map simplify_jn(cmps)
      case lx => cmps += lx; lx
    }

  def simplify_lb_cmp(l: LabelComp): LabelComp = 
    l map simplify_lb_cmp map simplify_e match {
      case lbx: MeetLabelComp => 
        val cmps = new CompSet
        simplify_mt(cmps)(lbx)
        (cmps.toList sortBy { _.hashCode }).foldRight(top) { _ meet _ }
      case lbx: JoinLabelComp => 
        val cmps = new CompSet
        simplify_jn(cmps)(lbx)
        (cmps.toList sortBy { _.hashCode }).foldRight(bot) { _ join _ }
      case lbx => lbx
    }

  def simplify_lb(l: Label) : Label = 
    l map simplify_lb map simplify_lb_cmp

  def simplify_e(e: Expression) : Expression =
    e map simplify_e map simplify_lb

  def simplify_s(s: Statement) : Statement =
    s map simplify_s map simplify_e map simplify_lb

  def simplify_p(p: Port) =
    p copy (lbl = simplify_lb(p.lbl))

  def simplify_labels(m: DefModule) : DefModule =
    m map simplify_p map simplify_s

  def run(c: Circuit) = {
    bannerprintb(name)
    dprint(c.serialize)
    
    val cprime = c copy (modules = c.modules map simplify_labels)

    bannerprintb(s"after $name")
    dprint(cprime.serialize)
    cprime
  }
}

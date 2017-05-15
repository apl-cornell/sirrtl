package firrtl.passes
import firrtl._
import firrtl.ir._
import firrtl.Mappers._
import scala.collection.mutable.HashSet
import scala.collection.mutable.Set

object LabelsToCNF extends Pass with PassDebug {
  def name = "LabelsToCNF"
  override def debugThisPass = true

  val top = PolicyHolder.top
  val bot = PolicyHolder.bottom
  
  implicit class CrossProdInfix[X](xs: Set[X]) {
    def cross[Y](ys: Set[Y]) = for { x <- xs; y <- ys } yield (x, y)
  }

  def sortByHash(s: Set[LabelComp]): Set[LabelComp]=
    Set((s.toList sortBy { _.hashCode }): _*)

  def clauses(l: LabelComp): Set[LabelComp] = {
    val cls = new HashSet[LabelComp]
    def clauses_(cls: Set[LabelComp])(l: LabelComp): LabelComp = 
      l match {
        case lbx: JoinLabelComp => lbx map clauses_(cls)
        case lbx => cls += lbx; lbx
      }

    clauses_(cls)(l)
    sortByHash(cls)
  }

  def cnf_lb_cmp(l: LabelComp): LabelComp = 
    l map cnf_lb_cmp map cnf_e match {
      case lbx: MeetLabelComp => 
        sortByHash( (clauses(lbx.l) cross clauses(lbx.r)) map {
          case (lhs:LabelComp, rhs:LabelComp) => lhs meet rhs
        }).foldRight(bot) { _ join _ }
      case lbx: JoinLabelComp =>
        // Not strictly necessary just to convert to CNF, but 
        // should further simplify
        sortByHash(clauses(lbx)).foldRight(bot) { _ join _ }
      case lbx => lbx
    }

  def cnf_lb(l: Label): Label =
    l map cnf_lb_cmp map cnf_lb

  def cnf_e(e: Expression) : Expression =
    e map cnf_e map cnf_lb

  def cnf_s(s: Statement) : Statement =
    s map cnf_s map cnf_e map cnf_lb

  def cnf_p(p: Port) =
    p copy (lbl = cnf_lb(p.lbl))

  def cnf_labels(m: DefModule) : DefModule =
    m map cnf_p map cnf_s

  def run(c: Circuit) = {
    bannerprintb(name)
    dprint(c.serialize)
    
    val cprime = c copy (modules = c.modules map cnf_labels)

    bannerprintb(s"after $name")
    dprint(cprime.serialize)
    cprime
  }
}

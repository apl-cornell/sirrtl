package firrtl.passes
import firrtl._
import firrtl.ir._
import firrtl.Mappers._
import scala.collection.mutable.LinkedHashSet
import scala.collection.mutable.Set

object SimplifyLabels extends Pass with PassDebug {
  def name = "Simplify Lables"
  override def debugThisPass = false

  
  implicit class CrossProdInfix[X](xs: Set[X]) {
    def cross[Y](ys: Set[Y]) = for { x <- xs; y <- ys } yield (x, y)
  }

  // Convert label components into simplified DNF.
  def dnf_lb_cmp(l: LabelComp): LabelComp =  {
    val bot = PolicyHolder.bottom
    val top = PolicyHolder.top
    
    def sortClauses(s: Set[LabelComp]): Set[LabelComp]=
      LinkedHashSet( (s.toList sortBy { _.hashCode }):_* )

    def clauses(l: LabelComp): Set[LabelComp] = {
      val cls = new LinkedHashSet[LabelComp]
      def clauses_(cls: Set[LabelComp])(l: LabelComp): LabelComp = 
        l match {
          case lbx: MeetLabelComp => lbx map clauses_(cls)
          case lbx => cls += lbx; lbx
        }
  
      clauses_(cls)(l)
      sortClauses(cls)
    }

    // Should only be called on clauses
    def terms(l: LabelComp): Set[LabelComp] = {
      val termSet = new LinkedHashSet[LabelComp]
      def terms_(l: LabelComp): LabelComp = l match {
        case lx: MeetLabelComp => throw new Exception
        case lx: JoinLabelComp => l map terms_
        case lx => termSet += lx; lx
      }
      terms_(l); termSet
    }

    // cnf_e gets called here even though integrity components are in
    // dnf because components have expressions which have labels and 
    // labels are in cnf.
    l map dnf_lb_cmp map cnf_e match {
      case lbx: JoinLabelComp => 
        sortClauses( (clauses(lbx.l) cross clauses(lbx.r)) map {
          case (lhs:LabelComp, rhs:LabelComp) => cnf_lb_cmp(lhs join rhs)
        }).foldLeft(top) { _ meet _ }
      case lbx: MeetLabelComp =>
        val simplified_clauses = new LinkedHashSet[LabelComp]
        val lx_clauses = clauses(lbx)
        lx_clauses foreach { cls_i =>
          var addme = true
          (lx_clauses - cls_i) foreach { cls_j =>
            if(terms(cls_j) subsetOf terms(cls_i)) addme = false
          }
          if(addme) simplified_clauses += cls_i
        }
        sortClauses(simplified_clauses).foldLeft(top) { _ meet _ }
      case lbx => lbx
    }
  }


  // Convert label components into simplified CNF.
  def cnf_lb_cmp(l: LabelComp): LabelComp =  {
    val bot = PolicyHolder.bottom
    val top = PolicyHolder.top
    
    def sortClauses(s: Set[LabelComp]): Set[LabelComp]=
      LinkedHashSet( (s.toList sortBy { _.hashCode }):_* )

    def clauses(l: LabelComp): Set[LabelComp] = {
      val cls = new LinkedHashSet[LabelComp]
      def clauses_(cls: Set[LabelComp])(l: LabelComp): LabelComp = 
        l match {
          case lbx: JoinLabelComp => lbx map clauses_(cls)
          case lbx => cls += lbx; lbx
        }
  
      clauses_(cls)(l)
      sortClauses(cls)
    }

    // Should only be called on clauses
    def terms(l: LabelComp): Set[LabelComp] = {
      val termSet = new LinkedHashSet[LabelComp]
      def terms_(l: LabelComp): LabelComp = l match {
        case lx: JoinLabelComp => throw new Exception
        case lx: MeetLabelComp => l map terms_
        case lx => termSet += lx; lx
      }
      terms_(l); termSet
    }

    l map cnf_lb_cmp map cnf_e match {
      case lbx: MeetLabelComp => 
        sortClauses( (clauses(lbx.l) cross clauses(lbx.r)) map {
          case (lhs:LabelComp, rhs:LabelComp) => dnf_lb_cmp(lhs meet rhs)
        }).foldLeft(bot) { _ join _ }
      case lbx: JoinLabelComp =>
        val simplified_clauses = new LinkedHashSet[LabelComp]
        val lx_clauses = clauses(lbx)
        lx_clauses foreach { cls_i =>
          var addme = true
          (lx_clauses - cls_i) foreach { cls_j =>
            if(terms(cls_j) subsetOf terms(cls_i)) addme = false
          }
          if(addme) simplified_clauses += cls_i
        }
        sortClauses(simplified_clauses).foldLeft(bot) { _ join _ }
      case lbx => lbx
    }
  }

  // Convert lables into simplified CNF.
  // Labels (not just label components) also need to be simplified
  // to improve label inference. For example, forward-propagation
  // of lables to a node might derive the label (bot join {var: foo}).
  // When converted to canonical form, this label will induce a
  // constraint on foo which requires that it can flow to bot even though
  // this is an artificial constraint.
  def cnf_lb(l: Label): Label =  {
    
    val bot: Label = ProdLabel(PolicyHolder.bottom, PolicyHolder.top)
    val top: Label = ProdLabel(PolicyHolder.top, PolicyHolder.bottom)

    // Sort clauses such that as much simplification as possible will happen.
    // Clauses are grouped by type and then sorted by hashcode.
    // By putting product labels at the front, labels are converted into 
    // products of label components as much as possible. The label 
    // components are then simplified further. Label variables are last
    // since they cannot be simplified.
    // The hashCode does what you want it to because the entire hierarchy of
    // labels is based on case classes.
    def sortClauses(s: Set[Label]): Set[Label]= {
      val prods = new LinkedHashSet[ProdLabel]
      val vars = new LinkedHashSet[VarLabel]
      val meets = new LinkedHashSet[MeetLabel]
      val other = new LinkedHashSet[Label] //Bundles as of writing
      def bin(s: Set[Label]) : Unit = s.foreach { _ match {
        case lx: ProdLabel => prods += lx
        case lx: MeetLabel => meets += lx
        case lx: VarLabel => vars += lx
        case lx => other += lx 
      }}
      bin(s)
      LinkedHashSet(((prods.toList sortBy { _.hashCode }) ++
        (meets.toList sortBy { _.hashCode }) ++
        (other.toList sortBy { _.hashCode }) ++
        (vars.toList sortBy { _.hashCode })):_*)
    }

    def clauses(l: Label): Set[Label] = {
      val cls = new LinkedHashSet[Label]
      def clauses_(cls: Set[Label])(l: Label): Label = 
        l match {
          case lbx: JoinLabel => lbx map clauses_(cls)
          case lbx => cls += lbx; lbx
        }

      clauses_(cls)(l)
      sortClauses(cls)
    }

    // Should only be called on clauses
    def terms(l: Label): Set[Label] = {
      val termSet = new LinkedHashSet[Label]
      def terms_(l: Label): Label = l match {
        case lx: JoinLabel => throw new Exception
        case lx: MeetLabel => l map terms_
        case lx => termSet += lx; lx
      }
      terms_(l); termSet
    }

    l map cnf_lb match {
      case lbx: MeetLabel=> 
        sortClauses( (clauses(lbx.l) cross clauses(lbx.r)) map {
          case (lhs:Label, rhs:Label) => lhs meet rhs
        }).foldLeft(bot) { _ join _ }
      case lbx: JoinLabel =>
        val simplified_clauses = new LinkedHashSet[Label]
        val lx_clauses = clauses(lbx)
        lx_clauses foreach { cls_i =>
          var addme = true
          (lx_clauses - cls_i) foreach { cls_j =>
            if(terms(cls_j) subsetOf terms(cls_i)) addme = false
          }
          if(addme) simplified_clauses += cls_i
        }
        sortClauses(simplified_clauses).foldLeft(bot) { _ join _ }
      case ProdLabel(conf, integ) =>
        // Confidentiality components are in the same normal form as labels,
        // but integrity components are in the dual of that normal form
        // since the conf/integ components are often duals and using the dual
        // normal form for integ makes this more clear after simplification
        // (and the simplified labels wind up being simpler)
        ProdLabel(cnf_lb_cmp(conf), dnf_lb_cmp(integ))
      case lbx => lbx
    }
  }

  // AF: cnf_e and cnf_el differ because we need to consider expressions in 
  // labels but not the labels of expressions in label. Only recursing through 
  // the subset of the structure that is actually used achieves considerable 
  // performance improvement. (Note that cnf_e is used in labelcomps but cnf_el 
  // is used in statemenents)
  def cnf_e(e: Expression) : Expression =
    e map cnf_e

  def cnf_el(e: Expression) : Expression =
    cnf_e(e) map cnf_lb

  def cnf_s(s: Statement) : Statement =
    s map cnf_s map cnf_el map cnf_lb

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

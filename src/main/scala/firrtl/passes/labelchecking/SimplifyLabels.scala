package firrtl.passes
import firrtl._
import firrtl.ir._
import firrtl.Mappers._
import scala.collection.mutable.LinkedHashSet
import scala.collection.mutable.Set

// TODO level 1: clean up this code.
// TODO level 2: make the apply methods of meet/join produce simplified 
// CNF labelComps/labels on the fly so this pass isn't needed and inference
// doesn't have to call its methods.

object SimplifyLabels extends Pass with PassDebug {
  def name = "Simplify Lables"
  override def debugThisPass = false 

  
  implicit class CrossProdInfix[X](xs: Set[X]) {
    def cross[Y](ys: Set[Y]) = for { x <- xs; y <- ys } yield (x, y)
  }

  // Convert label components into simplified CNF.
  def cnf_lb_cmp(l: LabelComp): LabelComp =  {
    val bot = PolicyHolder.bottom
    val top = PolicyHolder.top
    
    def sortClauses(s: Set[LabelComp]): Set[LabelComp]=
      LinkedHashSet( (s.toList sortBy { _.hashCode }):_* )

    def simplifyMeet(l: LabelComp): LabelComp = {
      val nonMeets = new LinkedHashSet[LabelComp]
      def simplifyMeet_(nm: Set[LabelComp])(l: LabelComp): LabelComp =
        l match {
          case lx: MeetLabelComp => lx map simplifyMeet_(nm)
          case lx => nonMeets += lx; lx
        }
      simplifyMeet_(nonMeets)(l)
      (nonMeets.toList.sortBy { _.hashCode }).foldLeft(top) { _ meet _ }
    }
  
    def clauses(l: LabelComp): Set[LabelComp] = {
      val cls = new LinkedHashSet[LabelComp]
      def clauses_(cls: Set[LabelComp])(l: LabelComp): LabelComp = 
        l match {
          case lbx: JoinLabelComp => lbx map clauses_(cls)
          case lbx: MeetLabelComp => cls += simplifyMeet(lbx); simplifyMeet(lbx)
          case lbx => cls += lbx; lbx
        }
  
      clauses_(cls)(l)
      sortClauses(cls)
    }

    def is_clause(l: LabelComp): Boolean = {
      var ret = true
      def is_clause_(l: LabelComp): LabelComp = 
        l map is_clause_ match {
        case lb: JoinLabelComp => ret = false; lb
        case lb => lb
      }
      is_clause_(l); ret
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

    // Can only be applied once the labelComp is in CNF
    def simplifySubsumptions(l: LabelComp): LabelComp = 
      l map simplifySubsumptions match {
        case JoinLabelComp(x, y) if is_clause(x) && is_clause(y) &&
          (terms(x) subsetOf terms(y)) => y
        case JoinLabelComp(y, x) if is_clause(x) && is_clause(y) &&
          (terms(x) subsetOf terms(y)) => y
        case lx => lx
      }


    simplifyMeet(simplifySubsumptions(l map cnf_lb_cmp map cnf_e map simplifyMeet match {
      case lbx: MeetLabelComp => 
        sortClauses( (clauses(lbx.l) cross clauses(lbx.r)) map {
          case (lhs:LabelComp, rhs:LabelComp) => lhs meet rhs
        }).foldLeft(bot) { _ join _ }
      case lbx: JoinLabelComp =>
        // Not strictly necessary just to convert to CNF, but 
        // should further simplify
        sortClauses(clauses(lbx)).foldLeft(bot) { _ join _ }
      case lbx => lbx
    }))
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

    (l map cnf_lb map cnf_lb_cmp match {
      case lbx: MeetLabel=> 
        sortClauses( (clauses(lbx.l) cross clauses(lbx.r)) map {
          case (lhs:Label, rhs:Label) => lhs meet rhs
        }).foldLeft(bot) { _ join _ }
      case lbx: JoinLabel =>
        // Not strictly necessary just to convert to CNF, but 
        // should further simplify
        sortClauses(clauses(lbx)).foldLeft(bot) { _ join _ }
      case lbx => lbx
    }) map cnf_lb map cnf_lb_cmp
  }

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

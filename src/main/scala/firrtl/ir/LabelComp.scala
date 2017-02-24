package firrtl
package ir

abstract class LabelComp extends FirrtlNode {
  def join(that: LabelComp) = JoinLabelComp(this, that)
  def meet(that: LabelComp) = MeetLabelComp(this, that)
  def serialize : String
  override def toString = serialize
  def mapExpr(f: Expression => Expression): LabelComp
  def mapLabelComp(f: LabelComp => LabelComp): LabelComp
}

case object UnknownLabelComp extends LabelComp {
  def serialize = ""
  def mapExpr(f: Expression => Expression) = this
  def mapLabelComp(f: LabelComp => LabelComp) = this
}

case class Level(label: String)  extends LabelComp{
  override def equals(that: Any) = that match {
    case o : Level => o.label equals label
    case _ => false
  }
  def serialize = label
  def mapExpr(f: Expression => Expression) = this
  def mapLabelComp(f: LabelComp => LabelComp) = this
}

// Behaves like a case class
// Not implemented like a case class to have the special factory-method apply 
object JoinLabelComp {
  val bottom : LabelComp = PolicyHolder.bottom
  val top : LabelComp = PolicyHolder.top
  def apply(l: LabelComp, r: LabelComp): LabelComp = (l, r) match {
    case(UnknownLabelComp, _) => UnknownLabelComp
    case(_, UnknownLabelComp) => UnknownLabelComp
    case(_, b: Level) if b == bottom => l
    case(b: Level, _) if b == bottom => r
    case(_, t: Level) if t == top => top
    case(t: Level, _) if t == top => top
    case (tl: Level, tr: Level)  => PolicyHolder.policy match {
      case p: LevelPolicy => p.levelLat.join(tl, tr)
      case _ => new JoinLabelComp(l, r)
    }
    case _ => new JoinLabelComp(l,r)
  }
  def apply(l: LabelComp*) : LabelComp = l.foldRight(bottom) { apply(_,_) }
  def unapply(j: JoinLabelComp) = Some((j.l, j.r))
}

sealed class JoinLabelComp private(val l: LabelComp, val r: LabelComp) extends LabelComp{
  override def equals(that: Any) = that match {
    case JoinLabelComp(lx, rx) => lx == l && rx == r
    case _ => false
  }
  def serialize = s"(join ${l.serialize} ${r.serialize})"
  def mapExpr(f: Expression => Expression) = this
  def mapLabelComp(f: LabelComp => LabelComp) = JoinLabelComp(f(l), f(r))
}

// Behaves like a case class
// Not implemented like a case class to have the special factory-method apply 
object MeetLabelComp {
  val bottom : LabelComp = PolicyHolder.bottom
  val top : LabelComp = PolicyHolder.top
  def meet(l: LabelComp, r: LabelComp): LabelComp = (l, r) match {
    case(UnknownLabelComp, _) => UnknownLabelComp
    case(_, UnknownLabelComp) => UnknownLabelComp
    case (tl: Level, tr: Level)  => PolicyHolder.policy match {
      case p: LevelPolicy => p.levelLat.join(tl, tr)
      case _ => new MeetLabelComp(l, r)
    }
    case _ => new MeetLabelComp(l,r)
  }
  def apply(l: LabelComp*) : LabelComp = l.foldRight(top) { apply(_,_) }
  def unapply(m: MeetLabelComp) = Some((m.l, m.r))
}

// Behaves like a case class
sealed class MeetLabelComp private(val l: LabelComp, val r: LabelComp) extends LabelComp{
  override def equals(that: Any) = that match{
    case MeetLabelComp(lx, rx) => lx == l && rx == r
    case _ => false
  }
  def serialize=  s"(meet ${l.serialize} ${r.serialize})"
  def mapExpr(f: Expression => Expression) = this
  def mapLabelComp(f: LabelComp => LabelComp) : LabelComp = MeetLabelComp(f(l), f(r))
}


case class FunLabel(fname: String, arg: Expression) extends LabelComp {
  def serialize = s"($fname ${arg.serialize})"
  def mapLabelComp(f: LabelComp => LabelComp): LabelComp = this
  def mapExpr(f: Expression => Expression): LabelComp = this.copy(arg = f(arg))
}

case class HLevel(arg: Expression) extends LabelComp {
  def serialize = s"[[${arg.serialize}]]"
  def mapLabelComp(f: LabelComp => LabelComp): LabelComp = this
  def mapExpr(f: Expression => Expression): LabelComp = this.copy(arg = f(arg))
}
/*
object IfLabel {
   def apply(cond: Node, t : Label, f : Label) = (cond,t,f) match {
     case(_,tt,ft) if tt == ft => tt
     case _ => new IfLabel(cond,t,f)
   }
   def unapply(ift: IfLabel) = Some((ift.cond, ift.tType, ift.fType))
}

// Behaves like a case class
class IfLabel private (var cond: Node, var tType : Label,
  var fType : Label) extends Label with DepLabel {
  override def toString = s"if(??) $tType else $fType"
  
  override def equals(that: Any) = that match {
    case IfLabel(c,t,f) => cond == c && tType == t && fType == f
    case _ => false
  }
  override def accept[T](visitor : LabelVisitor[T]) : T = visitor visit this
  override def accept(visitor : LabelSwapVisitor) : Label =
    visitor visit this
}

object CaseLabel {
  def apply(cond: Data, alternatives: Label*) =
    alternatives.zipWithIndex.map { case (alt: Label, idx: Int) =>
      IfLabel(cond === UInt(idx), alt, _: Label)
    }.foldRight(alternatives.last) {_ apply _}
}
*/

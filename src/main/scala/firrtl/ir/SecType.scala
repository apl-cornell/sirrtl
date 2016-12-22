package firrtl
package ir

abstract class Label extends FirrtlNode {
  def accept[T](visitor : LabelVisitor[T]) : T
  def accept(visitor : LabelSwapVisitor) : Label
  def join(that: Label) = JoinLabel(this, that)
  def meet(that: Label) = MeetLabel(this, that)
  def serialize = "TODO Label.serialize"
}

case class UnknownLabel(val nodeName: String) extends Label {
  override def toString = s"<${nodeName}>"
  override def accept[T](visitor : LabelVisitor[T]) : T = visitor visit this
  override def accept(visitor : LabelSwapVisitor) : Label =
    visitor visit this
}

case class Level(var label: String)  extends Label{
  override def equals(that: Any) = that match {
    case o : Level => o.label equals label
    case _ => false
  }
  def <=(that: Level) = PolicyHolder.policy.leq(this,that)
  override def hashCode = label.hashCode
  override def toString = label
  override def accept[T](visitor : LabelVisitor[T]) : T = visitor visit this
  override def accept(visitor : LabelSwapVisitor) : Label =
    visitor visit this
}

object JoinLabel {
  def apply(l : Label, r: Label) = (l, r) match {
    case (tl: Level, _) if tl == PolicyHolder.policy.bottom => r
    case (_, tr: Level) if tr == PolicyHolder.policy.bottom => l
    case (tl: Level, _) if tl == PolicyHolder.policy.top => 
      PolicyHolder.policy.top
    case (_, tr: Level) if tr == PolicyHolder.policy.top => 
      PolicyHolder.policy.top
    case (tl: Label, tr: Label) if tl == tr => tl
    case (tl: Level, tr: Level)  => 
      PolicyHolder.policy.join(tl, tr)
    case _ => new JoinLabel(l,r)
  }
  def unapply(j: JoinLabel) = Some((j.type_l, j.type_r))
}

// Behaves like a case class
class JoinLabel private (var type_l : Label, var type_r: Label) extends Label{
  override def equals(that: Any) = that match{
    case JoinLabel(l,r) => l == type_l && r == type_r
    case _ => false
  }
  override def toString = type_l.toString + " join " + type_r.toString
  override def accept[T](visitor : LabelVisitor[T]) : T = visitor visit this
  override def accept(visitor : LabelSwapVisitor) : Label =
    visitor visit this

}

object MeetLabel {
  def apply(l : Label, r: Label) = (l, r) match {
    case (tl: Level, tr: Level)  => 
      PolicyHolder.policy.meet(tl, tr)
    case _ => new MeetLabel(l,r)
  }
  def unapply(m: MeetLabel) = Some((m.type_l, m.type_r))
}

// Behaves like a case class
class MeetLabel private (var type_l : Label, var type_r: Label) extends Label{
  override def equals(that: Any) = that match{
    case MeetLabel(l,r) => l == type_l && r == type_r
    case _ => false
  }
  override def toString = type_l.toString + " join " + type_r.toString
  override def accept[T](visitor : LabelVisitor[T]) : T = visitor visit this
  override def accept(visitor : LabelSwapVisitor) : Label =
    visitor visit this
}

// Labels which are possibly dependent and contain subexpressions
trait DepLabel extends Label 

// TODO implement dependent labels

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

abstract class LabelVisitor[T] {
  def default : T
  def reduce(a: T, b: T) : T
  def visit(s: UnknownLabel) : T = default
  def visit(s: Level) : T = default
  def visit(s: JoinLabel) : T = s match {
    case JoinLabel(l, r) =>
      reduce((l accept this),(r accept this))
  }
  def visit(s: MeetLabel) : T = s match {
    case MeetLabel(l, r) =>
      reduce((l accept this),(r accept this))
  }

  /*
  def visit(s: IfLabel) : T = s match {
    case IfLabel(cond, tType, fType) =>
      reduce((tType accept this),(fType accept this))
  }
  */
}

abstract class LabelSwapVisitor {
  def visit(s: UnknownLabel) : Label = s
  def visit(s: Level) : Label = s
  def visit(s: JoinLabel) : Label = s match {
    case JoinLabel(l, r) =>
      JoinLabel((l accept this),(r accept this))
  }
  def visit(s: MeetLabel) : Label = s match {
    case MeetLabel(l, r) =>
      MeetLabel((l accept this),(r accept this))
  }

  /*
  def visit(s: IfLabel) : Label = s match {
    case IfLabel(cond, tType, fType) =>
      IfLabel(cond, tType accept this, fType accept this)
  }
  */
    
}

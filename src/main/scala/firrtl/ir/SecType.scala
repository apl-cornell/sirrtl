package firrtl
package ir

abstract class Label extends FirrtlNode {
  def join(that: Label) = JoinLabel(this, that)
  def meet(that: Label) = MeetLabel(this, that)
  def serialize : String
  override def toString = serialize
  def mapExpr(f: Expression => Expression): Label
  def mapLabel(f: Label => Label): Label
}

case object UnknownLabel extends Label {
  def serialize = ""
  def mapExpr(f: Expression => Expression) = this
  def mapLabel(f: Label => Label) = this
}

case class Level(label: String)  extends Label{
  override def equals(that: Any) = that match {
    case o : Level => o.label equals label
    case _ => false
  }
  def <=(that: Level) = PolicyHolder.policy.leq(this,that)
  def serialize = label
  def mapExpr(f: Expression => Expression) = this
  def mapLabel(f: Label => Label) = this
}

object JoinLabel {
  val bot : Label = PolicyHolder.policy.bottom
  val top : Label = PolicyHolder.policy.top
  def apply(l: Label, r: Label): Label = (l, r) match {
    case(UnknownLabel, _) => UnknownLabel
    case(_, UnknownLabel) => UnknownLabel
    case(_, b: Level) if b == bot => l
    case(b: Level, _) if b == bot => r
    case(_, t: Level) if t == top => top
    case(t: Level, _) if t == top => top
    case (tl: Level, tr: Level)  => PolicyHolder.policy.join(tl, tr)
    case _ => new JoinLabel(l,r)
  }
  def apply(l: Label*) : Label = l.foldRight(bot) { apply(_,_) }
  def unapply(j: JoinLabel) = Some((j.l, j.r))
}

// Behaves like a case class
class JoinLabel private (val l: Label, val r: Label) extends Label{
  override def equals(that: Any) = that match{
    case JoinLabel(lx,rx) => lx == l && rx == r
    case _ => false
  }
  def serialize=  s"(join ${l.serialize} ${r.serialize})"
  def mapExpr(f: Expression => Expression) = this
  def mapLabel(f: Label => Label) = JoinLabel(f(l), f(r))
}

object MeetLabel {
  val bot : Label = PolicyHolder.policy.bottom
  val top : Label = PolicyHolder.policy.top
  def apply(l: Label, r: Label): Label = (l, r) match {
    case(UnknownLabel, _) => UnknownLabel
    case(_, UnknownLabel) => UnknownLabel
    case (tl: Level, tr: Level)  => PolicyHolder.policy.meet(tl, tr)
    case _ => new MeetLabel(l,r)
  }
  def apply(l: Label*) : Label = l.foldRight(top) { apply(_,_) }
  def unapply(m: MeetLabel) = Some((m.l, m.r))
}

// Behaves like a case class
class MeetLabel private (val l: Label, val r: Label) extends Label{
  override def equals(that: Any) = that match{
    case MeetLabel(lx,rx) => lx == l && rx == r
    case _ => false
  }
  def serialize=  s"(meet ${l.serialize} ${r.serialize})"
  def mapExpr(f: Expression => Expression) = this
  def mapLabel(f: Label => Label) : Label = MeetLabel(f(l), f(r))
}

// These never get serialized in a z3 file
case class BundleLabel(fields: Seq[Field]) extends Label {
  def serializeField(f: Field) = f.flip.serialize + f.name + " : " + f.lbl.serialize
  def serialize: String = (fields map (serializeField(_)) mkString ", ") 
  def mapLabel(f: Label => Label): Label = 
    BundleLabel( fields map ( x => x.copy(lbl = f(x.lbl))))
  def mapExpr(f: Expression => Expression): Label = this
}

case class FunLabel(fname: String, arg: Expression) extends Label {
  def serialize = s"($fname ${arg.serialize})"
  def mapLabel(f: Label => Label): Label = this
  def mapExpr(f: Expression => Expression): Label = this.copy(arg = f(arg))
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

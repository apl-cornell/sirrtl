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
    case(lx, rx) if lx == rx => lx
    case(JoinLabelComp(lxx, rxx), rx) if lxx == rx || rxx == rx => JoinLabelComp(lxx, rxx)
    case(lx, JoinLabelComp(lxx, rxx)) if lxx == lx || rxx == lx => JoinLabelComp(lxx, rxx)
    case(UnknownLabelComp, _) => UnknownLabelComp
    case(_, UnknownLabelComp) => UnknownLabelComp
    case(x, MeetLabelComp(xx, y)) if xx == x => x
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

sealed class JoinLabelComp private(val l: LabelComp, val r: LabelComp) extends LabelComp {
  override def equals(that: Any) = that match {
    case JoinLabelComp(lx, rx) => lx == l && rx == r
    case _ => false
  }
  def serialize = s"(join ${l.serialize} ${r.serialize})"
  def mapExpr(f: Expression => Expression) = this
  def mapLabelComp(f: LabelComp => LabelComp) = JoinLabelComp(f(l), f(r))
  override def hashCode = serialize.hashCode
}

// Behaves like a case class
// Not implemented like a case class to have the special factory-method apply 
object MeetLabelComp {
  val bottom : LabelComp = PolicyHolder.bottom
  val top : LabelComp = PolicyHolder.top
  def apply(l: LabelComp, r: LabelComp): LabelComp = (l, r) match {
    case(lx, rx) if lx == rx => lx
    case(MeetLabelComp(lxx, rxx), rx) if lxx == rx || rxx == rx => MeetLabelComp(lxx, rxx)
    case(lx, MeetLabelComp(lxx, rxx)) if lxx == lx || rxx == lx => MeetLabelComp(lxx, rxx)
    case(UnknownLabelComp, _) => UnknownLabelComp
    case(_, UnknownLabelComp) => UnknownLabelComp
    case(x, JoinLabelComp(xx, yy)) if xx == x => x
    case(_, t: Level) if t == top => l
    case(t: Level, _) if t == top => r
    case(_, b: Level) if b == bottom => bottom
    case(b: Level, _) if b == bottom => bottom 
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
  override def hashCode = serialize.hashCode
}

case class FunLabel(fname: String, args: List[Expression]) extends LabelComp {
  def serialize = s"($fname ${args map { _ serialize } mkString(" ")})"
  def mapLabelComp(f: LabelComp => LabelComp): LabelComp = this
  def mapExpr(f: Expression => Expression): LabelComp = this.copy(args = args map f)
  override def hashCode = serialize.hashCode
}

object FunLabel{
  def apply(fname: String, args: Expression*) =
    new FunLabel(fname, args.toList)
}

case class HLevel(arg: Expression) extends LabelComp {
  def serialize = s"[[${arg.serialize}]]H"
  def mapLabelComp(f: LabelComp => LabelComp): LabelComp = this
  def mapExpr(f: Expression => Expression): LabelComp = this.copy(arg = f(arg))
  override def equals(that: Any) = that match {
    case HLevel(argx) => arg.serialize.hashCode == argx.serialize.hashCode
    case _ => false
  }
  override def hashCode = serialize.hashCode
}

// The arr should have a vector type. This is not currently enforced
case class VecHLevel(arr: Expression) extends LabelComp {
  def serialize = s"[[${arr.serialize}]]V"
  def mapLabelComp(f: LabelComp => LabelComp): LabelComp = this
  def mapExpr(f: Expression => Expression): LabelComp = this.copy(arr = f(arr))
  override def equals(that: Any) = that match {
    case VecHLevel(arrx) => arr.serialize.hashCode == arrx.serialize.hashCode
    case _ => false
  }
  override def hashCode = serialize.hashCode
}

// Arr should have a vector type and the value of index should be bounded by 
// the range of the array.
case class IndexedVecHLevel(arr: Expression, index: Expression) extends LabelComp {
  def serialize = s"[[${arr.serialize}]]V[${index.serialize}]"
  def mapLabelComp(f: LabelComp => LabelComp): LabelComp = this
  def mapExpr(f: Expression => Expression): LabelComp =
    this.copy(arr = f(arr), index = f(index))
  override def hashCode = serialize.hashCode
}

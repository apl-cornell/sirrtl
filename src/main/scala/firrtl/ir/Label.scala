package firrtl
package ir
import firrtl.Utils._

sealed abstract class Label extends FirrtlNode {
  def serialize: String
  def mapLabel(f: Label => Label): Label
  def mapLabelComp(f: LabelComp => LabelComp): Label
  def join(that: Label) = JoinLabel(this, that)
  def meet(that: Label) = MeetLabel(this, that)
}

// Behaves like a case class
// Not implemented as a case class so that UnknownLabel can inheret from it.
object ProdLabel {
  def apply(conf: LabelComp, integ: LabelComp) =
    new ProdLabel(conf, integ)
  def unapply(l: ProdLabel) = Some(l.conf, l.integ)
}

sealed class ProdLabel private[ir](val conf: LabelComp, val integ: LabelComp) extends Label {
  def serialize = s"$conf, $integ"
  def mapLabelComp(f: LabelComp => LabelComp): Label =
    ProdLabel(f(conf), f(integ))
  def mapLabel(f: Label => Label): Label = this
  override def equals(that: Any) = that match {
    case ProdLabel(confx, integx) => confx == conf && integx == integ
    case _ => false
  }
}

object IteLabel {
  val bot = ProdLabel(PolicyHolder.bottom, PolicyHolder.top)
  val top = ProdLabel(PolicyHolder.top, PolicyHolder.bottom)
  def apply(cond: Expression, condL: Label, trueL: Label, falseL: Label): Label = (cond, condL, trueL, falseL) match {
      case (_, cl: ProdLabel,_,_) if (cl == top) => top
      case (_,_,_,_) if (trueL == falseL && trueL != UnknownLabel) => JoinLabel(condL, trueL)
      case (_,cl: IteLabel,tl:Label,fl:Label) =>
        new IteLabel(cond,cl,tl,fl)
      case (_,cl: Label,tl:IteLabel,fl:Label) if (cond == tl.cond) =>
        IteLabel(cond,JoinLabel(cl,tl.condL),tl.trueL,JoinLabel(fl,tl.falseL))
      case (_,cl: Label,tl:Label,fl:IteLabel) if (cond == fl.cond)=>
        IteLabel(cond,JoinLabel(cl,fl.condL),JoinLabel(tl,fl.trueL),fl.falseL)
      case (_,_,_,_) => new IteLabel(cond, condL, trueL, falseL)
    }
  def unapply(l: IteLabel) = Some(l.cond, l.condL, l.trueL, l.falseL)
}

sealed class IteLabel private(val cond: Expression, val condL: Label, val trueL: Label, val falseL: Label) extends Label {
  def serialize = s"{${condL.serialize}} ? {${trueL.serialize}} : {${falseL.serialize}}"
  def mapLabelComp(f: LabelComp => LabelComp): Label = this
  def mapLabel(f: Label => Label): Label = IteLabel(cond, f(condL), f(trueL), f(falseL))
  override def equals(that: Any) = that match {
    case IteLabel(condx, condLx, truex, falsex) => cond == condx && condL == condLx && trueL == truex && falseL == falsex
    case _ => false
  }
}

object C {
  def apply(l: Label): LabelComp = l match {
    case ProdLabel(conf, _) => conf
    case _ =>
      throw new Exception(s"tried to conf project non-product:\n${l.serialize}\n${l.toString}")
      UnknownLabelComp
  }
}

object I {
  def apply(l: Label): LabelComp = l match {
    case ProdLabel(_, integ) => integ
    case _ =>
      throw new Exception(s"tried to integ project non-product:\n${l.serialize}\n${l.toString}")
      UnknownLabelComp
  }
}

case object UnknownLabel extends ProdLabel(UnknownLabelComp, UnknownLabelComp)

case class VarLabel(id: String) extends Label {
  def serialize = s"var: $id"
  override def toString = serialize
  def mapLabelComp(f: LabelComp => LabelComp): Label = this
  def mapLabel(f: Label => Label): Label = this
}

// Note: the join of two integrity components is defined in the same way as the 
// meet of two confidentiality components. So rather than needing to push 
// whether or not a component deals with integ or conf into the impl of 
// components, Meet is used as the join over integrity components and Join is 
// used as the meet over integrity components.

// These are "fake" case classes implemented using the same 
// fake-case-class-with-fancy-factory-apply idiom as the join and meet 
// label components
object JoinLabel {
  val bot = ProdLabel(PolicyHolder.bottom, PolicyHolder.top)
  val top = ProdLabel(PolicyHolder.top, PolicyHolder.bottom)
  def apply(l: Label, r: Label): Label = (l, r) match {
    case (lx, rx) if lx == rx => lx
    case (b:ProdLabel, _) if b == bot => r
    case (_, b:ProdLabel) if b == bot => l
    case (t:ProdLabel, _) if t == top => top
    case (_, t:ProdLabel) if t == top => top
    case (JoinLabel(lxx, rxx), rx) if lxx == rx || rxx == rx => JoinLabel(lxx, rxx)
    case (lx, JoinLabel(lxx, rxx)) if lxx == lx || rxx == lx => JoinLabel(lxx, rxx)
    case (ProdLabel(lc, li), ProdLabel(rc, ri)) =>
      ProdLabel(JoinLabelComp(lc, rc), MeetLabelComp(li, ri))
    case (bl: BundleLabel, br: BundleLabel) if(fields_match(bl, br)) =>
      BundleLabel(bl.fields map { f => f mapLabel { _ join field_label(br, f.name) } })
    case (bl: BundleLabel, br: BundleLabel) =>
        throw new Exception("Tried to join two bundles with non-matching fields")
    case (b: BundleLabel, r) => b mapLabel { _ join r }
    case (l, b: BundleLabel) => b mapLabel { _ join l }
    case (l: IteLabel, r: IteLabel) => {
      new JoinLabel(l,r)
    }
    case (l: IteLabel, r: Label) => IteLabel(l.cond, l.condL join r, l.trueL, l.falseL)
    case (l: Label, r: IteLabel) => IteLabel(r.cond, r.condL join l, r.trueL, r.falseL)
    case _ => new JoinLabel(l, r)
  }
  def apply(l: Label*) : Label = l.reduceRight { apply(_,_) }
  def unapply(j: JoinLabel) = Some((j.l, j.r))
}

sealed class JoinLabel private(val l: Label, val r: Label) extends Label {
  override def equals(that: Any) = that match {
    case JoinLabel(lx, rx) => lx == l && rx == r
    case _ => false
  }
  def serialize = s"{${l.serialize}} join {${r.serialize}}"
  def mapLabelComp(f: LabelComp => LabelComp): Label = this
  def mapLabel(f: Label => Label): Label = JoinLabel(f(l), f(r))
}

object MeetLabel {
  val bot = ProdLabel(PolicyHolder.bottom, PolicyHolder.top)
  val top = ProdLabel(PolicyHolder.top, PolicyHolder.bottom)
  def apply(l: Label, r: Label): Label = (l, r) match {
    case (lx, rx) if lx == rx => lx
    case (b:ProdLabel, _) if b == bot => bot
    case (_, b:ProdLabel) if b == bot => bot
    case (t:ProdLabel, _) if t == top => r
    case (_, t:ProdLabel) if t == top => l
    case (MeetLabel(lxx, rxx), rx) if lxx == rx || rxx == rx => MeetLabel(lxx, rxx)
    case (lx, MeetLabel(lxx, rxx)) if lxx == lx || rxx == lx => MeetLabel(lxx, rxx)
    case (ProdLabel(lc, li), ProdLabel(rc, ri)) =>
      ProdLabel(MeetLabelComp(lc, rc), JoinLabelComp(li, ri))
    case (bl: BundleLabel, br: BundleLabel) if(fields_match(bl, br)) =>
      BundleLabel(bl.fields map { f => f mapLabel { _ meet field_label(br, f.name) } })
    case (bl: BundleLabel, br: BundleLabel) =>
        throw new Exception("Tried to meet two Bundles with non-matching fields")
    case (b: BundleLabel, r) => b mapLabel { _ meet r }
    case (l, b: BundleLabel) => b mapLabel { _ meet l }
    case (l: IteLabel, r: IteLabel) => {
      new MeetLabel(l, r)
    }
    case (l: IteLabel, r: Label) => IteLabel(l.cond, l.condL meet r, l.trueL, l.falseL)
    case (l: Label, r: IteLabel) =>IteLabel(r.cond, r.condL meet l, r.trueL, r.falseL)
    case _ => new MeetLabel(l, r)
  }
  def apply(l: Label*) : Label = l.reduceRight { apply(_,_) }
  def unapply(j: MeetLabel) = Some((j.l, j.r))
}

sealed class MeetLabel private(val l: Label, val r: Label) extends Label {
  override def equals(that: Any) = that match {
    case MeetLabel(lx, rx) => lx == l && rx == r
    case _ => false
  }
  def serialize = s"{${l.serialize}} meet {${r.serialize}}"
  def mapLabelComp(f: LabelComp => LabelComp): Label = this
  def mapLabel(f: Label => Label): Label = MeetLabel(f(l), f(r))
}

// These never get serialized in a z3 file
sealed case class BundleLabel(fields: Seq[Field]) extends Label {
  def serializeField(f: Field) =  f.name + " : {" + f.lbl.serialize + "}"
  def serialize: String = (fields map (serializeField(_)) mkString ", ") 
  def mapLabel(f: Label => Label): Label = 
    BundleLabel( fields map ( x => x.copy(lbl = f(x.lbl))))
  def mapLabelComp(f: LabelComp => LabelComp): Label = this
}


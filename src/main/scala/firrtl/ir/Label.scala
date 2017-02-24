package firrtl
package ir

sealed abstract class Label extends FirrtlNode {
  def serialize: String
  def mapLabel(f: Label => Label): Label
  def mapLabelComp(f: LabelComp => LabelComp): Label
  def join(that: Label) = JoinLabel(this, that)
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

object C {
  def apply(l: Label): LabelComp = l match {
    case ProdLabel(conf, _) => conf
    case _ =>
      throw new Exception("tried to conf project Bundle")
      UnknownLabelComp
  }
}

object I {
  def apply(l: Label): LabelComp = l match {
    case ProdLabel(_, integ) => integ
    case _ =>
      throw new Exception("tried to integ project Bundle")
      UnknownLabelComp
  }
}

case object UnknownLabel extends ProdLabel(UnknownLabelComp, UnknownLabelComp)

object JoinLabel {
  def apply(l: Label, r: Label): Label = (l, r) match {
    case(ProdLabel(lc, li), ProdLabel(rc, ri)) =>
      ProdLabel(JoinLabelComp(lc, rc), JoinLabelComp(li, ri))
    case(_, _) => throw new Exception("Tried to join Bundle")
      UnknownLabel
  }
  def apply(l: Label*) : Label = l.reduceRight { apply(_,_) }
}

object MeetLabel {
  def apply(l: Label, r: Label): Label = (l, r) match {
    case(ProdLabel(lc, li), ProdLabel(rc, ri)) =>
      ProdLabel(MeetLabelComp(lc, rc), MeetLabelComp(li, ri))
    case(_, _) => throw new Exception("Tried to meet Bundle")
      UnknownLabel
  }
  def apply(l: Label*) : Label = l.reduceRight { apply(_,_) }
}

// These never get serialized in a z3 file
sealed case class BundleLabel(fields: Seq[Field]) extends Label {
  def serializeField(f: Field) = f.flip.serialize + f.name + " : " + f.lbl.serialize
  def serialize: String = (fields map (serializeField(_)) mkString ", ") 
  def mapLabel(f: Label => Label): Label = 
    BundleLabel( fields map ( x => x.copy(lbl = f(x.lbl))))
  def mapLabelComp(f: LabelComp => LabelComp): Label = this
}


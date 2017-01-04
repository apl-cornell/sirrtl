package firrtl.passes

//-----------------------------------------------------------------------------
// First Order Logic Constraints
//-----------------------------------------------------------------------------
// These are the same regardless of whether the integer theory or bitvector 
// theory is used.
abstract class Constraint {
  def serialize : String
  def mapCons(f: Constraint => Constraint) : Constraint
}

case class CEq(c1: Constraint, c2: Constraint) extends Constraint {
  def serialize = s"(= ${c1.serialize} ${c2.serialize})"
  def mapCons(f: Constraint => Constraint) = CEq(f(c1), f(c2))
}

case class CNot(c: Constraint) extends Constraint {
  def serialize = s"(not ${c.serialize})"
  def mapCons(f: Constraint => Constraint) = CNot(f(c))
}

case class CConj(c1: Constraint, c2: Constraint) extends Constraint {
  def serialize = s"(and ${c1.serialize} ${c2.serialize})"
  def mapCons(f: Constraint => Constraint) = CConj(f(c1),f(c2))
}

case class CDisj(c1: Constraint, c2: Constraint) extends Constraint {
  def serialize = s"(or ${c1.serialize} ${c2.serialize})"
  def mapCons(f: Constraint => Constraint) = CDisj(f(c1),f(c2))
}

case class CImpl(antec: Constraint, conseq: Constraint) extends Constraint {
  def serialize = s"(=> ${antec.serialize} ${conseq.serialize})"
  def mapCons(f: Constraint => Constraint) = CImpl(f(antec), f(conseq))
}

case class CIfTE(pred: Constraint, conseq: Constraint, alt: Constraint) extends Constraint {
  def serialize = s"(ite ${pred.serialize} ${conseq.serialize} ${alt.serialize})"
  def mapCons(f: Constraint => Constraint) = CIfTE(f(pred),f(conseq),f(alt))
}

case class CIdent(n: String) extends Constraint {
  def serialize = n
  def mapCons(f: Constraint => Constraint) = this
}

case object CTrue extends Constraint {
  def serialize = "true"
  def mapCons(f: Constraint => Constraint) = this
}

case class CBinOp(op: String, c1: Constraint, c2: Constraint) extends Constraint{
  def serialize = s"($op ${c1.serialize} ${c2.serialize})"
  def mapCons(f: Constraint => Constraint) = CBinOp(op, f(c1), f(c2))
}

case class CUnOp(op: String, c: Constraint) extends Constraint {
  def serialize = s"($op ${c.serialize})"
  def mapCons(f: Constraint => Constraint) = CUnOp(op, f(c))
}

case class CBVLit(value: BigInt, width: BigInt) extends Constraint {
  def serialize = s"(_ bv$value $width)"
  def mapCons(f: Constraint => Constraint) = this
}

case class CBVExtract(upper: BigInt, lower: BigInt, c: Constraint) extends Constraint {
  def serialize = s"((_ extract $upper $lower) ${c.serialize})"
  def mapCons(f: Constraint => Constraint) = CBVExtract(upper, lower, f(c))
}


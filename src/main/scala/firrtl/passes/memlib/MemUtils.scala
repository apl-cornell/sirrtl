// See LICENSE for license details.

package firrtl.passes

import firrtl._
import firrtl.ir._
import firrtl.Utils._
import firrtl.PrimOps._

object seqCat {
  def apply(args: Seq[Expression]): Expression = args.length match {
    case 0 => error("Empty Seq passed to seqcat")
    case 1 => args.head
    case 2 => DoPrim(PrimOps.Cat, args, Nil, UIntType(UnknownWidth), UnknownLabel)
    case _ =>
      val (high, low) = args splitAt (args.length / 2)
      DoPrim(PrimOps.Cat, Seq(seqCat(high), seqCat(low)), Nil, UIntType(UnknownWidth), UnknownLabel)
  }
}

/** Given an expression, return an expression consisting of all sub-expressions
 * concatenated (or flattened).
 */
object toBits {
  def apply(e: Expression): Expression = e match {
    case ex @ (_: WRef | _: WSubField | _: WSubIndex) => hiercat(ex)
    case t => error("Invalid operand expression for toBits!")
  }
  private def hiercat(e: Expression): Expression = e.tpe match {
    case t: VectorType => seqCat((0 until t.size).reverse map (i =>
      hiercat(WSubIndex(e, i, t.tpe, e.lbl, UNKNOWNGENDER))))
    case t: BundleType => seqCat(t.fields map (f =>
      hiercat(WSubField(e, f.name, f.tpe, e.lbl, UNKNOWNGENDER))))
    case t: GroundType => DoPrim(AsUInt, Seq(e), Seq.empty, UnknownType, UnknownLabel) 
    case t => error(s"Unknown type encountered in toBits! [${e.serialize} : ${e.tpe.serialize}]")
  }
}

/** Given a mask, return a bitmask corresponding to the desired datatype.
 *  Requirements:
 *    - The mask type and datatype must be equivalent, except any ground type in
 *         datatype must be matched by a 1-bit wide UIntType.
 *    - The mask must be a reference, subfield, or subindex
 *  The bitmask is a series of concatenations of the single mask bit over the
 *    length of the corresponding ground type, e.g.:
 *{{{
 * wire mask: {x: UInt<1>, y: UInt<1>}
 * wire data: {x: UInt<2>, y: SInt<2>}
 * // this would return:
 * cat(cat(mask.x, mask.x), cat(mask.y, mask.y))
 * }}}
 */
object toBitMask {
  def apply(mask: Expression, dataType: Type): Expression = mask match {
    case ex @ (_: WRef | _: WSubField | _: WSubIndex) => hiermask(ex, dataType)
    case t => error("Invalid operand expression for toBits!")
  }
  private def hiermask(mask: Expression, dataType: Type): Expression =
    (mask.tpe, dataType) match {
      case (mt: VectorType, dt: VectorType) =>
        seqCat((0 until mt.size).reverse map { i =>
          hiermask(WSubIndex(mask, i, mt.tpe, mask.lbl, UNKNOWNGENDER), dt.tpe)
        })
      case (mt: BundleType, dt: BundleType) =>
        seqCat((mt.fields zip dt.fields) map { case (mf, df) =>
          hiermask(WSubField(mask, mf.name, mf.tpe, mask.lbl, UNKNOWNGENDER), df.tpe)
        })
      case (UIntType(width), dt: GroundType) if width == IntWidth(BigInt(1)) =>
        seqCat(List.fill(bitWidth(dt).intValue)(mask))
      case (mt, dt) => error("Invalid type for mask component!")
    }
}

object getWidth {
  def apply(t: Type): Width = t match {
    case t: GroundType => t.width
    case _ => error("No width!")
  }
  def apply(e: Expression): Width = apply(e.tpe)
}

object bitWidth {
  def apply(dt: Type): BigInt = widthOf(dt)
  private def widthOf(dt: Type): BigInt = dt match {
    case t: VectorType => t.size * bitWidth(t.tpe)
    case t: BundleType => t.fields.map(f => bitWidth(f.tpe)).foldLeft(BigInt(0))(_+_)
    case GroundType(IntWidth(width)) => width
    case t => error(s"Unknown type encountered in bitWidth! [${dt.serialize}]")
  }
}

object castRhs {
  def apply(lhst: Type, rhs: Expression) = {
    lhst match {
      case _: SIntType => DoPrim(AsSInt, Seq(rhs), Seq.empty, lhst, UnknownLabel)
      case FixedType(_, IntWidth(p)) => DoPrim(AsFixedPoint, Seq(rhs), Seq(p), lhst,
        UnknownLabel)
      case _: UIntType => rhs
    }  
  }
}

object fromBits {
  def apply(lhs: Expression, rhs: Expression): Statement = {
    val fbits = lhs match {
      case ex @ (_: WRef | _: WSubField | _: WSubIndex) => getPart(ex, ex.tpe, rhs, 0)
      case _ => error("Invalid LHS expression for fromBits!")
    }
    Block(fbits._2)
  }
  private def getPartGround(lhs: Expression,
                            lhst: Type,
                            rhs: Expression,
                            offset: BigInt): (BigInt, Seq[Statement]) = {
    val intWidth = bitWidth(lhst)
    val sel = DoPrim(PrimOps.Bits, Seq(rhs), Seq(offset + intWidth - 1, offset), UnknownType, UnknownLabel)
    val rhsConnect = castRhs(lhst, sel)
    (offset + intWidth, Seq(Connect(NoInfo, lhs, rhsConnect)))
  }
  private def getPart(lhs: Expression,
                      lhst: Type,
                      rhs: Expression,
                      offset: BigInt): (BigInt, Seq[Statement]) =
    lhst match {
      case t: VectorType => (0 until t.size foldLeft (offset, Seq[Statement]())) {
        case ((curOffset, stmts), i) =>
          val subidx = WSubIndex(lhs, i, t.tpe, lhs.lbl, UNKNOWNGENDER)
          val (tmpOffset, substmts) = getPart(subidx, t.tpe, rhs, curOffset)
          (tmpOffset, stmts ++ substmts)
      }
      case t: BundleType => (t.fields foldRight (offset, Seq[Statement]())) {
        case (f, (curOffset, stmts)) =>
          val subfield = WSubField(lhs, f.name, f.tpe, f.lbl, UNKNOWNGENDER)
          val (tmpOffset, substmts) = getPart(subfield, f.tpe, rhs, curOffset)
          (tmpOffset, stmts ++ substmts)
      }
      case t: GroundType => getPartGround(lhs, t, rhs, offset)
      case t => error("Unknown type encountered in fromBits!")
    }
}

object createMask {
  def apply(dt: Type): Type = dt match {
    case t: VectorType => VectorType(apply(t.tpe), t.size)
    case t: BundleType => BundleType(t.fields map (f => f copy (tpe=apply(f.tpe))))
    case t: GroundType => BoolType
  }
}

object createRef {
  def apply(n: String, t: Type = UnknownType, l: Label = UnknownLabel, k: Kind = ExpKind) = WRef(n, t, l, k, UNKNOWNGENDER)
}

object createSubField {
  def apply(exp: Expression, n: String) = WSubField(exp, n, field_type(exp.tpe, n), exp.lbl, UNKNOWNGENDER)
}

object connectFields {
  def apply(lref: Expression, lname: String, rref: Expression, rname: String): Connect =
    Connect(NoInfo, createSubField(lref, lname), createSubField(rref, rname))
}

object flattenType {
  def apply(t: Type) = UIntType(IntWidth(bitWidth(t)))
}

object MemPortUtils {
  type MemPortMap = collection.mutable.HashMap[String, Expression]
  type Memories = collection.mutable.ArrayBuffer[DefMemory]
  type Modules = collection.mutable.ArrayBuffer[DefModule]

  def defaultPortSeq(mem: DefMemory): Seq[Field] = Seq(
    Field("addr", Default, UIntType(IntWidth(ceilLog2(mem.depth) max 1)), mem.lbl, false),
    Field("en", Default, BoolType, mem.lbl, false),
    Field("clk", Default, ClockType, mem.lbl, false)
  )

  // Todo: merge it with memToBundle
  def memType(mem: DefMemory): Type = {
    val rType = BundleType(defaultPortSeq(mem) :+
      Field("data", Flip, mem.dataType, mem.lbl, false))
    val wType = BundleType(defaultPortSeq(mem) ++ Seq(
      Field("data", Default, mem.dataType, mem.lbl, false),
      Field("mask", Default, createMask(mem.dataType), mem.lbl, false)))
    val rwType = BundleType(defaultPortSeq(mem) ++ Seq(
      Field("rdata", Flip, mem.dataType, mem.lbl, false),
      Field("wmode", Default, BoolType, mem.lbl, false),
      Field("wdata", Default, mem.dataType, mem.lbl, false),
      Field("wmask", Default, createMask(mem.dataType), mem.lbl, false)))
    BundleType(
      (mem.readers map (Field(_, Flip, rType, mem.lbl, false))) ++
      (mem.writers map (Field(_, Flip, wType, mem.lbl, false))) ++
      (mem.readwriters map (Field(_, Flip, rwType, mem.lbl, false))))
  }

  def memPortField(s: DefMemory, p: String, f: String): Expression = {
    val mem = WRef(s.name, memType(s), s.lbl, MemKind, UNKNOWNGENDER)
    val t1 = field_type(mem.tpe, p)
    val t2 = field_type(t1, f)
    WSubField(WSubField(mem, p, t1, mem.lbl, UNKNOWNGENDER), f, t2, mem.lbl, UNKNOWNGENDER)
  }
}

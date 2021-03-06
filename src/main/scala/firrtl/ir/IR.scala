// See LICENSE for license details.

package firrtl
package ir

import Utils.indent

/** Intermediate Representation */
abstract class FirrtlNode {
  def serialize: String
}

abstract class Info extends FirrtlNode {
  // default implementation
  def serialize: String = this.toString
  def ++(that: Info): Info
}
case object NoInfo extends Info {
  override def toString: String = ""
  def ++(that: Info): Info = that
}
case class FileInfo(info: StringLit) extends Info {
  override def toString: String = " @[" + info.serialize + "]"
  def ++(that: Info): Info = MultiInfo(Seq(this, that))
}
case class MultiInfo(infos: Seq[Info]) extends Info {
  private def collectStringLits(info: Info): Seq[StringLit] = info match {
    case FileInfo(lit) => Seq(lit)
    case MultiInfo(seq) => seq flatMap collectStringLits
    case NoInfo => Seq.empty
  }
  override def toString: String =
    collectStringLits(this).map(_.serialize).mkString(" @[", " ", "]")
  def ++(that: Info): Info = MultiInfo(Seq(this, that))
}

trait HasName {
  val name: String
}
trait HasInfo {
  val info: Info
}
trait IsDeclaration extends HasName with HasInfo

case class StringLit(array: Array[Byte]) extends FirrtlNode {
  def serialize: String = FIRRTLStringLitHandler.escape(this)
}

/** Primitive Operation
  *
  * See [[PrimOps]]
  */
abstract class PrimOp extends FirrtlNode {
  def serialize: String = this.toString
}

abstract class Expression extends FirrtlNode {
  def tpe: Type
  def lbl: Label
  def mapExpr(f: Expression => Expression): Expression
  def mapLabel(f: Label => Label): Expression
  def mapType(f: Type => Type): Expression
  def mapWidth(f: Width => Width): Expression
}

case object FnBinding extends Expression {
  def tpe = UnknownType
  def lbl = UnknownLabel
  def serialize: String = "_"
  def mapExpr(f: Expression => Expression): Expression = this
  def mapLabel(f: Label => Label): Expression = this
  def mapType(f: Type => Type): Expression = this
  def mapWidth(f: Width => Width): Expression = this
}

case class Declassify(expr: Expression, lbl: Label) extends Expression {
  def tpe = expr.tpe
  def serialize: String =
    s"declassify(${expr.serialize}, ${expr.lbl.serialize} to ${lbl.serialize})"
  def mapExpr(f: Expression => Expression): Expression = this.copy(expr = f(expr))
  def mapLabel(f: Label => Label): Expression = this.copy(lbl = f(lbl))
  def mapType(f: Type => Type): Expression = this
  def mapWidth(f: Width => Width): Expression = this
}

case class Endorse(expr: Expression, lbl: Label) extends Expression {
  def tpe = expr.tpe
  def serialize: String =
    s"endorse(${expr.serialize}, ${expr.lbl.serialize} to ${lbl.serialize})"
  def mapExpr(f: Expression => Expression): Expression = this.copy(expr = f(expr))
  def mapLabel(f: Label => Label): Expression = this.copy(lbl = f(lbl))
  def mapType(f: Type => Type): Expression = this
  def mapWidth(f: Width => Width): Expression = this
}

case class Reference(name: String, tpe: Type, lbl: Label) extends Expression with HasName {
  def serialize: String = name
  def mapExpr(f: Expression => Expression): Expression = this
  def mapType(f: Type => Type): Expression = this.copy(tpe = f(tpe))
  def mapLabel(f: Label => Label): Expression = this.copy(lbl = f(lbl))
  def mapWidth(f: Width => Width): Expression = this
}
case class SubField(expr: Expression, name: String, tpe: Type, lbl: Label) extends Expression with HasName {
  def serialize: String = s"${expr.serialize}.$name"
  def mapExpr(f: Expression => Expression): Expression = this.copy(expr = f(expr))
  def mapType(f: Type => Type): Expression = this.copy(tpe = f(tpe))
  def mapLabel(f: Label => Label): Expression = this.copy(lbl = f(lbl))
  def mapWidth(f: Width => Width): Expression = this
}
case class SubIndex(expr: Expression, value: Int, tpe: Type, lbl: Label) extends Expression {
  def serialize: String = s"${expr.serialize}[$value]"
  def mapExpr(f: Expression => Expression): Expression = this.copy(expr = f(expr))
  def mapType(f: Type => Type): Expression = this.copy(tpe = f(tpe))
  def mapLabel(f: Label => Label): Expression = this.copy(lbl = f(lbl))
  def mapWidth(f: Width => Width): Expression = this
}
case class SubAccess(expr: Expression, index: Expression, tpe: Type, lbl: Label) extends Expression {
  def serialize: String = s"${expr.serialize}[${index.serialize}]"
  def mapExpr(f: Expression => Expression): Expression =
    this.copy(expr = f(expr), index = f(index))
  def mapType(f: Type => Type): Expression = this.copy(tpe = f(tpe))
  def mapLabel(f: Label => Label): Expression = this.copy(lbl = f(lbl))
  def mapWidth(f: Width => Width): Expression = this
}
case class Mux(cond: Expression, tval: Expression, fval: Expression, tpe: Type, lbl: Label) extends Expression {
  def serialize: String = s"mux(${cond.serialize}, ${tval.serialize}, ${fval.serialize})"
  def mapExpr(f: Expression => Expression): Expression = Mux(f(cond), f(tval), f(fval), tpe, lbl)
  def mapType(f: Type => Type): Expression = this.copy(tpe = f(tpe))
  def mapLabel(f: Label => Label): Expression = this.copy(lbl = f(lbl))
  def mapWidth(f: Width => Width): Expression = this
}
case class ValidIf(cond: Expression, value: Expression, tpe: Type, lbl: Label) extends Expression {
  def serialize: String = s"validif(${cond.serialize}, ${value.serialize})"
  def mapExpr(f: Expression => Expression): Expression = ValidIf(f(cond), f(value), tpe, lbl)
  def mapType(f: Type => Type): Expression = this.copy(tpe = f(tpe))
  def mapLabel(f: Label => Label): Expression = this.copy(lbl = f(lbl))
  def mapWidth(f: Width => Width): Expression = this
}

case class Next(exp: Expression, tpe: Type, lbl: Label, gender: Gender) extends Expression {
  def serialize = s"next(${exp.serialize})"
  def mapExpr(f: Expression => Expression): Expression = this.copy(exp = f(exp))
  def mapType(f: Type => Type): Expression = this.copy(tpe = f(tpe))
  def mapLabel(f: Label => Label): Expression = this.copy(lbl = f(lbl))
  def mapWidth(f: Width => Width): Expression = this
}

abstract class Literal extends Expression {
  val value: BigInt
  val width: Width
}
case class UIntLiteral(value: BigInt, width: Width, lbl: Label) extends Literal {
  def tpe = UIntType(width)
  def serialize = s"UInt${width.serialize}(" + Utils.serialize(value) + ")"
  def mapExpr(f: Expression => Expression): Expression = this
  def mapType(f: Type => Type): Expression = this
  def mapLabel(f: Label => Label): Expression = this.copy(lbl = f(lbl))
  def mapWidth(f: Width => Width): Expression = this.copy(width = f(width))
}
case class SIntLiteral(value: BigInt, width: Width, lbl: Label) extends Literal {
  def tpe = SIntType(width)
  def serialize = s"SInt${width.serialize}(" + Utils.serialize(value) + ")"
  def mapExpr(f: Expression => Expression): Expression = this
  def mapType(f: Type => Type): Expression = this
  def mapLabel(f: Label => Label): Expression = this.copy(lbl = f(lbl))
  def mapWidth(f: Width => Width): Expression = this.copy(width = f(width))
}
case class FixedLiteral(value: BigInt, width: Width, point: Width, lbl: Label) extends Literal {
  def tpe = FixedType(width, point)
  def serialize = {
    val pstring = if(point == UnknownWidth) "" else s"<${point.serialize}>"
    s"Fixed${width.serialize}$pstring(" + Utils.serialize(value) + ")"
  }
  def mapExpr(f: Expression => Expression): Expression = this
  def mapType(f: Type => Type): Expression = this
  def mapLabel(f: Label => Label): Expression = this.copy(lbl = f(lbl))
  def mapWidth(f: Width => Width): Expression = FixedLiteral(value, f(width), f(point), lbl)
}
case class DoPrim(op: PrimOp, args: Seq[Expression], consts: Seq[BigInt], tpe: Type, lbl: Label) extends Expression {
  def serialize: String = op.serialize + "(" +
    (args.map(_.serialize) ++ consts.map(_.toString)).mkString(", ") + ")"
  def mapExpr(f: Expression => Expression): Expression = this.copy(args = args map f)
  def mapType(f: Type => Type): Expression = this.copy(tpe = f(tpe))
  def mapLabel(f: Label => Label): Expression = this.copy(lbl = f(lbl))
  def mapWidth(f: Width => Width): Expression = this
}

abstract class Statement extends FirrtlNode {
  def info : Info
  def mapStmt(f: Statement => Statement): Statement
  def mapExpr(f: Expression => Expression): Statement
  def mapType(f: Type => Type): Statement
  def mapLabel(f: Label => Label): Statement
  def mapString(f: String => String): Statement
}
case class DefWire(info: Info, name: String, tpe: Type, lbl: Label)
  extends Statement with IsDeclaration {
  def serialize: String = {
    val lbl_s = (lbl match {case UnknownLabel => ""; case _ => s"{${lbl.serialize}} "})
    s"wire $name : ${lbl_s}${tpe.serialize}" + info.serialize 
  }
  def mapStmt(f: Statement => Statement): Statement = this
  def mapExpr(f: Expression => Expression): Statement = this
  def mapType(f: Type => Type): Statement = DefWire(info, name, f(tpe), lbl)
  def mapString(f: String => String): Statement = DefWire(info, f(name), tpe, lbl)
  def mapLabel(f: Label => Label): Statement = this.copy(lbl = f(lbl))
}
case class DefRegister(
    info: Info,
    name: String,
    tpe: Type,
    lbl: Label,
    clock: Expression,
    reset: Expression,
    init: Expression) extends Statement with IsDeclaration {
  def serialize: String = {
    val lbl_s = lbl match {case UnknownLabel => ""; case _ => s"{${lbl.serialize}} "}
    s"reg $name : ${lbl_s}${tpe.serialize}, ${clock.serialize} with :" +
    indent("\n" + s"reset => (${reset.serialize}, ${init.serialize})"
      + info.serialize) 
  }
  def mapStmt(f: Statement => Statement): Statement = this
  def mapExpr(f: Expression => Expression): Statement =
    DefRegister(info, name, tpe, lbl, f(clock), f(reset), f(init))
  def mapType(f: Type => Type): Statement = this.copy(tpe = f(tpe))
  def mapString(f: String => String): Statement = this.copy(name = f(name))
  def mapLabel(f: Label => Label): Statement = this.copy(lbl = f(lbl))

}
case class DefInstance(info: Info, name: String, module: String) extends Statement with IsDeclaration {
  def serialize: String = s"inst $name of $module" + info.serialize
  def mapStmt(f: Statement => Statement): Statement = this
  def mapExpr(f: Expression => Expression): Statement = this
  def mapType(f: Type => Type): Statement = this
  def mapString(f: String => String): Statement = DefInstance(info, f(name), module)
  def mapLabel(f: Label => Label): Statement = this
}
case class DefMemory(
    info: Info,
    name: String,
    dataType: Type,
    lbl: Label,
    depth: Int,
    writeLatency: Int,
    readLatency: Int,
    readers: Seq[String],
    writers: Seq[String],
    readwriters: Seq[String],
    // TODO: handle read-under-write
    readUnderWrite: Option[String] = None) extends Statement with IsDeclaration {
  def serialize: String =
    s"mem $name :"+ info.serialize +
    indent(
      (Seq("\ndata-type => " + dataType.serialize,
          "depth => " + depth,
          "read-latency => " + readLatency,
          "write-latency => " + writeLatency) ++
          (readers map ("reader => " + _)) ++
          (writers map ("writer => " + _)) ++
          (readwriters map ("readwriter => " + _)) ++
       Seq("read-under-write => undefined")) mkString "\n")
  def mapStmt(f: Statement => Statement): Statement = this
  def mapExpr(f: Expression => Expression): Statement = this
  def mapType(f: Type => Type): Statement = this.copy(dataType = f(dataType))
  def mapString(f: String => String): Statement = this.copy(name = f(name))
  def mapLabel(f: Label => Label): Statement = this.copy(lbl = f(lbl))
}
case class DefNode(info: Info, name: String, value: Expression, lbl: Label) extends Statement with IsDeclaration {
  val lbl_s = lbl match {case UnknownLabel => ""; case _ => s"{${lbl.serialize}} "}
  def serialize: String = s"node $name ${lbl_s}= ${value.serialize}" + info.serialize
  def mapStmt(f: Statement => Statement): Statement = this
  def mapExpr(f: Expression => Expression): Statement = this.copy(value = f(value))
  def mapType(f: Type => Type): Statement = this
  def mapString(f: String => String): Statement = this.copy(name = f(name))
  def mapLabel(f: Label => Label): Statement = this.copy(lbl = f(lbl))
}
case class Conditionally(
    info: Info,
    pred: Expression,
    conseq: Statement,
    alt: Statement) extends Statement with HasInfo {
  def serialize: String =
    s"when ${pred.serialize} :" + info.serialize +
    indent("\n" + conseq.serialize) +
    (if (alt == EmptyStmt) ""
    else "\nelse :" + indent("\n" + alt.serialize))
  def mapStmt(f: Statement => Statement): Statement = Conditionally(info, pred, f(conseq), f(alt))
  def mapExpr(f: Expression => Expression): Statement = Conditionally(info, f(pred), conseq, alt)
  def mapType(f: Type => Type): Statement = this
  def mapString(f: String => String): Statement = this
  def mapLabel(f: Label => Label): Statement = this
}
case class Block(stmts: Seq[Statement]) extends Statement {
  def serialize: String = stmts map (_.serialize) mkString "\n"
  def info = NoInfo
  def mapStmt(f: Statement => Statement): Statement = Block(stmts map f)
  def mapExpr(f: Expression => Expression): Statement = this
  def mapType(f: Type => Type): Statement = this
  def mapString(f: String => String): Statement = this
  def mapLabel(f: Label => Label): Statement = this
}
case class PartialConnect(info: Info, loc: Expression, expr: Expression) extends Statement with HasInfo {
  def serialize: String =  s"${loc.serialize} <- ${expr.serialize}" + info.serialize
  def mapStmt(f: Statement => Statement): Statement = this
  def mapExpr(f: Expression => Expression): Statement = PartialConnect(info, f(loc), f(expr))
  def mapType(f: Type => Type): Statement = this
  def mapString(f: String => String): Statement = this
  def mapLabel(f: Label => Label): Statement = this
}
case class Connect(info: Info, loc: Expression, expr: Expression) extends Statement with HasInfo {
  // def serialize: String =  s"${loc.serialize} <= ${expr.serialize}" + info.serialize
  def serialize: String = {
    val lbl_l = loc.lbl match { case UnknownLabel => ""; case _ => s" {${loc.lbl.serialize}}" }
    val lbl_r = expr.lbl match { case UnknownLabel => ""; case _ => s" {${expr.lbl.serialize}}" }
    s"${loc.serialize}${lbl_l} <= ${expr.serialize}${lbl_r}" + info.serialize
  }
  def mapStmt(f: Statement => Statement): Statement = this
  def mapExpr(f: Expression => Expression): Statement = Connect(info, f(loc), f(expr))
  def mapType(f: Type => Type): Statement = this
  def mapString(f: String => String): Statement = this
  def mapLabel(f: Label => Label): Statement = this
}
case class IsInvalid(info: Info, expr: Expression) extends Statement with HasInfo {
  def serialize: String =  s"${expr.serialize} is invalid" + info.serialize
  def mapStmt(f: Statement => Statement): Statement = this
  def mapExpr(f: Expression => Expression): Statement = IsInvalid(info, f(expr))
  def mapType(f: Type => Type): Statement = this
  def mapString(f: String => String): Statement = this
  def mapLabel(f: Label => Label): Statement = this
}
case class Attach(info: Info, source: Expression, exprs: Seq[Expression]) extends Statement with HasInfo {
  def serialize: String = "attach " + source.serialize + " to (" + exprs.map(_.serialize).mkString(", ") + ")"
  def mapStmt(f: Statement => Statement): Statement = this
  def mapExpr(f: Expression => Expression): Statement = Attach(info, f(source), exprs map f)
  def mapType(f: Type => Type): Statement = this
  def mapString(f: String => String): Statement = this
  def mapLabel(f: Label => Label) : Statement = this
}
case class Stop(info: Info, ret: Int, clk: Expression, en: Expression) extends Statement with HasInfo {
  def serialize: String = s"stop(${clk.serialize}, ${en.serialize}, $ret)" + info.serialize
  def mapStmt(f: Statement => Statement): Statement = this
  def mapExpr(f: Expression => Expression): Statement = Stop(info, ret, f(clk), f(en))
  def mapType(f: Type => Type): Statement = this
  def mapString(f: String => String): Statement = this
  def mapLabel(f: Label => Label): Statement = this
}
case class Print(
    info: Info,
    string: StringLit,
    args: Seq[Expression],
    clk: Expression,
    en: Expression) extends Statement with HasInfo {
  def serialize: String = {
    val strs = Seq(clk.serialize, en.serialize, "\"" + string.serialize + "\"") ++
               (args map (_.serialize))
    "printf(" + (strs mkString ", ") + ")" + info.serialize
  }
  def mapStmt(f: Statement => Statement): Statement = this
  def mapExpr(f: Expression => Expression): Statement = Print(info, string, args map f, f(clk), f(en))
  def mapType(f: Type => Type): Statement = this
  def mapString(f: String => String): Statement = this
  def mapLabel(f: Label => Label): Statement = this 
}
case object EmptyStmt extends Statement {
  def serialize: String = "skip"
  def info = NoInfo
  def mapStmt(f: Statement => Statement): Statement = this
  def mapExpr(f: Expression => Expression): Statement = this
  def mapType(f: Type => Type): Statement = this
  def mapString(f: String => String): Statement = this
  def mapLabel(f: Label => Label): Statement = this
}

abstract class Width extends FirrtlNode {
  def +(x: Width): Width = (this, x) match {
    case (a: IntWidth, b: IntWidth) => IntWidth(a.width + b.width)
    case _ => UnknownWidth
  }
  def -(x: Width): Width = (this, x) match {
    case (a: IntWidth, b: IntWidth) => IntWidth(a.width - b.width)
    case _ => UnknownWidth
  }
  def max(x: Width): Width = (this, x) match {
    case (a: IntWidth, b: IntWidth) => IntWidth(a.width max b.width)
    case _ => UnknownWidth
  }
  def min(x: Width): Width = (this, x) match {
    case (a: IntWidth, b: IntWidth) => IntWidth(a.width min b.width)
    case _ => UnknownWidth
  }
}
/** Positive Integer Bit Width of a [[GroundType]] */
object IntWidth {
  private val maxCached = 1024
  private val cache = new Array[IntWidth](maxCached + 1)
  def apply(width: BigInt): IntWidth = {
    if (0 <= width && width <= maxCached) {
      val i = width.toInt
      var w = cache(i)
      if (w eq null) {
        w = new IntWidth(width)
        cache(i) = w
      }
      w
    } else new IntWidth(width)
  }
  // For pattern matching
  def unapply(w: IntWidth): Option[BigInt] = Some(w.width)
}
class IntWidth(val width: BigInt) extends Width with Product {
  def serialize: String = s"<$width>"
  override def equals(that: Any) = that match {
    case w: IntWidth => width == w.width
    case _ => false
  }
  override def hashCode = width.toInt
  override def productPrefix = "IntWidth"
  override def toString = s"$productPrefix($width)"
  def copy(width: BigInt = width) = IntWidth(width)
  def canEqual(that: Any) = that.isInstanceOf[Width]
  def productArity = 1
  def productElement(int: Int) = int match {
    case 0 => width
    case _ => throw new IndexOutOfBoundsException
  }
}
case object UnknownWidth extends Width {
  def serialize: String = ""
}

/** Orientation of [[Field]] */
abstract class Orientation extends FirrtlNode
case object Default extends Orientation {
  def serialize: String = ""
}
case object Flip extends Orientation {
  def serialize: String = "flip "
}

/** Field of [[BundleType]] */
case class Field(name: String, flip: Orientation, tpe: Type, lbl: Label,
  isSeq: Boolean)
  extends FirrtlNode with HasName {
  val lbl_s = lbl match {case UnknownLabel => ""; case _ => s"{${lbl.serialize}} "}
  def serialize: String = flip.serialize + name + " : " + lbl_s + tpe.serialize
  def mapLabel(f: Label => Label): Field = this.copy(lbl = f(lbl))
}

abstract class Type extends FirrtlNode {
  def mapType(f: Type => Type): Type
  def mapWidth(f: Width => Width): Type
}
abstract class GroundType extends Type {
  val width: Width
  def mapType(f: Type => Type): Type = this
}
object GroundType {
  def unapply(ground: GroundType): Option[Width] = Some(ground.width)
}
abstract class AggregateType extends Type {
  def mapWidth(f: Width => Width): Type = this
}
case class UIntType(width: Width) extends GroundType {
  def serialize: String = "UInt" + width.serialize
  def mapWidth(f: Width => Width): Type = UIntType(f(width))
}
case class SIntType(width: Width) extends GroundType {
  def serialize: String = "SInt" + width.serialize
  def mapWidth(f: Width => Width): Type = SIntType(f(width))
}
case class FixedType(width: Width, point: Width) extends GroundType {
  override def serialize: String = {
    val pstring = if(point == UnknownWidth) "" else s"<${point.serialize}>"
    s"Fixed${width.serialize}$pstring"
  }
  def mapWidth(f: Width => Width): Type = FixedType(f(width), f(point))
}
case class BundleType(fields: Seq[Field]) extends AggregateType {
  def serialize: String = "{ " + (fields map (_.serialize) mkString ", ") + "}"
  def mapType(f: Type => Type): Type =
    BundleType(fields map (x => x.copy(tpe = f(x.tpe))))
}
case class VectorType(tpe: Type, size: Int) extends AggregateType {
  def serialize: String = tpe.serialize + s"[$size]"
  def mapType(f: Type => Type): Type = this.copy(tpe = f(tpe))
}
case object ClockType extends GroundType {
  val width = IntWidth(1)
  def serialize: String = "Clock"
  def mapWidth(f: Width => Width): Type = this
}
case class AnalogType(width: Width) extends GroundType {
  def serialize: String = "Analog" + width.serialize
  def mapWidth(f: Width => Width): Type = AnalogType(f(width))
}
case object UnknownType extends Type {
  def serialize: String = "?"
  def mapType(f: Type => Type): Type = this
  def mapWidth(f: Width => Width): Type = this
}

/** [[Port]] Direction */
abstract class Direction extends FirrtlNode
case object Input extends Direction {
  def serialize: String = "input"
}
case object Output extends Direction {
  def serialize: String = "output"
}

/** [[DefModule]] Port */
case class Port(
    info: Info,
    name: String,
    direction: Direction,
    tpe: Type,
    lbl: Label) extends FirrtlNode with IsDeclaration {
  def serialize: String = {
    val lbl_s = lbl match {case UnknownLabel => ""; case _ => s"{${lbl.serialize}} "}
    s"${direction.serialize} $name : ${lbl_s}${tpe.serialize}" + info.serialize
  }
}

/** Parameters for external modules */
sealed abstract class Param extends FirrtlNode {
  def name: String
  def serialize: String = s"parameter $name = "
}
/** Integer (of any width) Parameter */
case class IntParam(name: String, value: BigInt) extends Param {
  override def serialize: String = super.serialize + value
}
/** IEEE Double Precision Parameter (for Verilog real) */
case class DoubleParam(name: String, value: Double) extends Param {
  override def serialize: String = super.serialize + value
}
/** String Parameter */
case class StringParam(name: String, value: StringLit) extends Param {
  override def serialize: String = super.serialize + value.serialize
}
/** Raw String Parameter
  * Useful for Verilog type parameters
  * @note Firrtl doesn't guarantee anything about this String being legal in any backend
  */
case class RawStringParam(name: String, value: String) extends Param {
  override def serialize: String = super.serialize + s"'$value'"
}

/** Base class for modules */
abstract class DefModule extends FirrtlNode with IsDeclaration {
  val info : Info
  val name : String
  val ports : Seq[Port]
  protected def serializeHeader(tpe: String): String =
    s"$tpe $name :${info.serialize}${indent(ports.map("\n" + _.serialize).mkString)}\n"
  def mapStmt(f: Statement => Statement): DefModule
  def mapPort(f: Port => Port): DefModule
  def mapString(f: String => String): DefModule
}
/** Internal Module
  *
  * An instantiable hardware block
  */
case class Module(info: Info, name: String, ports: Seq[Port], body: Statement) extends DefModule {
  def serialize: String = serializeHeader("module") + indent("\n" + body.serialize)
  def mapStmt(f: Statement => Statement): DefModule = this.copy(body = f(body))
  def mapPort(f: Port => Port): DefModule = this.copy(ports = ports map f)
  def mapString(f: String => String): DefModule = this.copy(name = f(name))
}
/** External Module
  *
  * Generally used for Verilog black boxes
  * @param defname Defined name of the external module (ie. the name Firrtl will emit)
  */
case class ExtModule(
    info: Info,
    name: String,
    ports: Seq[Port],
    defname: String,
    params: Seq[Param]) extends DefModule {
  def serialize: String = serializeHeader("extmodule") +
    indent(s"\ndefname = $defname\n" + params.map(_.serialize).mkString("\n"))
  def mapStmt(f: Statement => Statement): DefModule = this
  def mapPort(f: Port => Port): DefModule = this.copy(ports = ports map f)
  def mapString(f: String => String): DefModule = this.copy(name = f(name))
}

case class Circuit(info: Info, modules: Seq[DefModule], main: String) extends FirrtlNode with HasInfo {
  def serialize: String =
    s"circuit $main :" + info.serialize +
    (modules map ("\n" + _.serialize) map indent mkString "\n") + "\n"
}

/*
Copyright (c) 2014 - 2016 The Regents of the University of
California (Regents). All Rights Reserved.  Redistribution and use in
source and binary forms, with or without modification, are permitted
provided that the following conditions are met:
   * Redistributions of source code must retain the above
     copyright notice, this list of conditions and the following
     two paragraphs of disclaimer.
   * Redistributions in binary form must reproduce the above
     copyright notice, this list of conditions and the following
     two paragraphs of disclaimer in the documentation and/or other materials
     provided with the distribution.
   * Neither the name of the Regents nor the names of its contributors
     may be used to endorse or promote products derived from this
     software without specific prior written permission.
IN NO EVENT SHALL REGENTS BE LIABLE TO ANY PARTY FOR DIRECT, INDIRECT,
SPECIAL, INCIDENTAL, OR CONSEQUENTIAL DAMAGES, INCLUDING LOST PROFITS,
ARISING OUT OF THE USE OF THIS SOFTWARE AND ITS DOCUMENTATION, EVEN IF
REGENTS HAS BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
REGENTS SPECIFICALLY DISCLAIMS ANY WARRANTIES, INCLUDING, BUT NOT
LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
A PARTICULAR PURPOSE. THE SOFTWARE AND ACCOMPANYING DOCUMENTATION, IF
ANY, PROVIDED HEREUNDER IS PROVIDED "AS IS". REGENTS HAS NO OBLIGATION
TO PROVIDE MAINTENANCE, SUPPORT, UPDATES, ENHANCEMENTS, OR
MODIFICATIONS.
*/

package firrtl.passes

import com.typesafe.scalalogging.LazyLogging

import firrtl._
import firrtl.ir._
import firrtl.Utils._
import firrtl.Mappers._

// Datastructures
import scala.collection.mutable.HashMap

/** Removes all aggregate types from a [[firrtl.ir.Circuit]]
  *
  * @note Assumes [[firrtl.ir.SubAccess]]es have been removed
  * @note Assumes [[firrtl.ir.Connect]]s and [[firrtl.ir.IsInvalid]]s only operate on [[firrtl.ir.Expression]]s of ground type
  * @example
  * {{{
  *   wire foo : { a : UInt<32>, b : UInt<16> }
  * }}} lowers to
  * {{{
  *   wire foo_a : UInt<32>
  *   wire foo_b : UInt<16>
  * }}}
  */
object LowerTypes extends Pass {
  def name = "Lower Types"

  /** Delimiter used in lowering names */
  val delim = "_"
  /** Expands a chain of referential [[firrtl.ir.Expression]]s into the equivalent lowered name
    * @param e [[firrtl.ir.Expression]] made up of _only_ [[firrtl.WRef]], [[firrtl.WSubField]], and [[firrtl.WSubIndex]]
    * @return Lowered name of e
    */
  def loweredName(e: Expression): String = e match {
    case e: WRef => e.name
    case e: WSubField => s"${loweredName(e.exp)}$delim${e.name}"
    case e: WSubIndex => s"${loweredName(e.exp)}$delim${e.value}"
  }
  def loweredName(s: Seq[String]): String = s mkString delim

  private case class LowerTypesException(msg: String) extends FIRRTLException(msg)
  private def error(msg: String)(implicit sinfo: Info, mname: String) =
    throw new LowerTypesException(s"$sinfo: [module $mname] $msg")

  // TODO Improve? Probably not the best way to do this
  private def splitMemRef(e1: Expression): (WRef, WRef, WRef, Option[Expression]) = {
    val (mem, tail1) = splitRef(e1)
    val (port, tail2) = splitRef(tail1)
    tail2 match {
      case e2: WRef =>
        (mem, port, e2, None)
      case _ =>
        val (field, tail3) = splitRef(tail2)
        (mem, port, field, Some(tail3))
    }
  }

  // Everything wrapped in run so that it's thread safe
  def run(c: Circuit): Circuit = {
    // Debug state
    implicit var mname: String = ""
    implicit var sinfo: Info = NoInfo

    def lowerTypes(m: DefModule): DefModule = {
      val memDataTypeMap = HashMap[String, Type]()

      // Lowers an expression of MemKind
      // Since mems with Bundle type must be split into multiple ground type
      //   mem, references to fields addr, en, clk, and rmode must be replicated
      //   for each resulting memory
      // References to data, mask, rdata, wdata, and wmask have already been split in expand connects
      //   and just need to be converted to refer to the correct new memory
      def lowerTypesMemExp(e: Expression): Seq[Expression] = {
        val (mem, port, field, tail) = splitMemRef(e)
        field.name match {
          // Fields that need to be replicated for each resulting mem
          case "addr" | "en" | "clk" | "wmode" =>
            require(tail.isEmpty) // there can't be a tail for these
            memDataTypeMap(mem.name) match {
              case _: GroundType => Seq(e)
              case memType => create_exps(mem.name, memType) map { e =>
                val loMemName = loweredName(e)
                val loMem = WRef(loMemName, UnknownType, kind(mem), UNKNOWNGENDER)
                mergeRef(loMem, mergeRef(port, field))
              }
            }
          // Fields that need not be replicated for each
          // eg. mem.reader.data[0].a
          // (Connect/IsInvalid must already have been split to ground types)
          case "data" | "mask" | "rdata" | "wdata" | "wmask" =>
            val loMem = tail match {
              case Some(e) =>
                val loMemExp = mergeRef(mem, e)
                val loMemName = loweredName(loMemExp)
                WRef(loMemName, UnknownType, kind(mem), UNKNOWNGENDER)
              case None => mem
            }
            Seq(mergeRef(loMem, mergeRef(port, field)))
          case name => error(s"Error! Unhandled memory field ${name}")
        }
      }

      def lowerTypesExp(e: Expression): Expression = e match {
        case e: WRef => e
        case (_: WSubField | _: WSubIndex) => kind(e) match {
          case k: InstanceKind =>
            val (root, tail) = splitRef(e)
            val name = loweredName(tail)
            WSubField(root, name, e.tpe, gender(e))
          case k: MemKind =>
            val exps = lowerTypesMemExp(e)
            exps.size match {
              case 1 => exps.head
              case _ => error("Error! lowerTypesExp called on MemKind " + 
                              "SubField that needs to be expanded!")
            }
          case _ => WRef(loweredName(e), e.tpe, kind(e), gender(e))
        }
        case e: Mux => e map (lowerTypesExp)
        case e: ValidIf => e map (lowerTypesExp)
        case e: DoPrim => e map (lowerTypesExp)
        case e @ (_: UIntLiteral | _: SIntLiteral) => e
      }

      def lowerTypesStmt(s: Statement): Statement = s map lowerTypesStmt match {
        case s: DefWire =>
          sinfo = s.info
          s.tpe match {
            case _: GroundType => s
            case _ => Block(create_exps(s.name, s.tpe) map (
              e => DefWire(s.info, loweredName(e), e.tpe)))
          }
        case s: DefRegister =>
          sinfo = s.info
          s.tpe match {
            case _: GroundType => s map lowerTypesExp
            case _ =>
              val es = create_exps(s.name, s.tpe)
              val inits = create_exps(s.init) map (lowerTypesExp)
              val clock = lowerTypesExp(s.clock)
              val reset = lowerTypesExp(s.reset)
              Block(es zip inits map { case (e, i) =>
                DefRegister(s.info, loweredName(e), e.tpe, clock, reset, i)
              })
          }
        // Could instead just save the type of each Module as it gets processed
        case s: WDefInstance =>
          sinfo = s.info
          s.tpe match {
            case t: BundleType =>
              val fieldsx = t.fields flatMap (f =>
                create_exps(WRef(f.name, f.tpe, ExpKind(), times(f.flip, MALE))) map (
                  // Flip because inst genders are reversed from Module type
                  e => Field(loweredName(e), swap(to_flip(gender(e))), e.tpe)
                )
              )
              WDefInstance(s.info, s.name, s.module, BundleType(fieldsx))
            case _ => error("WDefInstance type should be Bundle!")
          }
        case s: DefMemory =>
          sinfo = s.info
          memDataTypeMap(s.name) = s.dataType
          s.dataType match {
            case _: GroundType => s
            case _ => Block(create_exps(s.name, s.dataType) map (e =>
              DefMemory(s.info, loweredName(e), e.tpe, s.depth,
                s.writeLatency, s.readLatency, s.readers, s.writers,
                s.readwriters)))
          }
        // wire foo : { a , b }
        // node x = foo
        // node y = x.a
        //  ->
        // node x_a = foo_a
        // node x_b = foo_b
        // node y = x_a
        case s: DefNode =>
          sinfo = s.info
          val names = create_exps(s.name, s.value.tpe) map (lowerTypesExp)
          val exps = create_exps(s.value) map (lowerTypesExp)
          Block(names zip exps map {case (n, e) => DefNode(s.info, loweredName(n), e)})
        case s: IsInvalid =>
          sinfo = s.info
          kind(s.expr) match {
            case k: MemKind =>
              Block(lowerTypesMemExp(s.expr) map (IsInvalid(s.info, _)))
            case _ => s map (lowerTypesExp)
          }
        case s: Connect =>
          sinfo = s.info
          kind(s.loc) match {
            case k: MemKind =>
              val exp = lowerTypesExp(s.expr)
              val locs = lowerTypesMemExp(s.loc)
              Block(locs map (Connect(s.info, _, exp)))
            case _ => s map (lowerTypesExp)
          }
        case s => s map (lowerTypesExp)
      }

      sinfo = m.info
      mname = m.name
      // Lower Ports
      val portsx = m.ports flatMap ( p =>
        create_exps(WRef(p.name, p.tpe, PortKind(), to_gender(p.direction))) map (
          e => Port(p.info, loweredName(e), to_dir(gender(e)), e.tpe)
        )
      )
      m match {
        case m: ExtModule => m.copy(ports = portsx)
        case m: Module => Module(m.info, m.name, portsx, lowerTypesStmt(m.body))
      }
    }

    sinfo = c.info
    Circuit(c.info, c.modules map lowerTypes, c.main)
  }
}


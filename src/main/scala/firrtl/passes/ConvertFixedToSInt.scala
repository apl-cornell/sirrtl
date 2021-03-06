// See LICENSE for license details.

package firrtl.passes

import scala.collection.mutable
import firrtl.PrimOps._
import firrtl.ir._
import firrtl._
import firrtl.Mappers._
import firrtl.Utils.{sub_type, module_type, field_type, BoolType, max, min, pow_minus_one}

/** Replaces FixedType with SIntType, and correctly aligns all binary points
  */
object ConvertFixedToSInt extends Pass {
  def name = "Convert Fixed Types to SInt Types"
  def alignArg(e: Expression, point: BigInt): Expression = e.tpe match {
    case FixedType(IntWidth(w), IntWidth(p)) => // assert(point >= p)
      if((point - p) > 0) {
        DoPrim(Shl, Seq(e), Seq(point - p), UnknownType, e.lbl)
      } else if (point - p < 0) {
        DoPrim(Shr, Seq(e), Seq(p - point), UnknownType, e.lbl)
      } else e
    case FixedType(w, p) => error("Shouldn't be here")
    case _ => e
  }
  def calcPoint(es: Seq[Expression]): BigInt =
    es.map(_.tpe match {
      case FixedType(IntWidth(w), IntWidth(p)) => p
      case _ => BigInt(0)
    }).reduce(max(_, _))
  def toSIntType(t: Type): Type = t match {
    case FixedType(IntWidth(w), IntWidth(p)) => SIntType(IntWidth(w))
    case FixedType(w, p) => error("Shouldn't be here")
    case _ => t
  }
  def run(c: Circuit): Circuit = {
    val moduleTypes = mutable.HashMap[String,Type]()
    def onModule(m:DefModule) : DefModule = {
      val types = mutable.HashMap[String,Type]()
      def updateExpType(e:Expression): Expression = e match {
        case DoPrim(Mul, args, consts, tpe, lbl) => e map updateExpType
        case DoPrim(AsFixedPoint, args, consts, tpe, lbl) => DoPrim(AsSInt, args, Seq.empty, tpe, lbl)
        case DoPrim(BPShl, args, consts, tpe, lbl) => DoPrim(Shl, args, consts, tpe, lbl)
        case DoPrim(BPShr, args, consts, tpe, lbl) => DoPrim(Shr, args, consts, tpe, lbl)
        case DoPrim(BPSet, args, consts, FixedType(w, IntWidth(p)), lbl) => alignArg(args.head, p)
        case DoPrim(op, args, consts, tpe, lbl) =>
          val point = calcPoint(args)
          val newExp = DoPrim(op, args.map(x => alignArg(x, point)), consts, UnknownType, lbl)
          newExp map updateExpType match {
            case DoPrim(AsFixedPoint, args, consts, tpe, lbl) => DoPrim(AsSInt, args, Seq.empty, tpe, lbl)
            case e => e
          }
        case Mux(cond, tval, fval, tpe, lbl) =>
          val point = calcPoint(Seq(tval, fval))
          val newExp = Mux(cond, alignArg(tval, point), alignArg(fval, point), UnknownType, lbl)
          newExp map updateExpType
        case e: UIntLiteral => e
        case e: SIntLiteral => e
        case _ => e map updateExpType match {
          case ValidIf(cond, value, tpe, lbl) => ValidIf(cond, value, value.tpe, lbl)
          case WRef(name, tpe, lbl, k, g) => WRef(name, types(name), lbl, k, g)
          case WSubField(exp, name, tpe, lbl, g) => WSubField(exp, name, field_type(exp.tpe, name), lbl, g)
          case WSubIndex(exp, value, tpe, lbl, g) => WSubIndex(exp, value, sub_type(exp.tpe), lbl, g)
          case WSubAccess(exp, index, tpe, lbl, g) => WSubAccess(exp, index, sub_type(exp.tpe), lbl, g)
        }
      }
      def updateStmtType(s: Statement): Statement = s match {
        case DefRegister(info, name, tpe, lbl, clock, reset, init) =>
          val newType = toSIntType(tpe)
          types(name) = newType
          DefRegister(info, name, newType, lbl, clock, reset, init) map updateExpType
        case DefWire(info, name, tpe, lbl) =>
          val newType = toSIntType(tpe)
          types(name) = newType
          DefWire(info, name, newType, lbl)
        case DefNode(info, name, value, lbl) =>
          val newValue = updateExpType(value)
          val newType = toSIntType(newValue.tpe)
          types(name) = newType
          DefNode(info, name, newValue, lbl)
        case DefMemory(info, name, dt, lbl, depth, wL, rL, rs, ws, rws, ruw) =>
          val newStmt = DefMemory(info, name, toSIntType(dt), lbl, depth, wL, rL, rs, ws, rws, ruw)
          val newType = MemPortUtils.memType(newStmt)
          types(name) = newType
          newStmt
        case WDefInstance(info, name, module, tpe, lbl) =>
          val newType = moduleTypes(module) 
          types(name) = newType
          WDefInstance(info, name, module, newType, lbl)
        case Connect(info, loc, exp) => 
          val point = calcPoint(Seq(loc))
          val newExp = alignArg(exp, point)
          Connect(info, loc, newExp) map updateExpType
        case PartialConnect(info, loc, exp) => 
          val point = calcPoint(Seq(loc))
          val newExp = alignArg(exp, point)
          PartialConnect(info, loc, newExp) map updateExpType
        // check Connect case, need to shl
        case s => (s map updateStmtType) map updateExpType
      }
 
      m.ports.foreach(p => types(p.name) = p.tpe)
      m match {
        case Module(info, name, ports, body) => Module(info,name,ports,updateStmtType(body))
        case m:ExtModule => m
      }
    }
 
    val newModules = for(m <- c.modules) yield { 
      val newPorts = m.ports.map(p => Port(p.info,p.name,p.direction,toSIntType(p.tpe),p.lbl))
      m match {
         case Module(info, name, ports, body) => Module(info,name,newPorts,body)
         case ext: ExtModule => ext.copy(ports = newPorts)
      }
    }
    newModules.foreach(m => moduleTypes(m.name) = module_type(m))
    firrtl.passes.InferTypes.run(Circuit(c.info, newModules.map(onModule(_)), c.main ))
  }
}

// vim: set ts=4 sw=4 et:

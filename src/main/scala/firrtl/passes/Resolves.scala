// See LICENSE for license details.

package firrtl.passes

import firrtl._
import firrtl.ir._
import firrtl.Mappers._

object ResolveKinds extends ResolveKindsT
trait ResolveKindsT extends Pass with PassDebug {
  def name = "Resolve Kinds"
  type KindMap = collection.mutable.LinkedHashMap[String, Kind]

  def find_port(kinds: KindMap)(p: Port): Port = {
    kinds(p.name) = PortKind ; p
  }

  def find_stmt(kinds: KindMap)(s: Statement):Statement = {
    s match {
      case sx: DefWire => kinds(sx.name) = WireKind
      case sx: DefNode => kinds(sx.name) = NodeKind
      case sx: DefRegister => kinds(sx.name) = RegKind
      case sx: WDefInstance => kinds(sx.name) = InstanceKind
      case sx: DefMemory => kinds(sx.name) = MemKind
      case sx: CDefMemory => kinds(sx.name) = MemKind
      case sx: CDefMPort => kinds(sx.name) = MemKind
      case _ =>
    } 
    s map find_stmt(kinds)
  }

  def resolve_lbl(kinds: KindMap)(l: Label): Label = l
    //l map resolve_expr(kinds) map resolve_lbl(kinds)

  def resolve_expr(kinds: KindMap)(e: Expression): Expression = 
    e map resolve_lbl(kinds) match {
    case ex: WRef => 
      if(kinds.contains(ex.name)) ex copy (kind = kinds(ex.name))
      else ex
    case _ => e map resolve_expr(kinds) map resolve_lbl(kinds)
  }

  def resolve_stmt(kinds: KindMap)(s: Statement): Statement = {
    dprint(s.info.serialize)
    s map resolve_stmt(kinds) map resolve_expr(kinds) map resolve_lbl(kinds)
  }

  def resolve_kinds(m: DefModule): DefModule = {
    val kinds = new KindMap
    (m map find_port(kinds)
       map find_stmt(kinds)
       map resolve_stmt(kinds))
  }
 
  def run(c: Circuit): Circuit = {
    bannerprintb(name)
    val cprime = c copy (modules = c.modules map resolve_kinds)
    bannerprintb(s"after $name")
    dprint(cprime.serialize)
    cprime
  }
}

object ResolveGenders extends Pass {
  def name = "Resolve Genders"

  def resolve_e(g: Gender)(e: Expression): Expression =  e match {
    case ex: WRef => ex copy (gender = g)
    case ex: Next => ex copy (gender = g) map resolve_e(g)
    case WSubField(exp, name, tpe, lbl, _) => WSubField(
      Utils.field_flip(exp.tpe, name) match {
        case Default => resolve_e(g)(exp)
        case Flip => resolve_e(Utils.swap(g))(exp)
      }, name, tpe, lbl, g)
    case WSubIndex(exp, value, tpe, lbl, _) =>
      WSubIndex(resolve_e(g)(exp), value, tpe, lbl, g)
    case WSubAccess(exp, index, tpe, lbl, _) =>
      WSubAccess(resolve_e(g)(exp), resolve_e(MALE)(index), tpe, lbl, g)
    case _ => e map resolve_e(g)
  }
        
  def resolve_s(s: Statement): Statement = s match {
    //TODO(azidar): pretty sure don't need to do anything for Attach, but not positive...
    case IsInvalid(info, expr) =>
      IsInvalid(info, resolve_e(FEMALE)(expr))
    case Connect(info, loc, expr) =>
      Connect(info, resolve_e(FEMALE)(loc), resolve_e(MALE)(expr))
    case PartialConnect(info, loc, expr) =>
      PartialConnect(info, resolve_e(FEMALE)(loc), resolve_e(MALE)(expr))
    case sx => sx map resolve_e(MALE) map resolve_s
  }

  def resolve_gender(m: DefModule): DefModule = m map resolve_s

  def run(c: Circuit): Circuit =
    c copy (modules = c.modules map resolve_gender)
}

object CInferMDir extends Pass {
  def name = "CInfer MDir"
  type MPortDirMap = collection.mutable.LinkedHashMap[String, MPortDir]

  def infer_mdir_e(mports: MPortDirMap, dir: MPortDir)(e: Expression): Expression = e match {
    case e: Reference =>
      mports get e.name match {
        case None =>
        case Some(p) => mports(e.name) = (p, dir) match {
          case (MInfer, MInfer) => Utils.error("Shouldn't be here")
          case (MInfer, MWrite) => MWrite
          case (MInfer, MRead) => MRead
          case (MInfer, MReadWrite) => MReadWrite
          case (MWrite, MInfer) => Utils.error("Shouldn't be here")
          case (MWrite, MWrite) => MWrite
          case (MWrite, MRead) => MReadWrite
          case (MWrite, MReadWrite) => MReadWrite
          case (MRead, MInfer) => Utils.error("Shouldn't be here")
          case (MRead, MWrite) => MReadWrite
          case (MRead, MRead) => MRead
          case (MRead, MReadWrite) => MReadWrite
          case (MReadWrite, MInfer) => Utils.error("Shouldn't be here")
          case (MReadWrite, MWrite) => MReadWrite
          case (MReadWrite, MRead) => MReadWrite
          case (MReadWrite, MReadWrite) => MReadWrite
        }
      }
      e
    case e: SubAccess =>
      infer_mdir_e(mports, dir)(e.expr)
      infer_mdir_e(mports, MRead)(e.index) // index can't be a write port
      e
    case e => e map infer_mdir_e(mports, dir)
  }

  def infer_mdir_s(mports: MPortDirMap)(s: Statement): Statement = s match { 
    case sx: CDefMPort =>
       mports(sx.name) = sx.direction
       sx map infer_mdir_e(mports, MRead)
    case sx: Connect =>
       infer_mdir_e(mports, MRead)(sx.expr)
       infer_mdir_e(mports, MWrite)(sx.loc)
       sx
    case sx: PartialConnect =>
       infer_mdir_e(mports, MRead)(sx.expr)
       infer_mdir_e(mports, MWrite)(sx.loc)
       sx
    case sx => sx map infer_mdir_s(mports) map infer_mdir_e(mports, MRead)
  }
        
  def set_mdir_s(mports: MPortDirMap)(s: Statement): Statement = s match { 
    case sx: CDefMPort => sx copy (direction = mports(sx.name))
    case sx => sx map set_mdir_s(mports)
  }
  
  def infer_mdir(m: DefModule): DefModule = {
    val mports = new MPortDirMap
    m map infer_mdir_s(mports) map set_mdir_s(mports)
  }
     
  def run(c: Circuit): Circuit =
    c copy (modules = c.modules map infer_mdir)
}

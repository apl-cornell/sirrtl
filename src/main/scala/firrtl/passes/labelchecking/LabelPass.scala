package firrtl.passes
import firrtl._
import firrtl.ir._
import firrtl.Utils._
import firrtl.Mappers._

trait LabelPass {
  def name: String
  def run(m: DefModule, conEnv: ConnectionEnv, conGen: ConstraintGenerator): (DefModule, ConnectionEnv)
}

abstract class LabelPassBased {
  def passSeq: Seq[LabelPass]
  def runPasses(mod: DefModule, conEnv: ConnectionEnv, conGen: ConstraintGenerator) : (DefModule, ConnectionEnv) =
    passSeq.foldLeft( (mod, conEnv) ) { case ( (m:DefModule, e:ConnectionEnv) , p: LabelPass) =>
      p.run(m,e,conGen)
    }
}

trait LabelPassDebug extends PassDebug {
  override def color = Console.GREEN
  def dprintConEnv(conEnv: ConnectionEnv) = conEnv.foreach {
    case(loc, (cons, info)) => dprint(s"(${loc.serialize} -> ${cons.serialize}) ${info.serialize}\n")
  }
}

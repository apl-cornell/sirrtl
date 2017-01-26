package firrtl.passes
import firrtl._
import firrtl.ir._
import firrtl.Utils._
import firrtl.Mappers._

trait LabelPass {
  def name: String
  def run(m: DefModule, conEnv: ConnectionEnv): (DefModule, ConnectionEnv)
}

abstract class LabelPassBased {
  def passSeq: Seq[LabelPass]
  def runPasses(mod: DefModule, conEnv: ConnectionEnv) : (DefModule, ConnectionEnv) =
    passSeq.foldLeft( (mod, conEnv) ) { case ( (m:DefModule, e:ConnectionEnv) , p: LabelPass) =>
      p.run(m,e)
    }
}

trait LabelPassDebug extends PassDebug {
  override def color = Console.GREEN
  def dprintConEnv(conEnv: ConnectionEnv) = conEnv.foreach {
    case(loc, cons) => dprint(s"(${loc.serialize} -> ${cons.serialize})\n")
  }
}

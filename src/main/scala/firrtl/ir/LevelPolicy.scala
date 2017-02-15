package firrtl
package ir

class LevelPolicy extends Policy {
  // TODO parse the covers relation from the firrtl source
  def levelLat = new Lattice[Level]{
    def covers: Map[Level,Set[Level]] = Map(
      Level("L") -> Set(Level("D1"),Level("D2")),
      Level("D1") -> Set(Level("H")),
      Level("D2") -> Set(Level("H")),
      Level("H") -> Set()
    )
  }
  def top = levelLat.top
  def bottom = levelLat.bottom
  def join(l: Label, r: Label): Label = (l, r) match {
    case (lx: Level, rx: Level) => levelLat.join(lx, rx)
    case _ => throw new Exception; UnknownLabel
  }
  def meet(l: Label, r: Label): Label = (l, r) match {
    case (lx: Level, rx: Level) => levelLat.meet(lx, rx)
    case _ => throw new Exception; UnknownLabel
  }
}

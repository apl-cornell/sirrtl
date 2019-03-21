package solutions
import chisel3._
import java.io.File


object FirrtlGenerator extends App {
  val examples = Map(
    "Adder" -> {() => new Adder(32)},
    "Accumulator" -> {() => new Accumulator}
  )

  if (args.length < 1) {
    println("Missing input file args");
    System.exit(1);
  }

  var i = 0;
  for (i <- 0 to args.length-1)
  {
    val testName = args(i);
    val outputfile = new File("output/" + testName + ".fir");
    val modMaybe = examples.get(testName);
    modMaybe match {
      case Some(mod) =>
        chisel3.Driver.dumpFirrtl(chisel3.Driver.elaborate(() => mod()), Option(outputfile));
      case None =>
        println("Module " + testName + " not found!");
    }
  }
}
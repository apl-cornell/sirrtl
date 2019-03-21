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

  val testName = args(0);
  val outputfile = new File("output/" + testName + ".fir");
  chisel3.Driver.dumpFirrtl(chisel3.Driver.elaborate(() => examples.getOrElse(testName, () => new Adder(32))()), Option(outputfile));
}
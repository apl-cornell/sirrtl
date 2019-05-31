;buildInfoPackage: chisel3, version: 3.0-SNAPSHOT, scalaVersion: 2.11.7, sbtVersion: 0.13.11, builtAtString: 2016-12-12 22:28:40.596, builtAtMillis: 1481581720596
circuit Accumulator : 
  module Accumulator : 
    input clock : Clock
    input reset : UInt<1>
    output io : {flip in : UInt<1>, out : UInt<8>}
    
    io is invalid
    io is invalid
    reg accumulator : UInt<8>, clock with : (reset => (reset, UInt<8>("h00"))) @[Accumulator.scala 11:24]
    node _T_7 = add(accumulator, io.in) @[Accumulator.scala 12:30]
    node _T_8 = tail(_T_7, 1) @[Accumulator.scala 12:30]
    accumulator <= _T_8 @[Accumulator.scala 12:15]
    io.out <= accumulator @[Accumulator.scala 13:10]
    

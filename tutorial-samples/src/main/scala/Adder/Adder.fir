;buildInfoPackage: chisel3, version: 3.0-SNAPSHOT, scalaVersion: 2.11.7, sbtVersion: 0.13.11, builtAtString: 2016-12-12 22:28:40.596, builtAtMillis: 1481581720596
circuit Adder : 
  module Adder : 
    input clock : Clock
    input reset : UInt<1>
    output io : {flip in0 : UInt<8>, flip in1 : UInt<8>, out : UInt<8>}
    
    io is invalid
    io is invalid
    node _T_8 = add(io.in0, io.in1) @[Adder.scala 12:20]
    node _T_9 = tail(_T_8, 1) @[Adder.scala 12:20]
    io.out <= _T_9 @[Adder.scala 12:10]
    

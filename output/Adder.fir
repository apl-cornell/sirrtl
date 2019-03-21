;buildInfoPackage: chisel3, version: 3.1-SNAPSHOT, scalaVersion: 2.11.7, sbtVersion: 0.13.11, builtAtString: 2019-03-21 14:11:22.015, builtAtMillis: 1553177482015
circuit Adder : 
  module Adder : 
    input clock : {L, H} Clock
    input reset : {L, H} UInt<1>
    output io : {flip in0 : UInt<32>, flip in1 : UInt<32>, out : UInt<32>}
    
    io is invalid
    io is invalid
    node _T_8 = add(io.in0, io.in1) @[Adder.scala 12:20]
    node _T_9 = tail(_T_8, 1) @[Adder.scala 12:20]
    io.out <= _T_9 @[Adder.scala 12:10]
    

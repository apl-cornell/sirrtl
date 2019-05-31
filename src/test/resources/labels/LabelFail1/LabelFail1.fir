;buildInfoPackage: chisel3, version: 3.1-SNAPSHOT, scalaVersion: 2.11.7, sbtVersion: 0.13.11, builtAtString: 2019-03-21 14:11:22.015, builtAtMillis: 1553177482015
circuit LabelFail1 : 
  module ExpectedFail : 
    input clock : {L, H} Clock
    input reset : {L, H} UInt<1>
    output io : {flip in : {L, L} UInt<1>, out : {H, H} UInt<1>}
    
    io is invalid
    io is invalid
    io.out <= io.in @[LabelTest.scala 228:12]
    
  module LabelFail1 : 
    input clock : {L, H} Clock
    input reset : {L, H} UInt<1>
    output io : {flip in : {L, H} UInt<1>, out : {L, H} UInt<1>}
    
    io is invalid
    io is invalid
    inst ST1 of ExpectedFail @[LabelTest.scala 22:19]
    ST1.io is invalid
    ST1.clock <= clock
    ST1.reset <= reset
    

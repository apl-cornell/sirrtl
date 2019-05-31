;buildInfoPackage: chisel3, version: 3.1-SNAPSHOT, scalaVersion: 2.11.7, sbtVersion: 0.13.11, builtAtString: 2019-03-21 14:11:22.015, builtAtMillis: 1553177482015
circuit LabelFail2 : 
  module ExpectedFail2 : 
    input clock : {L, H} Clock
    input reset : {L, H} UInt<1>
    output io : {flip in : {L, H} UInt<4>, out : {L, L} UInt<1>}
    
    io is invalid
    io is invalid
    reg my_reg : {L, H} {a : UInt<4>, b : UInt<4>}, clock @[LabelTest.scala 284:19]
    my_reg.a <= io.in @[LabelTest.scala 285:12]
    my_reg.b <= my_reg.a @[LabelTest.scala 286:12]
    reg reg2 : {[[my_reg.a]]H, H} UInt<1>, clock @[LabelTest.scala 288:17]
    reg2 <= my_reg.b @[LabelTest.scala 289:8]
    io.out <= reg2 @[LabelTest.scala 290:10]
    
  module LabelFail2 : 
    input clock : {L, H} Clock
    input reset : {L, H} UInt<1>
    output io : {flip in : {L, H} UInt<1>, out : {L, H} UInt<1>}
    
    io is invalid
    io is invalid
    inst ST5 of ExpectedFail2 @[LabelTest.scala 26:19]
    ST5.io is invalid
    ST5.clock <= clock
    ST5.reset <= reset
    

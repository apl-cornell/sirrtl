;buildInfoPackage: chisel3, version: 3.1-SNAPSHOT, scalaVersion: 2.11.7, sbtVersion: 0.13.11, builtAtString: 2019-03-21 14:11:22.015, builtAtMillis: 1553177482015
circuit SameLabel : 
  module Issue6 : 
    input clock : {L, H} Clock
    input reset : {L, H} UInt<1>
    output io : {out : {H, L} UInt<8>}
    
    io is invalid
    io is invalid
    reg conf : {L, H} UInt<4>, clock with : (reset => (reset, UInt<4>("h00"))) @[LabelTest.scala 76:17]
    reg integ : {L, H} UInt<4>, clock with : (reset => (reset, UInt<4>("h00"))) @[LabelTest.scala 77:18]
    conf <= conf @[LabelTest.scala 80:8]
    integ <= integ @[LabelTest.scala 81:9]
    reg a : {[[conf]]H, [[integ]]H} UInt<8>, clock @[LabelTest.scala 83:14]
    reg b : {[[conf]]H, [[integ]]H} UInt<8>, clock @[LabelTest.scala 84:14]
    reg c : {[[conf]]H, [[integ]]H} UInt<8>, clock @[LabelTest.scala 85:14]
    b <= a @[LabelTest.scala 87:5]
    c <= c @[LabelTest.scala 88:5]
    io.out <= c @[LabelTest.scala 90:10]
    
  module SameLabel : 
    input clock : {L, H} Clock
    input reset : {L, H} UInt<1>
    output io : {flip in : {L, H} UInt<1>, out : {L, H} UInt<1>}
    
    io is invalid
    io is invalid
    inst I6 of Issue6 @[LabelTest.scala 20:18]
    I6.io is invalid
    I6.clock <= clock
    I6.reset <= reset
    

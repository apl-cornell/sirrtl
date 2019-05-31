;buildInfoPackage: chisel3, version: 3.1-SNAPSHOT, scalaVersion: 2.11.7, sbtVersion: 0.13.11, builtAtString: 2019-03-21 14:11:22.015, builtAtMillis: 1553177482015
circuit ImplicitFail2 : 
  module Issue5 : 
    input clock : {L, H} Clock
    input reset : {L, H} UInt<1>
    output io : {flip in : {L, H} UInt<1>, flip req_conf : {L, H} UInt<4>, flip req_integ : {L, H} UInt<4>, flip req_data : {[[io.req_conf]]H, [[io.req_integ]]H} UInt<4>}
    
    io is invalid
    io is invalid
    reg reg_conf : {L, H} UInt<4>, clock @[LabelTest.scala 154:23]
    reg reg_integ : {L, H} UInt<4>, clock @[LabelTest.scala 155:24]
    reg reg_data : {[[reg_conf]]H, [[reg_integ]]H} UInt<4>, clock @[LabelTest.scala 157:23]
    node _T_14 = eq(io.in, UInt<1>("h01")) @[LabelTest.scala 159:16]
    when _T_14 : @[LabelTest.scala 159:25]
      reg_data <= io.req_data @[LabelTest.scala 160:16]
      reg_conf <= io.req_conf @[LabelTest.scala 161:16]
      reg_integ <= io.req_integ @[LabelTest.scala 162:17]
      skip @[LabelTest.scala 159:25]
    node _T_16 = eq(_T_14, UInt<1>("h00")) @[LabelTest.scala 159:25]
    when _T_16 : @[LabelTest.scala 163:17]
      reg_data <= io.req_data @[LabelTest.scala 164:16]
      skip @[LabelTest.scala 163:17]
        
  module ImplicitFail2 : 
    input clock : {L, H} Clock
    input reset : {L, H} UInt<1>
    output io : {flip in : {L, H} UInt<1>, out : {L, H} UInt<1>}
    
    io is invalid
    io is invalid
    inst B1 of Issue5 @[LabelTest.scala 17:19]
    B1.io is invalid
    B1.clock <= clock
    B1.reset <= reset    

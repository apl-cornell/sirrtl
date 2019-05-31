;buildInfoPackage: chisel3, version: 3.1-SNAPSHOT, scalaVersion: 2.11.7, sbtVersion: 0.13.11, builtAtString: 2019-03-21 14:11:22.015, builtAtMillis: 1553177482015
circuit ImplicitFail : 
  module Issue3 : 
    input clock : {L, H} Clock
    input reset : {L, H} UInt<1>
    output io : {flip ns_i : {L, L} UInt<4>, flip l_i : {L, L} UInt<1>, flip h_i : {H, L} UInt<1>, h_o : {H, L} UInt<1>, l_o : {L, L} UInt<1>}
    
    io is invalid
    io is invalid
    reg data_r : {[[io.ns_i]]H, L} UInt<1>, clock @[LabelTest.scala 176:21]
    node _T_14 = eq(io.ns_i, UInt<4>("h0f")) @[LabelTest.scala 177:18]
    when _T_14 : @[LabelTest.scala 177:30]
      data_r <= io.h_i @[LabelTest.scala 178:14]
      io.h_o <= data_r @[LabelTest.scala 179:14]
      skip @[LabelTest.scala 177:30]
    node _T_16 = eq(io.ns_i, UInt<1>("h00")) @[LabelTest.scala 180:24]
    node _T_18 = eq(_T_14, UInt<1>("h00")) @[LabelTest.scala 177:30]
    node _T_19 = and(_T_18, _T_16) @[LabelTest.scala 180:33]
    when _T_19 : @[LabelTest.scala 180:33]
      data_r <= io.l_i @[LabelTest.scala 181:14]
      io.l_o <= data_r @[LabelTest.scala 182:14]
      io.h_o <= io.h_o @[LabelTest.scala 183:14]
      skip @[LabelTest.scala 180:33]
    node _T_21 = eq(_T_14, UInt<1>("h00")) @[LabelTest.scala 177:30]
    node _T_23 = eq(_T_16, UInt<1>("h00")) @[LabelTest.scala 180:33]
    node _T_24 = and(_T_21, _T_23) @[LabelTest.scala 180:33]
    when _T_24 : @[LabelTest.scala 184:17]
      data_r <= UInt<1>("h00") @[LabelTest.scala 185:14]
      io.l_o <= UInt<1>("h00") @[LabelTest.scala 186:14]
      io.h_o <= UInt<1>("h00") @[LabelTest.scala 187:14]
      skip @[LabelTest.scala 184:17]
    
  module ImplicitFail : 
    input clock : {L, H} Clock
    input reset : {L, H} UInt<1>
    output io : {flip in : {L, H} UInt<1>, out : {L, H} UInt<1>}
    
    io is invalid
    io is invalid
    inst B2 of Issue3 @[LabelTest.scala 18:17]
    B2.io is invalid
    B2.clock <= clock
    B2.reset <= reset
    

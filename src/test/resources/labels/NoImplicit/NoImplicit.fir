;buildInfoPackage: chisel3, version: 3.1-SNAPSHOT, scalaVersion: 2.11.7, sbtVersion: 0.13.11, builtAtString: 2019-03-21 14:11:22.015, builtAtMillis: 1553177482015
circuit NoImplicit : 
  module Issue3Fix : 
    input clock : {L, H} Clock
    input reset : {L, H} UInt<1>
    output io : {flip ns_i : {L, L} UInt<4>, flip l_i : {L, L} UInt<1>, flip h_i : {H, L} UInt<1>, h_o : {H, L} UInt<1>, l_o : {L, L} UInt<1>}
    
    io is invalid
    io is invalid
    reg lbl_r : {L, L} UInt<4>, clock @[LabelTest.scala 199:20]
    node _T_14 = and(io.ns_i, UInt<4>("h0f")) @[LabelTest.scala 200:22]
    lbl_r <= _T_14 @[LabelTest.scala 200:11]
    reg data_r : {[[lbl_r]]H, L} UInt<1>, clock @[LabelTest.scala 201:21]
    node _T_17 = eq(io.ns_i, UInt<4>("h0f")) @[LabelTest.scala 202:18]
    when _T_17 : @[LabelTest.scala 202:30]
      data_r <= io.h_i @[LabelTest.scala 203:14]
      skip @[LabelTest.scala 202:30]
    node _T_19 = eq(io.ns_i, UInt<1>("h00")) @[LabelTest.scala 204:24]
    node _T_21 = eq(_T_17, UInt<1>("h00")) @[LabelTest.scala 202:30]
    node _T_22 = and(_T_21, _T_19) @[LabelTest.scala 204:33]
    when _T_22 : @[LabelTest.scala 204:33]
      data_r <= io.l_i @[LabelTest.scala 205:14]
      skip @[LabelTest.scala 204:33]
    node _T_24 = eq(_T_17, UInt<1>("h00")) @[LabelTest.scala 202:30]
    node _T_26 = eq(_T_19, UInt<1>("h00")) @[LabelTest.scala 204:33]
    node _T_27 = and(_T_24, _T_26) @[LabelTest.scala 204:33]
    when _T_27 : @[LabelTest.scala 206:17]
      data_r <= UInt<1>("h00") @[LabelTest.scala 207:14]
      skip @[LabelTest.scala 206:17]
    node _T_30 = eq(lbl_r, UInt<4>("h0f")) @[LabelTest.scala 209:16]
    when _T_30 : @[LabelTest.scala 209:28]
      io.h_o <= data_r @[LabelTest.scala 210:14]
      skip @[LabelTest.scala 209:28]
    node _T_32 = eq(lbl_r, UInt<1>("h00")) @[LabelTest.scala 211:22]
    node _T_34 = eq(_T_30, UInt<1>("h00")) @[LabelTest.scala 209:28]
    node _T_35 = and(_T_34, _T_32) @[LabelTest.scala 211:31]
    when _T_35 : @[LabelTest.scala 211:31]
      io.l_o <= data_r @[LabelTest.scala 212:14]
      io.h_o <= io.h_o @[LabelTest.scala 213:14]
      skip @[LabelTest.scala 211:31]
    node _T_37 = eq(_T_30, UInt<1>("h00")) @[LabelTest.scala 209:28]
    node _T_39 = eq(_T_32, UInt<1>("h00")) @[LabelTest.scala 211:31]
    node _T_40 = and(_T_37, _T_39) @[LabelTest.scala 211:31]
    when _T_40 : @[LabelTest.scala 214:17]
      io.l_o <= UInt<1>("h00") @[LabelTest.scala 215:14]
      io.h_o <= UInt<1>("h00") @[LabelTest.scala 216:14]
      skip @[LabelTest.scala 214:17]
    
  module NoImplicit : 
    input clock : {L, H} Clock
    input reset : {L, H} UInt<1>
    output io : {flip in : {L, H} UInt<1>, out : {L, H} UInt<1>}
    
    io is invalid
    io is invalid
    inst B2Good of Issue3Fix @[LabelTest.scala 19:22]
    B2Good.io is invalid
    B2Good.clock <= clock
    B2Good.reset <= reset
    

;buildInfoPackage: chisel3, version: 3.1-SNAPSHOT, scalaVersion: 2.11.7, sbtVersion: 0.13.11, builtAtString: 2019-03-21 14:11:22.015, builtAtMillis: 1553177482015
circuit Pipeline : 
  module Issue6_Fix : 
    input clock : {L, H} Clock
    input reset : {L, H} UInt<1>
    output io : {flip req_valid : {L, H} UInt<1>, flip req_conf : {L, H} UInt<4>, flip req_integ : {L, H} UInt<4>, flip req_data : {[[io.req_conf]]H, [[io.req_integ]]H} UInt<4>, resp_valid : {L, H} UInt<1>, resp_conf : {L, H} UInt<4>, resp_integ : {L, H} UInt<4>, resp_data : {[[io.resp_conf]]H, [[io.resp_integ]]H} UInt<4>}
    
    io is invalid
    io is invalid
    reg conf : {L, H} UInt<4>, clock @[LabelTest.scala 108:17]
    reg integ : {L, H} UInt<4>, clock @[LabelTest.scala 109:18]
    reg state : {L, H} UInt<8>, clock @[LabelTest.scala 116:18]
    reg data : {[[conf]]H, [[integ]]H} UInt<8>, clock @[LabelTest.scala 117:17]
    reg temp : {[[conf]]H, [[integ]]H} UInt<8>, clock @[LabelTest.scala 118:17]
    node _T_24 = eq(io.req_valid, UInt<1>("h01")) @[LabelTest.scala 121:21]
    when _T_24 : @[LabelTest.scala 121:30]
      conf <= io.req_conf @[LabelTest.scala 122:10]
      integ <= io.req_integ @[LabelTest.scala 123:11]
      data <= io.req_data @[LabelTest.scala 124:10]
      temp <= UInt<1>("h00") @[LabelTest.scala 125:10]
      state <= UInt<1>("h00") @[LabelTest.scala 126:11]
      skip @[LabelTest.scala 121:30]
    node _T_28 = eq(state, UInt<1>("h00")) @[LabelTest.scala 127:20]
    node _T_30 = eq(_T_24, UInt<1>("h00")) @[LabelTest.scala 121:30]
    node _T_31 = and(_T_30, _T_28) @[LabelTest.scala 127:29]
    when _T_31 : @[LabelTest.scala 127:29]
      node _T_33 = add(data, UInt<1>("h01")) @[LabelTest.scala 130:18]
      node _T_34 = tail(_T_33, 1) @[LabelTest.scala 130:18]
      temp <= _T_34 @[LabelTest.scala 130:10]
      state <= UInt<1>("h01") @[LabelTest.scala 131:11]
      skip @[LabelTest.scala 127:29]
    node _T_37 = eq(state, UInt<1>("h01")) @[LabelTest.scala 132:20]
    node _T_39 = eq(_T_24, UInt<1>("h00")) @[LabelTest.scala 121:30]
    node _T_41 = eq(_T_28, UInt<1>("h00")) @[LabelTest.scala 127:29]
    node _T_42 = and(_T_39, _T_41) @[LabelTest.scala 127:29]
    node _T_43 = and(_T_42, _T_37) @[LabelTest.scala 132:29]
    when _T_43 : @[LabelTest.scala 132:29]
      node _T_45 = add(temp, UInt<1>("h01")) @[LabelTest.scala 133:18]
      node _T_46 = tail(_T_45, 1) @[LabelTest.scala 133:18]
      temp <= _T_46 @[LabelTest.scala 133:10]
      state <= UInt<2>("h02") @[LabelTest.scala 134:11]
      skip @[LabelTest.scala 132:29]
    node _T_49 = eq(state, UInt<2>("h02")) @[LabelTest.scala 135:20]
    node _T_51 = eq(_T_24, UInt<1>("h00")) @[LabelTest.scala 121:30]
    node _T_53 = eq(_T_28, UInt<1>("h00")) @[LabelTest.scala 127:29]
    node _T_54 = and(_T_51, _T_53) @[LabelTest.scala 127:29]
    node _T_56 = eq(_T_37, UInt<1>("h00")) @[LabelTest.scala 132:29]
    node _T_57 = and(_T_54, _T_56) @[LabelTest.scala 132:29]
    node _T_58 = and(_T_57, _T_49) @[LabelTest.scala 135:29]
    when _T_58 : @[LabelTest.scala 135:29]
      io.resp_conf <= conf @[LabelTest.scala 136:18]
      io.resp_integ <= integ @[LabelTest.scala 137:19]
      io.resp_data <= temp @[LabelTest.scala 140:18]
      skip @[LabelTest.scala 135:29]
    node _T_60 = eq(state, UInt<2>("h02")) @[LabelTest.scala 143:27]
    io.resp_valid <= _T_60 @[LabelTest.scala 143:17]
    
  module Pipeline : 
    input clock : {L, H} Clock
    input reset : {L, H} UInt<1>
    output io : {flip in : {L, H} UInt<1>, out : {L, H} UInt<1>}
    
    io is invalid
    io is invalid
    inst I62 of Issue6_Fix @[LabelTest.scala 21:19]
    I62.io is invalid
    I62.clock <= clock
    I62.reset <= reset
    

circuit VectorFail : 
  module VectorLabelFail : 
    input clock : {L, H} Clock
    input reset : {L, H} UInt<1>
    output io : {flip in : {L, H} UInt<2>, out : {L, H} UInt<16>}
    
    io is invalid
    io is invalid
    reg cl : {L, H} UInt<4>[4], clock @[LabelTest.scala 241:15]
    reg il : {L, H} UInt<4>[4], clock @[LabelTest.scala 242:15]
    wire rf : {[[cl]]V, [[il]]V} UInt<16>[4] @[LabelTest.scala 243:16]
    rf is invalid @[LabelTest.scala 243:16]
    node _T_35 = eq(cl[io.in], UInt<4>("h0f")) @[LabelTest.scala 244:18]
    node _T_38 = eq(il[io.in], UInt<1>("h00")) @[LabelTest.scala 244:42]
    node _T_39 = and(_T_35, _T_38) @[LabelTest.scala 244:29]
    when _T_39 : @[LabelTest.scala 244:51]
      io.out <= rf[io.in] @[LabelTest.scala 245:12]
      skip @[LabelTest.scala 244:51]
    node _T_42 = eq(_T_39, UInt<1>("h00")) @[LabelTest.scala 244:51]
    when _T_42 : @[LabelTest.scala 246:14]
      io.out <= UInt<1>("h00") @[LabelTest.scala 247:12]
      skip @[LabelTest.scala 246:14]
    
  module VectorFail : 
    input clock : {L, H} Clock
    input reset : {L, H} UInt<1>
    output io : {flip in : {L, H} UInt<1>, out : {L, H} UInt<1>}
    
    io is invalid
    io is invalid
    inst vltf of VectorLabelFail @[LabelTest.scala 27:20]
    vltf.io is invalid
    vltf.clock <= clock
    vltf.reset <= reset
    

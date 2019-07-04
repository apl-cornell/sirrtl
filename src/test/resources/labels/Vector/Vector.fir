circuit Vector : 
  module VectorLabel : 
    input clock : {L, H} Clock
    input reset : {L, H} UInt<1>
    output io : {flip in : {L, H} UInt<2>, out : {L, H} UInt<16>}
    
    io is invalid
    io is invalid
    reg cl : {L, H} UInt<4>[4], clock @[LabelTest.scala 226:17]
    reg il : {L, H} UInt<4>[4], clock @[LabelTest.scala 227:17]
    wire rf : {[[cl]]V, [[il]]V} UInt<16>[4] @[LabelTest.scala 228:18]
    rf is invalid @[LabelTest.scala 228:18]
    node _T_35 = eq(cl[io.in], UInt<1>("h00")) @[LabelTest.scala 229:20]
    node _T_38 = eq(il[io.in], UInt<4>("h0f")) @[LabelTest.scala 229:41]
    node _T_39 = and(_T_35, _T_38) @[LabelTest.scala 229:28]
    when _T_39 : @[LabelTest.scala 229:53]
      io.out <= rf[io.in] @[LabelTest.scala 230:14]
      skip @[LabelTest.scala 229:53]
    node _T_42 = eq(_T_39, UInt<1>("h00")) @[LabelTest.scala 229:53]
    when _T_42 : @[LabelTest.scala 231:16]
      io.out <= UInt<1>("h00") @[LabelTest.scala 232:14]
      skip @[LabelTest.scala 231:16]
    
  module Vector : 
    input clock : {L, H} Clock
    input reset : {L, H} UInt<1>
    output io : {flip in : {L, H} UInt<1>, out : {L, H} UInt<1>}
    
    io is invalid
    io is invalid
    inst vlt of VectorLabel @[LabelTest.scala 26:19]
    vlt.io is invalid
    vlt.clock <= clock
    vlt.reset <= reset
    

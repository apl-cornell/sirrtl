circuit LabelCheckBasic : 
  module ExpectedSuccess : 
    input clock : {L, H} Clock
    input reset : {L, H} UInt<1>
    output io : {flip in : {L, H} UInt<1>, out : {H, L} UInt<1>}
    
    io is invalid
    io is invalid
    io.out <= io.in @[LabelTest.scala 238:12]
    
  module ExpectedSuccess2 : 
    input clock : {L, H} Clock
    input reset : {L, H} UInt<1>
    output io : {flip in_lbl : {L, H} UInt<4>, flip in : {[[io.in_lbl]]H, L} UInt<1>, out : {L, L} UInt<1>}
    
    io is invalid
    io is invalid
    node _T_9 = eq(io.in_lbl, UInt<1>("h00")) @[LabelTest.scala 248:20]
    when _T_9 : @[LabelTest.scala 248:29]
      io.out <= io.in @[LabelTest.scala 249:14]
      skip @[LabelTest.scala 248:29]
    node _T_11 = eq(_T_9, UInt<1>("h00")) @[LabelTest.scala 248:29]
    when _T_11 : @[LabelTest.scala 250:17]
      io.out <= UInt<1>("h01") @[LabelTest.scala 251:14]
      skip @[LabelTest.scala 250:17]
    
  module ExpectedSuccess3 : 
    input clock : {L, H} Clock
    input reset : {L, H} UInt<1>
    output io : {flip in : {L, H} UInt<1>, out : {H, L} UInt<1>}
    
    io is invalid
    io is invalid
    reg my_reg : {a : UInt<1>, b : UInt<1>}, clock @[LabelTest.scala 266:19]
    my_reg.a <= io.in @[LabelTest.scala 267:12]
    my_reg.b <= my_reg.a @[LabelTest.scala 268:12]
    io.out <= my_reg.b @[LabelTest.scala 270:10]
    
  module LabelCheckBasic : 
    input clock : {L, H} Clock
    input reset : {L, H} UInt<1>
    output io : {flip in : {L, H} UInt<1>, out : {L, H} UInt<1>}
    
    io is invalid
    io is invalid
    inst ST2 of ExpectedSuccess @[LabelTest.scala 23:19]
    ST2.io is invalid
    ST2.clock <= clock
    ST2.reset <= reset
    inst ST3 of ExpectedSuccess2 @[LabelTest.scala 24:18]
    ST3.io is invalid
    ST3.clock <= clock
    ST3.reset <= reset
    inst ST4 of ExpectedSuccess3 @[LabelTest.scala 25:18]
    ST4.io is invalid
    ST4.clock <= clock
    ST4.reset <= reset
    

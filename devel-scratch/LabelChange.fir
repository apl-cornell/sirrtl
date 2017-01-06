circuit LabelChange:
    module LabelChange:
        input clock : {L} Clock
        input rst : {L} UInt<1>
        output io : {flip in : {L} UInt<2>, out : {H} UInt<8>}
        io is invalid
        io is invalid

        reg  lbl : {L}       UInt<2> clock with : (reset => (rst UInt(0)))
        reg  foo : {Dom lbl} UInt<8> clock with : (reset => (rst UInt(0)))
        reg  bar : {Dom lbl} UInt<8> clock with : (reset => (rst UInt(0)))
        wire x   : {D1}      UInt<8>
        wire y   : {D2}      UInt<8>

        lbl <= io.in
        x <= UInt(4)
        y <= UInt(5)

        bar <= UInt(0)
        when eq(next(lbl), UInt(1)):
            foo <= x
            bar <= x
        when eq(next(lbl), UInt(2)):
            foo <= y
            bar <= y
            
        io.out <= foo

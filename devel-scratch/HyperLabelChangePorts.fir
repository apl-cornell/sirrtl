circuit HyperLabelChangePorts:
    module HyperLabelChangePorts:
        input clock : {L} Clock
        input rst : {L} UInt<1>
        output io : { flip lbl : seq {L} UInt<16>, flip next_lbl : {L} UInt<16>, out : {H} UInt<8> }
        io is invalid

        reg  foo : {[[io.lbl]]} UInt<8> clock with : (reset => (rst UInt(0)))
        reg  bar : {[[io.lbl]]} UInt<8> clock with : (reset => (rst UInt(0)))
        wire x   : {D1}      UInt<8>
        wire y   : {D2}      UInt<8>

        x <= UInt(4)
        y <= UInt(5)

        bar <= UInt(0)
        when eq(next( io.lbl ), UInt("h0001")):
            foo <= x
            bar <= x
        when eq(next( io.lbl ), UInt("h0010")):
            foo <= y
            bar <= y
            
        io.out <= foo

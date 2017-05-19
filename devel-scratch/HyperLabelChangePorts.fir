circuit HyperLabelChangePorts:
    module HyperLabelChangePorts:
        input clock : {L,H} Clock
        input rst : {L,H} UInt<1>
        output io : { flip clbl : seq {L,H} UInt<16>, flip next_clbl : {L,H} UInt<16>, flip ilbl : seq {L,H} UInt<16>, flip next_ilbl : {L,H} UInt<16>, out : {H,H} UInt<8> }
        io is invalid

        reg  foo : {[[io.clbl]]H,[[io.ilbl]]H} UInt<8> clock with : (reset => (rst UInt(0)))
        reg  bar : {[[io.clbl]]H,[[io.ilbl]]H} UInt<8> clock with : (reset => (rst UInt(0)))
        wire x   : {D1,D1} UInt<8>
        wire y   : {D2,D2} UInt<8>
        wire cand1 : {L,H} UInt<1>
        wire cand2 : {L,H} UInt<1>

        x <= UInt(4)
        y <= UInt(5)


        cand1 <= and(eq(UInt("h0001"), next(io.clbl)), eq(next(io.ilbl), UInt("h0001")))
        cand2 <= and(eq(UInt("h0010"), next(io.clbl)), eq(next(io.ilbl), UInt("h0010")))

        bar <= UInt(0)
        when eq(cand1, UInt(1)):
            foo <= x
            bar <= x
        when eq(cand2, UInt(1)):
            foo <= y
            bar <= y
            
        io.out <= foo

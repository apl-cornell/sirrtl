circuit Downgrades :
    module Downgrades :
        input clock : {[[UInt(0)]]H H} Clock
        input rst: {[[UInt(0)]]H H} UInt<1>
        output io : {flip in0 : {[[UInt(0)]]H H} UInt<8>, flip in1 : {[[UInt("h0001")]]H H} UInt<8>, out : {[[UInt("hFFFF")]]H H} UInt<8>}

        io is invalid
        io is invalid
        reg foo  : {[[UInt(0)]]H H} UInt<8> clock with : (reset => (rst UInt(0)))
        
        wire x : {[[UInt("h0001")]]H L} UInt<8>
        wire y : {[[UInt("h0010")]]H H} UInt<8>
        wire z:  {[[UInt("h0000")]]H H} UInt<8>

        x <= io.in0 @[rhs -> L]
        y <= io.in0 @[rhs -> L]
        z <= io.in0 @[rhs -> L]
            
        foo <= declassify(x {L L}) @[rhs -> H, not robust]
        when y:
            foo <= endorse(UInt(7) {[[UInt(0)]]H H}) @[rhs -> D2, not robust]
            skip
        when eq(z, UInt(2)):
            when eq(x, UInt(2)):
                foo <= declassify(UInt(7) {L H}) @[rhs -> H, not robust]
                skip
            when eq(y, UInt(2)):
                foo <= declassify(UInt(7) {L H}) @[rhs -> D2, robust]
                skip
            skip
        
        io.out <= foo

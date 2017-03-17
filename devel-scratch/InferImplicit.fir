circuit InferImplicit:
    module InferImplicit:
        input clock : {L,H} Clock
        input rst: {L,H} UInt<1>
        output io : {flip in: {D1,H} UInt<8>, out: {D1,H} UInt<8>}
        
        io is invalid
        
        reg foo : UInt<8> clock with : (reset => (rst UInt(0)))
        wire baz : {D2, H} UInt<8>
        
        wire x : UInt<8>
        wire y : UInt<8>

        x <= io.in
        y <= x
        baz <= y
       
        when y:
            foo <= UInt(1)

        io.out <= foo

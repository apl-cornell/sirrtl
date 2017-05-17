circuit InferSimple:
    module InferSimple:
        input clock : {L,L} Clock
        input rst: {L,L} UInt<1>
        output io : {flip in0 : {L,L} UInt<8>, flip in1 : {D1,L} UInt<8>, out1 : {D2,L} UInt<8>, out2 : {D3,L} UInt<8>}

        io is invalid

        wire x: UInt<8>
        wire y: UInt<8>
        wire z: UInt<8>

        x <= io.in0
        y <= io.in1
        z <= x
        io.out1 <= y
        io.out2 <= and(y, x)


circuit LabelSimplify:
    module LabelSimplify:
        output io : {L, H} UInt<1>
        io <= UInt(0)

        wire x : {[[x]]H, H} UInt<8>
        wire y : {[[y]]H, H} UInt<8>
        wire z : {[[z]]H, H} UInt<8>

        wire a : UInt<8>
        wire b : UInt<8>
        wire c : UInt<8>

        x <= and(a , b)
        y <= and(a , b)
        z <= and(a , b)
        a <= c
        b <= c



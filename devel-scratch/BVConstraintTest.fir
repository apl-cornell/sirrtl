circuit BVConstraintTest :
    module BVConstraintTest :
        output io : {flip in0 : {L} UInt<8>, flip in1 : {D1} UInt<8>, out : {H} UInt<8>}
        io is invalid
        io is invalid

        node n0  = bits(add(io.in0, io.in1), 7, 0)
        node n1  = bits(sub(n0, io.in1), 7, 0)
        node n2  = bits(mul(n1, io.in1), 7, 0)
        node n3  = div(n2, io.in1)
        node n4  = rem(n3, io.in1)
        node n5  = pad(lt(n4, io.in1), 8)
        node n6  = pad(gt(n5, io.in1), 8)
        node n7  = pad(geq(n6, io.in1), 8)
        node n8  = pad(eq(n7, io.in1), 8)
        node n9  = pad(neq(n8, io.in1), 8)
        node n10 = bits(shl(n9, 2), 7, 0)
        node n11 = pad(shr(n10, 2), 8)
        node n12 = bits(dshl(n11, io.in1), 7, 0)
        node n13 = bits(dshr(n12, io.in1), 7, 0)
        node n14 = bits(neg(n13), 7, 0)
        node n15 = pad(not(eq(n14,io.in1)), 8)
        node n16 = and(n15,io.in1)
        node n17 = or(n16,io.in1)
        node n18 = xor(n17,io.in1)
        node n19 = bits(n18,4,2)
        node n20 = cat(n19, UInt<2>(3))
        node n21 = pad(n20, 8)
        io.out <= n21



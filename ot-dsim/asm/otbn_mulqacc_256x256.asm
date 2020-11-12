* load first operand from dmem[0]
ADDI x4, x0, 0
BN.LID x4, 0(x0)

* load second operand from dmem[1]
ADDI x4, x0, 1
BN.LID x4, 1(x0)
break
* run multiplication
BN.MULQACC.Z w0.0, w1.0, 0
BN.MULQACC w0.1, w1.0, 64
BN.MULQACC.SO w2.l, w0.0, w1.1, 64
BN.MULQACC w0.2, w1.0, 0
BN.MULQACC w0.1, w1.1, 0
BN.MULQACC w0.0, w1.2, 0
BN.MULQACC w0.3, w1.0, 64
BN.MULQACC w0.2, w1.1, 64
BN.MULQACC w0.1, w1.2, 64
BN.MULQACC.SO w2.u, w0.0, w1.3, 64
BN.MULQACC w0.3, w1.1, 0
BN.MULQACC w0.2, w1.2, 0
BN.MULQACC w0.1, w1.3, 0
BN.MULQACC w0.3, w1.2, 64
BN.MULQACC.SO w3.l, w0.2, w1.3, 64
BN.MULQACC.SO w3.u, w0.3, w1.3, 0

* store lower 256 bit of result in dmem [2]
ADDI x4, x0, 2
BN.SID x4, 2(x0)

* store upper 256 bit of result in dmem [3]
ADDI x4, x0, 3
BN.SID x4, 3(x0)
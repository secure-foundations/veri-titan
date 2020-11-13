
/**
 * Function tag
 */
tag:
sigini #2

/**
 * Function SetupP256PandMuLow
 */
SetupP256PandMuLow:
BN.SUBI w29, w31, 1
movi r29.6h, #0
movi r29.6l, #1
movi r29.5h, #0
movi r29.5l, #0
movi r29.4h, #0
movi r29.4l, #0
movi r29.3h, #0
movi r29.3l, #0
ldmod r29
BN.SUBI w28, w31, 1
movi r28.7h, #0
movi r28.7l, #0
movi r28.5l, #65534
movi r28.4l, #65534
movi r28.3l, #65534
movi r28.1h, #0
movi r28.1l, #0
movi r28.0h, #0
movi r28.0l, #3
JALR x0, x1, 0

/**
 * Function p256init
 */
p256init:
ADDI x3, x0, 31
BN.LID x3, 0(x0)
BN.XOR w31, w31, w31
BN.ADDI w30, w31, 1
JAL x1, SetupP256PandMuLow
BN.MOV w27, w31
movi r27.7h, #23238
movi r27.7l, #13784
movi r27.6h, #43578
movi r27.6l, #37863
movi r27.5h, #46059
movi r27.5l, #48469
movi r27.4h, #30360
movi r27.4l, #34492
movi r27.3h, #25885
movi r27.3l, #1712
movi r27.2h, #52307
movi r27.2l, #45302
movi r27.1h, #15310
movi r27.1l, #15422
movi r27.0h, #10194
movi r27.0l, #24651
JALR x0, x1, 0

/**
 * Function MulMod
 */
MulMod:
BN.MULQACC.Z w24.0, w25.0, 0
BN.MULQACC w24.1, w25.0, 64
BN.MULQACC.SO w19.l, w24.0, w25.1, 64
BN.MULQACC w24.2, w25.0, 0
BN.MULQACC w24.1, w25.1, 0
BN.MULQACC w24.0, w25.2, 0
BN.MULQACC w24.3, w25.0, 64
BN.MULQACC w24.2, w25.1, 64
BN.MULQACC w24.1, w25.2, 64
BN.MULQACC.SO w19.u, w24.0, w25.3, 64
BN.MULQACC w24.3, w25.1, 0
BN.MULQACC w24.2, w25.2, 0
BN.MULQACC w24.1, w25.3, 0
BN.MULQACC w24.3, w25.2, 64
BN.MULQACC.SO w20.l, w24.2, w25.3, 64
BN.MULQACC.SO w20.u, w24.3, w25.3, 0
BN.ADD w20, w20, w31
BN.SEL w22, w28, w31, M
BN.RSHI w21, w19, w20 >> 255
BN.MULQACC.Z w21.0, w28.0, 0
BN.MULQACC w21.1, w28.0, 64
BN.MULQACC.SO w23.l, w21.0, w28.1, 64
BN.MULQACC w21.2, w28.0, 0
BN.MULQACC w21.1, w28.1, 0
BN.MULQACC w21.0, w28.2, 0
BN.MULQACC w21.3, w28.0, 64
BN.MULQACC w21.2, w28.1, 64
BN.MULQACC w21.1, w28.2, 64
BN.MULQACC.SO w23.u, w21.0, w28.3, 64
BN.MULQACC w21.3, w28.1, 0
BN.MULQACC w21.2, w28.2, 0
BN.MULQACC w21.1, w28.3, 0
BN.MULQACC w21.3, w28.2, 64
BN.MULQACC.SO w24.l, w21.2, w28.3, 64
BN.MULQACC.SO w24.u, w21.3, w28.3, 0
BN.ADD w20, w20, w31
BN.RSHI w25, w20, w31 >> 255
BN.ADD w24, w24, w21
BN.ADDC w25, w25, w31
BN.ADD w24, w24, w22
BN.ADDC w25, w25, w31
BN.RSHI w21, w24, w25 >> 1
BN.MULQACC.Z w29.0, w21.0, 0
BN.MULQACC w29.1, w21.0, 64
BN.MULQACC.SO w22.l, w29.0, w21.1, 64
BN.MULQACC w29.2, w21.0, 0
BN.MULQACC w29.1, w21.1, 0
BN.MULQACC w29.0, w21.2, 0
BN.MULQACC w29.3, w21.0, 64
BN.MULQACC w29.2, w21.1, 64
BN.MULQACC w29.1, w21.2, 64
BN.MULQACC.SO w22.u, w29.0, w21.3, 64
BN.MULQACC w29.3, w21.1, 0
BN.MULQACC w29.2, w21.2, 0
BN.MULQACC w29.1, w21.3, 0
BN.MULQACC w29.3, w21.2, 64
BN.MULQACC.SO w23.l, w29.2, w21.3, 64
BN.MULQACC.SO w23.u, w29.3, w21.3, 0
BN.ADD w23, w23, w31
BN.SUB w22, w19, w22
BN.SUBB w20, w20, w23
BN.SEL w21, w29, w31, L
BN.SUB w21, w22, w21
BN.ADDM w19, w21, w31
JALR x0, x1, 0

/**
 * Function p256isoncurve
 */
p256isoncurve:
ADDI x3, x0, 0
BN.LID x3, 0(x0)
lddmp r0
movi r0.5l, #24
movi r0.6l, #24
movi r0.0l, #0
ldrfp r0
BN.LID x14, 0(x22)
BN.MOV w25, w24
JAL x1, MulMod
BN.MOV w0, w19
BN.LID x13, 0(x21)
BN.MOV w25, w24
JAL x1, MulMod
BN.LID x13, 0(x21)
BN.MOV w25, w19
JAL x1, MulMod
BN.LID x13, 0(x21)
BN.SUBM w19, w19, w24
BN.SUBM w19, w19, w24
BN.SUBM w19, w19, w24
BN.ADDM w24, w19, w27
BN.SID x13, 0(x19)
BN.SID x8, 0(x20)
JALR x0, x1, 0

/**
 * Function ProjAdd
 */
ProjAdd:
BN.MOV w24, w11
BN.MOV w25, w8
JAL x1, MulMod
BN.MOV w14, w19
BN.MOV w24, w12
BN.MOV w25, w9
JAL x1, MulMod
BN.MOV w15, w19
BN.MOV w24, w13
BN.MOV w25, w10
JAL x1, MulMod
BN.MOV w16, w19
BN.ADDM w17, w11, w12
BN.ADDM w18, w8, w9
BN.MOV w24, w17
BN.MOV w25, w18
JAL x1, MulMod
BN.ADDM w18, w14, w15
BN.SUBM w17, w19, w18
BN.ADDM w18, w12, w13
BN.ADDM w19, w9, w10
BN.MOV w24, w18
BN.MOV w25, w19
JAL x1, MulMod
BN.MOV w18, w19
BN.ADDM w19, w15, w16
BN.SUBM w18, w18, w19
BN.ADDM w19, w11, w13
BN.ADDM w12, w8, w10
BN.MOV w24, w19
BN.MOV w25, w12
JAL x1, MulMod
BN.MOV w11, w19
BN.ADDM w12, w14, w16
BN.SUBM w12, w11, w12
BN.MOV w24, w27
BN.MOV w25, w16
JAL x1, MulMod
BN.SUBM w11, w12, w19
BN.ADDM w13, w11, w11
BN.ADDM w11, w11, w13
BN.SUBM w13, w15, w11
BN.ADDM w11, w15, w11
BN.MOV w24, w27
BN.MOV w25, w12
JAL x1, MulMod
BN.ADDM w15, w16, w16
BN.ADDM w16, w15, w16
BN.SUBM w12, w19, w16
BN.SUBM w12, w12, w14
BN.ADDM w15, w12, w12
BN.ADDM w12, w15, w12
BN.ADDM w15, w14, w14
BN.ADDM w14, w15, w14
BN.SUBM w14, w14, w16
BN.MOV w24, w18
BN.MOV w25, w12
JAL x1, MulMod
BN.MOV w15, w19
BN.MOV w24, w14
BN.MOV w25, w12
JAL x1, MulMod
BN.MOV w16, w19
BN.MOV w24, w11
BN.MOV w25, w13
JAL x1, MulMod
BN.ADDM w12, w19, w16
BN.MOV w24, w17
BN.MOV w25, w11
JAL x1, MulMod
BN.SUBM w11, w19, w15
BN.MOV w24, w18
BN.MOV w25, w13
JAL x1, MulMod
BN.MOV w13, w19
BN.MOV w24, w17
BN.MOV w25, w14
JAL x1, MulMod
BN.ADDM w13, w13, w19
JALR x0, x1, 0

/**
 * Function ProjToAffine
 */
ProjToAffine:
BN.ADDM w10, w10, w31
BN.MOV w24, w10
BN.MOV w25, w10
JAL x1, MulMod
BN.MOV w24, w19
BN.MOV w25, w10
JAL x1, MulMod
BN.MOV w12, w19
BN.MOV w24, w19
BN.MOV w25, w19
JAL x1, MulMod
BN.MOV w24, w19
BN.MOV w25, w19
JAL x1, MulMod
BN.MOV w24, w19
BN.MOV w25, w12
JAL x1, MulMod
BN.MOV w13, w19
LOOPI 4, 4
BN.MOV w24, w19
BN.MOV w25, w19
JAL x1, MulMod
ADDI x0, x0, 0
endloop
BN.MOV w24, w19
BN.MOV w25, w13
JAL x1, MulMod
BN.MOV w14, w19
LOOPI 8, 4
BN.MOV w24, w19
BN.MOV w25, w19
JAL x1, MulMod
ADDI x0, x0, 0
endloop
BN.MOV w24, w19
BN.MOV w25, w14
JAL x1, MulMod
BN.MOV w15, w19
LOOPI 16, 4
BN.MOV w24, w19
BN.MOV w25, w19
JAL x1, MulMod
ADDI x0, x0, 0
endloop
BN.MOV w24, w19
BN.MOV w25, w15
JAL x1, MulMod
BN.MOV w16, w19
LOOPI 32, 4
BN.MOV w24, w19
BN.MOV w25, w19
JAL x1, MulMod
ADDI x0, x0, 0
endloop
BN.MOV w17, w19
BN.MOV w24, w10
BN.MOV w25, w19
JAL x1, MulMod
LOOPI 192, 4
BN.MOV w24, w19
BN.MOV w25, w19
JAL x1, MulMod
ADDI x0, x0, 0
endloop
BN.MOV w18, w19
BN.MOV w24, w17
BN.MOV w25, w16
JAL x1, MulMod
LOOPI 16, 4
BN.MOV w24, w19
BN.MOV w25, w19
JAL x1, MulMod
ADDI x0, x0, 0
endloop
BN.MOV w24, w15
BN.MOV w25, w19
JAL x1, MulMod
LOOPI 8, 4
BN.MOV w24, w19
BN.MOV w25, w19
JAL x1, MulMod
ADDI x0, x0, 0
endloop
BN.MOV w24, w14
BN.MOV w25, w19
JAL x1, MulMod
LOOPI 4, 4
BN.MOV w24, w19
BN.MOV w25, w19
JAL x1, MulMod
ADDI x0, x0, 0
endloop
BN.MOV w24, w13
BN.MOV w25, w19
JAL x1, MulMod
LOOPI 2, 4
BN.MOV w24, w19
BN.MOV w25, w19
JAL x1, MulMod
ADDI x0, x0, 0
endloop
BN.MOV w24, w12
BN.MOV w25, w19
JAL x1, MulMod
LOOPI 2, 4
BN.MOV w24, w19
BN.MOV w25, w19
JAL x1, MulMod
ADDI x0, x0, 0
endloop
BN.MOV w24, w10
BN.MOV w25, w19
JAL x1, MulMod
BN.MOV w24, w19
BN.MOV w25, w18
JAL x1, MulMod
BN.MOV w14, w19
BN.MOV w24, w8
BN.MOV w25, w14
JAL x1, MulMod
BN.MOV w11, w19
BN.MOV w24, w9
BN.MOV w25, w14
JAL x1, MulMod
BN.MOV w12, w19
JALR x0, x1, 0

/**
 * Function ModInv
 */
ModInv:
stmod r2
BN.SUBI w2, w2, 2
BN.MOV w1, w30
LOOPI 256, 14
BN.MOV w24, w1
BN.MOV w25, w1
JAL x1, MulMod
BN.MOV w3, w19
BN.ADD w2, w2, w2
BN.SEL w1, w1, w3, C
CSRRS x2, 1984, x0
ANDI x2, x2, 1
BEQ x2, x0, nomul
BN.MOV w24, w3
BN.MOV w25, w0
JAL x1, MulMod
BN.MOV w1, w19

nomul:
ADDI x0, x0, 0
endloop
JALR x0, x1, 0

/**
 * Function FetchBandRandomize
 */
FetchBandRandomize:
strnd r2
BN.ADDM w26, w2, w31
BN.LID x10, 0(x21)
BN.MOV w25, w26
JAL x1, MulMod
BN.MOV w6, w19
BN.LID x10, 0(x22)
BN.MOV w25, w26
JAL x1, MulMod
BN.MOV w7, w19
JALR x0, x1, 0

/**
 * Function ProjDouble
 */
ProjDouble:
BN.MOV w11, w8
BN.MOV w12, w9
BN.MOV w13, w10
JAL x1, ProjAdd
JALR x0, x1, 0

/**
 * Function SetupP256NandMuLow
 */
SetupP256NandMuLow:
BN.SUBI w29, w31, 1
movi r29.6h, #0
movi r29.6l, #0
movi r29.3h, #48358
movi r29.3l, #64173
movi r29.2h, #42775
movi r29.2l, #40580
movi r29.1h, #62393
movi r29.1l, #51906
movi r29.0h, #64611
movi r29.0l, #9553
BN.SUBI w28, w31, 1
movi r28.7h, #0
movi r28.7l, #0
movi r28.5l, #65534
movi r28.3h, #17177
movi r28.3l, #1362
movi r28.2h, #57114
movi r28.2l, #27681
movi r28.1h, #303
movi r28.1l, #64901
movi r28.0h, #61151
movi r28.0l, #39934
ldmod r29
JALR x0, x1, 0

/**
 * Function ScalarMult_internal
 */
ScalarMult_internal:
JAL x1, SetupP256NandMuLow
BN.LID x9, 0(x17)
BN.ADDM w1, w1, w31
BN.SUBM w0, w0, w1
JAL x1, SetupP256PandMuLow
JAL x1, FetchBandRandomize
BN.MOV w8, w6
BN.MOV w9, w7
BN.MOV w10, w26
JAL x1, ProjDouble
BN.MOV w3, w11
BN.MOV w4, w12
BN.MOV w5, w13
BN.MOV w8, w31
BN.MOV w9, w30
BN.MOV w10, w31
LOOPI 256, 32
JAL x1, ProjDouble
JAL x1, FetchBandRandomize
BN.XOR w8, w0, w1
BN.SEL w8, w6, w3, M
BN.SEL w9, w7, w4, M
BN.SEL w10, w26, w5, M
BN.MOV w2, w11
BN.MOV w6, w12
BN.MOV w7, w13
JAL x1, ProjAdd
BN.OR w8, w0, w1
BN.SEL w8, w11, w2, M
BN.SEL w9, w12, w6, M
BN.SEL w10, w13, w7, M
BN.RSHI w0, w0, w0 >> 255
BN.RSHI w1, w1, w1 >> 255
strnd r11
strnd r12
strnd r13
strnd r2
BN.MOV w24, w3
BN.MOV w25, w2
JAL x1, MulMod
BN.MOV w3, w19
BN.MOV w24, w4
BN.MOV w25, w2
JAL x1, MulMod
BN.MOV w4, w19
BN.MOV w24, w5
BN.MOV w25, w2
JAL x1, MulMod
BN.MOV w5, w19
endloop
JAL x1, ProjToAffine
JALR x0, x1, 0

/**
 * Function get_P256B
 */
get_P256B:
BN.MOV w8, w31
movi r8.7h, #27415
movi r8.7l, #53746
movi r8.6h, #57644
movi r8.6l, #16967
movi r8.5h, #63676
movi r8.5l, #59109
movi r8.4h, #25508
movi r8.4l, #16626
movi r8.3h, #30467
movi r8.3l, #32129
movi r8.2h, #11755
movi r8.2l, #13216
movi r8.1h, #62625
movi r8.1l, #14661
movi r8.0h, #55448
movi r8.0l, #49814
BN.MOV w9, w31
movi r9.7h, #20451
movi r9.7l, #17122
movi r9.6h, #65050
movi r9.6l, #32667
movi r9.5h, #36583
movi r9.5l, #60234
movi r9.4h, #31759
movi r9.4l, #40470
movi r9.3h, #11214
movi r9.3l, #13143
movi r9.2h, #27441
movi r9.2l, #24270
movi r9.1h, #52150
movi r9.1l, #16488
movi r9.0h, #14271
movi r9.0l, #20981
JALR x0, x1, 0

/**
 * Function p256sign
 */
p256sign:
ADDI x0, x0, 0
ADDI x3, x0, 0
BN.LID x3, 0(x0)
lddmp r0
movi r0.0l, #0
movi r0.1l, #1
movi r0.2l, #24
movi r0.4l, #8
movi r0.5l, #9
ldrfp r0
JAL x1, get_P256B
BN.SID x12, 0(x21)
BN.SID x13, 0(x22)
ADDI x0, x0, 0
BN.LID x8, 0(x16)
JAL x1, ScalarMult_internal
JAL x1, SetupP256NandMuLow
BN.LID x8, 0(x16)
JAL x1, ModInv
BN.LID x10, 0(x23)
BN.MOV w25, w1
JAL x1, MulMod
BN.ADDM w24, w11, w31
BN.SID x10, 0(x19)
ADDI x0, x0, 0
BN.MOV w25, w19
JAL x1, MulMod
BN.MOV w0, w19
BN.LID x10, 0(x18)
BN.MOV w25, w1
JAL x1, MulMod
BN.ADDM w0, w19, w0
BN.SID x8, 0(x20)
JAL x1, SetupP256PandMuLow
JALR x0, x1, 0

/**
 * Function p256scalarbasemult
 */
p256scalarbasemult:
ADDI x0, x0, 0
ADDI x3, x0, 0
BN.LID x3, 0(x0)
lddmp r0
movi r0.0l, #0
movi r0.1l, #1
movi r0.2l, #24
movi r0.3l, #11
movi r0.4l, #8
movi r0.5l, #9
ldrfp r0
BN.LID x8, 0(x17)
ldrnd r0
JAL x1, get_P256B
BN.SID x12, 0(x21)
BN.SID x13, 0(x22)
ADDI x0, x0, 0
BN.LID x8, 0(x23)
JAL x1, ScalarMult_internal
BN.SID x11++, 0(x21)
BN.SID x11++, 0(x22)
JALR x0, x1, 0

/**
 * Function ModInvVar
 */
ModInvVar:
BN.MOV w2, w31
BN.MOV w3, w30
stmod r4
stmod r7
BN.MOV w5, w0

impvt_Loop:
BN.OR w4, w4, w4
CSRRS x2, 1984, x0
ANDI x2, x2, 2
BNE x2, x0, impvt_Uodd
BN.RSHI w4, w4, w31 >> 1
BN.OR w2, w2, w2
CSRRS x2, 1984, x0
ANDI x2, x2, 2
BNE x2, x0, impvt_Rodd
BN.RSHI w2, w2, w31 >> 1
JAL x0, impvt_Loop

impvt_Rodd:
BN.ADD w2, w7, w2
BN.ADDC w6, w31, w31
BN.RSHI w2, w2, w6 >> 1
JAL x0, impvt_Loop

impvt_Uodd:
BN.OR w5, w5, w5
CSRRS x2, 1984, x0
ANDI x2, x2, 2
BNE x2, x0, impvt_UVodd
BN.RSHI w5, w5, w31 >> 1
BN.OR w3, w3, w3
CSRRS x2, 1984, x0
ANDI x2, x2, 2
BNE x2, x0, impvt_Sodd
BN.RSHI w3, w3, w31 >> 1
JAL x0, impvt_Loop

impvt_Sodd:
BN.ADD w3, w7, w3
BN.ADDC w6, w31, w31
BN.RSHI w3, w3, w6 >> 1
JAL x0, impvt_Loop

impvt_UVodd:
BN.CMP w5, w4
CSRRS x2, 1984, x0
ANDI x2, x2, 1
BEQ x2, x0, impvt_V>=U
BN.SUBM w2, w2, w3
BN.SUB w4, w4, w5
JAL x0, impvt_Loop

impvt_V>=U:
BN.SUBM w3, w3, w2
BN.SUB w5, w5, w4
CSRRS x2, 1984, x0
ANDI x2, x2, 8
BEQ x2, x0, impvt_Loop
BN.ADDM w1, w2, w31
JALR x0, x1, 0

/**
 * Function p256verify
 */
p256verify:
ADDI x3, x0, 6
BN.LID x3, 0(x0)
lddmp r6
movi r6.3l, #24
movi r6.4l, #0
movi r6.5l, #8
movi r6.6l, #9
movi r6.0l, #11
movi r6.7l, #12
movi r6.2l, #24
ldrfp r6
BN.LID x11, 0(x19)
BN.MOV w24, w6
BN.NOT w24, w24
JAL x1, SetupP256NandMuLow
BN.CMP w6, w31
CSRRS x2, 1984, x0
ANDI x2, x2, 8
BNE x2, x0, fail
BN.CMP w6, w29
CSRRS x2, 1984, x0
ANDI x2, x2, 1
BEQ x2, x0, fail
BN.LID x12, 0(x20)
BN.CMP w0, w31
CSRRS x2, 1984, x0
ANDI x2, x2, 8
BNE x2, x0, fail
BN.CMP w0, w29
CSRRS x2, 1984, x0
ANDI x2, x2, 1
BEQ x2, x0, fail
JAL x1, ModInvVar
BN.LID x11, 0(x19)
BN.MOV w25, w1
JAL x1, MulMod
BN.MOV w0, w19
BN.LID x10, 0(x18)
BN.MOV w25, w1
JAL x1, MulMod
BN.MOV w1, w19
JAL x1, SetupP256PandMuLow
BN.LID x8, 0(x21)
BN.LID x15, 0(x22)
BN.MOV w13, w30
JAL x1, get_P256B
BN.MOV w10, w30
JAL x1, ProjAdd
BN.MOV w3, w11
BN.MOV w4, w12
BN.MOV w5, w13
BN.AND w2, w0, w1
BN.MOV w11, w31
BN.MOV w12, w30
BN.MOV w13, w31
LOOPI 256, 30
BN.MOV w8, w11
BN.MOV w9, w12
BN.MOV w10, w13
JAL x1, ProjAdd
BN.ADD w2, w2, w2
CSRRS x2, 1984, x0
ANDI x2, x2, 1
BEQ x2, x0, noBoth
BN.MOV w8, w3
BN.MOV w9, w4
BN.MOV w10, w5
JAL x1, ProjAdd
JAL x0, noY

noBoth:
BN.ADD w6, w0, w0
CSRRS x2, 1984, x0
ANDI x2, x2, 1
BEQ x2, x0, noG
BN.LID x13, 0(x21)
BN.LID x14, 0(x22)
BN.MOV w10, w30
JAL x1, ProjAdd

noG:
BN.ADD w6, w1, w1
CSRRS x2, 1984, x0
ANDI x2, x2, 1
BEQ x2, x0, noY
JAL x1, get_P256B
BN.MOV w10, w30
JAL x1, ProjAdd

noY:
BN.ADD w0, w0, w0
BN.ADD w1, w1, w1
endloop
BN.MOV w0, w13
JAL x1, ModInvVar
BN.MOV w24, w1
BN.MOV w25, w11
JAL x1, MulMod
JAL x1, SetupP256NandMuLow
BN.SUBM w24, w19, w31

fail:
BN.SID x11, 0(x17)
JALR x0, x1, 0

/**
 * Function p256scalarmult
 */
p256scalarmult:
ADDI x3, x0, 0
BN.LID x3, 0(x0)
lddmp r0
movi r0.0l, #0
movi r0.1l, #1
movi r0.2l, #24
movi r0.3l, #11
ldrfp r0
BN.LID x8, 0(x16)
JAL x1, ScalarMult_internal
BN.SID x11++, 0(x21)
BN.SID x11++, 0(x22)
JALR x0, x1, 0

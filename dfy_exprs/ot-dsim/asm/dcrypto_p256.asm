function tag[1] {
sigini #2
}
function SetupP256PandMuLow[21] {
subi r29, r31, #1
movi r29.6h, #0
movi r29.6l, #1
movi r29.5h, #0
movi r29.5l, #0
movi r29.4h, #0
movi r29.4l, #0
movi r29.3h, #0
movi r29.3l, #0
ldmod r29
subi r28, r31, #1
movi r28.7h, #0
movi r28.7l, #0
movi r28.5l, #65534
movi r28.4l, #65534
movi r28.3l, #65534
movi r28.1h, #0
movi r28.1l, #0
movi r28.0h, #0
movi r28.0l, #3
ret
}
function p256init[22] {
ldi r31, [#0]
xor r31, r31, r31
addi r30, r31, #1
call &SetupP256PandMuLow
mov r27, r31
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
ret
}
function MulMod[38] {
mul128 r19, r24l, r25l
mul128 r20, r24u, r25u
mul128 r21, r24u, r25l
add r19, r19, r21 << 128
addc r20, r20, r21 >> 128
mul128 r21, r24l, r25u
add r19, r19, r21 << 128
addc r20, r20, r21 >> 128
selm r22, r28, r31
rshi r21, r19, r20 >> 255
mul128 r23, r21l, r28l
mul128 r24, r21u, r28u
mul128 r25, r21u, r28l
add r23, r23, r25 << 128
addc r24, r24, r25 >> 128
mul128 r25, r21l, r28u
add r23, r23, r25 << 128
addc r24, r24, r25 >> 128
rshi r25, r20, r31 >> 255
add r24, r24, r21
addc r25, r25, r31
add r24, r24, r22
addc r25, r25, r31
rshi r21, r24, r25 >> 1
mul128 r22, r29l, r21l
mul128 r23, r29u, r21u
mul128 r24, r29u, r21l
add r22, r22, r24 << 128
addc r23, r23, r24 >> 128
mul128 r24, r29l, r21u
add r22, r22, r24 << 128
addc r23, r23, r24 >> 128
sub r22, r19, r22
subb r20, r20, r23
sell r21, r29, r31
sub r21, r22, r21
addm r19, r21, r31
ret
}
function p256isoncurve[24] {
ldi r0, [#0]
lddmp r0
movi r0.5l, #24
movi r0.6l, #24
movi r0.0l, #0
ldrfp r0
ld *6, *6
mov r25, r24
call &MulMod
mov r0, r19
ld *5, *5
mov r25, r24
call &MulMod
ld *5, *5
mov r25, r19
call &MulMod
ld *5, *5
subm r19, r19, r24
subm r19, r19, r24
subm r19, r19, r24
addm r24, r19, r27
st *5, *3
st *0, *4
ret
}
function ProjAdd[80] {
mov r24, r11
mov r25, r8
call &MulMod
mov r14, r19
mov r24, r12
mov r25, r9
call &MulMod
mov r15, r19
mov r24, r13
mov r25, r10
call &MulMod
mov r16, r19
addm r17, r11, r12
addm r18, r8, r9
mov r24, r17
mov r25, r18
call &MulMod
addm r18, r14, r15
subm r17, r19, r18
addm r18, r12, r13
addm r19, r9, r10
mov r24, r18
mov r25, r19
call &MulMod
mov r18, r19
addm r19, r15, r16
subm r18, r18, r19
addm r19, r11, r13
addm r12, r8, r10
mov r24, r19
mov r25, r12
call &MulMod
mov r11, r19
addm r12, r14, r16
subm r12, r11, r12
mov r24, r27
mov r25, r16
call &MulMod
subm r11, r12, r19
addm r13, r11, r11
addm r11, r11, r13
subm r13, r15, r11
addm r11, r15, r11
mov r24, r27
mov r25, r12
call &MulMod
addm r15, r16, r16
addm r16, r15, r16
subm r12, r19, r16
subm r12, r12, r14
addm r15, r12, r12
addm r12, r15, r12
addm r15, r14, r14
addm r14, r15, r14
subm r14, r14, r16
mov r24, r18
mov r25, r12
call &MulMod
mov r15, r19
mov r24, r14
mov r25, r12
call &MulMod
mov r16, r19
mov r24, r11
mov r25, r13
call &MulMod
addm r12, r19, r16
mov r24, r17
mov r25, r11
call &MulMod
subm r11, r19, r15
mov r24, r18
mov r25, r13
call &MulMod
mov r13, r19
mov r24, r17
mov r25, r14
call &MulMod
addm r13, r13, r19
ret
}
function ProjToAffine[116] {
addm r10, r10, r31
mov r24, r10
mov r25, r10
call &MulMod
mov r24, r19
mov r25, r10
call &MulMod
mov r12, r19
mov r24, r19
mov r25, r19
call &MulMod
mov r24, r19
mov r25, r19
call &MulMod
mov r24, r19
mov r25, r12
call &MulMod
mov r13, r19
loop #4 (
mov r24, r19
mov r25, r19
call &MulMod
nop
)
mov r24, r19
mov r25, r13
call &MulMod
mov r14, r19
loop #8 (
mov r24, r19
mov r25, r19
call &MulMod
nop
)
mov r24, r19
mov r25, r14
call &MulMod
mov r15, r19
loop #16 (
mov r24, r19
mov r25, r19
call &MulMod
nop
)
mov r24, r19
mov r25, r15
call &MulMod
mov r16, r19
loop #32 (
mov r24, r19
mov r25, r19
call &MulMod
nop
)
mov r17, r19
mov r24, r10
mov r25, r19
call &MulMod
loop #192 (
mov r24, r19
mov r25, r19
call &MulMod
nop
)
mov r18, r19
mov r24, r17
mov r25, r16
call &MulMod
loop #16 (
mov r24, r19
mov r25, r19
call &MulMod
nop
)
mov r24, r15
mov r25, r19
call &MulMod
loop #8 (
mov r24, r19
mov r25, r19
call &MulMod
nop
)
mov r24, r14
mov r25, r19
call &MulMod
loop #4 (
mov r24, r19
mov r25, r19
call &MulMod
nop
)
mov r24, r13
mov r25, r19
call &MulMod
loop #2 (
mov r24, r19
mov r25, r19
call &MulMod
nop
)
mov r24, r12
mov r25, r19
call &MulMod
loop #2 (
mov r24, r19
mov r25, r19
call &MulMod
nop
)
mov r24, r10
mov r25, r19
call &MulMod
mov r24, r19
mov r25, r18
call &MulMod
mov r14, r19
mov r24, r8
mov r25, r14
call &MulMod
mov r11, r19
mov r24, r9
mov r25, r14
call &MulMod
mov r12, r19
ret
}
function ModInv[17] {
stmod r2
subi r2, r2, #2
mov r1, r30
loop #256 (
mov r24, r1
mov r25, r1
call &MulMod
mov r3, r19
add r2, r2, r2
selc r1, r1, r3
bnc nomul
mov r24, r3
mov r25, r0
call &MulMod
mov r1, r19
nomul:
nop
)
ret
}
function FetchBandRandomize[11] {
strnd r2
addm r26, r2, r31
ld *2, *5
mov r25, r26
call &MulMod
mov r6, r19
ld *2, *6
mov r25, r26
call &MulMod
mov r7, r19
ret
}
function ProjDouble[5] {
mov r11, r8
mov r12, r9
mov r13, r10
call &ProjAdd
ret
}
function SetupP256NandMuLow[25] {
subi r29, r31, #1
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
subi r28, r31, #1
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
ret
}
function ScalarMult_internal[51] {
call &SetupP256NandMuLow
ld *1, *1
addm r1, r1, r31
subm r0, r0, r1
call &SetupP256PandMuLow
call &FetchBandRandomize
mov r8, r6
mov r9, r7
mov r10, r26
call &ProjDouble
mov r3, r11
mov r4, r12
mov r5, r13
mov r8, r31
mov r9, r30
mov r10, r31
loop #256 (
call &ProjDouble
call &FetchBandRandomize
xor r8, r0, r1
selm r8, r6, r3
selm r9, r7, r4
selm r10, r26, r5
mov r2, r11
mov r6, r12
mov r7, r13
call &ProjAdd
or r8, r0, r1
selm r8, r11, r2
selm r9, r12, r6
selm r10, r13, r7
rshi r0, r0, r0 >> 255
rshi r1, r1, r1 >> 255
strnd r11
strnd r12
strnd r13
strnd r2
mov r24, r3
mov r25, r2
call &MulMod
mov r3, r19
mov r24, r4
mov r25, r2
call &MulMod
mov r4, r19
mov r24, r5
mov r25, r2
call &MulMod
mov r5, r19
)
call &ProjToAffine
ret
}
function get_P256B[35] {
mov r8, r31
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
mov r9, r31
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
ret
}
function p256sign[34] {
nop
ldi r0, [#0]
lddmp r0
movi r0.0l, #0
movi r0.1l, #1
movi r0.2l, #24
movi r0.4l, #8
movi r0.5l, #9
ldrfp r0
call &get_P256B
st *4, *5
st *5, *6
nop
ld *0, *0
call &ScalarMult_internal
call &SetupP256NandMuLow
ld *0, *0
call &ModInv
ld *2, *7
mov r25, r1
call &MulMod
addm r24, r11, r31
st *2, *3
nop
mov r25, r19
call &MulMod
mov r0, r19
ld *2, *2
mov r25, r1
call &MulMod
addm r0, r19, r0
st *0, *4
call &SetupP256PandMuLow
ret
}
function p256scalarbasemult[21] {
nop
ldi r0, [#0]
lddmp r0
movi r0.0l, #0
movi r0.1l, #1
movi r0.2l, #24
movi r0.3l, #11
movi r0.4l, #8
movi r0.5l, #9
ldrfp r0
ld *0, *1
ldrnd r0
call &get_P256B
st *4, *5
st *5, *6
nop
ld *0, *7
call &ScalarMult_internal
st *3++, *5
st *3++, *6
ret
}
function ModInvVar[37] {
mov r2, r31
mov r3, r30
stmod r4
stmod r7
mov r5, r0
impvt_Loop:
or r4, r4, r4
bl impvt_Uodd
rshi r4, r4, r31 >> 1
or r2, r2, r2
bl impvt_Rodd
rshi r2, r2, r31 >> 1
b impvt_Loop
impvt_Rodd:
add r2, r7, r2
addc r6, r31, r31
rshi r2, r2, r6 >> 1
b impvt_Loop
impvt_Uodd:
or r5, r5, r5
bl impvt_UVodd
rshi r5, r5, r31 >> 1
or r3, r3, r3
bl impvt_Sodd
rshi r3, r3, r31 >> 1
b impvt_Loop
impvt_Sodd:
add r3, r7, r3
addc r6, r31, r31
rshi r3, r3, r6 >> 1
b impvt_Loop
impvt_UVodd:
cmp r5, r4
bnc impvt_V>=U
subm r2, r2, r3
sub r4, r4, r5
b impvt_Loop
impvt_V>=U:
subm r3, r3, r2
sub r5, r5, r4
bnz impvt_Loop
addm r1, r2, r31
ret
}
function p256verify[80] {
ldi r6, [#0]
lddmp r6
movi r6.3l, #24
movi r6.4l, #0
movi r6.5l, #8
movi r6.6l, #9
movi r6.0l, #11
movi r6.7l, #12
movi r6.2l, #24
ldrfp r6
ld *3, *3
mov r24, r6
not r24, r24
call &SetupP256NandMuLow
cmp r6, r31
bz fail
cmp r6, r29
bnc fail
ld *4, *4
cmp r0, r31
bz fail
cmp r0, r29
bnc fail
call &ModInvVar
ld *3, *3
mov r25, r1
call &MulMod
mov r0, r19
ld *2, *2
mov r25, r1
call &MulMod
mov r1, r19
call &SetupP256PandMuLow
ld *0, *5
ld *7, *6
mov r13, r30
call &get_P256B
mov r10, r30
call &ProjAdd
mov r3, r11
mov r4, r12
mov r5, r13
and r2, r0, r1
mov r11, r31
mov r12, r30
mov r13, r31
loop #256 (
mov r8, r11
mov r9, r12
mov r10, r13
call &ProjAdd
add r2, r2, r2
bnc noBoth
mov r8, r3
mov r9, r4
mov r10, r5
call &ProjAdd
b noY
noBoth:
add r6, r0, r0
bnc noG
ld *5, *5
ld *6, *6
mov r10, r30
call &ProjAdd
noG:
add r6, r1, r1
bnc noY
call &get_P256B
mov r10, r30
call &ProjAdd
noY:
add r0, r0, r0
add r1, r1, r1
)
mov r0, r13
call &ModInvVar
mov r24, r1
mov r25, r11
call &MulMod
call &SetupP256NandMuLow
subm r24, r19, r31
fail:
st *3, *1
ret
}
function p256scalarmult[12] {
ldi r0, [#0]
lddmp r0
movi r0.0l, #0
movi r0.1l, #1
movi r0.2l, #24
movi r0.3l, #11
ldrfp r0
ld *0, *0
call &ScalarMult_internal
st *3++, *5
st *3++, *6
ret
}

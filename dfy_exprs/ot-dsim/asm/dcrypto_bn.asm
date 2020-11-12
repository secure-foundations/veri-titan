function tag[1] {
sigini #1
}
function d0inv[14] {
xor r0, r0, r0
movi r0.0l, #1
mov r29, r0
loop #256 (
mul128 r1, r28l, r29l
mul128 r2, r28u, r29l
add r1, r1, r2 << 128
mul128 r2, r28l, r29u
add r1, r1, r2 << 128
and r1, r1, r0
or r29, r29, r1
add r0, r0, r0
)
sub r29, r31, r29
ret
}
function selcxSub[25] {
ldrfp r1
lddmp r0
strnd r4
add r4, r4, r31
bl selcxSub_invsel
addcx r3, r4, r4 << 16
loop *6 (
ld *2, *0++
ldr *3, *0
ldr *0, *4
subb r4, r2, r3
strnd r3
sellx r3, r4, r2
ldr *0++, *2
)
ret
selcxSub_invsel:
addcx r3, r4, r4 << 16
loop *6 (
ld *2, *0++
ldr *3, *0
ldr *0, *4
subb r4, r2, r3
strnd r3
sellx r3, r2, r4
ldr *0++, *2
)
ret
}
function computeRR[41] {
xor r31, r31, r31
ldi r0, [#0]
lddmp r0
xor r3, r3, r3
movi r3.0l, #65535
and r1, r3, r0 >> 192
not r3, r3
and r3, r3, r0
add r3, r3, r1 << 8
ldlc r3
movi r1.0l, #5
movi r1.2l, #3
movi r1.3l, #2
movi r1.4l, #4
ldrfp r1
xor r3, r3, r3
loop *6 (
ldr *0++, *2
)
subx r3, r31, r0
call &selcxSub
loop *0 (
ldrfp r1
subx r3, r3, r3
loop *6 (
ldr *3, *0
addcx r2, r2, r2
ldr *0++, *3
)
call &selcxSub
ldrfp r1
lddmp r0
subx r3, r3, r3
loop *6 (
ld *2, *0++
ldr *3, *0++
cmpbx r3, r2
)
call &selcxSub
nop
)
ldrfp r1
loop *6 (
st *0++, *2++
)
ret
}
function dmXd0[9] {
mul128 r27, r30l, r25l
mul128 r26, r30u, r25u
mul128 r23, r30u, r25l
add r27, r27, r23 << 128
addc r26, r26, r23 >> 128
mul128 r23, r30l, r25u
add r27, r27, r23 << 128
addc r26, r26, r23 >> 128
ret
}
function dmXa[9] {
mul128 r27, r30l, r2l
mul128 r26, r30u, r2u
mul128 r23, r30u, r2l
add r27, r27, r23 << 128
addc r26, r26, r23 >> 128
mul128 r23, r30l, r2u
add r27, r27, r23 << 128
addc r26, r26, r23 >> 128
ret
}
function mma_sub_cx[23] {
strnd r28
add r28, r28, r31
bl mma_invsel
addcx r28, r28, r28 << 16
loop *6 (
ld *5, *0++
ldr *4, *0
subb r29, r30, r24
strnd r24
ldr *0, *5
sellx r24, r29, r30
ldr *0++, *5
)
ret
mma_invsel:
addcx r28, r28, r28 << 16
loop *6 (
ld *5, *0++
ldr *4, *0
subb r29, r30, r24
strnd r24
ldr *0, *5
sellx r24, r30, r29
ldr *0++, *5
)
ret
}
function mma[39] {
movi r1.4l, #30
movi r1.5l, #24
ldrfp r1
ld *4, *3++
call &dmXa
ldr *5, *0++
add r30, r27, r24
addc r29, r26, r31
mov r25, r3
call &dmXd0
mov r25, r27
mov r28, r26
mov r24, r30
ld *4, *0++
call &dmXd0
add r27, r27, r24
addc r28, r26, r31
loop *7 (
ld *4, *3++
call &dmXa
ldr *5, *0++
add r27, r27, r24
addc r26, r26, r31
add r24, r27, r29
addc r29, r26, r31
ld *4, *0++
call &dmXd0
add r27, r27, r24
addc r26, r26, r31
addx r24, r27, r28
ldr *2++, *5
addcx r28, r26, r31
)
addcx r24, r29, r28
ldr *2++, *5
lddmp r0
ldrfp r1
call &mma_sub_cx
nop
ret
}
function setupPtrs[11] {
ldi r31, [#0]
xor r31, r31, r31
lddmp r0
ldlc r0
mov r1, r31
movi r1.0l, #4
movi r1.1l, #3
movi r1.2l, #4
movi r1.3l, #2
ldrfp r1
ret
}
function mulx[19] {
ldi r0, [#0]
call &setupPtrs
ld *1, *1
mov r2, r31
loop *6 (
ldr *2++, *3
)
ldrfp r1
loop *6 (
ld *3, *4++
stdmp r0
call &mma
lddmp r0
)
ldrfp r1
lddmp r0
loop *6 (
st *0++, *5++
)
ldrfp r1
lddmp r0
ret
}
function mm1_sub_cx[22] {
strnd r3
add r3, r3, r31
bl mm1_invsel
addcx r3, r3, r3 << 16
loop *6 (
ld *1, *0++
ldr *3, *0++
subb r3, r2, r3
sellx r2, r3, r2
st *3, *5++
nop
)
ret
nop
mm1_invsel:
addcx r3, r3, r3 << 16
loop *6 (
ld *1, *0++
ldr *3, *0++
subb r3, r2, r3
sellx r2, r2, r3
st *3, *5++
nop
)
ret
}
function mul1_exp[23] {
ld *1, *1
mov r2, r31
loop *6 (
ldr *2++, *3
)
ldrfp r1
movi r2.0l, #1
loop *6 (
lddmp r0
call &mma
mov r2, r31
)
ldrfp r1
lddmp r0
subx r2, r2, r2
loop *6 (
ld *1, *0++
ldr *3, *0++
cmpbx r3, r2
)
ldrfp r1
lddmp r0
call &mm1_sub_cx
ldrfp r1
lddmp r0
ret
}
function mul1[4] {
ldi r0, [#0]
call &setupPtrs
call &mul1_exp
ret
}
function sqrx_exp[19] {
ldi r0, [#1]
lddmp r0
ld *1, *1
mov r2, r31
loop *6 (
ldr *2++, *3
)
ldrfp r1
loop *6 (
ld *3, *4++
stdmp r0
call &mma
lddmp r0
)
ldrfp r1
lddmp r0
loop *6 (
st *0++, *5++
)
ldrfp r1
lddmp r0
ret
}
function mulx_exp[14] {
ldi r0, [#2]
lddmp r0
ld *1, *1
mov r2, r31
loop *6 (
ldr *2++, *3
)
ldrfp r1
loop *6 (
ld *3, *4++
stdmp r0
call &mma
lddmp r0
)
ldrfp r1
ret
}
function selOutOrC[30] {
strnd r3
or r3, r3, r3
bl selOutOrC_invsel
addc r3, r3, r3 << 16
loop *6 (
strnd r3
strnd r2
ld *1, *5
st *3, *5
ldr *3, *0++
strnd r0
mov r0, r2
strnd r2
sell r2, r0, r3
st *3, *5++
)
ret
nop
selOutOrC_invsel:
addc r3, r3, r3 << 16
loop *6 (
strnd r3
strnd r2
ld *1, *5
st *3, *5
ldr *3, *0++
strnd r0
mov r0, r2
strnd r2
sell r2, r3, r0
st *3, *5++
)
ret
}
function modexp[35] {
call &mulx
ldi r0, [#3]
lddmp r0
sub r2, r2, r2
loop *6 (
nop
ld *3, *0++
subb r2, r31, r2
st *3, *5++
)
nop
mov r2, r31
movi r2.0l, #65535
and r3, r2, r0 >> 192
not r2, r2
and r2, r2, r0
add r2, r2, r3 << 8
ldlc r2
loop *0 (
call &sqrx_exp
call &mulx_exp
ldi r0, [#3]
lddmp r0
strnd r2
add r2, r2, r2
loop *6 (
strnd r2
ld *3, *4
addc r2, r2, r2
st *3, *4++
)
call &selOutOrC
nop
)
ldi r0, [#3]
lddmp r0
call &mul1_exp
ret
}
function modexp_blinded[76] {
call &mulx
ldi r0, [#3]
lddmp r0
sub r2, r2, r2
loop *6 (
nop
ld *3, *0++
subb r2, r31, r2
st *3, *5++
)
nop
ld *3, *1++
ld *3, *1
addx r7, r31, r2 >> 128
mul128 r3, r2l, r2u
mov r6, r31
loop *6 (
strnd r2
ld *3, *4
mul128 r4, r2l, r3l
mul128 r5, r2u, r3u
mul128 r0, r2u, r3l
add r4, r4, r0 << 128
addc r5, r5, r0 >> 128
mul128 r0, r2l, r3u
add r4, r4, r0 << 128
addc r5, r5, r0 >> 128
add r4, r4, r6
addc r5, r5, r31
add r2, r2, r4
addc r6, r5, r31
subbx r2, r2, r7
st *3, *4++
sub r7, r7, r7
)
mov r2, r6
subbx r2, r2, r7
st *3, *4
nop
ldi r0, [#3]
mov r2, r31
movi r2.0l, #65535
and r3, r2, r0 >> 192
not r2, r2
and r2, r2, r0
addi r3, r3, #1
add r2, r2, r3 << 8
ldlc r2
loop *0 (
call &sqrx_exp
call &mulx_exp
ldi r0, [#3]
lddmp r0
strnd r2
sub r2, r2, r2
loop *6 (
strnd r2
ld *3, *4
addc r2, r2, r2
st *3, *4++
)
strnd r2
ld *3, *4
addc r2, r2, r2
st *3, *4++
loop *6 (
strnd r2
ld *1, *5
st *3, *5
ldr *3, *0++
mov r0, r2
strnd r2
selc r2, r0, r3
st *3, *5++
)
nop
)
ldi r0, [#3]
lddmp r0
call &mul1_exp
ret
}
function modload[12] {
xor r31, r31, r31
ldi r0, [#0]
lddmp r0
ldlc r0
movi r0.0l, #28
movi r0.1l, #29
ldrfp r0
ld *0, *0
call &d0inv
st *1, *1
call &computeRR
ret
}
function selA0orC4[16] {
strnd r0
or r0, r0, r0
bl selA0orC4_invsel
addc r1, r0, r0 << 16
sell r22, r26, r6
sell r23, r27, r7
sell r24, r28, r8
sell r25, r29, r9
ret
nop
selA0orC4_invsel:
addc r1, r0, r0 << 16
sell r22, r6, r26
sell r23, r7, r27
sell r24, r8, r28
sell r25, r9, r29
ret
}
function mul4[169] {
mul128 r22, r6l, r10l
mul128 r23, r6u, r10u
mul128 r2, r6u, r10l
add r22, r22, r2 << 128
addc r23, r23, r2 >> 128
mul128 r2, r6l, r10u
add r22, r22, r2 << 128
addc r23, r23, r2 >> 128
mul128 r24, r7l, r11l
mul128 r25, r7u, r11u
mul128 r2, r7u, r11l
add r24, r24, r2 << 128
addc r25, r25, r2 >> 128
mul128 r2, r7l, r11u
add r24, r24, r2 << 128
addc r25, r25, r2 >> 128
mul128 r26, r8l, r12l
mul128 r27, r8u, r12u
mul128 r2, r8u, r12l
add r26, r26, r2 << 128
addc r27, r27, r2 >> 128
mul128 r2, r8l, r12u
add r26, r26, r2 << 128
addc r27, r27, r2 >> 128
mul128 r28, r9l, r13l
mul128 r29, r9u, r13u
mul128 r2, r9u, r13l
add r28, r28, r2 << 128
addc r29, r29, r2 >> 128
mul128 r2, r9l, r13u
add r28, r28, r2 << 128
addc r29, r29, r2 >> 128
mul128 r0, r6l, r11l
mul128 r1, r6u, r11u
mul128 r2, r6u, r11l
add r0, r0, r2 << 128
addc r1, r1, r2 >> 128
mul128 r2, r6l, r11u
add r0, r0, r2 << 128
addc r1, r1, r2 >> 128
add r23, r23, r0
addc r24, r24, r1
addc r3, r31, r31
mul128 r0, r7l, r10l
mul128 r1, r7u, r10u
mul128 r2, r7u, r10l
add r0, r0, r2 << 128
addc r1, r1, r2 >> 128
mul128 r2, r7l, r10u
add r0, r0, r2 << 128
addc r1, r1, r2 >> 128
add r23, r23, r0
addc r24, r24, r1
addc r25, r25, r3
addc r3, r31, r31
mul128 r0, r6l, r12l
mul128 r1, r6u, r12u
mul128 r2, r6u, r12l
add r0, r0, r2 << 128
addc r1, r1, r2 >> 128
mul128 r2, r6l, r12u
add r0, r0, r2 << 128
addc r1, r1, r2 >> 128
add r24, r24, r0
addc r25, r25, r1
addc r3, r3, r31
mul128 r0, r8l, r10l
mul128 r1, r8u, r10u
mul128 r2, r8u, r10l
add r0, r0, r2 << 128
addc r1, r1, r2 >> 128
mul128 r2, r8l, r10u
add r0, r0, r2 << 128
addc r1, r1, r2 >> 128
add r24, r24, r0
addc r25, r25, r1
addc r26, r26, r3
addc r3, r31, r31
mul128 r0, r6l, r13l
mul128 r1, r6u, r13u
mul128 r2, r6u, r13l
add r0, r0, r2 << 128
addc r1, r1, r2 >> 128
mul128 r2, r6l, r13u
add r0, r0, r2 << 128
addc r1, r1, r2 >> 128
add r25, r25, r0
addc r26, r26, r1
addc r3, r3, r31
mul128 r0, r7l, r12l
mul128 r1, r7u, r12u
mul128 r2, r7u, r12l
add r0, r0, r2 << 128
addc r1, r1, r2 >> 128
mul128 r2, r7l, r12u
add r0, r0, r2 << 128
addc r1, r1, r2 >> 128
add r25, r25, r0
addc r26, r26, r1
addc r3, r3, r31
mul128 r0, r9l, r10l
mul128 r1, r9u, r10u
mul128 r2, r9u, r10l
add r0, r0, r2 << 128
addc r1, r1, r2 >> 128
mul128 r2, r9l, r10u
add r0, r0, r2 << 128
addc r1, r1, r2 >> 128
add r25, r25, r0
addc r26, r26, r1
addc r3, r3, r31
mul128 r0, r8l, r11l
mul128 r1, r8u, r11u
mul128 r2, r8u, r11l
add r0, r0, r2 << 128
addc r1, r1, r2 >> 128
mul128 r2, r8l, r11u
add r0, r0, r2 << 128
addc r1, r1, r2 >> 128
add r25, r25, r0
addc r26, r26, r1
addc r27, r27, r3
addc r3, r31, r31
mul128 r0, r7l, r13l
mul128 r1, r7u, r13u
mul128 r2, r7u, r13l
add r0, r0, r2 << 128
addc r1, r1, r2 >> 128
mul128 r2, r7l, r13u
add r0, r0, r2 << 128
addc r1, r1, r2 >> 128
add r26, r26, r0
addc r27, r27, r1
addc r3, r3, r31
mul128 r0, r9l, r11l
mul128 r1, r9u, r11u
mul128 r2, r9u, r11l
add r0, r0, r2 << 128
addc r1, r1, r2 >> 128
mul128 r2, r9l, r11u
add r0, r0, r2 << 128
addc r1, r1, r2 >> 128
add r26, r26, r0
addc r27, r27, r1
addc r28, r28, r3
addc r29, r29, r31
mul128 r0, r8l, r13l
mul128 r1, r8u, r13u
mul128 r2, r8u, r13l
add r0, r0, r2 << 128
addc r1, r1, r2 >> 128
mul128 r2, r8l, r13u
add r0, r0, r2 << 128
addc r1, r1, r2 >> 128
add r27, r27, r0
addc r28, r28, r1
addc r29, r29, r31
mul128 r0, r9l, r12l
mul128 r1, r9u, r12u
mul128 r2, r9u, r12l
add r0, r0, r2 << 128
addc r1, r1, r2 >> 128
mul128 r2, r9l, r12u
add r0, r0, r2 << 128
addc r1, r1, r2 >> 128
add r27, r27, r0
addc r28, r28, r1
addc r29, r29, r31
ret
}
function sqr4[117] {
mul128 r22, r6l, r6l
mul128 r23, r6u, r6u
mul128 r2, r6u, r6l
add r22, r22, r2 << 128
addc r23, r23, r2 >> 128
add r22, r22, r2 << 128
addc r23, r23, r2 >> 128
mul128 r24, r7l, r7l
mul128 r25, r7u, r7u
mul128 r2, r7u, r7l
add r24, r24, r2 << 128
addc r25, r25, r2 >> 128
add r24, r24, r2 << 128
addc r25, r25, r2 >> 128
mul128 r26, r8l, r8l
mul128 r27, r8u, r8u
mul128 r2, r8u, r8l
add r26, r26, r2 << 128
addc r27, r27, r2 >> 128
add r26, r26, r2 << 128
addc r27, r27, r2 >> 128
mul128 r28, r9l, r9l
mul128 r29, r9u, r9u
mul128 r2, r9u, r9l
add r28, r28, r2 << 128
addc r29, r29, r2 >> 128
add r28, r28, r2 << 128
addc r29, r29, r2 >> 128
mul128 r0, r6l, r7l
mul128 r1, r6u, r7u
mul128 r2, r6u, r7l
add r0, r0, r2 << 128
addc r1, r1, r2 >> 128
mul128 r2, r6l, r7u
add r0, r0, r2 << 128
addc r1, r1, r2 >> 128
add r23, r23, r0
addc r24, r24, r1
addc r3, r31, r31
add r23, r23, r0
addc r24, r24, r1
addc r25, r25, r3
addc r3, r31, r31
mul128 r0, r6l, r8l
mul128 r1, r6u, r8u
mul128 r2, r6u, r8l
add r0, r0, r2 << 128
addc r1, r1, r2 >> 128
mul128 r2, r6l, r8u
add r0, r0, r2 << 128
addc r1, r1, r2 >> 128
add r24, r24, r0
addc r25, r25, r1
addc r3, r3, r31
add r24, r24, r0
addc r25, r25, r1
addc r26, r26, r3
addc r3, r31, r31
mul128 r0, r6l, r9l
mul128 r1, r6u, r9u
mul128 r2, r6u, r9l
add r0, r0, r2 << 128
addc r1, r1, r2 >> 128
mul128 r2, r6l, r9u
add r0, r0, r2 << 128
addc r1, r1, r2 >> 128
add r25, r25, r0
addc r26, r26, r1
addc r3, r3, r31
add r25, r25, r0
addc r26, r26, r1
addc r3, r3, r31
mul128 r0, r7l, r8l
mul128 r1, r7u, r8u
mul128 r2, r7u, r8l
add r0, r0, r2 << 128
addc r1, r1, r2 >> 128
mul128 r2, r7l, r8u
add r0, r0, r2 << 128
addc r1, r1, r2 >> 128
add r25, r25, r0
addc r26, r26, r1
addc r3, r3, r31
add r25, r25, r0
addc r26, r26, r1
addc r27, r27, r3
addc r3, r31, r31
mul128 r0, r7l, r9l
mul128 r1, r7u, r9u
mul128 r2, r7u, r9l
add r0, r0, r2 << 128
addc r1, r1, r2 >> 128
mul128 r2, r7l, r9u
add r0, r0, r2 << 128
addc r1, r1, r2 >> 128
add r26, r26, r0
addc r27, r27, r1
addc r3, r3, r31
add r26, r26, r0
addc r27, r27, r1
addc r28, r28, r3
addc r29, r29, r31
mul128 r0, r8l, r9l
mul128 r1, r8u, r9u
mul128 r2, r8u, r9l
add r0, r0, r2 << 128
addc r1, r1, r2 >> 128
mul128 r2, r8l, r9u
add r0, r0, r2 << 128
addc r1, r1, r2 >> 128
add r27, r27, r0
addc r28, r28, r1
addc r29, r29, r31
add r27, r27, r0
addc r28, r28, r1
addc r29, r29, r31
ret
}
function dod0[15] {
ld *3, *1
mul128 r5, r1l, r0l
mul128 r2, r1u, r0l
add r5, r5, r2 << 128
mul128 r2, r1l, r0u
add r5, r5, r2 << 128
mul128 r0, r5l, r14l
mul128 r1, r5u, r14u
mul128 r2, r5u, r14l
add r0, r0, r2 << 128
addc r1, r1, r2 >> 128
mul128 r2, r5l, r14u
add r0, r0, r2 << 128
addc r1, r1, r2 >> 128
ret
}
function dod1[9] {
mul128 r0, r5l, r15l
mul128 r1, r5u, r15u
mul128 r2, r5u, r15l
add r0, r0, r2 << 128
addc r1, r1, r2 >> 128
mul128 r2, r5l, r15u
add r0, r0, r2 << 128
addc r1, r1, r2 >> 128
ret
}
function dod2[9] {
mul128 r0, r5l, r16l
mul128 r1, r5u, r16u
mul128 r2, r5u, r16l
add r0, r0, r2 << 128
addc r1, r1, r2 >> 128
mul128 r2, r5l, r16u
add r0, r0, r2 << 128
addc r1, r1, r2 >> 128
ret
}
function dod3[9] {
mul128 r0, r5l, r17l
mul128 r1, r5u, r17u
mul128 r2, r5u, r17l
add r0, r0, r2 << 128
addc r1, r1, r2 >> 128
mul128 r2, r5l, r17u
add r0, r0, r2 << 128
addc r1, r1, r2 >> 128
ret
}
function redc4[97] {
mov r0, r22
call &dod0
add r22, r22, r0
addc r23, r23, r1
addc r24, r24, r31
addc r4, r31, r31
call &dod1
add r23, r23, r0
addc r24, r24, r1
addc r25, r25, r4
addc r4, r31, r31
call &dod2
add r24, r24, r0
addc r25, r25, r1
addc r26, r26, r4
addc r4, r31, r31
call &dod3
add r25, r25, r0
addc r26, r26, r1
addc r27, r27, r4
addc r3, r31, r31
mov r0, r23
call &dod0
add r23, r23, r0
addc r24, r24, r1
addc r25, r25, r31
addc r4, r31, r31
call &dod1
add r24, r24, r0
addc r25, r25, r1
addc r26, r26, r4
addc r4, r31, r31
call &dod2
add r25, r25, r0
addc r26, r26, r1
addc r27, r27, r4
addc r3, r31, r31
call &dod3
add r26, r26, r0
addc r27, r27, r1
addc r28, r28, r3
addc r3, r31, r31
mov r0, r24
call &dod0
add r24, r24, r0
addc r25, r25, r1
addc r26, r26, r31
addc r4, r31, r31
call &dod1
add r25, r25, r0
addc r26, r26, r1
addc r27, r27, r4
addc r4, r31, r31
call &dod2
add r26, r26, r0
addc r27, r27, r1
addc r28, r28, r4
addc r4, r3, r31
call &dod3
add r27, r27, r0
addc r28, r28, r1
addc r29, r29, r4
addc r3, r31, r31
mov r0, r25
call &dod0
add r25, r25, r0
addc r22, r26, r1
addc r23, r27, r31
addc r4, r31, r31
call &dod1
add r22, r22, r0
addc r23, r23, r1
addc r24, r28, r4
addc r4, r31, r31
call &dod2
add r23, r23, r0
addc r24, r24, r1
addc r25, r29, r4
addc r3, r3, r31
call &dod3
add r24, r24, r0
addc r25, r25, r1
addc r3, r3, r31
subx r0, r31, r3
strnd r26
strnd r27
strnd r28
strnd r29
sub r2, r22, r14
subb r26, r23, r15
subb r27, r24, r16
subb r28, r25, r17
selcx r29, r28, r25
selcx r28, r27, r24
selcx r27, r26, r23
selcx r26, r2, r22
ret
}
function modexp_1024[101] {
mov r2, r31
movi r2.0l, #6
movi r2.1l, #10
movi r2.3l, #1
movi r2.4l, #14
movi r2.5l, #22
movi r2.6l, #18
ldrfp r2
mov r0, r31
movi r0.3l, #65535
ldi r1, [#0]
and r1, r1, r0
not r0, r0
ldi r2, [#3]
and r2, r2, r0
or r2, r2, r1
lddmp r2
loop #4 (
ld *0++, *3++
ld *1++, *2++
ld *4++, *0++
ld *6++, *4++
)
strnd r30
add r30, r30, r30
call &mul4
call &redc4
mov r10, r26
mov r11, r27
mov r12, r28
mov r13, r29
strnd r6
strnd r7
strnd r8
strnd r9
loop #1024 (
call &sqr4
call &redc4
strnd r6
strnd r7
strnd r8
strnd r9
mov r6, r26
mov r7, r27
mov r8, r28
mov r9, r29
call &mul4
call &redc4
strnd r0
add r0, r21, r21
strnd r0
addc r0, r18, r18
strnd r18
mov r18, r0
strnd r0
addc r0, r19, r19
strnd r19
mov r19, r0
strnd r0
addc r0, r20, r20
strnd r20
mov r20, r0
strnd r0
addc r0, r21, r21
strnd r21
mov r21, r0
strnd r22
strnd r23
strnd r24
strnd r25
call &selA0orC4
strnd r6
strnd r7
strnd r8
strnd r9
strnd r0
add r0, r0, r0
xor r0, r30, r0
strnd r30
add r30, r30, r30
xor r30, r30, r0
or r30, r30, r18
xor r0, r0, r30
sell r6, r10, r22
sell r7, r11, r23
sell r8, r12, r24
sell r9, r13, r25
)
mov r10, r31
movi r10.0l, #1
mov r11, r31
mov r12, r31
mov r13, r31
call &mul4
call &redc4
sub r6, r26, r14
subb r7, r27, r15
subb r8, r28, r16
subb r9, r29, r17
call &selA0orC4
loop #4 (
st *5++, *5++
)
ret
}

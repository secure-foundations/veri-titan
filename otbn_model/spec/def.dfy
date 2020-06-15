// Trusted specification for the OpenTitan Bignum semantics

module bignum_def {

// General purpose and control registers, 32b
datatype BNX =
| X0 | X1 | X2 | X3 | X4 | X5 | X6 | X7 | X8
| X9 | X10 | X11 | X12 | X13 | X14 | X15 | X16
| X17 | X18 | X19 | X20 | X21 | X22 | X23 | X24
| X25 | X26 | X27 | X28 | X29 | X30 | X31
| XMod(mod:int) // 0 through 7
| XRnd // Random number

// Wide data and special registers, 256b
datatype BNw =
| WDR(w:int)
| WMod // Wide modulo register
| WRnd // Wide random number

datatype operand = OXimm(n:uint32) | OBnx(x:BNx) | OBnw(w:BNw) | OStack(s:uint32)

datatype xins =
| ADD(xrd:operand, xrs1:operand, xrs2:operand)
| ADDI(xrd:operand, xrs1:operand, ximm:operand)
| LUI(xrd:operand, ximm:operand)
| SUB(xrd:operand, xrs1:operand, xrs2:operand)
| AND(xrd:operand, xrs1:operand, xrs2:operand)
| ANDI(xrd:operand, xrs1:operand, ximm:operand)
| OR(xrd:operand, xrs1:operand, xrs2:operand)
| ORI(xrd:operand, xrs1:operand, ximm:operand)
| XOR(xrd:operand, xrs1:operand, xrs2:operand)
| XORI(xrd:operand, xrs1:operand, ximm:operand)
| LW // TODO
| SW // TODO
| BEQ(xrs1:operand, xrs2:operand, offset:operand)
| BNE(xrs1:operand, xrs2:operand, offset:operand)
| LOOP(xrs1:operand, bodysize:operand)
| LOOPI(iterations:operand, bodysize:operand)
| JAL(xrd:operand, offset:operand)
| JALR(xrd:operand, xrs1:operand, offset:operand)
| CSRRS(xrd:operand, csr:operand, xrs2:operand)
| ECALL // TODO

datatype wins =
| ADD(wrd:operand, wrs1:operand, wrs2:operand, shift_type:bool, shift_bytes:operand, flg:bool)
| ADDC(wrd:operand, wrs1:operand, wrs2:operand, shift_type:bool, shift_bytes:operand, flg:bool)
| ADDI(wrd:operand, wrs1:operand, wimm:operand, flg:bool)
| ADDM(wrd:operand, wrs1:operand, wrs2:operand)
| MULQACC
| MULH(wrd:operand, wrs1:operand, hw1:bool, wrs2:operand, hw2:bool)
| SUB(wrd:operand, wrs1:operand, wrs2:operand, shift_type:bool, shift_bytes:operand, flg:bool)
| SUBB(wrd:operand, wrs1:operand, wrs2:operand, shift_type:bool, shift_bytes:operand, flg:bool)
| SUBI(wrd:operand, wrs1:operand, wimm:operand, flg:bool)
| SUBM(wrd:operand, wrs1:operand, wrs2:operand)
| AND(wrd:operand, wrs1:operand, wrs2:operand, shift_type:bool, shift_bytes:operand)
| OR(wrd:operand, wrs1:operand, wrs2:operand, shift_type:bool, shift_bytes:operand)
| NOT(wrd:operand, wrs1:operand, wrs2:operand, shift_type:bool, shift_bytes:operand)
| XOR(wrd:operand, wrs1:operand, wrs2:operand, shift_type:bool, shift_bytes:operand, flg:bool)
| RSHI(wrd:operand, wrs1:operand, wrs2:operand, wimm:operand)
| SEL(wrd:operand, wrs1:operand, wrs2:operand, flg:bool)
| CMP(wrs1:operand, wrs2:operand, flg:bool)
| CMPB(wrs1:operand, wrs2:operand, flg:bool)
| LID // TODO
| SID // TODO
| MOV(wrd:operand, wrs:operand)
| MOVR // TODO
| WSRRS // TODO
| WSRRW // TODO

datatype codes = CNil | va_CCons(hd:code, tl:codes)

datatype code =
| XIns(xins:xins)
| WIns(wins:wins)
| Block(block:codes)

type Frame = map<int, uint32>
type Stack = seq<Frame>

datatype state = state(
	 xregs: map<BNx, uint32>
	 wregs: map<BNw, octuple>,
	 flags: map<int, bool>,
	 ok: bool)

}


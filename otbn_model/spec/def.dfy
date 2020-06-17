// Trusted specification for the OpenTitan Bignum semantics

datatype Bignum = Bignum(l7:uint32, l6:uint32, l5:uint32, l4:uint32, l3:uint32, l2:uint32, l1:uint32, l0:uint32)

module bignum_def {

// General purpose and control registers, 32b
datatype Reg32 =
| Gpr(x:int)
| Rnd // Random number

// Wide data and special registers, 256b
datatype Reg256 =
| Wdr(w:int)
| WMod // Wide modulo register
| WRnd // Wide random number

datatype ins32 =
| ADD(xrd:Reg32, xrs1:Reg32, xrs2:Reg32)
| ADDI(xrd:Reg32, xrs1:Reg32, imm:uint32)
| LUI(xrd:Reg32, imm:uint32)
| SUB(xrd:Reg32, xrs1:Reg32, xrs2:Reg32)
| AND(xrd:Reg32, xrs1:Reg32, xrs2:Reg32)
| ANDI(xrd:Reg32, xrs1:Reg32, imm:uint32)
| OR(xrd:Reg32, xrs1:Reg32, xrs2:Reg32)
| ORI(xrd:Reg32, xrs1:Reg32, imm:uint32)
| XOR(xrd:Reg32, xrs1:Reg32, xrs2:Reg32)
| XORI(xrd:Reg32, xrs1:Reg32, imm:uint32)
| LW // TODO
| SW // TODO
| BEQ(xrs1:Reg32, xrs2:Reg32, offset:uint32)
| BNE(xrs1:Reg32, xrs2:Reg32, offset:uint32)
| LOOP(xrs1:Reg32, bodysize:uint32)
| LOOPI(iterations:uint32, bodysize:uint32)
| JAL(xrd:Reg32, offset:uint32)
| JALR(xrd:Reg32, xrs1:Reg32, offset:uint32)
| CSRRS(xrd:Reg32, csr:uint32, xrs2:Reg32)
| ECALL // TODO

datatype ins256 =
| ADD(wrd:Reg256, wrs1:Reg256, wrs2:Reg256, shift_type:bool, shift_bytes:uint256, flg:bool)
| ADDC(wrd:Reg256, wrs1:Reg256, wrs2:Reg256, shift_type:bool, shift_bytes:uint256, flg:bool)
| ADDI(wrd:Reg256, wrs1:Reg256, imm:uint256, flg:bool)
| ADDM(wrd:Reg256, wrs1:Reg256, wrs2:Reg256)
| MULQACC
| MULH(wrd:Reg256, wrs1:Reg256, hw1:bool, wrs2:Reg256, hw2:bool)
| SUB(wrd:Reg256, wrs1:Reg256, wrs2:Reg256, shift_type:bool, shift_bytes:uint256, flg:bool)
| SUBB(wrd:Reg256, wrs1:Reg256, wrs2:Reg256, shift_type:bool, shift_bytes:uint256, flg:bool)
| SUBI(wrd:Reg256, wrs1:Reg256, imm:uint256, flg:bool)
| SUBM(wrd:Reg256, wrs1:Reg256, wrs2:Reg256)
| AND(wrd:Reg256, wrs1:Reg256, wrs2:Reg256, shift_type:bool, shift_bytes:uint256)
| OR(wrd:Reg256, wrs1:Reg256, wrs2:Reg256, shift_type:bool, shift_bytes:uint256)
| NOT(wrd:Reg256, wrs1:Reg256, wrs2:Reg256, shift_type:bool, shift_bytes:uint256)
| XOR(wrd:Reg256, wrs1:Reg256, wrs2:Reg256, shift_type:bool, shift_bytes:uint256, flg:bool)
| RSHI(wrd:Reg256, wrs1:Reg256, wrs2:Reg256, imm:uint256)
| SEL(wrd:Reg256, wrs1:Reg256, wrs2:Reg256, flg:bool)
| CMP(wrs1:Reg256, wrs2:Reg256, flg:bool)
| CMPB(wrs1:Reg256, wrs2:Reg256, flg:bool)
| LID // TODO
| SID // TODO
| MOV(wrd:Reg256, wrs:uint256)
| MOVR // TODO
| WSRRS // TODO
| WSRRW // TODO

datatype codes = CNil | va_CCons(hd:code, tl:codes)

datatype code =
| Ins32(ins:ins32)
| Ins256(ins:ins256)
| Block(block:codes)

type Frame = map<int, uint32>
type Stack = seq<Frame>

datatype state = state(
	 xregs: map<Reg32, uint32>
	 wregs: map<Reg256, Bignum>,
	 flags: map<int, bool>,
	 ok: bool)

}


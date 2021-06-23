include "../gen/examples.dfy"
include "../gen/mont_loop.dfy"
include "../gen/modexp_var.dfy"
include "bv_ops.dfy"
include "vt_ops.dfy"
include "../code/vale.dfy"

module otbn_printer {

  import opened bv_ops
	import opened vt_ops
  import opened examples
  import opened mont_loop
  import opened modexp_var


method printReg32(r:reg32_t)
{
  match r
		    case GPR(x) => print("x"); print(x);
				// case RND => print("ERROR: rnd"); // TODO: Are we no longer modeling RND?
}

 method printReg256(r:reg256_t)
 {
   match r
 		    case WDR(w) => print("w"); print(w);
			  case _ => print("TODO");
 }

method printIns32(ins:ins32)
{
    match ins
      case LW(grd, grs1, offset) =>
        print ("  lw ");
        printReg32(grd); print(", "); print(offset); print("("); printReg32(grs1); print(")");
        print("\n");

      case SW(grs2, grs1, offset) =>
        print ("  sw ");
        printReg32(grs2); print(", "); print(offset); print("("); printReg32(grs1); print(")");
        print("\n");

      case ADD(dst, src1, src2) =>
        print ("  add ");
        printReg32(dst); print(", "); printReg32(src1); print(", "); printReg32(src2);
        print("\n");

      case ADDI(dst, src1, src2) =>
        print ("  addi ");
        printReg32(dst); print(", "); printReg32(src1); print(", "); print(src2);
        print("\n");

      case SUB(dst, src1, src2) =>
        print ("  sub ");
        printReg32(dst); print(", "); printReg32(src1); print(", "); printReg32(src2);
        print("\n");

      case AND(dst, src1, src2) =>
        print ("  and ");
        printReg32(dst); print(", "); printReg32(src1); print(", "); printReg32(src2);
        print("\n");

      case ANDI(dst, src1, src2) =>
        print ("  andi ");
        printReg32(dst); print(", "); printReg32(src1); print(", "); print(src2);
        print("\n");

      case OR(dst, src1, src2) =>
        print ("  or ");
        printReg32(dst); print(", "); printReg32(src1); print(", "); printReg32(src2);
        print("\n");

      case ORI(dst, src1, src2) =>
        print ("  ori ");
        printReg32(dst); print(", "); printReg32(src1); print(", "); print(src2);
        print("\n");

      case XOR(dst, src1, src2) =>
        print ("  xor ");
        printReg32(dst); print(", "); printReg32(src1); print(", "); printReg32(src2);
        print("\n");

      case XORI(dst, src1, src2) =>
        print ("  xori ");
        printReg32(dst); print(", "); printReg32(src1); print(", "); print(src2);
        print("\n");

      case LUI(dst, src) =>
        print ("  lui ");
        printReg32(dst); print(", "); print(src);
        print("\n");

      // TODO: this is case-by-case combo of addi and lui, should we print that instead?
      case LI(dst, src) =>
        print ("  li ");
        printReg32(dst); print(", "); print(src);
        print("\n");

			case _ => print("TODO32 "); print(ins);
}

method printShift(shift:shift_t)
{
	match shift
    case SFT(left, bytes) =>
      match left
		    case true => print("<< "); print(bytes);
		    case false => print(">> "); print(bytes);
}

method printFlags(fg:uint1)
{
  match fg
		case 0 => print("0");
		case 1 => print("1");
}

method printFlag(flag:uint2)
{
  match flag
		case 0 => print("C");
		case 1 => print("M");
		case 2 => print("L");
		case 3 => print("Z");
	  case _ => print("ERROR: Invalid flag.");
}

method printAccShift(shift:int)
{
	match shift
		case 0 => print("0");
		case 1 => print("64");
		case 2 => print("128");
		case 3 => print("192");
		case _ => print("ERROR");
}

method printIns256(ins:ins256)
{
    match ins

      case BN_XOR(dst, src1, src2, shift) =>
				print("  bn.xor ");
				printReg256(dst); print(", "); printReg256(src1); print(", "); printReg256(src2); print(" ");
				printShift(shift);
				print("\n");

      case BN_ADD(dst, src1, src2, shift, fg) =>
				print("  bn.add ");
				printReg256(dst); print(", "); printReg256(src1); print(", "); printReg256(src2); print(" ");
				printShift(shift); print(", "); printFlags(fg);
				print("\n");

      case BN_ADDC(dst, src1, src2, shift, fg) =>
				print("  bn.addc ");
				printReg256(dst); print(", "); printReg256(src1); print(", "); printReg256(src2); print(" ");
				printShift(shift); print(", "); printFlags(fg);
				print("\n");

      case BN_ADDI(dst, src, imm, fg) =>
				print("  bn.addi ");
				printReg256(dst); print(", "); printReg256(src); print(", "); print(imm);
				print(", "); printFlags(fg); print("\n");

		  case BN_MULQACC(zero, src1, qwsel1, src2, qwsel2, shift) =>
				if zero { print("  bn.mulqacc.z "); } else { print("  bn.mulqacc "); }
				printReg256(src1); print("."); print(qwsel1); print(", ");
				printReg256(src2); print("."); print(qwsel2); print(", ");
				printAccShift(shift); print("\n");

		  case BN_MULQACC_SO(zero, src1, qwsel1, src2, qwsel2, shift) =>
				if zero { print("  bn.mulqacc.so.z "); } else { print("  bn.mulqacc.so "); }
				printReg256(src1); print("."); print(qwsel1); print(", ");
				printReg256(src2); print("."); print(qwsel2); print(", ");
				printAccShift(shift); print("\n");

      // todo
			case BN_SUBI(dst, src1, src2, fg) =>
				print("  bn.subi ");
				printReg256(dst); print(", "); printReg256(src1); print(", "); print(src2); print(", ");
				printFlags(fg); print("\n");

			case BN_SUBB(dst, src1, src2, shift, fg) =>
				print("  bn.subb ");
				printReg256(dst); print(", "); printReg256(src1); print(", "); printReg256(src2); print(" ");
				printShift(shift); print(", "); printFlags(fg);
				print("\n");

			case BN_SUB(dst, src1, src2, shift, fg) =>
				print("  bn.sub ");
				printReg256(dst); print(", "); printReg256(src1); print(", "); printReg256(src2); print(" ");
				printShift(shift); print(", "); printFlags(fg);
				print("\n");

      // TODO: fix otbn_subm in vt_ops file
			case BN_SUBM(dst, src1, src2) =>
				print("  bn.subm ");
				printReg256(dst); print(", "); printReg256(src1); print(", "); printReg256(src2);
				print("\n");

			case BN_OR(dst, src1, src2, shift) =>
				print("  bn.or ");
				printReg256(dst); print(", "); printReg256(src1); print(", "); printReg256(src2); print(" ");
				printShift(shift);
				print("\n");

			case BN_AND(dst, src1, src2, shift) =>
				print("  bn.and ");
				printReg256(dst); print(", "); printReg256(src1); print(", "); printReg256(src2); print(" ");
				printShift(shift); print(" "); print("\n");

			case BN_LID(grd, grd_inc, offset, grs, grs_inc) =>
				print("  bn.lid ");
				printReg32(grd); if grd_inc { print("++"); } print(", ");
        print(offset); print("(");
        printReg32(grs); if grs_inc { print("++"); }
        print(")"); print("\n");

			case BN_RSHI(dst, src1, src2, imm) =>
				print("  bn.rshi ");
				printReg256(dst); print(", "); printReg256(src1); print(", ");
        printReg256(src2); print(" >> "); print(imm);
				print("\n");

			case BN_SEL(dst, src1, src2, fg, flag) =>
				print("  bn.sel ");
				printReg256(dst); print(", "); printReg256(src1); print(", "); printReg256(src2); print(", ");
				printFlags(fg); print("."); printFlag(flag); print("\n");

			case BN_SID(grs2, grs2_inc, offset, grs1, grs1_inc) =>
				print("  bn.sid ");
				printReg32(grs2); if grs2_inc { print("++"); } print(", ");
        print(offset); print("(");
        printReg32(grs1); if grs1_inc { print("++"); }
        print(")"); print("\n");

			case BN_MOV(dst, src) =>
				print("  bn.mov ");
				printReg256(dst); print(", "); printReg256(src); print("\n");

      case BN_MOVR(grd, grd_inc, grs, grs_inc) =>
        print("  bn.movr ");
				printReg32(grd); if grd_inc { print("++"); } print(", ");
        printReg32(grs); if grs_inc { print("++"); }
        print("\n");

			case _ => print("TODO256 "); print(ins);
}

method printBlock(b:codes, n:int) returns(n':int)
{
    n' := n;
    var i := b;
    while (i.va_CCons?)
        decreases i
    {
        n' := printCode(i.hd, n');
        i := i.tl;
    }
}

method printWhileCond(wcond: whileCond)
{
  match wcond
    case RegCond(r) => print("  loop "); printReg32(r);
    case ImmCond(imm) => print("  loopi "); print(imm);
}

function method blockSize(b: codes) : int
{
  match b
    case CNil => 0
    case va_CCons(hd, tl) => codeSize(hd) + blockSize(tl)
}

function method codeSize(c: code) : int
{
  match c
    case Block(block) => blockSize(block)
    case While(wcond, wbody) => codeSize(wbody) + 2 // +1 for inner loop and +1 for inner loop's nop
    case Ins32(ins) => 1
    case Ins256(bn_ins) => 1
    case Comment(com) => 0
}

method printCode(c:code, n:int) returns(n':int)
{
    match c
        case Ins32(ins) => printIns32(ins); n' := n;
        case Ins256(ins) => printIns256(ins); n' := n;
        case Block(block) => n' := printBlock(block, n);
        case While(wcond, wbody) =>
        {
          n' := n;
          print("\n");
          printWhileCond(wcond); print(", ");
          print(codeSize(wbody) + 1); print("\n"); // + 1 for nop instruction
          n' := printCode(wbody, n);
          print("  nop\n"); // ensures different end addrs for nested loops
          print("\n");
        }
        case Comment(com) => print(com);
}

method printProc(proc_name:seq<char>, code:code, n:int, ret_count:int)
{
  print(proc_name);
  print(" proc\n");
  var _ := printCode(code, n);
  print("  ret ");
  print(ret_count);
  print("\n");
  print(proc_name);
  print(" end\n\n");
}

datatype AsmTarget = OTBN
datatype PlatformTarget = Linux | MacOS

function method procName(proc_name:seq<char>, suffix:seq<char>, asm:AsmTarget, platform:PlatformTarget):seq<char>
{
    match platform
        case Linux => proc_name
        case MacOS => "_" + proc_name
}

method PrintDemo(asm:AsmTarget, platform:PlatformTarget)
{
    printProc("demo", va_code_mont_loop(), 0, 0);
}

method Main()
{
    PrintDemo(OTBN, MacOS);
}

}

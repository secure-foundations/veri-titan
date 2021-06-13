include "../gen/examples.dfy"
include "bv_ops.dfy"
include "vt_ops.dfy"
include "../code/vale.dfy"

module otbn_printer {

  import opened bv_ops
	import opened vt_ops
  import opened examples
  
		
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
      case ADD(dst, src1, src2) => print ("  add "); printReg32(dst); print(", "); printReg32(src1); print(", "); printReg32(src2);
			case _ => print("TODO");
}

method printShift(shift:shift_t)
{
	match shift
    case SFT(left, bytes) =>
      match left
		    case true => print("<< ", bytes);
		    case false => print(">> ", bytes);
}

method printFlags(fg:uint1)
{
  match fg
		case 0 => print("0");
		case 1 => print("1");
}

method printFlag(flag:flags_t)
{
  match flag
		case zero => print("Z");
		case lsb => print("L");
		case msb => print("M");
		case cf => print("C");
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
				printShift(shift); print(" "); print(", "); printFlags(fg);
				print("\n");

      case BN_ADDC(dst, src1, src2, shift, fg) =>
				print("  bn.addc ");
				printReg256(dst); print(", "); printReg256(src1); print(", "); printReg256(src2); print(" "); 
				printShift(shift); print(" "); print(", "); printFlags(fg);
				print("\n");

      case BN_ADDI(dst, src, imm, fg) =>
				print("  bn.addi ");
				printReg256(dst); print(", "); printReg256(src); print(", "); print(imm);
				print(", "); printFlags(fg); print("\n");

      // todo
      // handles mulqacc, mulqacc_safe, mulqacc_so and mulqacc_z
		  case BN_MULQACC(zero, src1, qwsel1, src2, qwsel2, shift) =>
				if zero { print("  bn.mulqacc "); } else { print("  bn.mulquacc.z "); }
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
				printShift(shift); print(" "); print(", "); printFlags(fg);
				print("\n");

			case BN_SUB(dst, src1, src2, shift, fg) =>
				print("  bn.sub ");
				printReg256(dst); print(", "); printReg256(src1); print(", "); printReg256(src2); print(" "); 
				printShift(shift); print(" "); print(", "); printFlags(fg);
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

			case BN_MOV(dst, src) =>
				print("  bn.mov ");
				printReg256(dst); print(", "); printReg256(src); print("\n");
				
			case _ => print("TODO");
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

method printCode(c:code, n:int) returns(n':int)
{
    match c
        case Ins32(ins) => printIns32(ins); n' := n;
        case Ins256(ins) => printIns256(ins); n' := n;
        case Block(block) => n' := printBlock(block, n);
				case While(wcond, wbody) => print("TODO: While");
				
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

method PrintDemo(asm:AsmTarget,
                 platform:PlatformTarget)
{
    printProc("demo", va_code_barrett384(), 0, 0);
}

method Main()
{
    PrintDemo(OTBN, MacOS);
}

}

include "../gen/examples.dfy"
include "def.dfy"
include "types.dfy"

module bignum_print {

	import opened examples
	import opened bignum_def
		
method printReg32(r:Reg32)
{
  match r
		    case Gpr(x) => print("x"); print(x);
				case Rnd => print("ERROR: rnd");
}

 method printReg256(r:Reg256)
 {
   match r
 		    case Wdr(w) => print("w"); print(w);
			  case _ => print("TODO");
 }

method printIns32(ins:ins32)
{
    match ins
      case ADD32(dst, src1, src2) => print ("  add "); printReg32(dst); print(", "); printReg32(src1); print(", "); printReg32(src2);
			case _ => print("TODO");
}

method printShiftType(st:bool)
{
	match st
		case false => print("<<");
		case true => print(">>");
}

method printFlags(fg:bool)
{
  match fg
		case false => print("FG0");
		case true => print("FG1");
}

method printFlag(flag:int)
{
  match flag
		case 0 => print("Z");
		case 1 => print("L");
		case 2 => print("M");
		case 3 => print("C");
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
      case ADD256(dst, src1, src2, st, sb, fg) =>
				print("  bn.add ");
				printReg256(dst); print(", "); printReg256(src1); print(", "); printReg256(src2); print(" "); 
				printShiftType(st); print(" "); print(sb); print(", "); printFlags(fg);
				print("\n");

      case ADDC256(dst, src1, src2, st, sb, fg) =>
				print("  bn.addc ");
				printReg256(dst); print(", "); printReg256(src1); print(", "); printReg256(src2); print(" "); 
				printShiftType(st); print(" "); print(sb); print(", "); printFlags(fg);
				print("\n");

      case ADDI256(dst, src, imm, fg) =>
				print("  bn.addi ");
				printReg256(dst); print(", "); printReg256(src); print(", "); print(imm);
				print(", "); printFlags(fg); print("\n");

		  case MULQACC256(zero, src1, qwsel1, src2, qwsel2, shift) =>
				if zero { print("  bn.mulqacc "); } else { print("  bn.mulquacc.z "); }
				printReg256(src1); print("."); print(qwsel1); print(", "); 
				printReg256(src2); print("."); print(qwsel2); print(", ");
				printAccShift(shift); print("\n");
				
		  case MULQACCSO256(zero, dst, hwsel, src1, qwsel1, src2, qwsel2, shift) =>
				if zero { print("  bn.mulqacc.so "); } else { print("  bn.mulquacc.so.z "); }
				printReg256(dst); if hwsel { print(".U "); } else { print(".L "); }
				printReg256(src1); print("."); print(qwsel1); print(", "); 
				printReg256(src2); print("."); print(qwsel2); print(", ");
				printAccShift(shift); print("\n");

			case SUBI256(dst, src1, src2, fg) =>
				print("  bn.subi ");
				printReg256(dst); print(", "); printReg256(src1); print(", "); print(src2); print(", ");
				printFlags(fg); print("\n");

			case SUBB256(dst, src1, src2, st, sb, fg) =>
				print("  bn.subb ");
				printReg256(dst); print(", "); printReg256(src1); print(", "); printReg256(src2); print(" "); 
				printShiftType(st); print(" "); print(sb); print(", "); printFlags(fg);
				print("\n");

			case SUB256(dst, src1, src2, st, sb, fg) =>
				print("  bn.sub ");
				printReg256(dst); print(", "); printReg256(src1); print(", "); printReg256(src2); print(" "); 
				printShiftType(st); print(" "); print(sb); print(", "); printFlags(fg);
				print("\n");

			case RSHI256(dst, src1, src2, imm) =>
				print("  bn.rshi ");
				printReg256(dst); print(", "); printReg256(src1); print(", "); printReg256(src2); print(" >> "); print(imm);
				print("\n");
			
			case SEL256(dst, src1, src2, fg, flag) =>
				print("  bn.sel ");
				printReg256(dst); print(", "); printReg256(src1); print(", "); printReg256(src2); print(", ");
				printFlags(fg); print("."); printFlag(flag); print("\n");

			case MOV256(dst, src) =>
				print("  bn.mov ");
				printReg256(dst); print(", "); printReg256(src); print("\n");
		
			case AND256(dst, src1, src2, st, sb) =>
				print("  bn.and ");
				printReg256(dst); print(", "); printReg256(src1); print(", "); printReg256(src2); print(" "); 
				printShiftType(st); print(" "); print(sb); print("\n");
				
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
    printProc("demo", va_code_DoubleRegExample256(), 0, 0);
    printProc("demo", va_code_barrett384(), 0, 0);
}

method Main()
{
    PrintDemo(OTBN, MacOS);
}

}

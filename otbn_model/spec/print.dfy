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
        case ADD32(dst, src1, src2) => print ("  add "); printReg32(dst); print(", "); printReg32(src1); print(", "); printReg32(src2); print("\n");
			  case _ => print("TODO");
}

method printIns256(ins:ins256)
{
    match ins
        case ADD256(dst, src1, src2, st, sb, flg) => print ("  bn.add "); printReg256(dst); print(", "); printReg256(src1); print(", "); printReg256(src2); print("\n");
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
  print(" endp\n");
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
}

method Main()
{
    PrintDemo(OTBN, MacOS);
}

}

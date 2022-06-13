include "vale.i.dfy"

module otbn_printer {
    import opened integers
    import opened ot_machine

method printReg32(r:reg32_t)
{
    match r
        case GPR(x) => print("x"); print(x);
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
        case LW(grd, offset, grs1) =>
            print ("lw ");
            printReg32(grd); print(", "); print(offset); print("("); printReg32(grs1); print(")");
            print("\n");

        case SW(grs2, offset, grs1) =>
            print ("sw ");
            printReg32(grs2); print(", "); print(offset); print("("); printReg32(grs1); print(")");
            print("\n");

        case ADD(dst, src1, src2) =>
            print ("add ");
            printReg32(dst); print(", "); printReg32(src1); print(", "); printReg32(src2);
            print("\n");

        case ADDI(dst, src1, src2) =>
            print ("addi ");
            printReg32(dst); print(", "); printReg32(src1); print(", "); print(src2);
            print("\n");

        // case SUB(dst, src1, src2) =>
        //     print ("sub ");
        //     printReg32(dst); print(", "); printReg32(src1); print(", "); printReg32(src2);
        //     print("\n");

        // case AND(dst, src1, src2) =>
        //     print ("and ");
        //     printReg32(dst); print(", "); printReg32(src1); print(", "); printReg32(src2);
        //     print("\n");

        case ANDI(dst, src1, src2) =>
            print ("andi ");
            printReg32(dst); print(", "); printReg32(src1); print(", "); print(src2);
            print("\n");

        // case OR(dst, src1, src2) =>
        //     print ("or ");
        //     printReg32(dst); print(", "); printReg32(src1); print(", "); printReg32(src2);
        //     print("\n");

        // case ORI(dst, src1, src2) =>
        //     print ("ori ");
        //     printReg32(dst); print(", "); printReg32(src1); print(", "); print(src2);
        //     print("\n");

        // case XOR(dst, src1, src2) =>
        //     print ("xor ");
        //     printReg32(dst); print(", "); printReg32(src1); print(", "); printReg32(src2);
        //     print("\n");

        // case XORI(dst, src1, src2) =>
        //     print ("xori ");
        //     printReg32(dst); print(", "); printReg32(src1); print(", "); print(src2);
        //     print("\n");

        // case LUI(dst, src) =>
        //     print ("lui ");
        //     printReg32(dst); print(", "); print(src);
        //     print("\n");

        // TODO: this is case-by-case combo of addi and lui, should we print that instead?
        case LI(dst, src) =>
            print ("li ");
            printReg32(dst); print(", "); print(src);
            print("\n");
        
        case CSRRS(grd, csr, grs1) =>
            print ("csrrs ");
            printReg32(grd); print(", "); print(csr); print(", "); printReg32(grs1);
            print("\n");

        case ECALL => 
            print ("ecall ");

        case BN_NOP =>
            print("nop\n");

        case UNIMP =>
            print ("unimp\n");
        

}

method printShift(shift:shift_t)
{
    match shift
        case SFT(left, bytes) =>
        match left
            case true => print("<< "); print(bytes * 8);
            case false => print(">> "); print(bytes * 8);
}

method printFlags(fg:uint1)
{
    match fg
        case 0 => print("FG0");
        case 1 => print("FG1");
}

method printFlag(flag:uint2)
{
    match flag
        case 0 => print("C");
        case 1 => print("M");
        case 2 => print("L");
        case 3 => print("Z");
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

        case BN_XOR(dst, src1, src2, shift, fg) =>
            print("bn.xor ");
            printReg256(dst); print(", "); printReg256(src1); print(", "); printReg256(src2); print(" "); 
            printShift(shift); print(", "); printFlags(fg);
            print("\n");

        case BN_ADD(dst, src1, src2, shift, fg) =>
            print("bn.add ");
            printReg256(dst); print(", "); printReg256(src1); print(", "); printReg256(src2); print(" ");
            printShift(shift); print(", "); printFlags(fg);
            print("\n");

        case BN_ADDC(dst, src1, src2, shift, fg) =>
            print("bn.addc ");
            printReg256(dst); print(", "); printReg256(src1); print(", "); printReg256(src2); print(" ");
            printShift(shift); print(", "); printFlags(fg);
            print("\n");

        case BN_ADDI(dst, src, imm, fg) =>
            print("bn.addi ");
            printReg256(dst); print(", "); printReg256(src); print(", "); print(imm);
            print(", "); printFlags(fg); print("\n");

        case BN_MULQACC(zero, src1, qwsel1, src2, qwsel2, shift) =>
            if zero { print("bn.mulqacc.z "); } else { print("bn.mulqacc "); }
            printReg256(src1); print("."); print(qwsel1); print(", ");
            printReg256(src2); print("."); print(qwsel2); print(", ");
            printAccShift(shift); print("\n");

        case BN_MULQACC_SO(zero, dst, lower, src1, qwsel1, src2, qwsel2, shift, fg) =>
            if zero { print("bn.mulqacc.so.z "); } else { print("bn.mulqacc.so "); }
                    printReg256(dst); print("."); if lower { print("L"); } else { print("U"); } print(", ");
            printReg256(src1); print("."); print(qwsel1); print(", ");
            printReg256(src2); print("."); print(qwsel2); print(", ");
            printAccShift(shift); print(", "); printFlags(fg); 
            print("\n");

        // todo
        // case BN_SUBI(dst, src1, src2, fg) =>
        //     print("bn.subi ");
        //     printReg256(dst); print(", "); printReg256(src1); print(", "); print(src2); print(", ");
        //     printFlags(fg); print("\n");

        case BN_SUBB(dst, src1, src2, shift, fg) =>
            print("bn.subb ");
            printReg256(dst); print(", "); printReg256(src1); print(", "); printReg256(src2); print(" ");
            printShift(shift); print(", "); printFlags(fg);
            print("\n");

        case BN_SUB(dst, src1, src2, shift, fg) =>
            print("bn.sub ");
            printReg256(dst); print(", "); printReg256(src1); print(", "); printReg256(src2); print(" ");
            printShift(shift); print(", "); printFlags(fg);
            print("\n");

        // TODO: fix otbn_subm in ot_machine file
        // case BN_SUBM(dst, src1, src2) =>
        //     print("bn.subm ");
        //     printReg256(dst); print(", "); printReg256(src1); print(", "); printReg256(src2);
        //     print("\n");

        // case BN_OR(dst, src1, src2, shift) =>
        //     print("bn.or ");
        //     printReg256(dst); print(", "); printReg256(src1); print(", "); printReg256(src2); print(" ");
        //     printShift(shift);
        //     print("\n");

        // case BN_AND(dst, src1, src2, shift) =>
        //     print("bn.and ");
        //     printReg256(dst); print(", "); printReg256(src1); print(", "); printReg256(src2); print(" ");
        //     printShift(shift); print(" "); print("\n");

        case BN_LID(grd, grd_inc, offset, grs, grs_inc) =>
            print("bn.lid ");
            printReg32(grd); if grd_inc { print("++"); } print(", ");
            print(offset); print("(");
            printReg32(grs); if grs_inc { print("++"); }
            print(")"); print("\n");

        // case BN_RSHI(dst, src1, src2, imm) =>
        //     print("bn.rshi ");
        //     printReg256(dst); print(", "); printReg256(src1); print(", ");
        //     printReg256(src2); print(" >> "); print(imm);
        //     print("\n");

        case BN_SEL(dst, src1, src2, fg, flag) =>
            print("bn.sel ");
            printReg256(dst); print(", "); printReg256(src1); print(", "); printReg256(src2); print(", ");
            printFlags(fg); print("."); printFlag(flag); print("\n");

        case BN_SID(grs2, grs2_inc, offset, grs1, grs1_inc) =>
            print("bn.sid ");
            printReg32(grs2); if grs2_inc { print("++"); } print(", ");
            print(offset); print("(");
            printReg32(grs1); if grs1_inc { print("++"); }
            print(")"); print("\n");

        case BN_MOV(dst, src) =>
            print("bn.mov ");
            printReg256(dst); print(", "); printReg256(src); print("\n");

        case BN_MOVR(grd, grd_inc, grs, grs_inc) =>
            print("bn.movr ");
            printReg32(grd); if grd_inc { print("++"); } print(", ");
            printReg32(grs); if grs_inc { print("++"); }
            print("\n");

        case _ => print("TODO256 "); print(ins);
}

method printWhileCond(wcond: whileCond)
{
    match wcond
        case RegCond(r) => print("loop "); printReg32(r);
        case ImmCond(imm) => print("loopi "); print(imm);
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
        case While(wcond, wbody) => codeSize(wbody) + 1 // +1 for inner loop
        case IfElse(icond, tbody, fbody) => codeSize(tbody) + codeSize(fbody) + 1
        case Function(_, _) => 1
        case Ins32(ins) => 1
        case Ins256(bn_ins) => 1
        case Comment(com) => 0
}

method printIfCond(icond: ifCond)
{
    var Cmp(op, r1, r2) := icond;

    // revert the operation
    match op {
        case Eq => print("bne "); 
        case Ne => print("beq "); 
    }

    printReg32(r1); print(", "); printReg32(r2); 
}

method getFunctionsFromCodes(block: codes, defs: set<string>, res: seq<(string, codes)>) 
    returns (defs': set<string>, res': seq<(string, codes)>) 
{
    var i := block;
    defs', res' := defs, res;

    while (i.va_CCons?)
        decreases i
    {
        defs', res' := getFunctions(i.hd, defs', res');
        i := i.tl;
    }
}

method getFunctions(c: code, defs: set<string>, res: seq<(string, codes)>) 
    returns (defs': set<string>, res': seq<(string, codes)>)
{
    defs', res' := defs, res;

    match c 
        case Block(block) =>
            defs', res' := getFunctionsFromCodes(block, defs, res);
        case Function(name, fbody) => {
            if name !in defs {
                defs' := defs + {name};
                res' := res + [(name, fbody)];
            }
            defs', res' := getFunctionsFromCodes(fbody, defs', res');
        }
        case While(_, wbody) => 
            defs', res' := getFunctions(wbody, defs', res');
        case _ =>
            defs', res' := defs, res;
}

class Printer {
    var labelCount: nat;
    var depth: int;
    var printed: set<string>;
    var globls: set<string>;

    constructor(globals: set<string>)
    {
        labelCount := 0;
        depth := 1;
        globls := globals;
    }

    method printIndent()
    {
        var i := 0;
        while i < depth
        {
            print("  ");
            i := i + 1;
        }
    }

    method printBlock(b: codes)
        modifies this
    {
        var i := b;
        while (i.va_CCons?)
            decreases i
        {
            printCode(i.hd);
            i := i.tl;
        }
    }

    method printCode(c: code)
        modifies this
    {
        match c
            case Ins32(ins) => printIndent(); printIns32(ins);
            case Ins256(ins) => printIndent(); printIns256(ins);
            case Block(block) => printBlock(block);
            case Function(name, fbody) =>
                printIndent(); print("jal x1, "); print(name); print("\n");
            case IfElse(icond, tbody, fbody) =>
            {
                printIndent(); printIfCond(icond); print(", label_"); print(labelCount); print("\n");
                printCode(tbody);
                printIndent(); print("label_"); print(labelCount); print(":\n");
                var fsize := codeSize(fbody);
                if fsize != 0 {
                    print("TODO else not yet implemented"); 
                }
                labelCount := labelCount + 1;
            }
            case While(wcond, wbody) =>
            {
                printIndent(); printWhileCond(wcond); print(", ");
                print(codeSize(wbody)); print("\n");
                depth := depth + 1;
                printCode(wbody);
                depth := depth - 1;
            }
            case Comment(com) =>
            {
                // Insert a newline if this is the beginning of the comment.
                if (2 <= |com| && com[..2] == "/*") { print("\n"); }
                printIndent(); print(com); print("\n");
            }
    }

    method printTopLevelProc(code: code)
        requires code.Function?
        modifies this
    {
        var defs, res := getFunctions(code, {}, []);
        var i := 0;
        while i < |res|
        {
            var func_name := res[i].0;
            if func_name !in printed {
                printed := printed + {func_name};
                if func_name in globls {
                    print(".globl "); print(func_name); print("\n");
                }
                print(func_name); print(":\n");
                var overlaps := has_overlap_seq(simplify_codes(res[i].1));
                if overlaps {
                  print("LOOP_ERROR detected:\n");
                  print(simplify_codes(res[i].1));
                }
                printCode(Block(res[i].1));
                printIndent(); print("ret\n\n");
            }
            i := i + 1;
        }
    }
}
}

include "machine.s.dfy"
include "vale.i.dfy"
include "../../../gen/impl/msp430/rsa/mod_exp.i.dfy"
include "../../../gen/impl/msp430/falcon/msp_falcon.i.dfy"

module msp_printer {
    import opened msp_machine
    import opened msp_vale

    method printReg(r: reg_t)
    {
        match r
            case SP => print("SP");
            case GPR(i) => print("R"); print(i);
    }

    method printOperand(op: operand_t)
    {
        match op
            case Reg(r) => printReg(r);
            case Idx(r, index) => 
                print(index); print("("); printReg(r); print(")");
            case RegIndir(r, inc) =>
                print("@"); printReg(r); if inc { print("+"); }
            case Imm(i) =>
                print("#"); print(i);
            case ISym(s) => 
                print("#"); print(s);
    }

    method printIns(ins: ins_t)
    {
        match ins
            case MSP_ADD_W(src, dst) =>
                print("ADD.W\t"); printOperand(src); print(","); printOperand(dst);
                print("\n");
            case MSP_ADC_W(dst) =>
                print("ADC.W\t"); printOperand(dst);
                print("\n");
            case MSP_ADDC_W(src, dst) =>
                print("ADDC.W\t"); printOperand(src); print(","); printOperand(dst);
                print("\n");
            case MSP_AND_W(src, dst) =>
                print("AND.W\t"); printOperand(src); print(","); printOperand(dst);
                print("\n");
            case MSP_CLR_W(dst) =>
                print("CLR.W\t"); printOperand(dst);
                print("\n");
            case MSP_SUB_W(src, dst) =>
                print("SUB.W\t"); printOperand(src); print(","); printOperand(dst);
                print("\n");
            case MSP_SUBC_W(src, dst) =>
                print("SUBC.W\t"); printOperand(src); print(","); printOperand(dst);
                print("\n");
            case MSP_MOV_W(src, dst) =>
                print("MOV.W\t"); printOperand(src); print(","); printOperand(dst);
                print("\n");
            case MSP_MOV_B(src, dst) =>
                print("MOV.B\t"); printOperand(src); print(","); printOperand(dst);
                print("\n");
            case MSP_RLA_W(dst) =>
                print("RLA.W\t"); printOperand(dst);
                print("\n");
            case MSP_RRA_W(dst) =>
                print("RRA.W\t"); printOperand(dst);
                print("\n");
            case MSP_PUSHM_W(n, dst) =>
                print("PUSHM.W\t"); printOperand(n); print(","); printOperand(dst);
                print("\n");
            case MSP_POPM_W(n, dst) =>
                print("POPM.W\t"); printOperand(n); print(","); printOperand(dst);
                print("\n");
    }
    
    method printWhileCond(wcond: cond, lcount: int)
    {
        match wcond
            case EQ(o1, o2) =>
                print("\tCMP.W\t"); printOperand(o2); print(","); printOperand(o1);
                print("\n");
                print("\tJNE\t"); print("w_end"); print(lcount);
                print("\n");
            case LO(o1, o2) =>
                print("\tCMP.W\t"); printOperand(o2); print(","); printOperand(o1);
                print("\n");
                print("\tJGE\t"); print("w_end"); print(lcount);
                print("\n");
    }

    method printIfCond(wcond: cond, lcount: int)
    {
        match wcond
            case EQ(o1, o2) =>
                print("\tCMP.W\t"); printOperand(o2); print(","); printOperand(o1);
                print("\n");
                print("\tJEQ\t"); print("if_true"); print(lcount);
                print("\n");
            case LO(o1, o2) =>
                print("\tCMP.W\t"); printOperand(o2); print(","); printOperand(o1);
                print("\n");
                print("\tJLO\t"); print("if_true"); print(lcount);
                print("\n");
    }


class Printer {
    var lcount: int;
    var depth: int;

    var printed: set<string>;
    var globls: set<string>;

    constructor(globals: set<string>)
    {
        lcount := 0;
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
            case Ins(ins) => printIndent(); printIns(ins); 
            case Block(block) => printBlock(block);
            case IfElse(icond, tbody, fbody) =>
            {
                var cur_label := lcount;
                lcount := lcount + 1;
                printIfCond(icond, cur_label);
                printCode(fbody);
                print("  JMP "); print("if_end"); print(cur_label); print("\n");
                print("\n"); print("if_true"); print(cur_label); print(":\n");
                printCode(tbody);
                print("\n"); print("if_end"); print(cur_label); print(":\n");
            }
            case While(wcond, wbody) =>
            {
                var cur_label := lcount;
                lcount := lcount + 1;

                print("\n"); print("w_start"); print(cur_label); print(":\n");
                printWhileCond(wcond, cur_label);
                printCode(wbody);
                print("  JMP "); print("w_start"); print(cur_label); print("\n");
                print("\n"); print("w_end"); print(cur_label); print(":\n");
            }
            case Function(name, fbody) =>
                printIndent(); 
                print("CALL #"); print(name); print("\n"); 
            case Comment(com) => print(com);
    }

    method printProc(code:code)
        requires code.Function?
        modifies this
    {
        var defs, res := getFunctions(code, {}, []); 
        // do not print these two as procs
        printed := printed + {"__mspabi_mpyl", "__mspabi_mpyi"};

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
                printCode(Block(res[i].1));
                printIndent(); print("RET\n\n");
            }
            i := i + 1;
        }
    }
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
        case IfElse(_, ifTrue, ifFalse) =>
            defs', res' := getFunctions(ifTrue, defs', res');
            defs', res' := getFunctions(ifFalse, defs', res');
        case _ =>
            defs', res' := defs, res;
}
}
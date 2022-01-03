include "vale.i.dfy"
include "../../gen/impl/riscv/mod_pow.i.dfy"

module riscv_printer {
    import opened integers
    import opened rv_machine
    import opened mod_pow

method printReg32(r:reg32_t)
{
    match r
        case X0 =>  print("x0");  // hardwired to 0, ignores writes	n/a
        case RA =>  print("ra");  // x1		return address for jumps	no
        case SP =>  print("sp");  // x2		stack pointer	yes
        case GP =>  print("gp");  // x3		global pointer	n/a
        case TP =>  print("tp");  // x4		thread pointer	n/a
        case T0 =>  print("t0");  // x5		temporary register 0	no
        case T1 =>  print("t1");  // x6		temporary register 1	no
        case T2 =>  print("t2");  // x7		temporary register 2	no
        case S0 =>  print("s0");  // x8	 	saved register 0 or frame pointer	yes
        case S1 =>  print("s1");  // x9		saved register 1	yes
        case A0 =>  print("a0");  // x10		return value or function argument 0	no
        case A1 =>  print("a1");  // x11		return value or function argument 1	no
        case A2 =>  print("a2");  // x12		function argument 2	no
        case A3 =>  print("a3");  // x13		function argument 3	no
        case A4 =>  print("a4");  // x14		function argument 4	no
        case A5 =>  print("a5");  // x15		function argument 5	no
        case A6 =>  print("a6");  // x16		function argument 6	no
        case A7 =>  print("a7");  // x17		function argument 7	no
        case S2 =>  print("s2");  // x18		saved register 2	yes
        case S3 =>  print("s3");  // x19		saved register 3	yes
        case S4 =>  print("s4");  // x20		saved register 4	yes
        case S5 =>  print("s5");  // x21		saved register 5	yes
        case S6 =>  print("s6");  // x22		saved register 6	yes
        case S7 =>  print("s7");  // x23		saved register 7	yes
        case S8 =>  print("s8");  // x24		saved register 8	yes
        case S9 =>  print("s9");  // x25		saved register 9	yes
        case S10 => print("s10"); // x26		saved register 10	yes
        case S11 => print("s11"); // x27		saved register 11	yes
        case T3 =>  print("t3");  // x28		temporary register 3	no
        case T4 =>  print("t4");  // x29		temporary register 4	no
        case T5 =>  print("t5");  // x30		temporary register 5	no
        case T6 =>  print("t6");  // x31		temporary register 6	no
        case _ =>   print("Register not recognized.");
}

method printIns32(ins:ins32)
{
    print("  ");
    match ins
        case RV_LW(rd, rs1, imm) =>
            print ("lw ");
            printReg32(rd); print(", "); print(imm); print("("); printReg32(rs1); print(")");
            print("\n");

        case RV_ADDI(rd, rs1, imm) =>
            print ("addi ");
            printReg32(rd); print(", "); printReg32(rs1); print(", "); print(imm);
            print("\n");                                              
                                                                      
        case RV_SLTI(rd, rs1, imm) =>                                  
            print ("slti ");                                          
            printReg32(rd); print(", "); printReg32(rs1); print(", "); print(imm);
            print("\n");                                              
                                                                      
        case RV_XORI(rd, rs1, imm) =>                                  
            print ("xori ");                                          
            printReg32(rd); print(", "); printReg32(rs1); print(", "); print(imm);
            print("\n");                                              
                                                                      
        case RV_ORI(rd, rs1, imm) =>                                   
            print ("ori ");                                           
            printReg32(rd); print(", "); printReg32(rs1); print(", "); print(imm);
            print("\n");                                              
                                                                      
        case RV_ANDI(rd, rs1, imm) =>                                  
            print ("andi ");                                          
            printReg32(rd); print(", "); printReg32(rs1); print(", "); print(imm);
            print("\n");                                              
                                                                      
        case RV_SRLI(rd, rs1, imm) =>                                  
            print ("srli ");                                          
            printReg32(rd); print(", "); printReg32(rs1); print(", "); print(imm);
            print("\n");                                              
                                                                      
        case RV_SRAI(rd, rs1, imm) =>                                  
            print ("srai ");                                          
            printReg32(rd); print(", "); printReg32(rs1); print(", "); print(imm);
            print("\n");                                              
                                                                      
        case RV_SW(rd, rs1, imm) =>                                    
            print ("sw ");                                          
            printReg32(rd); print(", "); print(imm); print("("); printReg32(rs1); print(")");
            print("\n");
            
        case RV_ADD(rd, rs1, rs2) =>
            print ("add ");
            printReg32(rd); print(", "); printReg32(rs1); print(", "); printReg32(rs2);
            print("\n");

        case RV_SUB(rd, rs1, rs2) =>
            print ("sub ");
            printReg32(rd); print(", "); printReg32(rs1); print(", "); printReg32(rs2);
            print("\n");

        case RV_SLL(rd, rs1, rs2) =>
            print ("sll ");
            printReg32(rd); print(", "); printReg32(rs1); print(", "); printReg32(rs2);
            print("\n");

        case RV_SLT(rd, rs1, rs2) =>
            print ("slt ");
            printReg32(rd); print(", "); printReg32(rs1); print(", "); printReg32(rs2);
            print("\n");

        case RV_SLTU(rd, rs1, rs2) =>
            print ("sltu ");
            printReg32(rd); print(", "); printReg32(rs1); print(", "); printReg32(rs2);
            print("\n");

        case RV_XOR(rd, rs1, rs2) =>
            print ("xor ");
            printReg32(rd); print(", "); printReg32(rs1); print(", "); printReg32(rs2);
            print("\n");

        case RV_SRL(rd, rs1, rs2) =>
            print ("srl ");
            printReg32(rd); print(", "); printReg32(rs1); print(", "); printReg32(rs2);
            print("\n");

        case RV_SRA(rd, rs1, rs2) =>
            print ("sra ");
            printReg32(rd); print(", "); printReg32(rs1); print(", "); printReg32(rs2);
            print("\n");

        case RV_OR(rd, rs1, rs2) =>
            print ("or ");
            printReg32(rd); print(", "); printReg32(rs1); print(", "); printReg32(rs2);
            print("\n");

        case RV_AND(rd, rs1, rs2) =>
            print ("and ");
            printReg32(rd); print(", "); printReg32(rs1); print(", "); printReg32(rs2);
            print("\n");

        case RV_LUI(rd, imm) =>
            print ("lui ");
            printReg32(rd); print(", "); print(imm);
            print("\n");

        case RV_LI(rd, imm) =>
            print ("li ");
            printReg32(rd); print(", "); print(imm);
            print("\n");

        case RV_MUL(rd, rs1, rs2) =>
            print ("mul ");
            printReg32(rd); print(", "); printReg32(rs1); print(", "); printReg32(rs2);
            print("\n");

        case RV_MULH(rd, rs1, rs2) =>
            print ("mulh ");
            printReg32(rd); print(", "); printReg32(rs1); print(", "); printReg32(rs2);
            print("\n");

        case RV_MULHU(rd, rs1, rs2) =>
            print ("mulhu ");
            printReg32(rd); print(", "); printReg32(rs1); print(", "); printReg32(rs2);
            print("\n");
            
        case RV_DIV(rd, rs1, rs2) =>
            print ("div ");
            printReg32(rd); print(", "); printReg32(rs1); print(", "); printReg32(rs2);
            print("\n");
            
        case _ => print("Instruction not supported: "); print(ins);
}

method printWCondOp(op: cmp)
{
    match op
        case Eq => print("  bne ");
        case Ne => print("  beq ");
        case Le => print("  bgt ");
        case Ge => print("  blt ");
        case Lt => print("  bge ");
        case Gt => print("  ble ");
}

method printIfCondOp(op: cmp)
{
  match op
    case Eq => print("  beq ");
    case Ne => print("  bne ");
    case Le => print("  ble ");
    case Ge => print("  bge ");
    case Lt => print("  blt ");
    case Gt => print("  bgt ");
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
        case While(wcond, wbody) => codeSize(wbody) + 1 // TODO: RV check
        case IfElse(ifcond, iftrue, iffalse) => codeSize(iftrue) + codeSize(iffalse) + 1
        case Function(_, _) => 1
        case Ins32(ins) => 1
        case Comment(com) => 0
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
        case IfElse(_, tbody, fbody) =>
            defs', res' := getFunctions(tbody, defs', res');
            defs', res' := getFunctions(fbody, defs', res');
        case _ =>
            defs', res' := defs, res;
}

class Printer {
    var labelCount: nat;

    constructor()
    {
        labelCount := 0;
    }

    method printWhileCond(wcond: cond)
    {
      printWCondOp(wcond.op);
      printReg32(wcond.r1); print(", "); printReg32(wcond.r2);
      print(", "); print("w_end"); print(labelCount); print("\n");
    }

    method printIfCond(icond: cond)
    {
      printIfCondOp(icond.op);
      printReg32(icond.r1); print(", "); printReg32(icond.r2);
      print(", "); print("if_true"); print(labelCount); print("\n");
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
        case Ins32(ins) => print("  "); printIns32(ins);
        case Block(block) => printBlock(block);
        case IfElse(icond, tbody, fbody) =>
      {
        printIfCond(icond);
        labelCount := labelCount + 1;
        printCode(fbody);
        print("  j "); print("if_end"); print(labelCount); print("\n");
        print("\n"); print("if_true"); print(labelCount); print(":\n");
        printCode(tbody);
        print("\n"); print("if_end"); print(labelCount); print(":\n");
      }
        case While(wcond, wbody) =>
      {
        print("\n"); print("w_start"); print(labelCount); print(":\n");
        printWhileCond(wcond);
        labelCount := labelCount + 1;
        printCode(wbody);
        print("  j "); print("w_start"); print(labelCount); print("\n");
        print("\n"); print("w_end"); print(labelCount); print(":\n");
      }
        case Function(name, fbody) =>
          print("TODO\n");
        case Comment(com) => print(com);
    }

    method printProc(code: code)
        requires code.Function?
        modifies this
    {
        print(".globl mod_pow"); print("\n");
        var defs, res := getFunctions(code, {}, []); 
        var i := 0;
        while i < |res|
        {
            print(res[i].0); print(":\n");
            printCode(Block(res[i].1));
            i := i + 1;
            print("ret\n\n");
        }
    }
}

method Main()
{
    reveal va_code_mod_pow();
    var p := new Printer();
    p.printProc(va_code_mod_pow());
}

}

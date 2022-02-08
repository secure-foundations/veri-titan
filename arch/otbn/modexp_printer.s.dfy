include "vale.i.dfy"
include "printer.s.dfy"
include "../../gen/impl/otbn/modexp_var.i.dfy"

module modexp_printer {
  
import opened ot_machine
import opened modexp_var
import opened otbn_printer

method Main()
{
    var p := new Printer({"modexp_var_3072_f4", "montmul"});

    reveal va_code_modexp_var_3072_f4();
    var c := va_code_modexp_var_3072_f4();

    var n :=  while_overlap(c);
    if n {
      print("ERROR: Overlapping 'While' loop.\n");
      p.printTopLevelProc(c);
    } else
    {
      p.printTopLevelProc(c);
    }
}

}

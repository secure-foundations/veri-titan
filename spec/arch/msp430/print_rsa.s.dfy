include "printer.s.dfy"

import opened msp_machine
import opened mod_exp
import opened msp_printer

method Main()
{
    reveal va_code_mod_pow();
    var printer := new Printer({"mod_pow"});
    printer.printProc(va_code_mod_pow());
}
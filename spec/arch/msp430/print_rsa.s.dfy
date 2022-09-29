include "printer.s.dfy"

import opened msp_machine
import opened mod_exp
import opened msp_printer

method Main()
{
    reveal va_code_mod_exp();
    var printer := new Printer({"mod_exp"});
    printer.printProc(va_code_mod_exp());
}
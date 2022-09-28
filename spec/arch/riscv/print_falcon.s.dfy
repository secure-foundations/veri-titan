include "printer.s.dfy"

import opened integers
import opened rv_machine
import opened mod_pow
import opened rv_falcon
import opened riscv_printer

method Main()
{
    reveal va_code_rv_falcon();
    var printer := new Printer({"rv_falcon"});
    printer.printProc(va_code_rv_falcon());
}
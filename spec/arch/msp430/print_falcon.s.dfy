include "printer.s.dfy"
include "../../../gen/impl/msp430/falcon/msp_falcon.i.dfy"

import opened msp_machine
import opened msp_falcon
import opened msp_printer

method Main()
{
    reveal va_code_msp_falcon();
    var printer := new Printer({"msp_falcon"});
    printer.printProc(va_code_msp_falcon());
}
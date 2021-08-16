include "code/vale.dfy"
include "gen/mul256.dfy" 

module otbn_exe {
    import opened bv_ops
    import opened vt_ops
    import opened mul256

method ExecuteDemo()
{
    var state := state.init();
    state := state.write_reg256(WDR(30), 321);
    state := state.write_reg256(WDR(2), 123);
    state := state.eval_code(va_code_mul256_w30xw2());
    state.dump();
}

method Main()
{
    ExecuteDemo();
}

}

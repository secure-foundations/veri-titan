include "vale.i.dfy"
include "../../gen/impl/otbn/test.dfy"

module otbn_exe {
    import opened integers
    import opened ot_machine
    import opened ot_abstraction
    import opened addc512

method ExecuteDemo()
{
    var state := state.init();

state := state.write_reg256(WDR(24), 40163065188442794063254903455135474380325149348580700926592284680584526109004);
state := state.write_reg256(WDR(31), 109244100131732487566533930731661067431131800049027042916527476462692967499568);
state := state.write_reg256(WDR(27), 60829475563728637100084755752523613753626231070386647216374262430696432176505);
state := state.write_reg256(WDR(26), 14761946310140337595457096356895286492896773213985669295438458246979193159199);

    state := state.debug_eval_code(va_code_mul_add_512());

}

method Main()
{
    ExecuteDemo();
}

}

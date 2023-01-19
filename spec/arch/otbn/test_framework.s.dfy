include "printer.s.dfy"
include "../../../gen/impl/otbn/nop_tests.i.dfy"

/* 
 A module for testing that OTBN code correctly includes NOP
 instructions to avoid LOOP_ERRORs, as described in:
 https://****   
*/
module test_framework {
    import opened integers
    import opened ot_machine
    import opened otbn_printer

    import opened nop_tests

method TestOverlap(p:Printer, name:string, c:code, overlap_expected:bool) 
  modifies p
{
  match c
    case Function(_, body) => {

    var overlaps := has_overlap_seq(simplify_codes(body));
    print("\nTesting loop overlap detection in " + name);

    if overlaps != overlap_expected {
      if overlap_expected {
        print("\n  ERROR: Expected to find an overlap but didn't\n");
      } else {
        print("\n  ERROR: Did not expect overlap but I think I found one\n");
      }

      print("  Simplified code: "); print(simplify_codes(body)); print("\n");
      
    } else {
      print("\n  PASSED!\n");
    }
  }
    case _ =>
    {
    print("ERROR: Expected a top-level function, found:\n" + name);
    print("\n");
  }
}

method Main()
{
    var p := new Printer({});

    var c;
    c := va_code_loop_overlap_nop();
    TestOverlap(p, "loop_overlap_nop", c, false);
    c := va_code_loop_overlap();
    TestOverlap(p, "loop_overlap", c, true);
    c := va_code_loop_no_overlap();
    TestOverlap(p, "loop_no_overlap", c, false);
    c := va_code_loop_overlap_inner_with_starting_ins();
    TestOverlap(p, "loop_overlap_inner_with_starting_ins", c, true);
    c := va_code_loop_overlap_inner_with_ending_ins();
    TestOverlap(p, "loop_overlap_inner_with_ending_ins", c, false);
    c := va_code_loop_if_overlap();
    TestOverlap(p, "loop_if_overlap", c, true);
    c := va_code_loop_if_with_starting_ins_overlap();
    TestOverlap(p, "loop_if_with_starting_ins_overlap", c, true);
    c := va_code_loop_if_with_ending_ins_no_overlap();
    TestOverlap(p, "loop_if_with_ending_ins_no_overlap", c, false);
    c := va_code_if_loop_no_overlap();
    TestOverlap(p, "if_loop_no_overlap", c, false);
    c := va_code_loop_loop_empty_overlap();
    TestOverlap(p, "if_loop_loop_empty_overlap", c, true);
    c := va_code_loop_if_empty_overlap();
    TestOverlap(p, "if_loop_if_empty_overlap", c, true);
    c := va_code_loop_function_overlap();
    TestOverlap(p, "if_loop_function_overlap", c, true);

    /* Examples provided in the OTBN documentation: */
    c := va_code_otbn_ok_example_1();
    TestOverlap(p, "otbn_ok_example_1", c, false);
    c := va_code_otbn_ok_example_2();
    TestOverlap(p, "otbn_ok_example_2", c, false);
    c := va_code_otbn_ok_example_3();
    TestOverlap(p, "otbn_ok_example_3", c, false);
    c := va_code_otbn_nok_example_1();
    TestOverlap(p, "otbn_nok_example_1", c, true);
    c := va_code_otbn_nok_example_2();
    TestOverlap(p, "otbn_nok_example_2", c, true);
}

}

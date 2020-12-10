// Formula: x + e == 0, where e = !x + 1


function xor(x:bool, y:bool) : bool {
  (x || y) && (!x || !y)
}

function x(i:nat) : bool

// Carry bit that emerges from x + e
function c(i:nat) : bool
{
  if i == 0 then x(0) && e(0)
  else ((x(i) && e(i)) || (c(i-1) && (x(i) || e(i))))
}

// Carry bit that emerges from !x + 1
function c'(i:nat) : bool
{
  if i == 0 then !x(0) && true
  else (c'(i-1) && !x(i))
}

// e == !x + 1
function e(i:nat) : bool
{
  if i == 0 then xor(!x(0), true)
  else xor(!x(i), c'(i-1))
}

// b == x + e
function b(i:nat) : bool
{
  if i == 0 then xor(x(0), e(0))
  else xor(xor(x(i), e(i)), c(i-1))
}


lemma rule_checker(x:bool, y:bool, z:bool)
  ensures (x || (y && z))    == ((x || y) && (x || z))
  ensures (x && (y || z))    == ((x && y) || (x && z))
  ensures (xor(x, (y || z))) == ((!x && (y || z)) || (x && (!y && !z)))
  ensures (x && xor(y, z))   == (xor(x && y, x && z))
  ensures !xor(x, y)         == xor(!x, y) == xor(x, !y)
  ensures xor(xor(y, x && y), (x || !y)) == true
  ensures xor(x, y && z) == (!x && (y && z)) || (x && !(y && z))
  ensures xor(x, y || z) == (!x && (y || z)) || (x && !(y || z))
  ensures (x && (x || y)) == x
  ensures (x || (x && y)) == x
  ensures (x && y) == !(!x || !y)
  //ensures xor(y, !z) == ((((x || !y) || z) && (!z || (x || y))) && ((y || !(x && (y || z))) && (z || !(x && (y || z)))))
{}

lemma function_test(i:nat) 
  // Sanity check base case
  ensures b(0) == false
  ensures xor(c(0), !c'(0)) == false
  // Induction hypothesis
  ensures i > 0 ==> b(i) == xor(!c'(i-1), c(i-1))
  ensures i > 0 ==> xor(!c'(i), c(i)) == xor(!c'(i-1), c(i-1))
  // Conclusion
  ensures b(i) == false   // Dafny's auto-induction solves this one, but the rest don't need it
{

}

/*
lemma test(b_i:bool, x_i:bool, x_i_minus_1:bool, c_i_minus_1:bool, c_i_minus_2:bool, e_i:bool, e_i_minus_1:bool, cp_i:bool, cp_i_minus_1:bool, cp_i_minus_2:bool)
  requires b_i == xor(xor(x_i,  e_i), c_i_minus_1)
  requires e_i == xor(!x_i, cp_i_minus_1)
  requires c_i_minus_1  == ((x_i_minus_1 && e_i_minus_1) || (c_i_minus_2  && (x_i_minus_1 || e_i_minus_1)))
  requires cp_i_minus_1 == ((!x_i_minus_1 && false)      || (cp_i_minus_2 && (!x_i_minus_1 || false)))
  ensures  b_i == xor(!cp_i_minus_1, c_i_minus_1);
  //ensures xor(!cp_i_minus_1, c_i_minus_1) == xor(!cp_i_minus_2, c_i_minus_2);
{  
  assert cp_i_minus_1 == (cp_i_minus_2 && !x_i_minus_1);
  calc {
    xor(!cp_i_minus_1, c_i_minus_1);
    xor(!(cp_i_minus_2 && !x_i_minus_1),
         ((x_i_minus_1 && e_i_minus_1) || (c_i_minus_2  && (x_i_minus_1 || e_i_minus_1))));
    xor( !cp_i_minus_2 || x_i_minus_1,
         ((x_i_minus_1 && e_i_minus_1) || (c_i_minus_2  && (x_i_minus_1 || e_i_minus_1))));
  }
}
*/

lemma {:induction false} carry_test_model0(the_x:bool, old_carry_1:bool, old_carry_2:bool, py_c1:bool, py_c2:bool)
  requires py_c1 == (((!the_x) && false) || (old_carry_1 && ((!the_x) || false)));
  requires py_c2 == ((the_x && xor((!the_x), xor(false, old_carry_1))) || (old_carry_2 && (the_x || xor((!the_x), xor(false, old_carry_1)))))

  // Hand simplification
  ensures py_c1 == (old_carry_1 && !the_x)
  ensures py_c2 == ((the_x && xor(!the_x, old_carry_1)) || (old_carry_2 && (the_x || xor(!the_x, old_carry_1))));

  // Fails:
//  ensures  xor(old_carry_1, !old_carry_2) == xor(py_c1, !py_c2)
{}

lemma {:induction false} carry_test_model1(the_x:bool, old_carry_1:bool, old_carry_2:bool, py_c1:bool, py_c2:bool, py_c2_simp:bool, i:nat)
  requires i > 10;
  // Final ensures fails without the next two lines
  requires old_carry_1 == c'(i-1)   
  requires old_carry_2 == c(i-1)
//  requires the_x == x(i)
  //requires old_carry_1 == c'(i-1) == c'(i-2) && !x(i-1)
  requires py_c1 == (((!the_x) && false) || (old_carry_1 && ((!the_x) || false)));
  requires py_c2 == ((the_x && xor((!the_x), xor(false, old_carry_1))) || (old_carry_2 && (the_x || xor((!the_x), xor(false, old_carry_1)))))
//  requires py_c2_simp == ((the_x && xor((!the_x), old_carry_1)) || (old_carry_2 && (the_x || xor((!the_x), old_carry_1))))
//  ensures py_c1 == c'(i)      // Passes
//  ensures py_c2 == py_c2_simp // Passes
//  ensures py_c2 == c(i)       // Passes
  ensures  xor(old_carry_1, !old_carry_2) == xor(py_c1, !py_c2)
{}

//lemma {:induction false} carry_test_model2(the_x:bool, old_carry_1:bool, old_carry_2:bool, py_c1:bool, py_c2:bool, i:nat)
//  requires i > 0;
//  requires the_x == x(i)
//  requires py_c1 == c'(i) 
//  requires py_c2 == c(i) 
//  requires py_c1 == (((!the_x) && false) || (old_carry_1 && ((!the_x) || false)));
//  requires py_c2 == ((the_x && xor((!the_x), xor(false, old_carry_1))) || (old_carry_2 && (the_x || xor((!the_x), xor(false, old_carry_1)))))
//  ensures old_carry_1 == c'(i-1) // Fails
//  ensures old_carry_2 == c(i-1)  // Fails
//  ensures  xor(old_carry_1, !old_carry_2) == xor(py_c1, !py_c2)
//{
//}

lemma carry_test(x:bool, x':bool, old_carry_1:bool, old_carry_2:bool, old_carry_1':bool, old_carry_2':bool, py_c1:bool, py_c2:bool, py_c1':bool, py_c2':bool, r_c1:bool, r_c2:bool)
  requires old_carry_1 == (((!x') && false) || (old_carry_1' && ((!x') || false)));
  requires old_carry_2 == ((x' && xor((!x'), xor(false, old_carry_1'))) || (old_carry_2' && (x' || xor((!x'), xor(false, old_carry_1')))))
  requires py_c1 == (((!x) && false) || (old_carry_1 && ((!x) || false)));
  requires py_c2 == ((x && xor((!x), xor(false, old_carry_1))) || (old_carry_2 && (x || xor((!x), xor(false, old_carry_1)))))

  requires r_c1 == ((!x && false) || (old_carry_1 && (!x || false)));
  requires r_c2 == ((x && xor(!x, xor(false, old_carry_1))) || (old_carry_2 && (x || xor(!x, xor(false, old_carry_1)))))
  
  // Python and Rust agree
  ensures py_c1 == r_c1
  ensures py_c2 == r_c2

  // Recursion holds
  ensures  xor(old_carry_1, !old_carry_2) == xor(py_c1, !py_c2)

  // Rust's starting point for simplifying the recursion relation is on the right path
  ensures xor(old_carry_1, !old_carry_2) == xor(((!x && false) || (old_carry_1 && (!x || false))), !((x && xor(!x, xor(false, old_carry_1))) || (old_carry_2 && (x || xor(!x, xor(false, old_carry_1))))))

  // Rust's initial simplification of the recursion relation is on the right path
  ensures xor(old_carry_1, !old_carry_2) == 
          xor(! x && old_carry_1, (!((x && old_carry_1) || (old_carry_2 && (x || (xor(!x, old_carry_1)))))))

// Rust's simplification is sound
  ensures xor(((!x && false) || (old_carry_1 && (!x || false))), !((x && xor(!x, xor(false, old_carry_1))) || (old_carry_2 && (x || xor(!x, xor(false, old_carry_1)))))) ==
          xor(! x && old_carry_1, (!((x && old_carry_1) || (old_carry_2 && (x || (xor(!x, old_carry_1)))))))
{
}

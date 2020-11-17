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

lemma function_test(i:nat) 
  // Sanity check base case
  ensures b(0) == false
  ensures xor(c(0), !c'(0)) == false
  // Induction
  ensures i > 0 ==> b(i) == xor(!c'(i-1), c(i-1))
  ensures i > 0 ==> xor(!c'(i), c(i)) == xor(!c'(i-1), c(i-1))
  // Conclusion
  ensures b(i) == false
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

lemma carry_test(x:bool, old_carry_1:bool, old_carry_2:bool)
  ensures xor(old_carry_1, !old_carry_2) == xor(((!x && false) || (old_carry_1 && (!x || false))), !((x && xor(!x, xor(false, ((!x && false) || (old_carry_1 && (!x || false)))))) || (old_carry_2 && (x || xor(!x, xor(false, ((!x && false) || (old_carry_1 && (!x || false)))))))))
{
}

// Formula: x + e == 0, where e = !x + 1

function xor(x:bool, y:bool) : bool {
  (x || y) && (!x || !y)
}

function x(i:nat) : bool

// Carry bit that emerges from x + e
function c(i:nat) : bool
  ensures i > 0 ==> (c(i) == ((x(i) && xor(!x(i), c'(i-1))) || (c(i-1) && (x(i) || xor(!x(i), c'(i-1))))))
//{
//  if i == 0 then x(0) && e(0)
//  else ((x(i) && xor(!x(i), c'(i-1))) || (c(i-1) && (x(i) || xor(!x(i), c'(i-1)))))
//}

// Carry bit that emerges from !x + 1
function c'(i:nat) : bool
  ensures i > 0 ==> (c'(i) == (c'(i-1) && !x(i)))
//{
//  if i == 0 then !x(0) && true
//  else (c'(i-1) && !x(i))
//}


lemma {:induction false} function_test(i:nat) 
  ensures i > 1 ==> xor(!c'(i), c(i)) == xor(!c'(i-1), c(i-1))
{
}

lemma {:induction false} carry_test_model1(the_x:bool, old_c:bool, old_c':bool, new_c:bool, new_c':bool, i:nat)
  requires i > 1;
  // Final ensures fails without the next two lines
  requires old_c  == c(i-1)
  requires old_c' == c'(i-1)   
//  requires the_x == x(i)      // R1
  requires new_c == ((the_x && xor((!the_x), old_c')) || (old_c && (the_x || xor((!the_x), old_c'))))
  requires new_c' == (old_c' && !the_x);
//  ensures new_c  == c(i)       // Passes when R1 is uncommented
//  ensures new_c' == c'(i)      // Passes when R1 is uncommented
  ensures  xor(!new_c', new_c) == xor(!old_c', old_c)
{}

lemma {:induction false} carry_test_model2(older_c:bool, older_c':bool, old_x:bool, the_x:bool, old_c:bool, old_c':bool, new_c:bool, new_c':bool, i:nat)
  requires i > 1;

  requires old_c == ((old_x && xor(!old_x, older_c')) || (older_c && (old_x || xor(!old_x, older_c'))))
  requires old_c' == (older_c' && !old_x)

  requires new_c == ((the_x && xor((!the_x), old_c')) || (old_c && (the_x || xor((!the_x), old_c'))))
  requires new_c' == (old_c' && !the_x);

  ensures  xor(!new_c', new_c) == xor(!old_c', old_c)
{
}

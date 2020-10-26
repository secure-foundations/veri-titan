import data.int.basic
#check id

set_option pp.beta true

namespace BV

lemma x_xor_x (x:Prop) : xor x x = false :=
begin
    simp [xor]
end


lemma test2 (decideable x:Prop) : (¬¬x) ↔ x :=
    by apply not_not

lemma test1 (x:bool) : (¬¬x) ↔ x :=
    by apply not_not

lemma x_minus_x (b_i  x_i x_i_minus_1 c_i_minus_1 c_i_minus_2 e_i e_i_minus_1 cp_i cp_i_minus_1 cp_i_minus_2 : bool) 
                (hb : b_i = xor (xor x_i e_i) c_i_minus_1)
                (he : e_i = xor (not x_i) cp_i_minus_1)
                (hc : c_i_minus_1  = or (and x_i_minus_1 e_i_minus_1) (and c_i_minus_2 (or x_i_minus_1 e_i_minus_1)))
                (hcp: cp_i_minus_1 = or (and (not x_i_minus_1) false) (and cp_i_minus_2 (or (not x_i_minus_1) false)))
: b_i = xor (not cp_i_minus_1) c_i_minus_1  :=
begin        
    simp [xor],
    -- simp [xor, hb, he, hc],
    tauto, 
    -- try { tauto },  --closer := not_not,
    sorry
end

end BV


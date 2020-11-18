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

/-
    Jay's Blast
-/
meta def rw_with_a_hyp : list expr → tactic unit
| [] := tactic.fail "no more rewrites"
| (h :: hs) := tactic.rewrite_target h <|> rw_with_a_hyp hs
meta def simp_with_extras : tactic unit :=
do
    let XOR : pexpr := ```(xor),
    let NOTNOT : pexpr := ```(classical.not_not),
    tactic.interactive.simp none false [
        tactic.simp_arg_type.all_hyps, 
        tactic.simp_arg_type.expr XOR, 
        tactic.simp_arg_type.expr NOTNOT] [] (interactive.loc.ns [none])
meta def case_on_variable (h:expr) : tactic unit :=
do
    tactic.by_cases h `h,
    simp_with_extras,
    tactic.try tactic.swap, 
    tactic.try simp_with_extras
meta def by_cases_on_a_hyp : list expr → tactic unit
| [] := tactic.fail "no more vars"
| (h :: hs) := do
    T₀ ← tactic.target,
    orig_state ← tactic.read,
    tactic.try (case_on_variable h),
    tactic.try (do
        T ← tactic.target,
        if expr.alpha_eqv T₀ T then (do
            tactic.write orig_state, 
            by_cases_on_a_hyp hs
        ) else (do
            tactic.skip
        )
    )
meta def by_cases_on_arb_hyp : tactic unit :=
do
    hs ← tactic.local_context,
    by_cases_on_a_hyp hs
meta def simp_fully_using_hyps : tactic unit :=
do
    hs ← tactic.local_context,
    tactic.repeat (rw_with_a_hyp hs),
    simp_with_extras
meta def blast : tactic unit :=
do
    tactic.classical,
    simp_fully_using_hyps,
    tactic.repeat (tactic.all_goals by_cases_on_arb_hyp)
lemma x_minus_x (b_i  x_i x_i_minus_1 c_i_minus_1 c_i_minus_2 e_i e_i_minus_1 cp_i cp_i_minus_1 cp_i_minus_2 : Prop)
                (hb : b_i = xor (xor x_i e_i) c_i_minus_1)
                (he : e_i = xor (not x_i) cp_i_minus_1)
                (hc : c_i_minus_1  = or (and x_i_minus_1 e_i_minus_1) (and c_i_minus_2 (or x_i_minus_1 e_i_minus_1)))
                (hcp: cp_i_minus_1 = or (and (not x_i_minus_1) false) (and cp_i_minus_2 (or (not x_i_minus_1) false)))
: b_i = xor (not cp_i_minus_1) c_i_minus_1  :=
begin
    blast,
end

/-
  Some test lemmas
-/

lemma x_minus_x_easy (b_i  x_i x_i_minus_1 c_i_minus_1 c_i_minus_2 e_i e_i_minus_1 cp_i cp_i_minus_1 cp_i_minus_2 : Prop) 
                (hb : b_i = xor (xor x_i e_i) c_i_minus_1)
                (he : e_i = xor (not x_i) cp_i_minus_1)
                (hc : c_i_minus_1  = or (and x_i_minus_1 e_i_minus_1) (and c_i_minus_2 (or x_i_minus_1 e_i_minus_1)))
                (hcp: cp_i_minus_1 = or (and (not x_i_minus_1) false) (and cp_i_minus_2 (or (not x_i_minus_1) false)))
: b_i = xor (not cp_i_minus_1) c_i_minus_1  :=
begin        
    -- simp [xor],
    -- simp [xor, hb, he, hc],
    -- tauto, 
    -- try { tauto },  --closer := not_not,
    -- sorry
    blast
end

lemma x_minus_x_hard (b_i  x_i x_i_minus_1 c_i c_i_minus_1 c_i_minus_2 e_i e_i_minus_1 cp_i cp_i_minus_1 cp_i_minus_2 : Prop)                             
                (he0 : e_i         = xor (not x_i) cp_i_minus_1)            
                (hc0 : c_i          = or (and x_i       e_i)   (and c_i_minus_1  (or x_i       e_i        )))             
                (hcp0: cp_i         = or (and (not x_i) false) (and cp_i_minus_1 (or (not x_i) false)))             
                (he1 : e_i_minus_1  = xor (not x_i_minus_1) cp_i_minus_2)            
                (hc1 : c_i_minus_1  = or (and x_i_minus_1 e_i_minus_1)   (and c_i_minus_2  (or x_i_minus_1 e_i_minus_1)))             
                (hcp1: cp_i_minus_1 = or (and (not x_i_minus_1) false) (and cp_i_minus_2 (or (not x_i_minus_1) false)))             
: xor (not cp_i) c_i = xor (not cp_i_minus_1) c_i_minus_1 :=
begin        
    -- simp [xor],
    -- simp [xor, hb, he, hc],
    -- tauto, 
    -- try { tauto },  --closer := not_not,
    blast
end

end BV


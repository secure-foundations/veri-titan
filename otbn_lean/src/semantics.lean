import data.zmod.basic 
import init.data.nat
open nat

namespace otbn
set_option pp.beta true

/- Basic types -/
attribute [reducible]
def uint32 := zmod 0x100000000

/- Register definitions and lemmas adapted from lovelib.lean's definition of state -/
def registers := nat -> uint32

/- 
   TODO: This all belongs in a generic (finite) map library, 
         with a set of lemmas that match F*/Dafny's axioms
 -/
def registers.update (id:nat) (val:uint32) (regs:registers) : registers :=
  λ id', if id' = id then val else regs id'

notation r `{` id ` ↦ ` val `}` := registers.update id val r
meta def tactic.dec_trivial := `[exact dec_trivial]

@[simp] lemma update_apply (id : nat) (val : uint32) (r : registers) :
  r {id ↦ val} id = val := if_pos rfl

@[simp] lemma update_apply_ne (id id' : nat) (val : uint32) (r : registers)
    (h : id' ≠ id . tactic.dec_trivial) :
  r {id ↦ val} id' = r id' :=
if_neg h

@[simp] lemma update_override (id : nat) (val₁ val₂ : uint32) (r : registers) :
  r{id ↦ val₂}{id ↦ val₁} = r{id ↦ val₁} :=
begin
  apply funext,
  intro id',
  by_cases id' = id;
    simp [h]
end

@[simp] lemma update_swap (id₁ id₂ : nat) (val₁ val₂ : uint32) (r : registers)
    (h : id₁ ≠ id₂ . tactic.dec_trivial) :
  r{id₂ ↦ val₂}{id₁ ↦ val₁} = r{id₁ ↦ val₁}{id₂ ↦ val₂} :=
begin
  apply funext,
  intro id',
  by_cases id' = id₁;
    by_cases id' = id₂;
    simp * at *
end

@[simp] lemma update_id (id : nat) (r : registers) :
  r{id ↦ r id} = r :=
begin
  apply funext,
  intro id',
  by_cases id' = id;
    simp * at *
end

def decide (i:nat) (r0 r1:registers) : bool := 
  if i = 1 then r0 i = r1 i else ff

def decide_proof (r0 r1:registers) (h:decide 1 r0 r1 = tt) : Prop :=
  have h : ∀ i:nat , i = 1 → r0 i = r1 i, from
  begin
    intro i,
    intro hi,
    cases i,
    { exfalso,
      have h_nz : succ 0 ≠ 0 := succ_ne_zero 0,
      have hi_rev : 1 = 0 := 
        begin
          symmetry,
          exact hi         
        end,
      exact (h_nz hi_rev) },
    {
      rw hi,      
      have h_duh : r0 1 = r1 1 := h, 
    }

  end
/-
def registers.eq (r0 r1:registers) : bool :=
  let p := ∀ i:nat , i = 1 → r0 i = r1 i in
  let proof : decidable p :=
  begin
    
    

  end


def registers.eq (r0 r1:registers) : bool :=
  let p := ∀ i:nat , (0 ≤ i ∧ i < 32) → r0 i = r1 i in
  let proof : decidable p :=
  begin
    
  end

/- State definition -/
structure state : Type :=
  (regs : registers)
  (ok : bool)


/- Instructions -/
inductive instr : Type
/- | add32 : (dst: nat) -> (src1:nat) -> (src2:nat) -> instr -/
| add32 : nat -> nat -> nat -> instr
/-| mov32 : (dst:nat) -> (src:nat) -> instr -/
| mov32 : nat -> nat -> instr

/- Top-level code definitions -/
inductive code : Type 
| Ins : instr -> code
| Block : list code -> code

/- Instruction semantics -/
def eval_ins32 : instr -> state -> state -> bool
| (instr.add32 dst src1 src2) s r := 
  let new_regs := s.regs { dst ↦ (s.regs src1) + (s.regs src2) } in
  r = { regs := new_regs, ok := s.ok }
| (instr.mov32 dst src) s r := tt


/- Code semantics -/

-/
end otbn

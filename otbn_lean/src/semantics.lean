import topology.basic
/- #check topological_space -/
import data.zmod.basic 

namespace otbn
set_option pp.beta true

/-! Basic types -/
/- def uint32 := {i : ℕ // i ≤ 0x100000000} -/
def uint32 := zmod 0x100000000

/-! Register definitions and lemmas adapted from lovelib.lean's definition of state -/
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

def registers.eq (r0 r1:registers) : bool :=
  ∀ i . 0 ≤ i ∧ i < 32 → r0 i = r1 i

/-! State definition -/
structure state : Type :=
  (regs : registers)
  (ok : bool)


/-! Instructions -/
inductive instr : Type
/- | add32 : (dst: nat) -> (src1:nat) -> (src2:nat) -> instr -/
| add32 : nat -> nat -> nat -> instr
/--| mov32 : (dst:nat) -> (src:nat) -> instr -/
| mov32 : nat -> nat -> instr

/-! Top-level code definitions -/
inductive code : Type 
| Ins : instr -> code
| Block : list code -> code

/-! Instruction semantics -/
def eval_ins32 : instr -> state -> state -> bool
| (instr.add32 dst src1 src2) s r := 
  let sum : nat := zmod.val (s.regs src1) + zmod.val (s.regs src2) in
  let sum32 : uint32 := sum % 0x100000000 in
  let new_regs := s.regs { dst ↦ sum32 } in
  r = { regs := new_regs, ok := s.ok }
| (instr.mov32 dst src) s r := tt


/-! Code semantics -/

end otbn
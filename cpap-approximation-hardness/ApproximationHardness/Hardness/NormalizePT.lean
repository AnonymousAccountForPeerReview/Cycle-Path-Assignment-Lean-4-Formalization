module

public import ApproximationHardness.Hardness.Normalize
public import PT.All

/-!
# The normalization is polynomial-time

`normalize` is polynomial-time on codes (`pt_normalize`), in the `PT` framework of the
MaxSNP-completeness formalization: the code of a formula is `SAT.encode`.
-/

@[expose] public section

namespace STACS2027.Hardness

open Complexity Complexity.PT

theorem pt_unitGadget : PT (fun q : Nat × Nat × SAT.Literal => unitGadget q.1 q.2.1 q.2.2) := by
  unfold unitGadget
  fun_prop

@[fun_prop] theorem PT.unitGadget' {α : Type} [Code α] {b i : α → Nat} {l : α → SAT.Literal}
    (hb : PT b) (hi : PT i) (hl : PT l) : PT (fun a => unitGadget (b a) (i a) (l a)) :=
  pt_unitGadget.comp (PT.pair hb (PT.pair hi hl))

theorem pt_normClause : PT (fun q : Nat × (SAT.Clause × Nat) => normClause q.1 q.2) := by
  unfold normClause
  fun_prop

@[fun_prop] theorem PT.normClause' {α : Type} [Code α] {b : α → Nat} {p : α → SAT.Clause × Nat}
    (hb : PT b) (hp : PT p) : PT (fun a => normClause (b a) (p a)) :=
  pt_normClause.comp (PT.pair hb hp)

/-- `normalize` is polynomial-time. -/
theorem pt_normalize : PT normalize := by
  have : PT (fun f : SAT.CNF => (f.zipIdx 0).flatMap (normClause (SAT.variableBound f))) := by
    fun_prop
  exact this.of_eq fun f => rfl

end STACS2027.Hardness

module

public import ApproximationHardness.PolarizeLReduction
public import PT.All

/-!
# Lemma 10's recovery map is polynomial-time

The assignment `recover f b` of Lemma 10 ("undo the complementations and restore the eliminated
variables"), evaluated at a variable, is polynomial-time in the formula, the variable, and an
assignment given by a polynomial-time function (`PT.recover'`).
-/

@[expose] public section

namespace STACS2027.Hardness

open Complexity Complexity.PT

theorem pt_occurrences :
    PT (fun q : SAT.CNF × Nat × Bool => STACS2027.occurrences q.1 q.2.1 q.2.2) := by
  unfold STACS2027.occurrences
  fun_prop

@[fun_prop] theorem PT.occurrences' {α : Type} [Code α] {f : α → SAT.CNF} {v : α → Nat}
    {p : α → Bool} (hf : PT f) (hv : PT v) (hp : PT p) :
    PT (fun a => STACS2027.occurrences (f a) (v a) (p a)) :=
  pt_occurrences.comp (PT.pair hf (PT.pair hv hp))

theorem pt_pureThree : PT (fun q : SAT.CNF × Nat => pureThree q.1 q.2) := by
  unfold pureThree
  fun_prop

@[fun_prop] theorem PT.pureThree' {α : Type} [Code α] {f : α → SAT.CNF} {v : α → Nat}
    (hf : PT f) (hv : PT v) : PT (fun a => pureThree (f a) (v a)) :=
  pt_pureThree.comp (PT.pair hf hv)

theorem pt_pureValue : PT (fun q : SAT.CNF × Nat => pureValue q.1 q.2) := by
  unfold pureValue
  fun_prop

@[fun_prop] theorem PT.pureValue' {α : Type} [Code α] {f : α → SAT.CNF} {v : α → Nat}
    (hf : PT f) (hv : PT v) : PT (fun a => pureValue (f a) (v a)) :=
  pt_pureValue.comp (PT.pair hf hv)

theorem pt_tautological : PT tautological := by
  unfold tautological
  fun_prop

@[fun_prop] theorem PT.tautological' {α : Type} [Code α] {c : α → SAT.Clause} (hc : PT c) :
    PT (fun a => tautological (c a)) :=
  pt_tautological.comp hc

theorem pt_deleted : PT (fun q : SAT.CNF × SAT.Clause => deleted q.1 q.2) := by
  unfold deleted
  fun_prop

@[fun_prop] theorem PT.deleted' {α : Type} [Code α] {f : α → SAT.CNF} {c : α → SAT.Clause}
    (hf : PT f) (hc : PT c) : PT (fun a => deleted (f a) (c a)) :=
  pt_deleted.comp (PT.pair hf hc)

theorem pt_kept : PT kept := by
  unfold kept
  fun_prop

@[fun_prop] theorem PT.kept' {α : Type} [Code α] {f : α → SAT.CNF} (hf : PT f) :
    PT (fun a => kept (f a)) :=
  pt_kept.comp hf

theorem pt_complemented : PT (fun q : SAT.CNF × Nat => complemented q.1 q.2) := by
  unfold complemented
  fun_prop

@[fun_prop] theorem PT.complemented' {α : Type} [Code α] {f : α → SAT.CNF} {v : α → Nat}
    (hf : PT f) (hv : PT v) : PT (fun a => complemented (f a) (v a)) :=
  pt_complemented.comp (PT.pair hf hv)

/-- `recover f b v`, for an assignment `b` given in uncurried form. -/
@[fun_prop] theorem PT.recover' {α : Type} [Code α] {f : α → SAT.CNF} {b : α → SAT.Assignment}
    {v : α → Nat} (hf : PT f) (hb : PT (fun q : α × Nat => b q.1 q.2)) (hv : PT v) :
    PT (fun a => recover (f a) (b a) (v a)) := by
  have hb' : PT (fun a => b a (v a)) := hb.comp (PT.pair PT.id hv)
  have : PT (fun a => if pureThree (f a) (v a) then pureValue (f a) (v a)
      else if complemented (f a) (v a) then !(b a (v a)) else b a (v a)) := by
    fun_prop
  exact this.of_eq fun a => rfl

end STACS2027.Hardness

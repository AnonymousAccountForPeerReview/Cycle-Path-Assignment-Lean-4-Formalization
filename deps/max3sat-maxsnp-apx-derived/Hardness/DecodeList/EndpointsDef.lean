module

public import Hardness.DecodeList.Common

/-!
# List forms of the two endpoint decoders: definitions and polynomial time

* `finalList vertices y` is the list program for `Decode.finalDecode` (§1 of
  `Hardness/Decode/NOTES.md`): the label of the vertex `v < vertices` is
  `Σ_{j<6} [y_{6v+j}] 2^j`, where `y_i = SAT.assignmentOf y i` is the `i`-th bit of the
  assignment word (`false` beyond its end).
* `initialList nvars L` is the list program for `Decode.initialDecode` (§3): the value of the
  variable `x < nvars` is bit `0` of `L[x]`.

The equalities with `finalDecode` and `initialDecode` are proved in
`Hardness/DecodeList/Endpoints.lean`.
-/

@[expose] public section

set_option linter.dupNamespace false

namespace Complexity.DecodeList

open Complexity.PT

/-! ### Final stage -/

/-- The label of the vertex `v` read off the assignment word `y`: the number with binary digits
`y_{6v}, …, y_{6v+5}`, least significant first. -/
def finalLabel (y : Word) (v : Nat) : Nat :=
  (SAT.assignmentOf y (6 * v)).toNat + 2 * (SAT.assignmentOf y (6 * v + 1)).toNat +
    4 * (SAT.assignmentOf y (6 * v + 2)).toNat + 8 * (SAT.assignmentOf y (6 * v + 3)).toNat +
    16 * (SAT.assignmentOf y (6 * v + 4)).toNat + 32 * (SAT.assignmentOf y (6 * v + 5)).toNat

/-- List form of `finalDecode`: `y` is the assignment word; vertex `v` gets
`Σ_{j<6} [y_{6v+j}] 2^j`. -/
def finalList (vertices : Nat) (y : Word) : List Nat :=
  (List.range vertices).map (finalLabel y)

@[simp] theorem finalList_length (vertices : Nat) (y : Word) :
    (finalList vertices y).length = vertices := by
  simp [finalList]

theorem pt_finalLabel : PT (fun p : Word × Nat => finalLabel p.1 p.2) := by
  unfold finalLabel
  fun_prop

@[fun_prop] protected theorem PT.finalLabel {α : Type} [Code α] {y : α → Word} {v : α → Nat}
    (hy : PT y) (hv : PT v) : PT (fun a => finalLabel (y a) (v a)) :=
  PT.comp (f := fun p : Word × Nat => finalLabel p.1 p.2) (g := fun a => (y a, v a))
    pt_finalLabel (PT.pair hy hv)

/-- The list form of `finalDecode` is polynomial-time. -/
theorem pt_finalList : PT (fun p : Nat × Word => finalList p.1 p.2) := by
  unfold finalList
  fun_prop

/-! ### Initial stage -/

/-- List form of `initialDecode`: variable `x` gets bit `0` of `L[x]`. -/
def initialList (nvars : Nat) (L : List Nat) : Word :=
  (List.range nvars).map fun x => (L.getD x 0).testBit 0

@[simp] theorem initialList_length (nvars : Nat) (L : List Nat) :
    (initialList nvars L).length = nvars := by
  simp [initialList]

/-- The list form of `initialDecode` is polynomial-time. -/
theorem pt_initialList : PT (fun p : Nat × List Nat => initialList p.1 p.2) := by
  have h : PT (fun p : Nat × List Nat =>
      (List.range p.1).map fun x => decide (p.2.getD x 0 % 2 = 1)) := by
    fun_prop
  refine h.of_eq fun p => ?_
  unfold initialList
  simp only [Nat.testBit_zero]

end Complexity.DecodeList

module

public import Hardness.DecodeList.Common

/-!
# List form of the cloud-majority decoder: definition and polynomial time

`cloudList vertices tails sigma` is the list program for `Decode.roundPreprocessed` (Step C of
`Hardness/Decode/NOTES.md` §2).  From the tail column `tails` of a table with `vertices` vertices
it computes

* the cloud sizes `c_v = tails.count v`;
* the padded sizes `paddedSizeG g c` (`0` for `c = 0`, otherwise the least power of `g` that is
  `≥ c`, found by at most `c` multiplications by `g`, never exceeding `g * c`);
* the list `cloudOwners g vertices tails` of the owners of all regular vertices: the tails of the
  darts, followed, for `v = 0, 1, …, vertices - 1`, by `padding(v) = paddedSizeG g c_v - c_v`
  copies of `v`;

and returns, for every `v < vertices`, the least `a < 64` maximising the number of positions
`z` with `owners[z] = v` and `sigma[z] = a`.

The growth factor `g` is a parameter of the generic program `cloudListG`; `cloudList` is its
instance at the constant `cloudGrowth` (the value of `ExpanderFamily.growth`), which is never
evaluated: the polynomial-time proof is uniform in `g`.

The equality with `roundPreprocessed` is proved in `Hardness/DecodeList/Cloud.lean`.
-/

@[expose] public section

set_option linter.dupNamespace false

namespace Complexity.DecodeList

open Complexity.PT
open OAI.UniqueGamesTheorem.Foundations.PCP.Decode

/-! ### The program -/

/-- The growth factor of the cloud expander family (`ExpanderFamily.growth = baseDegree ^ 4`,
`baseDegree = (2 ^ 16) ^ 7`), as a plain arithmetic expression. -/
def cloudGrowth : Nat := ((2 ^ 16) ^ 7) ^ 4

/-- One step of the search for the least power of `g` that is `≥ c`. -/
def padStep (g c s : Nat) : Nat := if c ≤ s then s else s * g

/-- Padded cloud size: `0` for an empty cloud, otherwise the result of at most `c`
multiplications by `g` starting from `1`, stopping at the first value `≥ c`. -/
def paddedSizeG (g c : Nat) : Nat := if c = 0 then 0 else (padStep g c)^[c] 1

/-- Number of dummy darts added to the cloud of `v`. -/
def cloudPadding (g : Nat) (tails : List Nat) (v : Nat) : Nat :=
  paddedSizeG g (tails.count v) - tails.count v

/-- Owners of the regular vertices: the tails of the darts, then `cloudPadding g tails v` copies
of `v` for `v = 0, …, vertices - 1`. -/
def cloudOwners (g vertices : Nat) (tails : List Nat) : List Nat :=
  tails ++ (List.range vertices).flatMap fun v => List.replicate (cloudPadding g tails v) v

/-- Number of positions `z` with `owners[z] = v` and `sigma[z] = a`. -/
def cloudCountList (owners sigma : List Nat) (v a : Nat) : Nat :=
  (owners.zip sigma).countP fun q => decide (q.1 = v ∧ q.2 = a)

/-- The cloud-majority program with growth factor `g`. -/
def cloudListG (g vertices : Nat) (tails sigma : List Nat) : List Nat :=
  (List.range vertices).map fun v =>
    argMaxUpTo (cloudCountList (cloudOwners g vertices tails) sigma v) 63

/-- List form of `roundPreprocessed`: `vertices` is `t.vertices`, `tails` the tail column
(so `t.darts = tails.length`), `sigma` the labeling of the preprocessed table as a list. -/
def cloudList (vertices : Nat) (tails : List Nat) (sigma : List Nat) : List Nat :=
  cloudListG cloudGrowth vertices tails sigma

@[simp] theorem cloudListG_length (g vertices : Nat) (tails sigma : List Nat) :
    (cloudListG g vertices tails sigma).length = vertices := by
  simp [cloudListG]

@[simp] theorem cloudList_length (vertices : Nat) (tails sigma : List Nat) :
    (cloudList vertices tails sigma).length = vertices :=
  cloudListG_length _ _ _ _

/-! ### Size of the padded sizes -/

theorem padStep_iterate_le (g c i : Nat) : (padStep g c)^[i] 1 ≤ g * c + 1 := by
  have key : ∀ i, (padStep g c)^[i] 1 = 1 ∨ (padStep g c)^[i] 1 ≤ g * c := by
    intro i
    induction i with
    | zero => exact Or.inl rfl
    | succ i ih =>
      rw [Function.iterate_succ_apply']
      unfold padStep
      split
      · exact ih
      · rename_i h
        refine Or.inr ?_
        rw [Nat.mul_comm]
        exact Nat.mul_le_mul_left g (Nat.le_of_lt (Nat.lt_of_not_ge h))
  rcases key i with h | h <;> omega

theorem paddedSizeG_le (g c : Nat) : paddedSizeG g c ≤ g * c + 1 := by
  unfold paddedSizeG
  split
  · exact Nat.zero_le _
  · exact padStep_iterate_le g c c

/-! ### Polynomial time -/

variable {α : Type} [Code α]

theorem pt_paddedSizeG (g : Nat) : PT (fun c : Nat => paddedSizeG g c) := by
  have hstep : PT (fun p : Nat × Nat => padStep g p.1 p.2) := by
    unfold padStep
    fun_prop
  have hiter : PT (fun c : Nat => (padStep g c)^[c] 1) := by
    refine PT.iterate (step := fun c s => padStep g c s) (init := fun _ => 1) (n := fun c => c)
      hstep (PT.const 1) PT.id (fun N => g * N + 2)
      (((PolynomialBound.constant g).mul PolynomialBound.identity).add
        (PolynomialBound.constant 2)) ?_
    intro c i _
    have h1 : (fun s => padStep g c s)^[i] 1 ≤ g * c + 1 := padStep_iterate_le g c i
    have h2 : g * c ≤ g * (c + 1) := Nat.mul_le_mul_left g (Nat.le_succ c)
    simp only [size_nat]
    omega
  unfold paddedSizeG
  fun_prop

@[fun_prop] protected theorem PT.paddedSizeG (g : Nat) {c : α → Nat} (hc : PT c) :
    PT (fun a => paddedSizeG g (c a)) :=
  (pt_paddedSizeG g).comp hc

theorem pt_cloudPadding (g : Nat) :
    PT (fun p : List Nat × Nat => cloudPadding g p.1 p.2) := by
  unfold cloudPadding
  fun_prop

@[fun_prop] protected theorem PT.cloudPadding (g : Nat) {tails : α → List Nat} {v : α → Nat}
    (ht : PT tails) (hv : PT v) : PT (fun a => cloudPadding g (tails a) (v a)) :=
  (pt_cloudPadding g).comp (PT.pair ht hv)

theorem pt_cloudOwners (g : Nat) :
    PT (fun p : Nat × List Nat => cloudOwners g p.1 p.2) := by
  unfold cloudOwners
  fun_prop

@[fun_prop] protected theorem PT.cloudOwners (g : Nat) {n : α → Nat} {tails : α → List Nat}
    (hn : PT n) (ht : PT tails) : PT (fun a => cloudOwners g (n a) (tails a)) :=
  (pt_cloudOwners g).comp (PT.pair hn ht)

theorem pt_cloudCountList :
    PT (fun p : (List Nat × List Nat) × Nat × Nat => cloudCountList p.1.1 p.1.2 p.2.1 p.2.2) := by
  unfold cloudCountList
  fun_prop

@[fun_prop] protected theorem PT.cloudCountList {owners sigma : α → List Nat} {v b : α → Nat}
    (ho : PT owners) (hs : PT sigma) (hv : PT v) (hb : PT b) :
    PT (fun a => cloudCountList (owners a) (sigma a) (v a) (b a)) :=
  pt_cloudCountList.comp (PT.pair (PT.pair ho hs) (PT.pair hv hb))

/-- The cloud-majority program is polynomial-time, for every growth factor. -/
theorem pt_cloudListG (g : Nat) :
    PT (fun p : Nat × List Nat × List Nat => cloudListG g p.1 p.2.1 p.2.2) := by
  unfold cloudListG
  have hcount : PT (fun r : ((Nat × List Nat × List Nat) × Nat) × Nat =>
      cloudCountList (cloudOwners g r.1.1.1 r.1.1.2.1) r.1.1.2.2 r.1.2 r.2) := by
    fun_prop
  have hsel : PT (fun q : (Nat × List Nat × List Nat) × Nat =>
      argMaxUpTo (cloudCountList (cloudOwners g q.1.1 q.1.2.1) q.1.2.2 q.2) 63) :=
    PT.argMaxUpTo
      (count := fun (q : (Nat × List Nat × List Nat) × Nat) a => cloudCountList (cloudOwners g q.1.1 q.1.2.1) q.1.2.2 q.2 a)
      (k := fun _ => 63) hcount (PT.const 63)
  exact PT.map (f := fun (p : Nat × List Nat × List Nat) v =>
    argMaxUpTo (cloudCountList (cloudOwners g p.1 p.2.1) p.2.2 v) 63)
    (l := fun p => List.range p.1) hsel (PT.range PT.fst')

/-- The list form of `roundPreprocessed` is polynomial-time. -/
theorem pt_cloudList : PT (fun p : Nat × List Nat × List Nat => cloudList p.1 p.2.1 p.2.2) :=
  pt_cloudListG cloudGrowth

end Complexity.DecodeList

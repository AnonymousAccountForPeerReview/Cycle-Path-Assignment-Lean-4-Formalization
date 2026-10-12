module

public import NPHardness.SourceReduction
public import Complexity.RestrictedSATComplete
public import Complexity.PlanarSATComplete

/-!
Adapters to the unchanged NP-completeness foundation (`NPCompleteness-Lean4`),
at commit 3e603e795b44fedcf7d6dd65b7d1e30547ead925.
The signed occurrence bounds count multiplicity on both sides. These results
do not combine the separate planarity and occurrence restrictions into a
planar bounded-occurrence hardness theorem.
-/

@[expose] public section
namespace STACS2027
open Complexity Complexity.SAT

theorem occurrences_registered_positive (f : CNF) (v : Nat) :
    occurrences f v true =
      (f.flatten.filter fun l => l.positive && Nat.beq l.var v).length := by
  unfold occurrences
  congr 2
  funext l
  apply Bool.eq_iff_iff.mpr
  cases l.positive <;> simp [Nat.beq_eq]

theorem occurrences_registered_negative (f : CNF) (v : Nat) :
    occurrences f v false =
      (f.flatten.filter fun l => !l.positive && Nat.beq l.var v).length := by
  unfold occurrences
  congr 2
  funext l
  apply Bool.eq_iff_iff.mpr
  cases l.positive <;> simp [Nat.beq_eq]

/-- The manuscript's exact Definition 7 agrees with the registered restriction. -/
theorem boundedOccurrence_iff_registered (f : CNF) :
    BoundedOccurrence f ↔ IsLeOneLeTwoCNF f := by
  simp only [BoundedOccurrence, IsLeOneLeTwoCNF,
    occurrences_registered_positive, occurrences_registered_negative]
  constructor
  · rintro ⟨hc, hp, hn⟩
    exact ⟨fun c h => by have := hc c h; omega, fun v => ⟨hp v, hn v⟩⟩
  · rintro ⟨hc, h⟩
    exact ⟨fun c hmem => by have := hc c hmem; omega,
      fun v => (h v).1, fun v => (h v).2⟩

end STACS2027

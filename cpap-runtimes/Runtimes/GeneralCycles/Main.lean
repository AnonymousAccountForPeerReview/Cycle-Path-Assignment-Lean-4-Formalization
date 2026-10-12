module

public import Runtimes.GeneralCycles.Validity
public import Runtimes.GeneralCycles.Polynomial
public import Runtimes.NamedHoles
import Mathlib.Tactic

/-! A uniform label-independent RAM enumerator for every fixed cycle length.
The output contains exactly one representative of each simple cycle, and both
resource bounds have constants independent of the input labels.
Artifact date: 2026-10-12. -/

@[expose] public section

namespace STACS2027.Runtimes.GeneralCycles

open STACS2027 STACS2027.RAM

theorem validCheck_validitySpec (indices values k d B : ℕ)
    (hv : 100 ≤ values) (hd : 40 ≤ d) (hd' : d ≤ 41)
    (hB : validityConstant values k d ≤ B) :
    ValiditySpec (validCheck values k d) indices values k d B := by
  intro g is c₀ S hl hS hc hm hp
  have hregs : ∀ r ∈ registers values k, 100 ≤ r := by
    intro r hr
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hr
    omega
  have h := validRegisters_frozen (g := g) (rs := registers values k) (k := k)
    (d := d) (S := S) c₀ hregs hd (by omega) hS hc hm
  refine h.mono (fun _ he => he) ?_ ?_
  · intro c ⟨hf, ha⟩
    refine ⟨?_, ha.mono ?_⟩
    · change c.reg d = bit (decide (IsCycle g k (tupleLabels g is)))
      simpa only [regValues_registers, Placed.emission_labels hl hp] using hf
    · intro r hr
      simp only [List.mem_cons] at hr
      rcases hr with rfl | hr
      · simp [checkerScratch]
      · simp only [edgeScratch, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [checkerScratch, rT, edgeCounter, edgeAddr, edgeFirst, edgeSecond,
            edgeFound, List.mem_range'_1]
  · exact (validCheck_bound values k d g.length).trans (Nat.mul_le_mul_right _ hB)

def validityBudget (k : ℕ) : ℕ :=
  validityConstant (outerValues k) k acceptanceFlag +
    validityConstant (innerValues k) k innerValidFlag

def cycleEnumerator (k : ℕ) : Stmt :=
  enumerateProgram (validCheck (outerValues k) k acceptanceFlag)
    (validCheck (innerValues k) k innerValidFlag) k

def cycleEnumeratorConstant (k : ℕ) : ℕ := programConstant k (validityBudget k)

theorem cycleEnumerator_correct (k : ℕ) (g : Graph) :
    ∃ (cs : List Cycle) (steps : ℕ), cs.Perm (cycles g k) ∧
      ComputesIn (cycleEnumerator k) (graphInput g) cs.flatten steps
        (cycleEnumeratorConstant k * (g.length + 1) ^ (2 * k + 4)) ∧
      steps ≤ cycleEnumeratorConstant k * (g.length + 1) ^ (2 * k + 4) := by
  have ho : ValiditySpec (validCheck (outerValues k) k acceptanceFlag)
      outerIndices (outerValues k) k acceptanceFlag (validityBudget k) :=
    validCheck_validitySpec _ _ _ _ _ (by simp [outerValues]) (by decide) (by decide)
      (Nat.le_add_right _ _)
  have hi : ValiditySpec (validCheck (innerValues k) k innerValidFlag)
      (innerIndices k) (innerValues k) k innerValidFlag (validityBudget k) :=
    validCheck_validitySpec _ _ _ _ _ (by simp [innerValues]) (by decide) (by decide)
      (Nat.le_add_left _ _)
  exact enumerateProgram_polynomial ho hi g

end STACS2027.Runtimes.GeneralCycles

namespace STACS2027.Runtimes

open STACS2027 STACS2027.RAM

/-- Every fixed cycle length admits a uniform polynomial-time RAM enumeration
with resource bounds independent of the numeric vertex labels. -/
theorem generalCycleEnumerationRam : GeneralCycleEnumerationRam := by
  intro k _
  exact ⟨GeneralCycles.cycleEnumerator k, GeneralCycles.cycleEnumeratorConstant k,
    GeneralCycles.cycleEnumerator_correct k⟩

end STACS2027.Runtimes

module

public import Outerplanar.Algo.Combine
import Mathlib.Tactic

/-!
# Optimal outputs of a `K₄` block

`k4Out k [a, b, c, d]`: for `k = 3` the four triangles of the `K₄` on `a, b, c, d`, each
written from the vertex its path (a single edge) omits, the four paths being distinct; for
`k = 4` the three four-cycles, written from the vertices omitted by the paths of Section 8's
`k4Assignment` (`{ab, bc}`, `{bd, cd}`, `{ad, ac}`); otherwise nothing. The output is
optimal, of cost zero (`optimalAssignmentOutput_k4Out`): checked on `k4` by evaluation, then
renamed (`optimalAssignmentOutput_relabel`).
-/

@[expose] public section

namespace STACS2027.Algo

/-- The output cycles on the `K₄` on `0, 1, 2, 3`. -/
def k4Base (k : ℕ) : List Cycle :=
  if k = 3 then [[0, 1, 2], [1, 0, 3], [3, 0, 2], [1, 2, 3]]
  else if k = 4 then [[3, 0, 1, 2], [0, 1, 3, 2], [1, 3, 0, 2]]
  else []

/-- The output cycles on the `K₄` on the vertices `vs = [a, b, c, d]`. -/
def k4Out (k : ℕ) (vs : List ℕ) : List (List ℕ) :=
  (k4Base k).map (List.map fun i => vs.getD i 0)

theorem k4Out_three (a b c d : ℕ) :
    k4Out 3 [a, b, c, d] = [[a, b, c], [b, a, d], [d, a, c], [b, c, d]] := rfl

theorem k4Out_four (a b c d : ℕ) :
    k4Out 4 [a, b, c, d] = [[d, a, b, c], [a, b, d, c], [b, d, a, c]] := rfl

theorem k4Out_large {k : ℕ} (hk : 5 ≤ k) (vs : List ℕ) : k4Out k vs = [] := by
  simp [k4Out, k4Base, show k ≠ 3 by omega, show k ≠ 4 by omega]

namespace Comb

theorem k4Base_three :
    (∀ c ∈ k4Base 3, IsCycle k4 3 c) ∧ (k4Base 3).Pairwise (fun c d => ¬ SameCycle c d) ∧
      (∀ c ∈ cycles k4 3, ∃ d ∈ k4Base 3, SameCycle c d) ∧
      cost ((k4Base 3).map fun c => selected c 0) = 0 := by
  decide

theorem k4Base_four :
    (∀ c ∈ k4Base 4, IsCycle k4 4 c) ∧ (k4Base 4).Pairwise (fun c d => ¬ SameCycle c d) ∧
      (∀ c ∈ cycles k4 4, ∃ d ∈ k4Base 4, SameCycle c d) ∧
      cost ((k4Base 4).map fun c => selected c 0) = 0 := by
  decide

theorem k4Base_output_of {k : ℕ}
    (h : (∀ c ∈ k4Base k, IsCycle k4 k c) ∧ (k4Base k).Pairwise (fun c d => ¬ SameCycle c d) ∧
      (∀ c ∈ cycles k4 k, ∃ d ∈ k4Base k, SameCycle c d) ∧
      cost ((k4Base k).map fun c => selected c 0) = 0) :
    OptimalAssignmentOutput k4 k (k4Base k).flatten := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine optimalAssignmentOutput_of_cost_zero h1 h2 (fun c hc => ?_) h4
  obtain ⟨d, hd, hs⟩ := isCycle_represented hc
  obtain ⟨d', hd', hs'⟩ := h3 d hd
  exact ⟨d', hd', hs.trans hs'⟩

/-- The output on `k4` is optimal. -/
theorem k4Base_output {k : ℕ} : OptimalAssignmentOutput k4 k (k4Base k).flatten := by
  rcases (by omega : k = 3 ∨ k = 4 ∨ k ≠ 3 ∧ k ≠ 4) with rfl | rfl | ⟨h3, h4⟩
  · exact k4Base_output_of k4Base_three
  · exact k4Base_output_of k4Base_four
  · have hnil : k4Base k = [] := by simp [k4Base, h3, h4]
    rw [hnil]
    refine optimalAssignmentOutput_of_cost_zero (by simp) (by simp) (fun c hc => ?_) rfl
    have := hc.length_le_vertices k4_verticesBelow
    have := hc.1
    exfalso
    omega

end Comb

open Comb

/-- **`K₄` outputs**: for a graph `B` whose simple graph is the `K₄` on the distinct
vertices `a, b, c, d`, `k4Out k [a, b, c, d]` writes an optimal output (of cost zero). -/
theorem optimalAssignmentOutput_k4Out {B : Graph} {a b c d : ℕ} (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hadj : ∀ u v, Adj B u v ↔
      u ≠ v ∧ (u = a ∨ u = b ∨ u = c ∨ u = d) ∧ (v = a ∨ v = b ∨ v = c ∨ v = d))
    (k : ℕ) : OptimalAssignmentOutput B k (k4Out k [a, b, c, d]).flatten := by
  let t : ℕ → ℕ := fun i => [a, b, c, d].getD i 0
  have t0 : t 0 = a := rfl
  have t1 : t 1 = b := rfl
  have t2 : t 2 = c := rfl
  have t3 : t 3 = d := rfl
  have ht : ∀ i, i < 4 → ∀ j, j < 4 → t i = t j → i = j := by
    intro i hi j hj hij
    interval_cases i <;> interval_cases j <;> simp_all
  have he : ∀ x y, x ≠ y → (edge x y ∈ B ↔ edge x y ∈ mapGraph t k4) := by
    intro x y hxy
    have h1 : edge x y ∈ B ↔ Adj B x y := ⟨fun h => ⟨hxy, h⟩, fun h => h.2⟩
    rw [h1, hadj, mem_mapGraph_k4, t0, t1, t2, t3]
    simp only [edge_eq_iff]
    constructor
    · rintro ⟨-, hx, hy⟩
      rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;> simp_all
    · intro h
      refine ⟨hxy, ?_⟩
      rcases h with (⟨h1, h2⟩ | ⟨h1, h2⟩) | (⟨h1, h2⟩ | ⟨h1, h2⟩) | (⟨h1, h2⟩ | ⟨h1, h2⟩) |
        (⟨h1, h2⟩ | ⟨h1, h2⟩) | (⟨h1, h2⟩ | ⟨h1, h2⟩) | (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> simp [h1, h2]
  have h := optimalAssignmentOutput_relabel k4_verticesBelow k4_normalized t ht he
    (k4Base_output (k := k))
  rwa [List.map_flatten] at h

end STACS2027.Algo

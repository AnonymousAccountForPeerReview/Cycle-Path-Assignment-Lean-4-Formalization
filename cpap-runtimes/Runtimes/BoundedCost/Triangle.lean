module

public import Runtimes.Flow.SortTri
import BoundedCost.Algorithm3Search
import Mathlib.Tactic

/-!
# Theorem 4 for `k = 3`, under the min-cost flow hypothesis: the optimization form

Algorithm 3 treats `k ≤ 4` by min-cost flow (Section 3): it computes an optimal assignment and
compares its cost with `Ψ`. The machine of `Runtimes/BoundedCost/Main.lean` covers `k ≥ 4` through
Almost 2-SAT; for `k = 3` the triangle pipeline with the sorting front end
(`triangle_sort_single`, `Runtimes/Flow/SortTri.lean`, with the cited min-cost flow program `F`
as the explicit hypothesis `MinCostFlowSolver F T`) computes the positions of an optimal
assignment, and an optimal cost answers every budget (`optCost_budget`). This file states that
**optimization form**, on Theorem 4's enumeration `cycles g 3`:

* `boundedCost_triangle_opt`: one program writes, within `C (t² + m + 1) + 4 T(21t + 5)` steps and
  the addresses below `C (t + m + 1) + 4 T(21t + 5)`, `t` positions `pos` (each `< 3`) of a valid
  assignment such that for **every** `Ψ`, an assignment of cost `≤ Ψ` exists iff the cost of
  `pos` is `≤ Ψ` (the output is then itself such an assignment);
* `boundedCost_triangle_opt_almostLinear`: with an almost-linear `T` (the cited bound), within
  `C (t² + m + 1)` steps and addresses, inside Theorem 4's `O(k²t + kt² + Υ_k)` term for `k = 3`.

Theorem 4 is a polynomial-time claim, so no program indexes memory by a vertex label: the
construction relabels the vertices by sorting (`Sort.front`, as for `k ≥ 4`), and the memory
bounds have no `labelBound g` term. (Theorem 2 and the triangle corollary, linear-time claims,
keep the label dictionary and `labelBound g`: `Runtimes/Flow/Single.lean`.)

The **decision form** — the machine reads `Ψ`, compares the cost of the optimal assignment with
it, and writes `[0]` or `1 :: pos`, on the same input `boundedCostInput g 3 Ψ` as for `k ≥ 4` — is
`boundedCost_triangle` and `boundedCost_triangle_almostLinear` in `Runtimes/BoundedCost/TriDecide.lean`.
-/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 STACS2027.RAM STACS2027.Runtimes.Flow

/-- An optimal cost answers every budget. -/
theorem optCost_budget {g : Graph} {k C : ℕ} (h : OptCost g k C) (Ψ : ℕ) :
    HasAssignment g k Ψ ↔ C ≤ Ψ :=
  ⟨fun hΨ => h.2 Ψ hΨ, fun hC => hasAssignment_mono hC h.1⟩

/-- **Theorem 4 for `k = 3`, optimization form** (with the cited min-cost flow program `F`,
running in time `T` and the addresses below `T`): one program and one constant `C` such that for
every graph `g`, on `flowInput g (cycles g 3) 3` (the graph, `3`, `t` and the enumerated simple
triangles) the program writes positions `pos` (one per triangle, each `< 3`) within
`C (t² + m + 1) + 4 T(21t + 5)` steps, accessing only the addresses below
`C (t + m + 1) + 4 T(21t + 5)` (no memory indexed by a vertex label); the paths
`selected C_i pos_i` are a valid assignment, and for every budget `Ψ`, an assignment of cost at
most `Ψ` exists iff their cost is at most `Ψ`. -/
theorem boundedCost_triangle_opt {F : RAM.Stmt} {T : ℕ → ℕ} (hF : MinCostFlowSolver F T) :
    ∃ (prog : RAM.Stmt) (C : ℕ), ∀ g : Graph,
      ∃ (pos : List ℕ) (steps : ℕ),
        RAM.ComputesIn prog (flowInput g (cycles g 3) 3) pos steps
          (C * ((cycles g 3).length + g.length + 1) + 4 * T (21 * (cycles g 3).length + 5)) ∧
        steps ≤ C * ((cycles g 3).length * (cycles g 3).length + g.length + 1) +
          4 * T (21 * (cycles g 3).length + 5) ∧
        pos.length = (cycles g 3).length ∧ (∀ p ∈ pos, p < 3) ∧
        ValidChoices ((cycles g 3).map selectedOptions) (List.zipWith selected (cycles g 3) pos) ∧
        ∀ Ψ : ℕ, HasAssignment g 3 Ψ ↔ cost (List.zipWith selected (cycles g 3) pos) ≤ Ψ := by
  obtain ⟨prog, C, h⟩ := triangle_sort_single hF
  refine ⟨prog, C, fun g => ?_⟩
  obtain ⟨pos, steps, hc, hs, hl, hlt, hv, hopt⟩ := h g
  exact ⟨pos, steps, hc, hs, hl, hlt, hv, optCost_budget hopt⟩

/-- `(C₀ x + C y : ℝ) ≤ (C₀ + ⌈C⌉) (x + y)` in `ℕ`, for the conversion of the almost-linear
bounds with `ε = 1`. -/
theorem real_bound_le {v C₀ a b : ℕ} {C : ℝ} (hv : (v : ℝ) ≤ C₀ * (a : ℝ) + C * (b : ℝ)) :
    v ≤ (C₀ + ⌈C⌉₊) * (a + b) := by
  have h3 : C * (b : ℝ) ≤ (⌈C⌉₊ : ℝ) * (b : ℝ) :=
    mul_le_mul_of_nonneg_right (Nat.le_ceil C) (Nat.cast_nonneg _)
  have h4 : (0 : ℝ) ≤ (⌈C⌉₊ : ℝ) * (a : ℝ) := by positivity
  have h5 : (0 : ℝ) ≤ (C₀ : ℝ) * (b : ℝ) := by positivity
  have : (v : ℝ) ≤ ((C₀ + ⌈C⌉₊ : ℕ) : ℝ) * ((a + b : ℕ) : ℝ) := by
    push_cast
    nlinarith
  exact_mod_cast this

/-- **Theorem 4 for `k = 3`, optimization form, with an almost-linear min-cost flow program**:
within `C (t² + m + 1)` steps (inside the term `O(kt² + Υ_k)` of Theorem 4's bound) and the
addresses below `C (t² + m + 1)`. -/
theorem boundedCost_triangle_opt_almostLinear {F : RAM.Stmt} {T : ℕ → ℕ}
    (hF : MinCostFlowSolver F T) (hT : AlmostLinear T) :
    ∃ (prog : RAM.Stmt) (C : ℕ), ∀ g : Graph,
      ∃ (pos : List ℕ) (steps : ℕ),
        RAM.ComputesIn prog (flowInput g (cycles g 3) 3) pos steps
          (C * ((cycles g 3).length * (cycles g 3).length + g.length + 1)) ∧
        steps ≤ C * ((cycles g 3).length * (cycles g 3).length + g.length + 1) ∧
        pos.length = (cycles g 3).length ∧ (∀ p ∈ pos, p < 3) ∧
        ValidChoices ((cycles g 3).map selectedOptions) (List.zipWith selected (cycles g 3) pos) ∧
        ∀ Ψ : ℕ, HasAssignment g 3 Ψ ↔ cost (List.zipWith selected (cycles g 3) pos) ≤ Ψ := by
  obtain ⟨prog, C₀, h⟩ := triangle_sort_single_almostLinear hF hT
  obtain ⟨C, hC⟩ := h 1 one_pos
  refine ⟨prog, 2 * (C₀ + ⌈max C 0⌉₊), fun g => ?_⟩
  obtain ⟨pos, steps, space, hc, hs, hsp, hl, hlt, hv, hopt⟩ := hC g
  set t := (cycles g 3).length
  have h2 : (t : ℝ) ^ ((1 : ℝ) + 1) = ((t * t : ℕ) : ℝ) := by
    rw [show (1 : ℝ) + 1 = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    push_cast; ring
  rw [h2] at hs hsp
  have hCm : C ≤ max C 0 := le_max_left _ _
  have hu : (0 : ℝ) ≤ ((t * t : ℕ) : ℝ) := Nat.cast_nonneg _
  have hm := mul_le_mul_of_nonneg_right hCm hu
  have hs' : (steps : ℝ) ≤ C₀ * ((t * t + g.length + 1 : ℕ) : ℝ) +
      max C 0 * ((t * t : ℕ) : ℝ) := by
    have e : ((t * t + g.length + 1 : ℕ) : ℝ) = ((t * t : ℕ) : ℝ) + g.length + 1 := by
      push_cast; ring
    rw [e]; linarith
  have hsp' : (space : ℝ) ≤ C₀ * ((t + g.length + 1 : ℕ) : ℝ) +
      max C 0 * ((t * t : ℕ) : ℝ) := by
    have e : ((t + g.length + 1 : ℕ) : ℝ) = (t : ℝ) + g.length + 1 := by
      push_cast; ring
    rw [e]; linarith
  have e1 := real_bound_le hs'
  have e2 := real_bound_le hsp'
  have htt : t ≤ t * t + 1 := by nlinarith
  refine ⟨pos, steps, hc.mono (e2.trans ?_), e1.trans ?_, hl, hlt, hv, optCost_budget hopt⟩
  · calc _ ≤ (C₀ + ⌈max C 0⌉₊) * (2 * (t * t + g.length + 1)) :=
          Nat.mul_le_mul_left _ (by omega)
      _ = _ := by ring
  · calc _ ≤ (C₀ + ⌈max C 0⌉₊) * (2 * (t * t + g.length + 1)) :=
          Nat.mul_le_mul_left _ (by omega)
      _ = _ := by ring

end STACS2027.Runtimes.BoundedCost

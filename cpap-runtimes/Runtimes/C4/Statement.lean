module

public import Runtimes.C4.Main
import Mathlib.Tactic

/-!
# Four-cycle listing on the RAM: the statements without `pow43`

The theorems of `Runtimes/C4/Main.lean` state the bounds with `pow43 m = ⌈m^{4/3}⌉`, the least
`X` with `m ^ 4 ≤ X ^ 3`, defined by `Nat.find` (its value contains the proof
`exists_pow43 m`). The forms below state the same bounds for **every** `X` with
`m ^ 4 ≤ X ^ 3`; since `pow43 m` is such an `X` (`pow43_spec`) and every such `X` is at least
`pow43 m` (`pow43_min`), they are equivalent to the originals, and they need no auxiliary
definition. Here `N = numV g` (the vertices on an edge), `m = g.length`,
`t = (cycles g 4).length`, `labelBound g = 1 + the largest label`. Each form bounds the time
`T` and the memory (`RAM.ComputesIn`: the run reads and writes only the addresses below the
space bound, input included); the space bound is the time bound plus `labelBound g` (R0's
label dictionary).

* `fourCycles_ram_semantic`: `T ≤ C · (m + 1 + t + min (N², X))`, space
  `C · (labelBound g + m + 1 + t + min (N², X))`;
* `fourCycles_ram_paper_semantic`: `T ≤ C · (min (N² + t, X + t) + m + 1)`, space
  `C · (labelBound g + min (N² + t, X + t) + m + 1)`;
* `fourCycles_ram_simple_semantic`: for a simple graph given by its edges, each once, smaller end
  first, `T ≤ C · (1 + min (N² + t, X + t))`, space `C · (labelBound g + 1 + min (N² + t, X + t))`.
-/

@[expose] public section

namespace STACS2027.Runtimes.C4

open STACS2027 STACS2027.Algo STACS2027.RAM

/-- The bounds are monotone in `X`: `min (a, pow43 m) ≤ min (a, X)` for every `X ≥ m^{4/3}`. -/
theorem min_pow43_le {a m X : ℕ} (hX : m ^ 4 ≤ X ^ 3) : min a (pow43 m) ≤ min a X :=
  min_le_min le_rfl (pow43_min hX)

/-- **Four-cycle listing** (Corollary 3's enumeration): `cs.flatten` for an order `cs` of
`cycles g 4` within `C (m + 1 + t + min (n², X))` steps, plus `C labelBound g` addresses. -/
theorem fourCycles_ram_semantic :
    ∃ (prog : RAM.Stmt) (C : ℕ), ∀ g : Graph,
      ∃ (out : List ℕ) (T : ℕ),
        (∀ X : ℕ, g.length ^ 4 ≤ X ^ 3 →
          RAM.ComputesIn prog (RAM.graphInput g) out T
            (C * (labelBound g + g.length + 1 + (cycles g 4).length + min (numV g * numV g) X)) ∧
          T ≤ C * (g.length + 1 + (cycles g 4).length + min (numV g * numV g) X)) ∧
        ∃ cs : List Cycle, cs.Perm (cycles g 4) ∧ out = cs.flatten := by
  obtain ⟨prog, C, h⟩ := fourCycles_ram
  refine ⟨prog, C, fun g => ?_⟩
  obtain ⟨out, T, hc, hT, hcs⟩ := h g
  refine ⟨out, T, fun X hX => ⟨hc.mono (Nat.mul_le_mul_left C ?_),
    hT.trans (Nat.mul_le_mul_left C ?_)⟩, hcs⟩
  all_goals have := min_pow43_le (a := numV g * numV g) hX; omega

/-- **Four-cycle listing, paper form**: within `C (min (n² + t, X + t) + m + 1)` steps and the
same bound plus `C labelBound g` addresses, for every `X ≥ m^{4/3}`. -/
theorem fourCycles_ram_paper_semantic :
    ∃ (prog : RAM.Stmt) (C : ℕ), ∀ g : Graph,
      ∃ (out : List ℕ) (T : ℕ),
        (∀ X : ℕ, g.length ^ 4 ≤ X ^ 3 →
          RAM.ComputesIn prog (RAM.graphInput g) out T
            (C * (labelBound g + min (numV g * numV g + (cycles g 4).length)
              (X + (cycles g 4).length) + g.length + 1)) ∧
          T ≤ C * (min (numV g * numV g + (cycles g 4).length) (X + (cycles g 4).length) +
            g.length + 1)) ∧
        ∃ cs : List Cycle, cs.Perm (cycles g 4) ∧ out = cs.flatten := by
  obtain ⟨prog, C, h⟩ := fourCycles_ram_paper
  refine ⟨prog, C, fun g => ?_⟩
  obtain ⟨out, T, hc, hT, hcs⟩ := h g
  refine ⟨out, T, fun X hX => ⟨hc.mono (Nat.mul_le_mul_left C ?_),
    hT.trans (Nat.mul_le_mul_left C ?_)⟩, hcs⟩
  all_goals
    have := pow43_min hX
    have : min (numV g * numV g + (cycles g 4).length) (pow43 g.length + (cycles g 4).length) ≤
        min (numV g * numV g + (cycles g 4).length) (X + (cycles g 4).length) :=
      min_le_min le_rfl (by omega)
    omega

/-- **Four-cycle listing for a simple graph** (its edges, each once, smaller end first): within
`C (1 + min (n² + t, X + t))` steps and that bound plus `C labelBound g` addresses. -/
theorem fourCycles_ram_simple_semantic :
    ∃ (prog : RAM.Stmt) (C : ℕ), ∀ g : Graph, g.Nodup → (∀ e ∈ g, e.1 < e.2) →
      ∃ (out : List ℕ) (T : ℕ),
        (∀ X : ℕ, g.length ^ 4 ≤ X ^ 3 →
          RAM.ComputesIn prog (RAM.graphInput g) out T
            (C * (labelBound g + 1 + min (numV g * numV g + (cycles g 4).length)
              (X + (cycles g 4).length))) ∧
          T ≤ C * (1 + min (numV g * numV g + (cycles g 4).length) (X + (cycles g 4).length))) ∧
        ∃ cs : List Cycle, cs.Perm (cycles g 4) ∧ out = cs.flatten := by
  obtain ⟨prog, C, h⟩ := fourCycles_ram_simple
  refine ⟨prog, C, fun g hnd hlt => ?_⟩
  obtain ⟨out, T, hc, hT, hcs⟩ := h g hnd hlt
  refine ⟨out, T, fun X hX => ⟨hc.mono (Nat.mul_le_mul_left C ?_),
    hT.trans (Nat.mul_le_mul_left C ?_)⟩, hcs⟩
  all_goals
    have := pow43_min hX
    have : min (numV g * numV g + (cycles g 4).length) (pow43 g.length + (cycles g 4).length) ≤
        min (numV g * numV g + (cycles g 4).length) (X + (cycles g 4).length) :=
      min_le_min le_rfl (by omega)
    omega

end STACS2027.Runtimes.C4

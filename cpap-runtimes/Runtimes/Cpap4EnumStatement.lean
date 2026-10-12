module

public import Runtimes.Cpap4Enum
import Runtimes.C4.Statement
import Mathlib.Tactic

/-!
# Corollary 3: the statement without `pow43`

`cpap4_enum_ram` and `cpap4_enum_ram_explicit` (`Runtimes/Cpap4Enum.lean`) state the bounds (time
and memory) with `C4.pow43 m = ⌈m^{4/3}⌉`, defined by `Nat.find`. `cpap4_enum_ram_semantic` and
`cpap4_enum_ram_explicit_semantic` state them for every `X` with `m ^ 4 ≤ X ^ 3`, which is
equivalent (`C4.pow43_spec`, `C4.pow43_min`) and needs no auxiliary definition.
-/

@[expose] public section

namespace STACS2027.Runtimes

open STACS2027 STACS2027.RAM STACS2027.Runtimes.Flow

/-- **Corollary 3**: the listing `E`, then `build`, `F`, `extract` (each on the input followed by
the previous output) take `C (t + m + 1 + min (n², X)) + T(30t + 5)` steps and that bound plus
`C labelBound g` addresses in all, for every `X ≥ m^{4/3}`, and write an optimal assignment. -/
theorem cpap4_enum_ram_explicit_semantic {F : RAM.Stmt} {T : ℕ → ℕ} (hF : MinCostFlowSolver F T) :
    ∃ (E build extract : RAM.Stmt) (C : ℕ), ∀ g : Graph,
      ∃ (cs : List Cycle) (net out pos : List ℕ) (t₀ t₁ t₂ t₃ s₀ s₁ s₂ s₃ : ℕ),
        cs.Perm (cycles g 4) ∧ RAM.ComputesIn E (graphInput g) cs.flatten t₀ s₀ ∧
        RAM.ComputesIn build (graphInput g ++ 4 :: cs.length :: cs.flatten) net t₁ s₁ ∧
        RAM.ComputesIn F net out t₂ s₂ ∧
        RAM.ComputesIn extract (graphInput g ++ 4 :: cs.length :: cs.flatten ++ out) pos t₃ s₃ ∧
        (∀ X : ℕ, g.length ^ 4 ≤ X ^ 3 →
          t₀ + t₁ + t₂ + t₃ ≤ C * ((cycles g 4).length + g.length + 1 +
            min (Algo.numV g * Algo.numV g) X) + T (30 * (cycles g 4).length + 5) ∧
          s₀ + s₁ + s₂ + s₃ ≤ C * (labelBound g + (cycles g 4).length + g.length + 1 +
            min (Algo.numV g * Algo.numV g) X) + T (30 * (cycles g 4).length + 5)) ∧
        pos.length = cs.length ∧ (∀ p ∈ pos, p < 4) ∧
        ValidChoices (cs.map selectedOptions) (List.zipWith selected cs pos) ∧
        OptCost g 4 (cost (List.zipWith selected cs pos)) := by
  obtain ⟨E, build, extract, C, h⟩ := cpap4_enum_ram_explicit hF
  refine ⟨E, build, extract, C, fun g => ?_⟩
  obtain ⟨cs, net, out, pos, t₀, t₁, t₂, t₃, s₀, s₁, s₂, s₃, hp, h₀, h₁, h₂, h₃, hb, hsb, hl, hlt,
    hv, hopt⟩ := h g
  refine ⟨cs, net, out, pos, t₀, t₁, t₂, t₃, s₀, s₁, s₂, s₃, hp, h₀, h₁, h₂, h₃, fun X hX => ?_,
    hl, hlt, hv, hopt⟩
  have hmin := C4.min_pow43_le (a := Algo.numV g * Algo.numV g) hX
  have := Nat.mul_le_mul_left C (Nat.add_le_add_left hmin ((cycles g 4).length + g.length + 1))
  have := Nat.mul_le_mul_left C
    (Nat.add_le_add_left hmin (labelBound g + (cycles g 4).length + g.length + 1))
  omega

/-- **Corollary 3**, almost-linear `T`: `C₀ (t + m + 1 + min (n², X)) + C_ε t^{1+ε}` steps and
that bound plus `C₀ labelBound g` addresses in all, for every `ε > 0` and `X ≥ m^{4/3}`. -/
theorem cpap4_enum_ram_semantic {F : RAM.Stmt} {T : ℕ → ℕ} (hF : MinCostFlowSolver F T)
    (hT : AlmostLinear T) :
    ∃ (E build extract : RAM.Stmt) (C₀ : ℕ), ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ g : Graph,
      ∃ (cs : List Cycle) (net out pos : List ℕ) (t₀ t₁ t₂ t₃ s₀ s₁ s₂ s₃ : ℕ),
        cs.Perm (cycles g 4) ∧ RAM.ComputesIn E (graphInput g) cs.flatten t₀ s₀ ∧
        RAM.ComputesIn build (graphInput g ++ 4 :: cs.length :: cs.flatten) net t₁ s₁ ∧
        RAM.ComputesIn F net out t₂ s₂ ∧
        RAM.ComputesIn extract (graphInput g ++ 4 :: cs.length :: cs.flatten ++ out) pos t₃ s₃ ∧
        (∀ X : ℕ, g.length ^ 4 ≤ X ^ 3 →
          ((t₀ + t₁ + t₂ + t₃ : ℕ) : ℝ) ≤
            C₀ * (((cycles g 4).length : ℝ) + g.length + 1 +
              (min (Algo.numV g * Algo.numV g) X : ℕ)) +
            C * ((cycles g 4).length : ℝ) ^ (1 + ε) ∧
          ((s₀ + s₁ + s₂ + s₃ : ℕ) : ℝ) ≤
            C₀ * ((labelBound g : ℝ) + (cycles g 4).length + g.length + 1 +
              (min (Algo.numV g * Algo.numV g) X : ℕ)) +
            C * ((cycles g 4).length : ℝ) ^ (1 + ε)) ∧
        pos.length = cs.length ∧ (∀ p ∈ pos, p < 4) ∧
        ValidChoices (cs.map selectedOptions) (List.zipWith selected cs pos) ∧
        OptCost g 4 (cost (List.zipWith selected cs pos)) := by
  obtain ⟨E, build, extract, C₀, h⟩ := cpap4_enum_ram hF hT
  refine ⟨E, build, extract, C₀, fun ε hε => ?_⟩
  obtain ⟨C, hC⟩ := h ε hε
  refine ⟨C, fun g => ?_⟩
  obtain ⟨cs, net, out, pos, t₀, t₁, t₂, t₃, s₀, s₁, s₂, s₃, hp, h₀, h₁, h₂, h₃, hb, hsb, hl, hlt,
    hv, hopt⟩ := hC g
  refine ⟨cs, net, out, pos, t₀, t₁, t₂, t₃, s₀, s₁, s₂, s₃, hp, h₀, h₁, h₂, h₃, fun X hX => ?_,
    hl, hlt, hv, hopt⟩
  have hmin : ((min (Algo.numV g * Algo.numV g) (C4.pow43 g.length) : ℕ) : ℝ) ≤
      ((min (Algo.numV g * Algo.numV g) X : ℕ) : ℝ) := by exact_mod_cast C4.min_pow43_le hX
  have hC₀ : (0 : ℝ) ≤ C₀ := Nat.cast_nonneg _
  exact ⟨by nlinarith [mul_le_mul_of_nonneg_left hmin hC₀],
    by nlinarith [mul_le_mul_of_nonneg_left hmin hC₀]⟩

end STACS2027.Runtimes

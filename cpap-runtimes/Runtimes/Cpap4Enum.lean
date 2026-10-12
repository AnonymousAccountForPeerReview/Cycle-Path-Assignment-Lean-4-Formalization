module

public import Runtimes.Flow.Main
public import Runtimes.C4.Main

/-!
# Corollary 3 with its running time and its memory

**Corollary 3** of the manuscript: for a simple graph `G = (V, E)` with `t` simple 4-cycles,
`CPAP(G, 4)` admits an `O(t^{1+o(1)} + min(|V|² + t, (|E|^{4/3} + t) · log² |V|))` time
algorithm. Here: the four-cycles are listed by the verified program of `Runtimes/C4/Main.lean`
(`C4.fourCycles_ram`: `O(m + 1 + t + min(n², ⌈m^{4/3}⌉))` steps, without logarithmic
factors, and the addresses below `O(labelBound g + m + 1 + t + min(n², ⌈m^{4/3}⌉))`), the flow
network is built and the assignment is read off by the verified programs of `Runtimes/Flow/`
(`O(t + m + 1)` steps each; the construction accesses the addresses below
`O(labelBound g + t + m + 1)`, its label dictionary having `labelBound g = 1 + the largest label`
cells), and the minimum-cost flow is computed by a program `F` satisfying the explicit
hypothesis `Flow.MinCostFlowSolver F T` (time and addresses below `T`) with an almost-linear `T`
(`Flow.AlmostLinear T`) — the cited result of ANONYMIZED, ANONYMIZED, ANONYMIZED, ANONYMIZED, ANONYMIZED, Probst
ANONYMIZED, ANONYMIZED and ANONYMIZED (FOCS 2023), the one result that is not formalized.

* `cpap4_enum_ram_explicit`: the total time is at most
  `C (t + m + 1 + min(n², ⌈m^{4/3}⌉)) + T(30t + 5)`, and the four programs together access at
  most `C (labelBound g + t + m + 1 + min(n², ⌈m^{4/3}⌉)) + T(30t + 5)` addresses (the sum of their
  address bounds), for any solver time `T`;
* `cpap4_enum_ram`: with an almost-linear `T`, at most
  `C₀ (t + m + 1 + min(n², ⌈m^{4/3}⌉)) + C_ε t^{1+ε}` steps and
  `C₀ (labelBound g + t + m + 1 + min(n², ⌈m^{4/3}⌉)) + C_ε t^{1+ε}` addresses for every `ε > 0`,
  `C₀` independent of `ε`.
-/

@[expose] public section

namespace STACS2027.Runtimes

open STACS2027 STACS2027.RAM STACS2027.Runtimes.Flow

/-- The four-cycle listing of `Runtimes/C4` as an enumeration program for Corollary 3. -/
theorem fourCycles_lister :
    ∃ (E : RAM.Stmt) (CE : ℕ), ∀ g : Graph, ∃ (cs : List Cycle) (steps : ℕ),
      cs.Perm (cycles g 4) ∧
      RAM.ComputesIn E (graphInput g) cs.flatten steps
        (CE * (labelBound g + g.length + 1 + (cycles g 4).length +
          min (Algo.numV g * Algo.numV g) (C4.pow43 g.length))) ∧
      steps ≤ CE * (g.length + 1 + (cycles g 4).length +
        min (Algo.numV g * Algo.numV g) (C4.pow43 g.length)) := by
  obtain ⟨prog, C, h⟩ := C4.fourCycles_ram
  refine ⟨prog, C, fun g => ?_⟩
  obtain ⟨out, T, hc, hT, cs, hp, rfl⟩ := h g
  exact ⟨cs, T, hp, hc, hT⟩

/-- **Corollary 3 (timed), with the solver's time explicit**: given a minimum-cost flow solver
`F` with running time and memory `T` (the cited hypothesis), there are verified RAM programs `E`
(four-cycle listing), `build` (the flow network) and `extract` (the assignment) and a constant
`C` such that on every graph `g` the pipeline `E`, `build`, `F`, `extract` takes at most
`C · (t + m + 1 + min(n², ⌈m^{4/3}⌉)) + T(30t + 5)` steps in total (`t` four-cycles, `m` input
entries, `n` vertices), its programs access at most
`C · (labelBound g + t + m + 1 + min(n², ⌈m^{4/3}⌉)) + T(30t + 5)` addresses in total (each `sᵢ`
bounds the addresses of one program, input included; `labelBound g = 1 + the largest label`), and
it outputs one position `pos_i < 4` per cycle, the paths `selected C_i pos_i` forming an optimal
assignment of `CPAP(g, 4)`. -/
theorem cpap4_enum_ram_explicit {F : RAM.Stmt} {T : ℕ → ℕ} (hF : MinCostFlowSolver F T) :
    ∃ (E build extract : RAM.Stmt) (C : ℕ), ∀ g : Graph,
      ∃ (cs : List Cycle) (net out pos : List ℕ) (t₀ t₁ t₂ t₃ s₀ s₁ s₂ s₃ : ℕ),
        cs.Perm (cycles g 4) ∧ RAM.ComputesIn E (graphInput g) cs.flatten t₀ s₀ ∧
        RAM.ComputesIn build (graphInput g ++ 4 :: cs.length :: cs.flatten) net t₁ s₁ ∧
        RAM.ComputesIn F net out t₂ s₂ ∧
        RAM.ComputesIn extract (graphInput g ++ 4 :: cs.length :: cs.flatten ++ out) pos t₃ s₃ ∧
        t₀ + t₁ + t₂ + t₃ ≤ C * ((cycles g 4).length + g.length + 1 +
            min (Algo.numV g * Algo.numV g) (C4.pow43 g.length)) +
          T (30 * (cycles g 4).length + 5) ∧
        s₀ + s₁ + s₂ + s₃ ≤ C * (labelBound g + (cycles g 4).length + g.length + 1 +
            min (Algo.numV g * Algo.numV g) (C4.pow43 g.length)) +
          T (30 * (cycles g 4).length + 5) ∧
        pos.length = cs.length ∧ (∀ p ∈ pos, p < 4) ∧
        ValidChoices (cs.map selectedOptions) (List.zipWith selected cs pos) ∧
        OptCost g 4 (cost (List.zipWith selected cs pos)) := by
  obtain ⟨E, CE, hE⟩ := fourCycles_lister
  obtain ⟨build, extract, C₀, h⟩ := cpap4_enum_of_lister hF hE
  refine ⟨E, build, extract, CE + C₀ + C₀, fun g => ?_⟩
  obtain ⟨cs, net, out, pos, t₀, t₁, t₂, t₃, hp, h₀, ht₀, h₁, ht₁, h₂, ht₂, h₃, ht₃, hl, hlt, hv,
    hopt⟩ := h g
  refine ⟨cs, net, out, pos, t₀, t₁, t₂, t₃, _, _, _, _, hp, h₀, h₁, h₂, h₃, ?_, ?_, hl, hlt, hv,
    hopt⟩
  · set t := (cycles g 4).length
    set X := min (Algo.numV g * Algo.numV g) (C4.pow43 g.length)
    have e0 : CE * (g.length + 1 + t + X) = CE * (t + g.length + 1 + X) := by ring_nf
    have e1 : C₀ * (t + g.length + 1) ≤ C₀ * (t + g.length + 1 + X) :=
      Nat.mul_le_mul_left _ (by omega)
    rw [Nat.add_mul, Nat.add_mul]
    omega
  · set t := (cycles g 4).length
    set X := min (Algo.numV g * Algo.numV g) (C4.pow43 g.length)
    set L := labelBound g
    have e0 : CE * (L + g.length + 1 + t + X) = CE * (L + t + g.length + 1 + X) := by ring_nf
    have e1 : C₀ * (L + t + g.length + 1) ≤ C₀ * (L + t + g.length + 1 + X) :=
      Nat.mul_le_mul_left _ (by omega)
    have e2 : C₀ * (t + g.length + 1) ≤ C₀ * (L + t + g.length + 1 + X) :=
      Nat.mul_le_mul_left _ (by omega)
    rw [Nat.add_mul, Nat.add_mul]
    omega

/-- **Corollary 3 (timed)**: given a minimum-cost flow solver `F` with almost-linear running
time and memory `T` (the cited hypothesis), there are verified RAM programs `E` (four-cycle
listing), `build` (the flow network) and `extract` (the assignment) and a constant `C₀` such that,
for every `ε > 0` and some constant `C`, on every graph `g` the pipeline `E`, `build`, `F`,
`extract` takes at most `C₀ · (t + m + 1 + min(n², ⌈m^{4/3}⌉)) + C · t^{1+ε}` steps in total, its
programs access at most `C₀ · (labelBound g + t + m + 1 + min(n², ⌈m^{4/3}⌉)) + C · t^{1+ε}`
addresses in total (`t` four-cycles, `m` input entries, `n` vertices), and it outputs one position
`pos_i < 4` per cycle, the paths `selected C_i pos_i` forming an optimal assignment of
`CPAP(g, 4)`. The constant `C₀` of the linear terms does not depend on `ε`: this is the
manuscript's `O(t^{1+o(1)} + min(n² + t, m^{4/3} + t))` (without the logarithmic factors), in
time and in space (with the label term in space). -/
theorem cpap4_enum_ram {F : RAM.Stmt} {T : ℕ → ℕ} (hF : MinCostFlowSolver F T)
    (hT : AlmostLinear T) :
    ∃ (E build extract : RAM.Stmt) (C₀ : ℕ), ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ g : Graph,
      ∃ (cs : List Cycle) (net out pos : List ℕ) (t₀ t₁ t₂ t₃ s₀ s₁ s₂ s₃ : ℕ),
        cs.Perm (cycles g 4) ∧ RAM.ComputesIn E (graphInput g) cs.flatten t₀ s₀ ∧
        RAM.ComputesIn build (graphInput g ++ 4 :: cs.length :: cs.flatten) net t₁ s₁ ∧
        RAM.ComputesIn F net out t₂ s₂ ∧
        RAM.ComputesIn extract (graphInput g ++ 4 :: cs.length :: cs.flatten ++ out) pos t₃ s₃ ∧
        ((t₀ + t₁ + t₂ + t₃ : ℕ) : ℝ) ≤
          C₀ * (((cycles g 4).length : ℝ) + g.length + 1 +
            (min (Algo.numV g * Algo.numV g) (C4.pow43 g.length) : ℕ)) +
          C * ((cycles g 4).length : ℝ) ^ (1 + ε) ∧
        ((s₀ + s₁ + s₂ + s₃ : ℕ) : ℝ) ≤
          C₀ * ((labelBound g : ℝ) + (cycles g 4).length + g.length + 1 +
            (min (Algo.numV g * Algo.numV g) (C4.pow43 g.length) : ℕ)) +
          C * ((cycles g 4).length : ℝ) ^ (1 + ε) ∧
        pos.length = cs.length ∧ (∀ p ∈ pos, p < 4) ∧
        ValidChoices (cs.map selectedOptions) (List.zipWith selected cs pos) ∧
        OptCost g 4 (cost (List.zipWith selected cs pos)) :=
  cpap4_enum_of_fourCycles hF hT (fun g => min (Algo.numV g * Algo.numV g) (C4.pow43 g.length))
    fourCycles_lister

end STACS2027.Runtimes

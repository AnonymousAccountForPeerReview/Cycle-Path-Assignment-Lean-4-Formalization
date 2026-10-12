module

public import Runtimes.Flow.Main
public import Runtimes.Flow.Pipe
import Mathlib.Tactic

/-!
# Theorem 2 and the triangle corollary as single RAM programs

With the composition theorem `pipe3_spec`, the pipeline of `cpap4_flow_ram` (construction, the
cited min-cost flow program `F`, extraction) becomes **one** RAM program,
`pipe3 lenFlow build4 F extract4`, containing `F` as a (relocated) subroutine:

* `cpap4_flow_single`: within `C (t + m + 1) + 4 T(30t + 5)` steps it writes the positions of an
  optimal assignment of `CPAP(G, 4)`, accessing only the addresses below
  `C (labelBound g + t + m + 1) + 4 T(30t + 5)` (`labelBound g = 1 + the largest label`: the label
  dictionary of the construction; `4 T(30t + 5)`: the solver's memory, relocated into one residue
  class modulo `4`);
* `cpap4_flow_single_almostLinear`: with an almost-linear `T`, within `C₀ (t + m + 1) + C_ε t^{1+ε}`
  steps and `C₀ (labelBound g + t + m + 1) + C_ε t^{1+ε}` addresses for every `ε > 0` (`C₀`
  independent of `ε`) — Theorem 2's `O(t^{1+o(1)} + Υ₄)` as a single algorithm (the
  enumeration, time `Υ₄ ≥ m`, being charged separately as in the paper);
* `triangle_single`, `triangle_single_almostLinear`: the same for `k = 3`.

`lenFlow` computes the length `2m + 3 + kt` of the input `flowInput g cs k` (needed to spread the
input, `Runtimes/Flow/Pipe.lean`); it reads only cells of `flowInput g cs k`, so it computes the
same on that input followed by anything (`lenFlow_value_app`).
-/

@[expose] public section

namespace STACS2027.Runtimes.Flow

open STACS2027 STACS2027.RAM

/-! ### The length of the input -/

/-- `m`. -/
abbrev yM : ℕ := 627
/-- `2m + 3`. -/
abbrev yV : ℕ := 631
/-- A constant. -/
abbrev yC : ℕ := 635
/-- An address. -/
abbrev yA : ℕ := 639
/-- `k`. -/
abbrev yK : ℕ := 643
/-- `t`. -/
abbrev yT : ℕ := 647
/-- `kt`. -/
abbrev yKT : ℕ := 651
/-- The multiplication counter. -/
abbrev yQ : ℕ := 655

/-- Reading `m`, `k`, `t` (registers of class `3`). -/
def lenRead : Stmt :=
  .seq (.load yM xZ) (.seq (.add yV yM yM) (.seq (.const yC 3) (.seq (.add yV yV yC)
  (.seq (.const yC 2) (.seq (.sub yA yV yC) (.seq (.load yK yA) (.seq (.const yC 1)
  (.seq (.sub yA yV yC) (.load yT yA)))))))))

/-- `xL := 2m + 3 + kt`, the length of `flowInput g cs k`. -/
def lenFlow : Stmt := .seq lenRead (.seq (mul yKT yK yT yQ) (.add xL yV yKT))

section len

variable {g : Graph} {cs : List Cycle} {k : ℕ} {S : ℕ}

/-- `lenFlow` on `flowInput g cs k` followed by any `rest`: `xL = |flowInput g cs k|`; it reads
the cells `0`, `2m + 1`, `2m + 2` only. -/
theorem lenFlow_value_app (hcs : ∀ c ∈ cs, IsCycle g k c) (rest : List ℕ) (hS : bV g ≤ S) :
    HTB S lenFlow (· = initial (flowInput g cs k ++ rest))
      (fun c => c.reg xL = (flowInput g cs k).length ∧
        c.mem = (initial (flowInput g cs k ++ rest)).mem ∧ c.out = []) (5 * cs.length + 15) := by
  obtain ⟨h0, hk, ht, -, -⟩ := input_facts hcs rest
  set P : Config → Prop := fun c => c.reg yV = 2 * g.length + 3 ∧ c.reg yK = k ∧
    c.reg yT = cs.length ∧ c.mem = (initial (flowInput g cs k ++ rest)).mem ∧ c.out = [] with hP
  have h1 : HTB S lenRead (· = initial (flowInput g cs k ++ rest)) P 10 :=
    HTB.of_HT_addrOK (by decide) (fun c hc => by
      subst hc
      have hb : bV g = 2 * g.length + 3 := rfl
      addr_ok [lenRead, initial_reg, h0]) <| by
    refine HT.run_le (by decide) (by decide) fun c hc => ?_
    subst hc
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    all_goals simp +decide only [lenRead, run_seq', run_load, run_add, run_sub, run_const,
      setReg_reg, setReg_mem, setReg_out, ↓reduceIte, initial_reg, h0, initial_out]
    · omega
    · rw [show g.length + g.length + 3 - 2 = 2 * g.length + 1 by omega, hk]
    · rw [show g.length + g.length + 3 - 1 = 2 * g.length + 2 by omega, ht]
  have h2 := HTB.mul (S := S) (d := yKT) (a := yK) (b := yT) (k := yQ) (x := k) (y := cs.length)
    (P := P) (by decide) (by rw [hP]; indep) (fun c h => h.2.1) (fun c h => h.2.2.1)
  have h3 : HTB S (.add xL yV yKT) (fun c => P c ∧ c.reg yKT = k * cs.length)
      (fun c => c.reg xL = (flowInput g cs k).length ∧
        c.mem = (initial (flowInput g cs k ++ rest)).mem ∧ c.out = []) 1 := HTB.of_HT rfl <| by
    refine HT.run_le (by decide) (by decide) fun c ⟨⟨hv, _, _, hm, ho⟩, hkt⟩ => ?_
    refine ⟨?_, by simpa using hm, by simpa using ho⟩
    simp +decide only [run_add, setReg_reg, ↓reduceIte, hv, hkt]
    rw [length_flowInput hcs, bD, bV]
  exact (h1.seq (h2.seq h3)).weaken (by omega)

theorem lenFlow_value (hcs : ∀ c ∈ cs, IsCycle g k c) (hS : bV g ≤ S) :
    HTB S lenFlow (· = initial (flowInput g cs k))
      (fun c => c.reg xL = (flowInput g cs k).length ∧ c.mem = (initial (flowInput g cs k)).mem ∧
        c.out = []) (5 * cs.length + 15) := by
  simpa using lenFlow_value_app hcs [] hS

/-- **The length of the input** (`LenPost`). -/
theorem lenFlow_spec (hcs : ∀ c ∈ cs, IsCycle g k c) (hS : bV g ≤ S) :
    HTB S lenFlow (· = initial (flowInput g cs k)) (LenPost (flowInput g cs k))
      (5 * cs.length + 15) := by
  intro c hc
  obtain ⟨c', t, he, ⟨h1, h2, h3⟩, ht⟩ := lenFlow_value hcs hS c hc
  refine ⟨c', t, he, ⟨h1, h2, h3, fun r hr => ?_⟩, ht⟩
  have hw : ∀ x ∈ wregs lenFlow, x % 4 = 3 ∧ x ≠ xJ 0 ∧ x ≠ xZ := by decide
  have hr' : r ∉ wregs lenFlow := fun hm => by
    obtain ⟨a, b, d⟩ := hw r hm
    rcases hr with hr | hr | hr
    · exact hr a
    · exact b hr
    · exact d hr
  rw [he.frame.reg r hr', hc]; rfl

end len

/-! ### The single programs -/

/-- **Theorem 2 as one RAM program** (`F` a subroutine): an optimal assignment within
`C (t + m + 1) + 4 T(30t + 5)` steps and `C (labelBound g + t + m + 1) + 4 T(30t + 5)` addresses. -/
theorem cpap4_flow_single {F : RAM.Stmt} {T : ℕ → ℕ} (hF : MinCostFlowSolver F T) :
    ∃ (prog : RAM.Stmt) (C : ℕ), ∀ (g : Graph) (cs : List Cycle), cs.Perm (cycles g 4) →
      ∃ (pos : List ℕ) (steps : ℕ),
        RAM.ComputesIn prog (flowInput g cs 4) pos steps
          (C * (labelBound g + cs.length + g.length + 1) + 4 * T (30 * cs.length + 5)) ∧
        steps ≤ C * (cs.length + g.length + 1) + 4 * T (30 * cs.length + 5) ∧
        pos.length = cs.length ∧ (∀ p ∈ pos, p < 4) ∧
        ValidChoices (cs.map selectedOptions) (List.zipWith selected cs pos) ∧
        OptCost g 4 (cost (List.zipWith selected cs pos)) := by
  refine ⟨pipe3 lenFlow build4 F extract4, 6000, fun g cs hperm => ?_⟩
  have hcs := isCycle_of_perm hperm
  obtain ⟨out, pos, t₁, t₂, t₃, h₁, ht₁, h₂, ht₂, h₃, ht₃, hol, hl, hlt, hv, hopt⟩ :=
    cpap4_flow_core hF hperm
  have hx := length_flowInput hcs
  have hd : bD g cs 4 = 2 * g.length + 3 + 4 * cs.length := rfl
  have hbv : bV g = 2 * g.length + 3 := rfl
  obtain ⟨steps, hc, hs⟩ := pipe3_spec (lenFlow_spec hcs (S := bD g cs 4) (by omega)) h₁ h₂ h₃
  have hy : (netEnc4 cs).length = 30 * cs.length + 5 := by
    rw [netEnc4, length_netInput, length_net4 hcs]; ring
  have hb := bOFF_le_flow (by norm_num) hcs
  refine ⟨pos, steps, hc.mono ?_, ?_, hl, hlt, hv, hopt⟩
  · rw [hx, hy, hol]; nlinarith
  · rw [hx] at hs; omega

/-- **The corollary for triangles as one RAM program**: within `C (t + m + 1) + 4 T(21t + 5)`
steps and `C (labelBound g + t + m + 1) + 4 T(21t + 5)` addresses. -/
theorem triangle_single {F : RAM.Stmt} {T : ℕ → ℕ} (hF : MinCostFlowSolver F T) :
    ∃ (prog : RAM.Stmt) (C : ℕ), ∀ (g : Graph) (cs : List Cycle), cs.Perm (cycles g 3) →
      ∃ (pos : List ℕ) (steps : ℕ),
        RAM.ComputesIn prog (flowInput g cs 3) pos steps
          (C * (labelBound g + cs.length + g.length + 1) + 4 * T (21 * cs.length + 5)) ∧
        steps ≤ C * (cs.length + g.length + 1) + 4 * T (21 * cs.length + 5) ∧
        pos.length = cs.length ∧ (∀ p ∈ pos, p < 3) ∧
        ValidChoices (cs.map selectedOptions) (List.zipWith selected cs pos) ∧
        OptCost g 3 (cost (List.zipWith selected cs pos)) := by
  refine ⟨pipe3 lenFlow build3 F extract3, 6000, fun g cs hperm => ?_⟩
  have hcs := isCycle_of_perm hperm
  obtain ⟨out, pos, t₁, t₂, t₃, h₁, ht₁, h₂, ht₂, h₃, ht₃, hol, hl, hlt, hv, hopt⟩ :=
    triangle_core hF hperm
  have hx := length_flowInput hcs
  have hd : bD g cs 3 = 2 * g.length + 3 + 3 * cs.length := rfl
  have hbv : bV g = 2 * g.length + 3 := rfl
  obtain ⟨steps, hc, hs⟩ := pipe3_spec (lenFlow_spec hcs (S := bD g cs 3) (by omega)) h₁ h₂ h₃
  have hy : (netEnc3 cs).length = 21 * cs.length + 5 := by
    rw [netEnc3, length_netInput, length_net3 hcs]; ring
  have hb := bOFF_le_flow (by norm_num) hcs
  refine ⟨pos, steps, hc.mono ?_, ?_, hl, hlt, hv, hopt⟩
  · rw [hx, hy, hol]; nlinarith
  · rw [hx] at hs; omega

/-- **Theorem 2 as one RAM program in almost-linear time**: within `C₀ (t + m + 1) + C_ε t^{1+ε}`
steps and `C₀ (labelBound g + t + m + 1) + C_ε t^{1+ε}` addresses, for every `ε > 0`. -/
theorem cpap4_flow_single_almostLinear {F : RAM.Stmt} {T : ℕ → ℕ} (hF : MinCostFlowSolver F T)
    (hT : AlmostLinear T) :
    ∃ (prog : RAM.Stmt) (C₀ : ℕ), ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ (g : Graph) (cs : List Cycle),
      cs.Perm (cycles g 4) → ∃ (pos : List ℕ) (steps space : ℕ),
        RAM.ComputesIn prog (flowInput g cs 4) pos steps space ∧
        (steps : ℝ) ≤ C₀ * ((cs.length : ℝ) + g.length + 1) + C * (cs.length : ℝ) ^ (1 + ε) ∧
        (space : ℝ) ≤
          C₀ * ((labelBound g : ℝ) + cs.length + g.length + 1) + C * (cs.length : ℝ) ^ (1 + ε) ∧
        pos.length = cs.length ∧ (∀ p ∈ pos, p < 4) ∧
        ValidChoices (cs.map selectedOptions) (List.zipWith selected cs pos) ∧
        OptCost g 4 (cost (List.zipWith selected cs pos)) := by
  obtain ⟨prog, C₀, h⟩ := cpap4_flow_single hF
  refine ⟨prog, C₀ + 4 * T 5, fun ε hε => ?_⟩
  obtain ⟨Cε, hCε⟩ := hT ε hε
  refine ⟨(4 : ℕ) * (Cε * (35 : ℝ) ^ (1 + ε)), fun g cs hperm => ?_⟩
  obtain ⟨pos, steps, hc, hs, hl, hlt, hv, hopt⟩ := h g cs hperm
  refine ⟨pos, steps, _, hc, ?_, ?_, hl, hlt, hv, hopt⟩
  · have := split_bound (s := steps) (L := cs.length + g.length + 1) (k := 4) (C₀ := C₀)
      (t := cs.length) (a := 30) hε (almostLinear_const hCε) hCε le_rfl (by omega) hs
    push_cast at this ⊢
    linarith
  · have := split_bound (s := C₀ * (labelBound g + cs.length + g.length + 1) +
      4 * T (30 * cs.length + 5)) (L := labelBound g + cs.length + g.length + 1) (k := 4)
      (C₀ := C₀) (t := cs.length) (a := 30) hε (almostLinear_const hCε) hCε le_rfl (by omega) le_rfl
    push_cast at this ⊢
    linarith

/-- **The corollary for triangles as one RAM program in almost-linear time**: as
`cpap4_flow_single_almostLinear`. -/
theorem triangle_single_almostLinear {F : RAM.Stmt} {T : ℕ → ℕ} (hF : MinCostFlowSolver F T)
    (hT : AlmostLinear T) :
    ∃ (prog : RAM.Stmt) (C₀ : ℕ), ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ (g : Graph) (cs : List Cycle),
      cs.Perm (cycles g 3) → ∃ (pos : List ℕ) (steps space : ℕ),
        RAM.ComputesIn prog (flowInput g cs 3) pos steps space ∧
        (steps : ℝ) ≤ C₀ * ((cs.length : ℝ) + g.length + 1) + C * (cs.length : ℝ) ^ (1 + ε) ∧
        (space : ℝ) ≤
          C₀ * ((labelBound g : ℝ) + cs.length + g.length + 1) + C * (cs.length : ℝ) ^ (1 + ε) ∧
        pos.length = cs.length ∧ (∀ p ∈ pos, p < 3) ∧
        ValidChoices (cs.map selectedOptions) (List.zipWith selected cs pos) ∧
        OptCost g 3 (cost (List.zipWith selected cs pos)) := by
  obtain ⟨prog, C₀, h⟩ := triangle_single hF
  refine ⟨prog, C₀ + 4 * T 5, fun ε hε => ?_⟩
  obtain ⟨Cε, hCε⟩ := hT ε hε
  refine ⟨(4 : ℕ) * (Cε * (35 : ℝ) ^ (1 + ε)), fun g cs hperm => ?_⟩
  obtain ⟨pos, steps, hc, hs, hl, hlt, hv, hopt⟩ := h g cs hperm
  refine ⟨pos, steps, _, hc, ?_, ?_, hl, hlt, hv, hopt⟩
  · have := split_bound (s := steps) (L := cs.length + g.length + 1) (k := 4) (C₀ := C₀)
      (t := cs.length) (a := 21) hε (almostLinear_const hCε) hCε (by norm_num) (by omega) hs
    push_cast at this ⊢
    linarith
  · have := split_bound (s := C₀ * (labelBound g + cs.length + g.length + 1) +
      4 * T (21 * cs.length + 5)) (L := labelBound g + cs.length + g.length + 1) (k := 4)
      (C₀ := C₀) (t := cs.length) (a := 21) hε (almostLinear_const hCε) hCε (by norm_num)
      (by omega) le_rfl
    push_cast at this ⊢
    linarith

end STACS2027.Runtimes.Flow

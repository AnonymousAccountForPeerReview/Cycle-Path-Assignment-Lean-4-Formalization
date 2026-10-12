module

public import Runtimes.Flow.Out
public import Runtimes.Flow.Extract
import Mathlib.Tactic

/-!
# Theorem 2 and the triangle corollary with their running times and memory

The manuscript's Theorem 2 (`T1`): *`CPAP(G, 4)` admits an `O(t^{1+o(1)} + Υ₄)` time algorithm*,
and its case `k = 3` (the triangles, which Algorithm 3 and the proofs of Theorem 4 and
Corollary 5 treat by min-cost flow), by the reduction of Section 3 to
min-cost flow and the almost-linear-time min-cost flow algorithm of ANONYMIZED et al.
(FOCS 2023). The flow algorithm stays cited: it is the hypothesis `MinCostFlowSolver F T`
(`Runtimes/Flow/Solver.lean`: time and addresses below `T`), the only one. Everything else is a
RAM program proved here, with its time and its space (`RAM.ComputesIn`: the run accesses only
the addresses below the space bound, input included).

**The pipeline** (the RAM's output is write-only, so the three programs are run one after
another, the output of one being the input of the next):
1. `build4` on `flowInput g cs 4` (the graph, `4`, `t`, and the vertices of the cycles of any
   enumeration `cs` of the simple four-cycles, `cs.Perm (cycles g 4)`) writes the encoded network
   `netInput (num4 cs) (n4 cs) (2t) (net4 cs)` — Section 3's network `𝓕` for the list `cs`
   (`net4 (cycles g 4) = fourCycleNetwork g`), within `C (t + m + 1)` steps (in fact `C (t + 1)`)
   and the addresses below `C (labelBound g + t + m + 1)` (its label dictionary has
   `labelBound g = 1 + the largest label` cells; it is allocated, not cleared, so it costs no
   time);
2. the cited solver `F` on it: at most `T (30t + 5)` steps and addresses, output `1 :: bits`, a
   minimum-cost integral flow of value `2t`;
3. `extract4` on the input followed by the answer of `F` writes one position per cycle within
   `C (t + m + 1)` steps and addresses: the paths `selected C_i pos_i` form an optimal
   cycle-path assignment (`OptCost`: its cost is the least budget `B` with `HasAssignment g 4 B`).

`cpap4_flow_ram` states this; `cpap4_flow_ram_almostLinear` adds the hypothesis that `T` is almost
linear (`AlmostLinear T`, what the cited algorithm gives on this RAM) and bounds the total time
by `C₀ (t + m + 1) + C_ε t^{1+ε}` and the total space by `C₀ (labelBound g + t + m + 1) + C_ε t^{1+ε}`
for every `ε > 0` — the manuscript's `O(t^{1+o(1)} + Υ₄)`, the enumeration (time `Υ₄ ≥ m`)
being charged separately as in the paper. `triangle_ram` and `triangle_ram_almostLinear` are the
same for `k = 3` (value `t`, network `net3`, `21t + 5` words).

The three programs are also combined into **one** RAM program, the solver being a relocated
subroutine (`cpap4_flow_single`, `triangle_single` and their almost-linear forms in
`Runtimes/Flow/Single.lean`, by the composition theorem `pipe3_spec`).

**Corollary 3** (`cpap4_enum_of_lister`, `cpap4_enum_of_fourCycles`): the same pipeline
preceded by any enumeration program `E` that writes a permutation of `cycles g 4` (as
`cs.flatten`) within `B g` steps and the addresses below `BS g`; with the four-cycle enumeration
theorem of `Runtimes/C4` (`B g = C (m + 1 + t + min(n², ⌈m^{4/3}⌉))`,
`BS g = C (labelBound g + m + 1 + t + min(n², ⌈m^{4/3}⌉))`), `cpap4_enum_of_fourCycles` gives
Corollary 3's bounds.
-/

@[expose] public section

namespace STACS2027.Runtimes.Flow

open STACS2027 STACS2027.RAM

section main

variable {g : Graph} {cs : List Cycle}

theorem isCycle_of_perm {k : ℕ} (h : cs.Perm (cycles g k)) : ∀ c ∈ cs, IsCycle g k c :=
  fun _ hc => enumerated_isCycle (h.subset hc)

/-- Every list of cycles has an assignment (delete the first vertex of every cycle). -/
theorem validChoices_first {k : ℕ} (hcs : ∀ c ∈ cs, IsCycle g k c) :
    ValidChoices (cs.map selectedOptions) (cs.map fun c => selected c 0) := by
  induction cs with
  | nil => trivial
  | cons c cs ih =>
    refine validChoices_cons.mpr ⟨?_, ih fun d hd => hcs d (by simp [hd])⟩
    have hc := hcs c (by simp)
    exact List.mem_map.mpr ⟨0, List.mem_range.mpr (by have := hc.1; have := hc.2.1; omega), rfl⟩

/-- **The construction machine of Theorem 2** writes the encoded network within `1400 (t + 1)`
steps, accessing only the addresses below any `S ≥ bOFF g cs 4`. -/
theorem build4_spec (hcs : ∀ c ∈ cs, IsCycle g 4 c) {S : ℕ} (hS : bOFF g cs 4 ≤ S) :
    HTB S build4 (fun c => c = initial (flowInput g cs 4)) (fun c => c.out = netEnc4 cs)
      (1400 * (cs.length + 1)) :=
  ((edgePhase_spec hcs hS).seq (out4_spec hcs hS)).weaken (by omega)

/-- **The construction machine of the triangle corollary.** -/
theorem build3_spec (hcs : ∀ c ∈ cs, IsCycle g 3 c) {S : ℕ} (hS : bOFF g cs 3 ≤ S) :
    HTB S build3 (fun c => c = initial (flowInput g cs 3)) (fun c => c.out = netEnc3 cs)
      (1400 * (cs.length + 1)) :=
  ((edgePhase_spec hcs hS).seq (out3_spec hcs hS)).weaken (by omega)

/-- The space of the construction machines: `bOFF g cs k ≤ 44 (labelBound g + t + m + 1)` for
`k ≤ 4`. -/
theorem bOFF_le_flow {k : ℕ} (hk : k ≤ 4) (hcs : ∀ c ∈ cs, IsCycle g k c) :
    bOFF g cs k ≤ 44 * (labelBound g + cs.length + g.length + 1) := by
  have h := bOFF_le hcs
  have : k * cs.length ≤ 4 * cs.length := Nat.mul_le_mul_right _ hk
  omega

end main

/-- The pipeline of Theorem 2 with the concrete programs `build4`, `extract4`: the construction
within the space `bOFF g cs 4`, the solver within `T (30t + 5)` steps and addresses, the
extraction within the addresses `bD g cs 4 + 6t + 1` (it reads the input and the answer only). -/
theorem cpap4_flow_core {F : RAM.Stmt} {T : ℕ → ℕ} (hF : MinCostFlowSolver F T) {g : Graph}
    {cs : List Cycle} (hperm : cs.Perm (cycles g 4)) :
    ∃ (out pos : List ℕ) (t₁ t₂ t₃ : ℕ),
      RAM.ComputesIn build4 (flowInput g cs 4) (netEnc4 cs) t₁ (bOFF g cs 4) ∧
        t₁ ≤ 1400 * (cs.length + 1) ∧
      RAM.ComputesIn F (netEnc4 cs) out t₂ (T (30 * cs.length + 5)) ∧
        t₂ ≤ T (30 * cs.length + 5) ∧
      RAM.ComputesIn extract4 (flowInput g cs 4 ++ out) pos t₃ (bD g cs 4 + 6 * cs.length + 1) ∧
        t₃ ≤ 18 * cs.length + 20 ∧
      out.length = 10 * cs.length + 1 ∧
      pos.length = cs.length ∧ (∀ p ∈ pos, p < 4) ∧
      ValidChoices (cs.map selectedOptions) (List.zipWith selected cs pos) ∧
      OptCost g 4 (cost (List.zipWith selected cs pos)) := by
  have hcs := isCycle_of_perm hperm
  obtain ⟨t₁, ht₁, h₁⟩ := HTB.computesIn (build4_spec hcs le_rfl)
  obtain ⟨out, t₂, hc₂, ht₂, hans⟩ := hF (num4 cs) (n4 cs) (2 * cs.length) (net4 cs) (goodNet4 hcs)
  rw [length_netInput, length_net4 hcs, show 3 * (10 * cs.length) + 5 = 30 * cs.length + 5 by ring]
    at hc₂ ht₂
  rcases hans with ⟨_, hnone⟩ | ⟨bits, rfl, hlen, _, hmin⟩
  · exfalso
    obtain ⟨flow, hflow, hval, _⟩ := flow_of_assignment4 hcs _ (validChoices_first hcs)
    exact hnone ⟨flow, hflow, hval⟩
  obtain ⟨c₃, t₃, he₃, ho₃, ht₃⟩ := extract4_spec hcs bits le_rfl _ rfl
  obtain ⟨hv, hopt⟩ := optimal_of_minFlow4 hcs hmin
  rw [readOff4_select hcs hlen] at hv hopt
  have hpos : (List.range cs.length).map (pos4 cs.length bits) =
      (List.range cs.length).map fun i =>
        optionIndex (decide (bits.getD (2 * cs.length + (i * 4 + 1)) 0 ≠ 0))
          (decide (bits.getD (2 * cs.length + (i * 4 + 3)) 0 ≠ 0)) := rfl
  refine ⟨1 :: bits, c₃.out, t₁, t₂, t₃, h₁, ht₁, hc₂, ht₂, ⟨c₃, he₃, rfl⟩, ht₃,
    by rw [List.length_cons, hlen, length_net4 hcs], by rw [ho₃]; simp, ?_, ?_, ?_⟩
  · rw [ho₃]
    simp only [List.mem_map, List.mem_range]
    rintro p ⟨i, -, rfl⟩
    exact optionIndex_lt _ _
  · rw [ho₃, hpos]; exact hv
  · rw [ho₃, hpos]; exact optCost_of_optimal hperm hv hopt

/-- The pipeline of the triangle corollary with the concrete programs `build3`, `extract3`. -/
theorem triangle_core {F : RAM.Stmt} {T : ℕ → ℕ} (hF : MinCostFlowSolver F T) {g : Graph}
    {cs : List Cycle} (hperm : cs.Perm (cycles g 3)) :
    ∃ (out pos : List ℕ) (t₁ t₂ t₃ : ℕ),
      RAM.ComputesIn build3 (flowInput g cs 3) (netEnc3 cs) t₁ (bOFF g cs 3) ∧
        t₁ ≤ 1400 * (cs.length + 1) ∧
      RAM.ComputesIn F (netEnc3 cs) out t₂ (T (21 * cs.length + 5)) ∧
        t₂ ≤ T (21 * cs.length + 5) ∧
      RAM.ComputesIn extract3 (flowInput g cs 3 ++ out) pos t₃ (bD g cs 3 + 4 * cs.length) ∧
        t₃ ≤ 15 * cs.length + 20 ∧
      out.length = 7 * cs.length + 1 ∧
      pos.length = cs.length ∧ (∀ p ∈ pos, p < 3) ∧
      ValidChoices (cs.map selectedOptions) (List.zipWith selected cs pos) ∧
      OptCost g 3 (cost (List.zipWith selected cs pos)) := by
  have hcs := isCycle_of_perm hperm
  obtain ⟨t₁, ht₁, h₁⟩ := HTB.computesIn (build3_spec hcs le_rfl)
  obtain ⟨out, t₂, hc₂, ht₂, hans⟩ := hF (num3 cs) (n3 cs) cs.length (net3 cs) (goodNet3 hcs)
  rw [length_netInput, length_net3 hcs, show 3 * (7 * cs.length) + 5 = 21 * cs.length + 5 by ring]
    at hc₂ ht₂
  rcases hans with ⟨_, hnone⟩ | ⟨bits, rfl, hlen, _, hmin⟩
  · exfalso
    obtain ⟨flow, hflow, hval, _⟩ := flow_of_assignment3 hcs _ (validChoices_first hcs)
    exact hnone ⟨flow, hflow, hval⟩
  obtain ⟨c₃, t₃, he₃, ho₃, ht₃⟩ := extract3_spec hcs bits le_rfl _ rfl
  obtain ⟨hv, hopt⟩ := optimal_of_minFlow3 hcs hmin
  rw [readOff3_select hcs hlen] at hv hopt
  refine ⟨1 :: bits, c₃.out, t₁, t₂, t₃, h₁, ht₁, hc₂, ht₂, ⟨c₃, he₃, rfl⟩, ht₃,
    by rw [List.length_cons, hlen, length_net3 hcs], by rw [ho₃]; simp, ?_, ?_, ?_⟩
  · rw [ho₃]
    simp only [List.mem_map, List.mem_range]
    rintro p ⟨i, -, rfl⟩
    unfold pos3b
    split_ifs <;> omega
  · rw [ho₃]; exact hv
  · rw [ho₃]; exact optCost_of_optimal hperm hv hopt

/-- **Theorem 2 on the RAM**, with the min-cost flow algorithm as the hypothesis `hF`: two RAM
programs `build`, `extract` and a constant `C` such that for every graph `g` and every
enumeration `cs` of its simple four-cycles (`cs.Perm (cycles g 4)`; `t = |cs|`, `m = |g|`):
`build` writes, from the graph and the cycles, Section 3's network `net4 cs` (encoded, value
`2t`) within `C (t + m + 1)` steps, accessing only the addresses below
`C (labelBound g + t + m + 1)` (`labelBound g = 1 + the largest label`, the size of its label
dictionary, which costs space but no time); the solver `F` runs on it within `T (30t + 5)` steps
and addresses; and `extract`, on the input followed by the answer of `F`, writes within
`C (t + m + 1)` steps and addresses one position `pos_i` per cycle such that the paths
`selected C_i pos_i` form an optimal cycle-path assignment of `CPAP(G, 4)`. -/
theorem cpap4_flow_ram {F : RAM.Stmt} {T : ℕ → ℕ} (hF : MinCostFlowSolver F T) :
    ∃ (build extract : RAM.Stmt) (C : ℕ), ∀ (g : Graph) (cs : List Cycle), cs.Perm (cycles g 4) →
      ∃ (net out pos : List ℕ) (t₁ t₂ t₃ : ℕ),
        RAM.ComputesIn build (flowInput g cs 4) net t₁
            (C * (labelBound g + cs.length + g.length + 1)) ∧
          t₁ ≤ C * (cs.length + g.length + 1) ∧
        net = netInput (num4 cs) (n4 cs) (2 * cs.length) (net4 cs) ∧
        RAM.ComputesIn F net out t₂ (T (30 * cs.length + 5)) ∧ t₂ ≤ T (30 * cs.length + 5) ∧
        RAM.ComputesIn extract (flowInput g cs 4 ++ out) pos t₃ (C * (cs.length + g.length + 1)) ∧
          t₃ ≤ C * (cs.length + g.length + 1) ∧
        pos.length = cs.length ∧ (∀ p ∈ pos, p < 4) ∧
        ValidChoices (cs.map selectedOptions) (List.zipWith selected cs pos) ∧
        OptCost g 4 (cost (List.zipWith selected cs pos)) := by
  refine ⟨build4, extract4, 1400, fun g cs hperm => ?_⟩
  obtain ⟨out, pos, t₁, t₂, t₃, h₁, ht₁, h₂, ht₂, h₃, ht₃, -, hl, hlt, hv, hopt⟩ :=
    cpap4_flow_core hF hperm
  have hb := bOFF_le_flow (by norm_num) (isCycle_of_perm hperm)
  have hd : bD g cs 4 = 2 * g.length + 3 + 4 * cs.length := rfl
  exact ⟨netEnc4 cs, out, pos, t₁, t₂, t₃, h₁.mono (by omega), by nlinarith, rfl, h₂, ht₂,
    h₃.mono (by omega), by nlinarith, hl, hlt, hv, hopt⟩

/-- **The triangle case (`k = 3`) on the RAM**, with the min-cost flow
algorithm as the hypothesis `hF`: as `cpap4_flow_ram`, with the triangle network `net3 cs` of
value `t` (`7t` arcs, `21t + 5` words) and an optimal assignment of `CPAP(G, 3)`. -/
theorem triangle_ram {F : RAM.Stmt} {T : ℕ → ℕ} (hF : MinCostFlowSolver F T) :
    ∃ (build extract : RAM.Stmt) (C : ℕ), ∀ (g : Graph) (cs : List Cycle), cs.Perm (cycles g 3) →
      ∃ (net out pos : List ℕ) (t₁ t₂ t₃ : ℕ),
        RAM.ComputesIn build (flowInput g cs 3) net t₁
            (C * (labelBound g + cs.length + g.length + 1)) ∧
          t₁ ≤ C * (cs.length + g.length + 1) ∧
        net = netInput (num3 cs) (n3 cs) cs.length (net3 cs) ∧
        RAM.ComputesIn F net out t₂ (T (21 * cs.length + 5)) ∧ t₂ ≤ T (21 * cs.length + 5) ∧
        RAM.ComputesIn extract (flowInput g cs 3 ++ out) pos t₃ (C * (cs.length + g.length + 1)) ∧
          t₃ ≤ C * (cs.length + g.length + 1) ∧
        pos.length = cs.length ∧ (∀ p ∈ pos, p < 3) ∧
        ValidChoices (cs.map selectedOptions) (List.zipWith selected cs pos) ∧
        OptCost g 3 (cost (List.zipWith selected cs pos)) := by
  refine ⟨build3, extract3, 1400, fun g cs hperm => ?_⟩
  obtain ⟨out, pos, t₁, t₂, t₃, h₁, ht₁, h₂, ht₂, h₃, ht₃, -, hl, hlt, hv, hopt⟩ :=
    triangle_core hF hperm
  have hb := bOFF_le_flow (by norm_num) (isCycle_of_perm hperm)
  have hd : bD g cs 3 = 2 * g.length + 3 + 3 * cs.length := rfl
  exact ⟨netEnc3 cs, out, pos, t₁, t₂, t₃, h₁.mono (by omega), by nlinarith, rfl, h₂, ht₂,
    h₃.mono (by omega), by nlinarith, hl, hlt, hv, hopt⟩

/-! ### Almost-linear time -/

/-- `N^{1+ε} ≤ 35^{1+ε} (t^{1+ε} + 1)` for `N ≤ 30t + 5`. -/
theorem rpow_bound {ε : ℝ} (hε : 0 < ε) (t N : ℕ) (hN : N ≤ 30 * t + 5) :
    (N : ℝ) ^ (1 + ε) ≤ (35 : ℝ) ^ (1 + ε) * ((t : ℝ) ^ (1 + ε) + 1) := by
  have he : (0 : ℝ) ≤ 1 + ε := by linarith
  have h35 : (0 : ℝ) ≤ (35 : ℝ) ^ (1 + ε) := Real.rpow_nonneg (by norm_num) _
  have ht : (0 : ℝ) ≤ (t : ℝ) ^ (1 + ε) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  rcases Nat.eq_zero_or_pos t with rfl | htp
  · have : (N : ℝ) ≤ 35 := by exact_mod_cast (show N ≤ 35 by omega)
    calc (N : ℝ) ^ (1 + ε) ≤ (35 : ℝ) ^ (1 + ε) := Real.rpow_le_rpow (Nat.cast_nonneg _) this he
      _ ≤ (35 : ℝ) ^ (1 + ε) * (((0 : ℕ) : ℝ) ^ (1 + ε) + 1) := by
        rw [Nat.cast_zero, Real.zero_rpow (by linarith), zero_add, mul_one]
  · have : (N : ℝ) ≤ 35 * t := by exact_mod_cast (show N ≤ 35 * t by omega)
    calc (N : ℝ) ^ (1 + ε) ≤ (35 * (t : ℝ)) ^ (1 + ε) :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) this he
      _ = (35 : ℝ) ^ (1 + ε) * (t : ℝ) ^ (1 + ε) := Real.mul_rpow (by norm_num) (Nat.cast_nonneg _)
      _ ≤ (35 : ℝ) ^ (1 + ε) * ((t : ℝ) ^ (1 + ε) + 1) := by nlinarith

/-- `t ≤ t^{1+ε}` for a natural number `t`. -/
theorem le_rpow_self {ε : ℝ} (hε : 0 < ε) (t : ℕ) : (t : ℝ) ≤ (t : ℝ) ^ (1 + ε) := by
  rcases Nat.eq_zero_or_pos t with rfl | htp
  · simp [Real.zero_rpow (show (1 : ℝ) + ε ≠ 0 by linarith)]
  · have h1 : (1 : ℝ) ≤ t := by exact_mod_cast htp
    calc (t : ℝ) = (t : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (t : ℝ) ^ (1 + ε) := Real.rpow_le_rpow_of_exponent_le h1 (by linarith)

/-- The solver's constant is nonnegative. -/
theorem almostLinear_const {T : ℕ → ℕ} {ε C : ℝ}
    (h : ∀ N : ℕ, 1 ≤ N → (T N : ℝ) ≤ C * (N : ℝ) ^ (1 + ε)) : 0 ≤ C := by
  have := h 1 le_rfl
  simp only [Nat.cast_one, Real.one_rpow, mul_one] at this
  exact le_trans (Nat.cast_nonneg _) this

/-- **The solver's time under an almost-linear `T`**, split into a constant and the
almost-linear part: `T(at + 5) ≤ T(5) + C_ε 35^{1+ε} t^{1+ε}` for `a ≤ 30` (for `t = 0` the
argument is `5` and `t^{1+ε} = 0`; for `t ≥ 1` it is at most `35t`). -/
theorem solver_le {T : ℕ → ℕ} {ε Cε : ℝ} (hε : 0 < ε) (hC : 0 ≤ Cε)
    (hT : ∀ N : ℕ, 1 ≤ N → (T N : ℝ) ≤ Cε * (N : ℝ) ^ (1 + ε)) {a : ℕ} (ha : a ≤ 30) (t : ℕ) :
    (T (a * t + 5) : ℝ) ≤ T 5 + Cε * (35 : ℝ) ^ (1 + ε) * (t : ℝ) ^ (1 + ε) := by
  have h5 : (0 : ℝ) ≤ T 5 := Nat.cast_nonneg _
  rcases Nat.eq_zero_or_pos t with rfl | htp
  · simp [Real.zero_rpow (show (1 : ℝ) + ε ≠ 0 by linarith)]
  · have hN : ((a * t + 5 : ℕ) : ℝ) ≤ 35 * (t : ℝ) := by
      have : a * t ≤ 30 * t := Nat.mul_le_mul_right t ha
      exact_mod_cast (show a * t + 5 ≤ 35 * t by omega)
    calc (T (a * t + 5) : ℝ) ≤ Cε * ((a * t + 5 : ℕ) : ℝ) ^ (1 + ε) := hT _ (by omega)
      _ ≤ Cε * (35 * (t : ℝ)) ^ (1 + ε) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) hN (by linarith)) hC
      _ = Cε * (35 : ℝ) ^ (1 + ε) * (t : ℝ) ^ (1 + ε) := by
          rw [Real.mul_rpow (by norm_num) (Nat.cast_nonneg _)]; ring
      _ ≤ T 5 + Cε * (35 : ℝ) ^ (1 + ε) * (t : ℝ) ^ (1 + ε) := by linarith

/-- **A time `s ≤ C₀ L + k T(at + 5)` under an almost-linear `T`** (`L ≥ 1` the linear terms):
`s ≤ (C₀ + k T(5)) L + k C_ε 35^{1+ε} t^{1+ε}` — the constant of the linear terms does not depend
on `ε`. -/
theorem split_bound {T : ℕ → ℕ} {ε Cε : ℝ} (hε : 0 < ε) (hC : 0 ≤ Cε)
    (hT : ∀ N : ℕ, 1 ≤ N → (T N : ℝ) ≤ Cε * (N : ℝ) ^ (1 + ε)) {a k C₀ t L s : ℕ} (ha : a ≤ 30)
    (hL : 1 ≤ L) (hs : s ≤ C₀ * L + k * T (a * t + 5)) :
    (s : ℝ) ≤ ((C₀ + k * T 5 : ℕ) : ℝ) * L + k * (Cε * (35 : ℝ) ^ (1 + ε)) * (t : ℝ) ^ (1 + ε) := by
  have h1 := solver_le hε hC hT ha t
  have hs' : (s : ℝ) ≤ C₀ * L + k * (T (a * t + 5) : ℝ) := by exact_mod_cast hs
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have h5 : (0 : ℝ) ≤ T 5 := Nat.cast_nonneg _
  have e : (k : ℝ) * T 5 ≤ k * T 5 * L := le_mul_of_one_le_right (mul_nonneg hk h5) hL'
  push_cast
  nlinarith [mul_le_mul_of_nonneg_left h1 hk]

/-- **Theorem 2 in almost-linear time**: the pipeline within `C₀ (t + m + 1) + C_ε t^{1+ε}` steps
and `C₀ (labelBound g + t + m + 1) + C_ε t^{1+ε}` addresses in all, for every `ε > 0`. -/
theorem cpap4_flow_ram_almostLinear {F : RAM.Stmt} {T : ℕ → ℕ} (hF : MinCostFlowSolver F T)
    (hT : AlmostLinear T) :
    ∃ (build extract : RAM.Stmt) (C₀ : ℕ), ∀ ε : ℝ, 0 < ε → ∃ C : ℝ,
      ∀ (g : Graph) (cs : List Cycle), cs.Perm (cycles g 4) →
      ∃ (net out pos : List ℕ) (t₁ t₂ t₃ s₁ s₂ s₃ : ℕ),
        RAM.ComputesIn build (flowInput g cs 4) net t₁ s₁ ∧ RAM.ComputesIn F net out t₂ s₂ ∧
        RAM.ComputesIn extract (flowInput g cs 4 ++ out) pos t₃ s₃ ∧
        ((t₁ + t₂ + t₃ : ℕ) : ℝ) ≤
          C₀ * ((cs.length : ℝ) + g.length + 1) + C * (cs.length : ℝ) ^ (1 + ε) ∧
        ((s₁ + s₂ + s₃ : ℕ) : ℝ) ≤
          C₀ * ((labelBound g : ℝ) + cs.length + g.length + 1) + C * (cs.length : ℝ) ^ (1 + ε) ∧
        pos.length = cs.length ∧ (∀ p ∈ pos, p < 4) ∧
        ValidChoices (cs.map selectedOptions) (List.zipWith selected cs pos) ∧
        OptCost g 4 (cost (List.zipWith selected cs pos)) := by
  obtain ⟨build, extract, C₀, h⟩ := cpap4_flow_ram hF
  refine ⟨build, extract, C₀ + C₀ + 1 * T 5, fun ε hε => ?_⟩
  obtain ⟨Cε, hCε⟩ := hT ε hε
  refine ⟨(1 : ℕ) * (Cε * (35 : ℝ) ^ (1 + ε)), fun g cs hperm => ?_⟩
  obtain ⟨net, out, pos, t₁, t₂, t₃, h₁, ht₁, _, h₂, ht₂, h₃, ht₃, hl, hlt, hv, hopt⟩ := h g cs hperm
  refine ⟨net, out, pos, t₁, t₂, t₃, _, _, _, h₁, h₂, h₃, ?_, ?_, hl, hlt, hv, hopt⟩
  · have := split_bound (s := t₁ + t₂ + t₃) (L := cs.length + g.length + 1) (k := 1)
      (C₀ := C₀ + C₀) (t := cs.length) (a := 30) hε (almostLinear_const hCε) hCε (le_refl 30)
      (by omega) (by rw [Nat.add_mul]; omega)
    push_cast at this ⊢
    linarith
  · have e : C₀ * (cs.length + g.length + 1) ≤ C₀ * (labelBound g + cs.length + g.length + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have := split_bound (s := C₀ * (labelBound g + cs.length + g.length + 1) +
      T (30 * cs.length + 5) + C₀ * (cs.length + g.length + 1))
      (L := labelBound g + cs.length + g.length + 1) (k := 1)
      (C₀ := C₀ + C₀) (t := cs.length) (a := 30) hε (almostLinear_const hCε) hCε (le_refl 30)
      (by omega) (by rw [Nat.add_mul]; omega)
    push_cast at this ⊢
    linarith

/-- **The corollary for triangles in almost-linear time**: as `cpap4_flow_ram_almostLinear`. -/
theorem triangle_ram_almostLinear {F : RAM.Stmt} {T : ℕ → ℕ} (hF : MinCostFlowSolver F T)
    (hT : AlmostLinear T) :
    ∃ (build extract : RAM.Stmt) (C₀ : ℕ), ∀ ε : ℝ, 0 < ε → ∃ C : ℝ,
      ∀ (g : Graph) (cs : List Cycle), cs.Perm (cycles g 3) →
      ∃ (net out pos : List ℕ) (t₁ t₂ t₃ s₁ s₂ s₃ : ℕ),
        RAM.ComputesIn build (flowInput g cs 3) net t₁ s₁ ∧ RAM.ComputesIn F net out t₂ s₂ ∧
        RAM.ComputesIn extract (flowInput g cs 3 ++ out) pos t₃ s₃ ∧
        ((t₁ + t₂ + t₃ : ℕ) : ℝ) ≤
          C₀ * ((cs.length : ℝ) + g.length + 1) + C * (cs.length : ℝ) ^ (1 + ε) ∧
        ((s₁ + s₂ + s₃ : ℕ) : ℝ) ≤
          C₀ * ((labelBound g : ℝ) + cs.length + g.length + 1) + C * (cs.length : ℝ) ^ (1 + ε) ∧
        pos.length = cs.length ∧ (∀ p ∈ pos, p < 3) ∧
        ValidChoices (cs.map selectedOptions) (List.zipWith selected cs pos) ∧
        OptCost g 3 (cost (List.zipWith selected cs pos)) := by
  obtain ⟨build, extract, C₀, h⟩ := triangle_ram hF
  refine ⟨build, extract, C₀ + C₀ + 1 * T 5, fun ε hε => ?_⟩
  obtain ⟨Cε, hCε⟩ := hT ε hε
  refine ⟨(1 : ℕ) * (Cε * (35 : ℝ) ^ (1 + ε)), fun g cs hperm => ?_⟩
  obtain ⟨net, out, pos, t₁, t₂, t₃, h₁, ht₁, _, h₂, ht₂, h₃, ht₃, hl, hlt, hv, hopt⟩ := h g cs hperm
  refine ⟨net, out, pos, t₁, t₂, t₃, _, _, _, h₁, h₂, h₃, ?_, ?_, hl, hlt, hv, hopt⟩
  · have := split_bound (s := t₁ + t₂ + t₃) (L := cs.length + g.length + 1) (k := 1)
      (C₀ := C₀ + C₀) (t := cs.length) (a := 21) hε (almostLinear_const hCε) hCε (by norm_num)
      (by omega) (by rw [Nat.add_mul]; omega)
    push_cast at this ⊢
    linarith
  · have e : C₀ * (cs.length + g.length + 1) ≤ C₀ * (labelBound g + cs.length + g.length + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have := split_bound (s := C₀ * (labelBound g + cs.length + g.length + 1) +
      T (21 * cs.length + 5) + C₀ * (cs.length + g.length + 1))
      (L := labelBound g + cs.length + g.length + 1) (k := 1)
      (C₀ := C₀ + C₀) (t := cs.length) (a := 21) hε (almostLinear_const hCε) hCε (by norm_num)
      (by omega) (by rw [Nat.add_mul]; omega)
    push_cast at this ⊢
    linarith

/-! ### Corollary 3: with an enumeration program -/

/-- **Corollary 3, the composition**: an enumeration program `E` writing, on `graphInput g`, the
vertices `cs.flatten` of a permutation `cs` of `cycles g 4` within `B g` steps and the addresses
below `BS g`, followed by the pipeline of Theorem 2 (`build` reads the graph followed by `4`, `t`
and the output of `E`). -/
theorem cpap4_enum_of_lister {F : RAM.Stmt} {T : ℕ → ℕ} (hF : MinCostFlowSolver F T)
    {E : RAM.Stmt} {B BS : Graph → ℕ}
    (hE : ∀ g : Graph, ∃ (cs : List Cycle) (steps : ℕ), cs.Perm (cycles g 4) ∧
      RAM.ComputesIn E (graphInput g) cs.flatten steps (BS g) ∧ steps ≤ B g) :
    ∃ (build extract : RAM.Stmt) (C : ℕ), ∀ g : Graph,
      ∃ (cs : List Cycle) (net out pos : List ℕ) (t₀ t₁ t₂ t₃ : ℕ),
        cs.Perm (cycles g 4) ∧ RAM.ComputesIn E (graphInput g) cs.flatten t₀ (BS g) ∧ t₀ ≤ B g ∧
        RAM.ComputesIn build (graphInput g ++ 4 :: cs.length :: cs.flatten) net t₁
            (C * (labelBound g + (cycles g 4).length + g.length + 1)) ∧
          t₁ ≤ C * ((cycles g 4).length + g.length + 1) ∧
        RAM.ComputesIn F net out t₂ (T (30 * (cycles g 4).length + 5)) ∧
          t₂ ≤ T (30 * (cycles g 4).length + 5) ∧
        RAM.ComputesIn extract (graphInput g ++ 4 :: cs.length :: cs.flatten ++ out) pos t₃
            (C * ((cycles g 4).length + g.length + 1)) ∧
          t₃ ≤ C * ((cycles g 4).length + g.length + 1) ∧
        pos.length = cs.length ∧ (∀ p ∈ pos, p < 4) ∧
        ValidChoices (cs.map selectedOptions) (List.zipWith selected cs pos) ∧
        OptCost g 4 (cost (List.zipWith selected cs pos)) := by
  obtain ⟨build, extract, C, h⟩ := cpap4_flow_ram hF
  refine ⟨build, extract, C, fun g => ?_⟩
  obtain ⟨cs, t₀, hperm, hE₀, ht₀⟩ := hE g
  obtain ⟨net, out, pos, t₁, t₂, t₃, h₁, ht₁, _, h₂, ht₂, h₃, ht₃, hpl, hlt, hv, hopt⟩ :=
    h g cs hperm
  have hl : cs.length = (cycles g 4).length := hperm.length_eq
  refine ⟨cs, net, out, pos, t₀, t₁, t₂, t₃, hperm, hE₀, ht₀, ?_, by rw [← hl]; exact ht₁,
    by rw [← hl]; exact h₂, by rw [← hl]; exact ht₂, ?_, by rw [← hl]; exact ht₃, hpl, hlt, hv,
    hopt⟩
  · rw [← hl]; simpa [flowInput, verts] using h₁
  · rw [← hl]; simpa [flowInput, verts] using h₃

/-- **Corollary 3 in almost-linear time**, for an enumeration within `C (m + 1 + t + X g)` steps
and `C (labelBound g + m + 1 + t + X g)` addresses (the four-cycle enumeration of `Runtimes/C4`
has `X g = min(n², ⌈m^{4/3}⌉)`): the whole pipeline runs within `C₀ (t + m + 1 + X g) + C_ε t^{1+ε}`
steps, and its four programs together access at most
`C₀ (labelBound g + t + m + 1 + X g) + C_ε t^{1+ε}` addresses, for every `ε > 0`, `C₀` not
depending on `ε`. -/
theorem cpap4_enum_of_fourCycles {F : RAM.Stmt} {T : ℕ → ℕ} (hF : MinCostFlowSolver F T)
    (hT : AlmostLinear T) (X : Graph → ℕ)
    (hE : ∃ (E : RAM.Stmt) (CE : ℕ), ∀ g : Graph, ∃ (cs : List Cycle) (steps : ℕ),
      cs.Perm (cycles g 4) ∧
      RAM.ComputesIn E (graphInput g) cs.flatten steps
        (CE * (labelBound g + g.length + 1 + (cycles g 4).length + X g)) ∧
      steps ≤ CE * (g.length + 1 + (cycles g 4).length + X g)) :
    ∃ (E build extract : RAM.Stmt) (C₀ : ℕ), ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ g : Graph,
      ∃ (cs : List Cycle) (net out pos : List ℕ) (t₀ t₁ t₂ t₃ s₀ s₁ s₂ s₃ : ℕ),
        cs.Perm (cycles g 4) ∧ RAM.ComputesIn E (graphInput g) cs.flatten t₀ s₀ ∧
        RAM.ComputesIn build (graphInput g ++ 4 :: cs.length :: cs.flatten) net t₁ s₁ ∧
        RAM.ComputesIn F net out t₂ s₂ ∧
        RAM.ComputesIn extract (graphInput g ++ 4 :: cs.length :: cs.flatten ++ out) pos t₃ s₃ ∧
        ((t₀ + t₁ + t₂ + t₃ : ℕ) : ℝ) ≤
          C₀ * (((cycles g 4).length : ℝ) + g.length + 1 + X g) +
            C * ((cycles g 4).length : ℝ) ^ (1 + ε) ∧
        ((s₀ + s₁ + s₂ + s₃ : ℕ) : ℝ) ≤
          C₀ * ((labelBound g : ℝ) + (cycles g 4).length + g.length + 1 + X g) +
            C * ((cycles g 4).length : ℝ) ^ (1 + ε) ∧
        pos.length = cs.length ∧ (∀ p ∈ pos, p < 4) ∧
        ValidChoices (cs.map selectedOptions) (List.zipWith selected cs pos) ∧
        OptCost g 4 (cost (List.zipWith selected cs pos)) := by
  obtain ⟨E, CE, hE⟩ := hE
  obtain ⟨build, extract, C₀, h⟩ := cpap4_enum_of_lister hF hE
  refine ⟨E, build, extract, CE + C₀ + C₀ + 1 * T 5, fun ε hε => ?_⟩
  obtain ⟨Cε, hCε⟩ := hT ε hε
  refine ⟨(1 : ℕ) * (Cε * (35 : ℝ) ^ (1 + ε)), fun g => ?_⟩
  obtain ⟨cs, net, out, pos, t₀, t₁, t₂, t₃, hperm, h₀, ht₀, h₁, ht₁, h₂, ht₂, h₃, ht₃, hpl, hlt,
    hv, hopt⟩ := h g
  refine ⟨cs, net, out, pos, t₀, t₁, t₂, t₃, _, _, _, _, hperm, h₀, h₁, h₂, h₃, ?_, ?_, hpl, hlt,
    hv, hopt⟩
  · set t := (cycles g 4).length
    have e0 : CE * (g.length + 1 + t + X g) = CE * (t + g.length + 1 + X g) := by ring_nf
    have e1 : C₀ * (t + g.length + 1) ≤ C₀ * (t + g.length + 1 + X g) :=
      Nat.mul_le_mul_left _ (by omega)
    have := split_bound (s := t₀ + t₁ + t₂ + t₃) (L := t + g.length + 1 + X g) (k := 1)
      (C₀ := CE + C₀ + C₀) (t := t) (a := 30) hε (almostLinear_const hCε) hCε (le_refl 30)
      (by omega) (by rw [Nat.add_mul, Nat.add_mul]; omega)
    push_cast at this ⊢
    linarith
  · set t := (cycles g 4).length
    set L := labelBound g
    have e0 : CE * (L + g.length + 1 + t + X g) = CE * (L + t + g.length + 1 + X g) := by ring_nf
    have e1 : C₀ * (L + t + g.length + 1) ≤ C₀ * (L + t + g.length + 1 + X g) :=
      Nat.mul_le_mul_left _ (by omega)
    have e2 : C₀ * (t + g.length + 1) ≤ C₀ * (L + t + g.length + 1 + X g) :=
      Nat.mul_le_mul_left _ (by omega)
    have := split_bound (s := CE * (L + g.length + 1 + t + X g) + C₀ * (L + t + g.length + 1) +
      T (30 * t + 5) + C₀ * (t + g.length + 1)) (L := L + t + g.length + 1 + X g) (k := 1)
      (C₀ := CE + C₀ + C₀) (t := t) (a := 30) hε (almostLinear_const hCε) hCε (le_refl 30)
      (by omega) (by rw [Nat.add_mul, Nat.add_mul]; omega)
    push_cast at this ⊢
    linarith

end STACS2027.Runtimes.Flow

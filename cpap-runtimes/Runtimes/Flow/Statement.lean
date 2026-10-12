module

public import Runtimes.Flow.Main
import Mathlib.Tactic

/-!
# Theorem 2 and the triangle corollary: the statements without the network construction

`cpap4_flow_ram` and `triangle_ram` (`Runtimes/Flow/Main.lean`) say that the construction program
writes exactly `netInput (num4 cs) (n4 cs) (2t) (net4 cs)` (respectively the triangle network),
which names the internal construction of the network (`num4`, `n4`, `net4` and their layers).
The forms below say instead what that network is: the encoding `netInput num n d arcs` of a
network of the class `GoodNet num n arcs` handled by the min-cost flow solver, with `d = 2t`
(respectively `t`), `10t` arcs and at most `6t + 2` nodes (respectively `7t` and `4t + 2`, the
sizes of Section 3), on which `CPAP(G, 4)` (respectively `CPAP(G, 3)`) is the min-cost flow
problem: for every budget `B`, an assignment of cost at most `B` exists iff an integral flow of
value `d` and cost at most `B` exists (Section 3's reduction, for the list `cs`:
`net4_hasAssignment_iff`, `net3_hasAssignment_iff`).

* `cpap4_flow_ram_semantic` (Theorem 2), `triangle_ram_semantic` (the corollary for triangles):
  `cpap4_flow_ram` and `triangle_ram` with this description of the network. Each program runs
  within its time bound and accesses only the addresses below its space bound
  (`RAM.ComputesIn`, input included): the construction `C (labelBound g + t + m + 1)` (its label
  dictionary has `1 + the largest label` cells), the solver `T (30t + 5)` (the hypothesis), the
  extraction `C (t + m + 1)`.
-/

@[expose] public section

namespace STACS2027.Runtimes.Flow

open STACS2027 STACS2027.RAM

section reduction

variable {g : Graph} {cs : List Cycle}

/-- **Section 3's reduction for `k = 4`, for any enumeration `cs` of the four-cycles**: `CPAP(G, 4)`
has an assignment of cost at most `B` iff the network `net4 cs` has an integral flow of value
`2t` and cost at most `B`. -/
theorem net4_hasAssignment_iff (hperm : cs.Perm (cycles g 4)) (B : ℕ) :
    HasAssignment g 4 B ↔
      ∃ flow, IsFlow (net4 cs) flow ∧ flowValue flow = 2 * cs.length ∧ flowCost flow ≤ B := by
  have hcs := isCycle_of_perm hperm
  rw [hasAssignment_iff_perm hperm]
  constructor
  · rintro ⟨ps, hv, hc⟩
    obtain ⟨flow, hf, hval, hcost⟩ := flow_of_assignment4 hcs ps hv
    exact ⟨flow, hf, hval, hcost ▸ hc⟩
  · rintro ⟨flow, hf, hval, hc⟩
    obtain ⟨hv, hcost⟩ := assignment_of_flow4 hcs flow hf hval
    exact ⟨_, hv, hcost.trans hc⟩

/-- **Section 3's reduction for `k = 3`, for any enumeration `cs` of the triangles**: `CPAP(G, 3)`
has an assignment of cost at most `B` iff the network `net3 cs` has an integral flow of value
`t` and cost at most `B`. -/
theorem net3_hasAssignment_iff (hperm : cs.Perm (cycles g 3)) (B : ℕ) :
    HasAssignment g 3 B ↔
      ∃ flow, IsFlow (net3 cs) flow ∧ flowValue flow = cs.length ∧ flowCost flow ≤ B := by
  have hcs := isCycle_of_perm hperm
  rw [hasAssignment_iff_perm hperm]
  constructor
  · rintro ⟨ps, hv, hc⟩
    obtain ⟨flow, hf, hval, hcost⟩ := flow_of_assignment3 hcs ps hv
    exact ⟨flow, hf, hval, hcost ▸ hc⟩
  · rintro ⟨flow, hf, hval, hc⟩
    obtain ⟨hv, hcost⟩ := assignment_of_flow3 hcs flow hf hval
    exact ⟨_, hv, hcost.trans hc⟩

end reduction

/-- **Theorem 2 on the RAM** (the min-cost flow hypothesis `hF`): for any order `cs` of the
four-cycles, `build` writes a network of the solver's class (`10t` arcs, `≤ 6t + 2` nodes) on which
`CPAP(G, 4)` is the min-cost flow problem of value `2t`, `F` answers, and `extract` writes one
position `pos_i < 4` per cycle forming an optimal assignment, each within the stated bounds. -/
theorem cpap4_flow_ram_semantic {F : RAM.Stmt} {T : ℕ → ℕ} (hF : MinCostFlowSolver F T) :
    ∃ (build extract : RAM.Stmt) (C : ℕ), ∀ (g : Graph) (cs : List Cycle), cs.Perm (cycles g 4) →
      ∃ (net out pos : List ℕ) (t₁ t₂ t₃ : ℕ),
        RAM.ComputesIn build (flowInput g cs 4) net t₁
            (C * (labelBound g + cs.length + g.length + 1)) ∧
          t₁ ≤ C * (cs.length + g.length + 1) ∧
        (∃ (num : FlowNode → ℕ) (n : ℕ) (arcs : List Arc), GoodNet num n arcs ∧
          net = netInput num n (2 * cs.length) arcs ∧
          arcs.length = 10 * cs.length ∧ n ≤ 6 * cs.length + 2 ∧
          ∀ B, HasAssignment g 4 B ↔
            ∃ flow, IsFlow arcs flow ∧ flowValue flow = 2 * cs.length ∧ flowCost flow ≤ B) ∧
        RAM.ComputesIn F net out t₂ (T (30 * cs.length + 5)) ∧ t₂ ≤ T (30 * cs.length + 5) ∧
        RAM.ComputesIn extract (flowInput g cs 4 ++ out) pos t₃ (C * (cs.length + g.length + 1)) ∧
          t₃ ≤ C * (cs.length + g.length + 1) ∧
        pos.length = cs.length ∧ (∀ p ∈ pos, p < 4) ∧
        ValidChoices (cs.map selectedOptions) (List.zipWith selected cs pos) ∧
        OptCost g 4 (cost (List.zipWith selected cs pos)) := by
  obtain ⟨build, extract, C, h⟩ := cpap4_flow_ram hF
  refine ⟨build, extract, C, fun g cs hperm => ?_⟩
  obtain ⟨net, out, pos, t₁, t₂, t₃, h₁, ht₁, hnet, h₂, ht₂, h₃, ht₃, hl, hlt, hv, hopt⟩ :=
    h g cs hperm
  have hcs := isCycle_of_perm hperm
  have hn : n4 cs ≤ 6 * cs.length + 2 := by
    have := length_eList4 hcs
    simp only [n4]
    omega
  exact ⟨net, out, pos, t₁, t₂, t₃, h₁, ht₁, ⟨num4 cs, n4 cs, net4 cs, goodNet4 hcs, hnet,
    length_net4 hcs, hn, net4_hasAssignment_iff hperm⟩, h₂, ht₂, h₃, ht₃, hl, hlt, hv, hopt⟩

/-- **The corollary for triangles on the RAM** (`k = 3`): as `cpap4_flow_ram_semantic`, with a network
of value `t` (`7t` arcs, `≤ 4t + 2` nodes), the solver within `T (21t + 5)`, positions `< 3`. -/
theorem triangle_ram_semantic {F : RAM.Stmt} {T : ℕ → ℕ} (hF : MinCostFlowSolver F T) :
    ∃ (build extract : RAM.Stmt) (C : ℕ), ∀ (g : Graph) (cs : List Cycle), cs.Perm (cycles g 3) →
      ∃ (net out pos : List ℕ) (t₁ t₂ t₃ : ℕ),
        RAM.ComputesIn build (flowInput g cs 3) net t₁
            (C * (labelBound g + cs.length + g.length + 1)) ∧
          t₁ ≤ C * (cs.length + g.length + 1) ∧
        (∃ (num : FlowNode → ℕ) (n : ℕ) (arcs : List Arc), GoodNet num n arcs ∧
          net = netInput num n cs.length arcs ∧
          arcs.length = 7 * cs.length ∧ n ≤ 4 * cs.length + 2 ∧
          ∀ B, HasAssignment g 3 B ↔
            ∃ flow, IsFlow arcs flow ∧ flowValue flow = cs.length ∧ flowCost flow ≤ B) ∧
        RAM.ComputesIn F net out t₂ (T (21 * cs.length + 5)) ∧ t₂ ≤ T (21 * cs.length + 5) ∧
        RAM.ComputesIn extract (flowInput g cs 3 ++ out) pos t₃ (C * (cs.length + g.length + 1)) ∧
          t₃ ≤ C * (cs.length + g.length + 1) ∧
        pos.length = cs.length ∧ (∀ p ∈ pos, p < 3) ∧
        ValidChoices (cs.map selectedOptions) (List.zipWith selected cs pos) ∧
        OptCost g 3 (cost (List.zipWith selected cs pos)) := by
  obtain ⟨build, extract, C, h⟩ := triangle_ram hF
  refine ⟨build, extract, C, fun g cs hperm => ?_⟩
  obtain ⟨net, out, pos, t₁, t₂, t₃, h₁, ht₁, hnet, h₂, ht₂, h₃, ht₃, hl, hlt, hv, hopt⟩ :=
    h g cs hperm
  have hcs := isCycle_of_perm hperm
  have hn : n3 cs ≤ 4 * cs.length + 2 := by
    have := length_eList3 hcs
    simp only [n3]
    omega
  exact ⟨net, out, pos, t₁, t₂, t₃, h₁, ht₁, ⟨num3 cs, n3 cs, net3 cs, goodNet3 hcs, hnet,
    length_net3 hcs, hn, net3_hasAssignment_iff hperm⟩, h₂, ht₂, h₃, ht₃, hl, hlt, hv, hopt⟩

end STACS2027.Runtimes.Flow

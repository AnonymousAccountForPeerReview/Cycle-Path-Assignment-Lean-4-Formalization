module

public import Runtimes.Flow.SortTri
public import Runtimes.Flow.Statement
import Mathlib.Tactic

/-!
# The four-cycle network with the sorting front end

The program below constructs the network from the canonical enumeration `cycles g 4`.
Its addresses are independent of vertex labels, and its construction time is logarithmic
in the number of cycles per edge occurrence. `Flow/EnumeratedConstruction.lean` generalizes
the front end and proves the broader `SortedNetworkConstruction` proposition, whose input
permits any cycle permutation.
The minimum-cost flow solver remains an explicit hypothesis only in the pipeline theorem.
-/

@[expose] public section

namespace STACS2027.Runtimes.Flow

open STACS2027 STACS2027.RAM

/-- Construct the four-cycle network using the proved sorting front end. -/
def buildSorted : Stmt := .seq ZeroCost.stepInit (.seq Sort.front out4)

/-- The end of the sorting front end's workspace, measured from the initial input. -/
def sortedBuildSpace (g : Graph) : ℕ := Sort.fEnd g 4 (ZeroCost.bD g 4)

/-- A uniform constant for the sorting construction. -/
def sortedBuildConstant : ℕ := 4 * Sort.CF + 200

/-- The exact logarithmic bound used for the construction. -/
def sortedBuildTime (g : Graph) : ℕ :=
  sortedBuildConstant * (((cycles g 4).length + 1) *
    (Nat.clog 2 (4 * (cycles g 4).length) + 1))

/-- The sorting construction writes the same network as the label-dictionary construction. -/
theorem sortedBuild_spec (g : Graph) {S : ℕ} (hS : sortedBuildSpace g ≤ S) :
    HTB S buildSorted (fun c => c = initial (flowInput g (cycles g 4) 4))
      (fun c => c.out = netEnc4 (cycles g 4)) (sortedBuildTime g) := by
  set t := (cycles g 4).length with ht
  have hf := Sort.ffits g 4 (ZeroCost.bD g 4) hS
  have hd : ZeroCost.bD g 4 ≤ S := by
    have := hf.1
    omega
  have h₁ := ZeroCost.stepInit_spec (S := S) g 4 hd
  have h₂ : HTB S Sort.front (ZeroCost.InitPost g 4)
      (fun c => OB (cycles g 4) 4 (Sort.fEID g 4 (ZeroCost.bD g 4))
        (Sort.fCNT g 4 (ZeroCost.bD g 4)) c ∧ c.out = [])
      (Sort.CF * (Sort.fL g 4 * (Nat.clog 2 (Sort.fL g 4) + 1) + 1)) :=
    HTB.of_forall fun c₀ hI => (Sort.front_spec g 4 c₀ (Sort.frontIn_of_initPost hI)
      (by rw [hI.rfree]; exact hS)).post fun c ⟨hP, _, ho⟩ => by
        rw [hI.rfree] at hP
        exact ⟨ob_of_front hP, by rw [ho, hI.rout]⟩
  have h₃ := out4_specA (isCycle_cycles g 4) (S := S)
    hf.2.2.2.2.2.1 hf.2.2.2.2.2.2
  refine ((h₁.seq (h₂.seq h₃)).pre fun c hc => hc).weaken ?_
  change 5 * t + 16 + (Sort.CF * (4 * t * (Nat.clog 2 (4 * t) + 1) + 1) +
    (130 * t + 30)) ≤ sortedBuildConstant * ((t + 1) * (Nat.clog 2 (4 * t) + 1))
  unfold sortedBuildConstant
  have hlog : 1 ≤ Nat.clog 2 (4 * t) + 1 := by omega
  nlinarith [Nat.zero_le Sort.CF]

/-- Memory is linear in the graph input and cycle list, with no dependence on labels. -/
theorem sortedBuild_memory (g : Graph) :
    sortedBuildSpace g ≤ 2 * g.length + 64 * (cycles g 4).length + 4 := by
  have := Sort.fEnd_le g 4 (ZeroCost.bD g 4)
  have hD : ZeroCost.bD g 4 = 2 * g.length + 3 + 4 * (cycles g 4).length := rfl
  have hL : Sort.fL g 4 = 4 * (cycles g 4).length := rfl
  unfold sortedBuildSpace
  omega

/-- Changing the upper logarithm of `4t` to the manuscript's `log₂(t+1)` costs a constant. -/
theorem sortedBuild_logarithm (t : ℕ) :
    Nat.clog 2 (4 * t) + 1 ≤ 4 * (Nat.log 2 (t + 1) + 1) := by
  have hclog : Nat.clog 2 (4 * t) ≤ Nat.log 2 (t + 1) + 3 := by
    apply Nat.clog_le_of_le_pow
    have hpow := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (t + 1)
    rw [Nat.succ_eq_add_one, pow_add] at hpow
    rw [pow_add]
    norm_num at hpow ⊢
    omega
  omega

/-- The construction bound in the logarithmic form used in Appendix A. -/
theorem sortedBuildTime_paper (g : Graph) :
    sortedBuildTime g ≤ 4 * sortedBuildConstant *
      (((cycles g 4).length + 1) * (Nat.log 2 ((cycles g 4).length + 1) + 1)) := by
  have hlog := sortedBuild_logarithm (cycles g 4).length
  unfold sortedBuildTime
  calc
    sortedBuildConstant * (((cycles g 4).length + 1) *
        (Nat.clog 2 (4 * (cycles g 4).length) + 1)) ≤
      sortedBuildConstant * (((cycles g 4).length + 1) *
        (4 * (Nat.log 2 ((cycles g 4).length + 1) + 1))) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hlog)
    _ = _ := by ring

/-- An actual bounded RAM run of the sorting construction. -/
theorem sortedBuild_computes (g : Graph) :
    ∃ steps : ℕ,
      RAM.ComputesIn buildSorted (flowInput g (cycles g 4) 4)
        (netEnc4 (cycles g 4)) steps (sortedBuildSpace g) ∧
      steps ≤ sortedBuildTime g := by
  obtain ⟨steps, hsteps, hrun⟩ := HTB.computesIn (sortedBuild_spec g le_rfl)
  exact ⟨steps, hrun, hsteps⟩

/-- One deterministic program, uniform logarithmic time, and linear memory on canonical
cycle inputs; unlike the pipeline theorem, this construction needs no flow hypothesis. -/
theorem sortedNetwork_construction :
    ∃ (build : RAM.Stmt) (C : ℕ), ∀ g : Graph,
      ∃ (net : List ℕ) (steps : ℕ),
        RAM.ComputesIn build (flowInput g (cycles g 4) 4) net steps
          (C * ((cycles g 4).length + g.length + 1)) ∧
        steps ≤ C * (((cycles g 4).length + g.length + 1) *
          (Nat.log 2 ((cycles g 4).length + 1) + 1)) ∧
        (∃ (num : FlowNode → ℕ) (n : ℕ) (arcs : List Arc), GoodNet num n arcs ∧
          net = netInput num n (2 * (cycles g 4).length) arcs ∧
          arcs.length = 10 * (cycles g 4).length ∧
          n ≤ 6 * (cycles g 4).length + 2 ∧
          ∀ B, HasAssignment g 4 B ↔
            ∃ flow, IsFlow arcs flow ∧ flowValue flow = 2 * (cycles g 4).length ∧
              flowCost flow ≤ B) := by
  refine ⟨buildSorted, 4 * sortedBuildConstant + 64, fun g => ?_⟩
  obtain ⟨steps, hrun, hsteps⟩ := sortedBuild_computes g
  have hmemory := sortedBuild_memory g
  have htime := sortedBuildTime_paper g
  have hcs := isCycle_cycles g 4
  have hn : n4 (cycles g 4) ≤ 6 * (cycles g 4).length + 2 := by
    have := length_eList4 hcs
    simp only [n4]
    omega
  refine ⟨netEnc4 (cycles g 4), steps, hrun.mono ?_, ?_,
    ⟨num4 (cycles g 4), n4 (cycles g 4), net4 (cycles g 4), goodNet4 hcs,
      rfl, length_net4 hcs, hn, net4_hasAssignment_iff (List.Perm.refl _)⟩⟩
  · refine hmemory.trans ?_
    calc
      2 * g.length + 64 * (cycles g 4).length + 4 ≤
        64 * ((cycles g 4).length + g.length + 1) := by omega
      _ ≤ (4 * sortedBuildConstant + 64) * ((cycles g 4).length + g.length + 1) :=
        Nat.mul_le_mul_right _ (by omega)
  · have hinput : (cycles g 4).length + 1 ≤ (cycles g 4).length + g.length + 1 := by omega
    have hfactor : 4 * sortedBuildConstant ≤ 4 * sortedBuildConstant + 64 := by omega
    exact hsteps.trans (htime.trans (Nat.mul_le_mul hfactor
      (Nat.mul_le_mul_right _ hinput)))

/-- The complete four-cycle pipeline with the sorting construction on the canonical list.
Only its flow-solver stage has an external hypothesis. -/
theorem sortedNetwork_pipeline {F : RAM.Stmt} {T : ℕ → ℕ}
    (hF : MinCostFlowSolver F T) (g : Graph) :
    ∃ (out pos : List ℕ) (t₁ t₂ t₃ : ℕ),
      RAM.ComputesIn buildSorted (flowInput g (cycles g 4) 4)
        (netEnc4 (cycles g 4)) t₁ (sortedBuildSpace g) ∧
      t₁ ≤ sortedBuildTime g ∧
      RAM.ComputesIn F (netEnc4 (cycles g 4)) out t₂
        (T (30 * (cycles g 4).length + 5)) ∧
      t₂ ≤ T (30 * (cycles g 4).length + 5) ∧
      RAM.ComputesIn extract4 (flowInput g (cycles g 4) 4 ++ out) pos t₃
        (bD g (cycles g 4) 4 + 6 * (cycles g 4).length + 1) ∧
      t₃ ≤ 18 * (cycles g 4).length + 20 ∧
      pos.length = (cycles g 4).length ∧ (∀ p ∈ pos, p < 4) ∧
      ValidChoices ((cycles g 4).map selectedOptions)
        (List.zipWith selected (cycles g 4) pos) ∧
      OptCost g 4 (cost (List.zipWith selected (cycles g 4) pos)) := by
  obtain ⟨t₁, h₁, ht₁⟩ := sortedBuild_computes g
  obtain ⟨out, pos, _, t₂, t₃, _, _, h₂, ht₂, h₃, ht₃, _, hl, hp, hv, ho⟩ :=
    cpap4_flow_core hF (List.Perm.refl (cycles g 4))
  exact ⟨out, pos, t₁, t₂, t₃, h₁, ht₁, h₂, ht₂, h₃, ht₃, hl, hp, hv, ho⟩

end STACS2027.Runtimes.Flow

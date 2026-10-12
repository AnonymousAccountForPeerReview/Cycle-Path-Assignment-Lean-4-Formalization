module

public import Runtimes.Flow.CutFacts
public import Mathlib.Logic.Relation
import Mathlib.Tactic

/-! # Finite reverse residual reachability and the maximal cut region -/

@[expose] public section

namespace STACS2027.Runtimes.Flow

/-- The unique available residual orientation of each original occurrence. -/
def availableEdge {arcs : ℕ} (flow : IndexedFlow arcs) (i : Fin arcs) : ResidualEdge arcs :=
  ⟨i, flow i⟩

/-- One available residual step between numbered vertices. -/
def ResidualStep {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs) (flow : IndexedFlow arcs)
    (u v : Fin nodes) : Prop :=
  ∃ i, residualTail net (availableEdge flow i) = u ∧ residualHead net (availableEdge flow i) = v

/-- Any finite sequence of available residual steps, including length zero. -/
def ResidualReach {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs) (flow : IndexedFlow arcs)
    (u v : Fin nodes) : Prop := Relation.ReflTransGen (ResidualStep net flow) u v

/-- Add the immediate residual predecessors of a finite node set. -/
def reverseStep {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs) (flow : IndexedFlow arcs)
    (vertices : Finset (Fin nodes)) : Finset (Fin nodes) :=
  vertices ∪ Finset.univ.filter fun v =>
    ∃ i : Fin arcs, residualTail net (availableEdge flow i) = v ∧
      residualHead net (availableEdge flow i) ∈ vertices

/-- Reverse residual reachability after at most `rounds` edges. -/
def reverseReachSet {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs) (flow : IndexedFlow arcs) :
    ℕ → Finset (Fin nodes)
  | 0 => {net.sink}
  | rounds + 1 => reverseStep net flow (reverseReachSet net flow rounds)

private theorem subset_reverseStep {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    (flow : IndexedFlow arcs) (vertices : Finset (Fin nodes)) :
    vertices ⊆ reverseStep net flow vertices := Finset.subset_union_left

private theorem reverseReachSet_stays_fixed {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    (flow : IndexedFlow arcs) {rounds : ℕ}
    (h : reverseReachSet net flow (rounds + 1) = reverseReachSet net flow rounds) (extra : ℕ) :
    reverseReachSet net flow (rounds + extra) = reverseReachSet net flow rounds := by
  induction extra with
  | zero => simp
  | succ extra ih =>
    change reverseStep net flow (reverseReachSet net flow (rounds + extra)) =
      reverseReachSet net flow rounds
    rw [ih]
    exact h

/-- `nodes` rounds suffice: every earlier strict expansion adds at least one node. -/
theorem reverseReachSet_fixed {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    (flow : IndexedFlow arcs) :
    reverseStep net flow (reverseReachSet net flow nodes) = reverseReachSet net flow nodes := by
  by_contra hnot
  have hne : ∀ k, k ≤ nodes → reverseReachSet net flow k ≠ reverseReachSet net flow (k + 1) := by
    intro k hk heq
    have ha := reverseReachSet_stays_fixed net flow heq.symm (nodes - k)
    have hb := reverseReachSet_stays_fixed net flow heq.symm (nodes - k + 1)
    have hka : k + (nodes - k) = nodes := by omega
    have hkb : k + (nodes - k + 1) = nodes + 1 := by omega
    rw [hka] at ha
    rw [hkb] at hb
    exact hnot (hb.trans ha.symm)
  have hcard : ∀ k, k ≤ nodes + 1 → k + 1 ≤ (reverseReachSet net flow k).card := by
    intro k
    induction k with
    | zero => intro _; simp [reverseReachSet]
    | succ k ih =>
      intro hk
      have hi := ih (by omega)
      have hlt : (reverseReachSet net flow k).card < (reverseReachSet net flow (k + 1)).card := by
        apply Finset.card_lt_card
        exact Finset.ssubset_iff_subset_ne.mpr
          ⟨subset_reverseStep net flow _, hne k (by omega)⟩
      omega
  have hlarge := hcard (nodes + 1) (by omega)
  have hsmall := Finset.card_le_univ (reverseReachSet net flow (nodes + 1))
  simp only [Fintype.card_fin] at hsmall
  omega

/-- A node marked by the executable reverse expansion really reaches the sink. -/
theorem reverseReachSet_sound {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    (flow : IndexedFlow arcs) (rounds : ℕ) (v : Fin nodes)
    (hv : v ∈ reverseReachSet net flow rounds) : ResidualReach net flow v net.sink := by
  induction rounds generalizing v with
  | zero =>
    have : v = net.sink := by simpa [reverseReachSet] using hv
    subst v
    exact .refl
  | succ rounds ih =>
    rcases Finset.mem_union.mp hv with hv | hv
    · exact ih v hv
    · obtain ⟨i, hi, hh⟩ := (Finset.mem_filter.mp hv).2
      exact (ih _ hh).head ⟨i, hi, rfl⟩

/-- Every node that reaches the sink has been found after the bounded expansion. -/
theorem reverseReachSet_complete {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    (flow : IndexedFlow arcs) (v : Fin nodes) (hv : ResidualReach net flow v net.sink) :
    v ∈ reverseReachSet net flow nodes := by
  induction hv using Relation.ReflTransGen.head_induction_on with
  | refl =>
    have hmem : ∀ k, net.sink ∈ reverseReachSet net flow k := by
      intro k
      induction k with
      | zero => simp [reverseReachSet]
      | succ k ih => exact subset_reverseStep net flow _ ih
    exact hmem nodes
  | head hstep _ ih =>
    obtain ⟨i, hi, hh⟩ := hstep
    rw [← reverseReachSet_fixed net flow]
    apply Finset.mem_union_right
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, ⟨i, hi, hh ▸ ih⟩⟩

/-- Source side of the maximal residual-closed cut: nodes not reaching the sink. -/
def maximalCutRegion {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    (flow : IndexedFlow arcs) (v : Fin nodes) : Bool :=
  decide (v ∉ reverseReachSet net flow nodes)

/-- The reverse-reachability complement is residual-closed. -/
theorem maximalCutRegion_closed {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    (flow : IndexedFlow arcs) : ResidualClosed net flow (maximalCutRegion net flow) := by
  intro edge ha htail
  simp only [maximalCutRegion, decide_eq_true_eq] at htail ⊢
  intro hh
  apply htail
  apply reverseReachSet_complete net flow
  have hreach := reverseReachSet_sound net flow nodes _ hh
  apply hreach.head
  exact ⟨edge.index, by cases edge; simp_all [availableEdge, residualAvailable],
    by cases edge; simp_all [availableEdge, residualAvailable]⟩

/-- Every residual-closed region avoiding the sink is contained in the maximal region. -/
theorem residualClosed_subset_maximalCutRegion {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    (flow : IndexedFlow arcs) {region : Fin nodes → Bool} (hc : ResidualClosed net flow region)
    (ht : region net.sink = false) (v : Fin nodes) (hv : region v = true) :
    maximalCutRegion net flow v = true := by
  simp only [maximalCutRegion, decide_eq_true_eq]
  intro hmem
  have hreach := reverseReachSet_sound net flow nodes v hmem
  have hprop : ∀ {u w}, ResidualReach net flow u w → region u = true → region w = true := by
    intro u w h
    induction h with
    | refl => exact id
    | tail _ hstep ih =>
      intro hu
      obtain ⟨i, hi, hh⟩ := hstep
      have hav : residualAvailable flow (availableEdge flow i) := rfl
      rw [← hh]
      apply hc _ hav
      rw [hi]
      exact ih hu
  have := hprop hreach hv
  simp [ht] at this

/-- The bounded reverse closure yields the maximum source-side minimum cut whenever a
concrete feasible flow has no residual source/sink path. -/
theorem maximalCutRegion_minimum {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    {flow : IndexedFlow arcs} {d : ℕ} (hf : IsIndexedFlow net d flow)
    (hno : ¬ ResidualReach net flow net.source net.sink) :
    IsMinimumCut net (maximalCutRegion net flow) ∧
      cutSize net (maximalCutRegion net flow) = d ∧
      ∀ other : Fin nodes → Bool, IsMinimumCut net other →
        ∀ v, other v = true → maximalCutRegion net flow v = true := by
  have hs : maximalCutRegion net flow net.source = true := by
    simp only [maximalCutRegion, decide_eq_true_eq]
    exact fun hmem => hno (reverseReachSet_sound net flow nodes _ hmem)
  have ht : maximalCutRegion net flow net.sink = false := by
    have hmem := reverseReachSet_complete net flow net.sink Relation.ReflTransGen.refl
    simp [maximalCutRegion, hmem]
  obtain ⟨hmin, heq⟩ := minimumCut_of_flow_closed net hf hs ht (maximalCutRegion_closed net flow)
  refine ⟨hmin, heq, fun other hother v hv => ?_⟩
  have heqOther : cutSize net other = d := by
    have hl := value_le_cutSize net hf hother.1 hother.2.1
    have hu := hother.2.2 _ hs ht
    rw [heq] at hu
    omega
  exact residualClosed_subset_maximalCutRegion net flow
    (residualClosed_of_value_eq_cutSize net hf hother.1 hother.2.1 heqOther) hother.2.1 v hv

end STACS2027.Runtimes.Flow

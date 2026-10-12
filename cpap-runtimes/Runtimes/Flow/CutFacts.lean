module

public import Runtimes.Flow.IndexedFacts
import Mathlib.Tactic

/-! # Cut cardinalities and integral-flow certificates -/

@[expose] public section

namespace STACS2027.Runtimes.Flow

/-- Number of original arc occurrences leaving a Boolean node region. -/
def cutSize {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs) (region : Fin nodes → Bool) : ℕ :=
  ∑ i : Fin arcs, if region (net.tail i) && !(region (net.head i)) then 1 else 0

/-- Signed selected-flow divergence across a Boolean node region. -/
def cutDivergence {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    (flow : IndexedFlow arcs) (region : Fin nodes → Bool) : ℤ :=
  ∑ i : Fin arcs, if flow i then
    (if region (net.tail i) then (1 : ℤ) else 0) -
      (if region (net.head i) then (1 : ℤ) else 0) else 0

/-- An available residual arc cannot leave this region. -/
def ResidualClosed {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    (flow : IndexedFlow arcs) (region : Fin nodes → Bool) : Prop :=
  ∀ edge, residualAvailable flow edge → region (residualTail net edge) = true →
    region (residualHead net edge) = true

/-- Minimum cardinality source/sink cut, with original nodes retained. -/
def IsMinimumCut {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    (region : Fin nodes → Bool) : Prop :=
  region net.source = true ∧ region net.sink = false ∧
    ∀ other : Fin nodes → Bool, other net.source = true → other net.sink = false →
      cutSize net region ≤ cutSize net other

private theorem sumRegionBalance {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    (flow : IndexedFlow arcs) (region : Fin nodes → Bool) :
    (∑ v : Fin nodes, if region v then indexedBalance net flow v else 0) =
      cutDivergence net flow region := by
  unfold indexedBalance cutDivergence
  have h : (∑ v : Fin nodes,
      if region v then ∑ i : Fin arcs, if flow i then
        (if net.tail i = v then (1 : ℤ) else 0) - (if net.head i = v then (1 : ℤ) else 0)
        else 0 else 0) =
      ∑ v : Fin nodes, ∑ i : Fin arcs, if region v then
        (if flow i then
          (if net.tail i = v then (1 : ℤ) else 0) - (if net.head i = v then (1 : ℤ) else 0)
          else 0) else 0 := by
    apply Finset.sum_congr rfl
    intro v _
    cases region v <;> simp
  rw [h, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  cases hf : flow i
  · simp [hf]
  · have hterm : ∀ v : Fin nodes,
        (if region v then
          (if net.tail i = v then (1 : ℤ) else 0) - (if net.head i = v then (1 : ℤ) else 0)
          else 0) =
          (if v = net.tail i then (if region (net.tail i) then (1 : ℤ) else 0) else 0) -
            (if v = net.head i then (if region (net.head i) then (1 : ℤ) else 0) else 0) := by
      intro v
      by_cases ht : v = net.tail i
      · subst v
        by_cases hh : net.tail i = net.head i
        · rw [hh]
          simp
        · simp [hh, Ne.symm hh]
      · by_cases hh : v = net.head i
        · subst v
          cases region (net.head i) <;> simp [ht, Ne.symm ht]
        · simp [ht, hh, Ne.symm ht, Ne.symm hh]
    simp only [ite_true]
    simp_rw [hterm]
    rw [Finset.sum_sub_distrib]
    simp

/-- Conservation telescopes: every source/sink region has divergence exactly the value. -/
theorem cutDivergence_eq_value {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    {flow : IndexedFlow arcs} {d : ℕ} (hf : IsIndexedFlow net d flow)
    {region : Fin nodes → Bool} (hs : region net.source = true) (ht : region net.sink = false) :
    cutDivergence net flow region = (d : ℤ) := by
  rw [← sumRegionBalance]
  have hterm : ∀ v : Fin nodes,
      (if region v then indexedBalance net flow v else 0) =
        if v = net.source then (d : ℤ) else 0 := by
    intro v
    rw [hf v]
    by_cases hsource : v = net.source
    · subst v
      simp [hs]
    · by_cases hsink : v = net.sink
      · subst v
        simp [ht, net.source_ne_sink, Ne.symm net.source_ne_sink]
      · simp [hsource, hsink]
  simp_rw [hterm]
  simp

/-- Any feasible integral flow lower-bounds the cardinality of every source/sink cut. -/
theorem value_le_cutSize {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    {flow : IndexedFlow arcs} {d : ℕ} (hf : IsIndexedFlow net d flow)
    {region : Fin nodes → Bool} (hs : region net.source = true) (ht : region net.sink = false) :
    d ≤ cutSize net region := by
  have h : cutDivergence net flow region ≤ (cutSize net region : ℤ) := by
    unfold cutDivergence cutSize
    rw [Nat.cast_sum]
    apply Finset.sum_le_sum
    intro i _
    cases flow i <;> cases region (net.tail i) <;> cases region (net.head i) <;> norm_num
  rw [cutDivergence_eq_value net hf hs ht] at h
  exact_mod_cast h

/-- A residual-closed source/sink cut is saturated outward and carries no inward flow. -/
theorem cutDivergence_eq_cutSize_of_closed {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    (flow : IndexedFlow arcs) (region : Fin nodes → Bool) (hc : ResidualClosed net flow region) :
    cutDivergence net flow region = (cutSize net region : ℤ) := by
  unfold cutDivergence cutSize
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hclosed := hc (⟨i, flow i⟩ : ResidualEdge arcs) rfl
  cases hf : flow i <;> cases htail : region (net.tail i) <;>
    cases hhead : region (net.head i) <;>
    simp [residualTail, residualHead, hf, htail, hhead] at hclosed ⊢

/-- A concrete integral flow and residual-closed region certify a minimum cut; the theorem
introduces no new algorithmic assumption. -/
theorem minimumCut_of_flow_closed {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    {flow : IndexedFlow arcs} {d : ℕ} (hf : IsIndexedFlow net d flow)
    {region : Fin nodes → Bool} (hs : region net.source = true) (ht : region net.sink = false)
    (hc : ResidualClosed net flow region) :
    IsMinimumCut net region ∧ cutSize net region = d := by
  have heq : cutSize net region = d := by
    have h := cutDivergence_eq_cutSize_of_closed net flow region hc
    rw [cutDivergence_eq_value net hf hs ht] at h
    exact_mod_cast h.symm
  refine ⟨⟨hs, ht, fun other hos hot => ?_⟩, heq⟩
  rw [heq]
  exact value_le_cutSize net hf hos hot

/-- Equality in the flow/cut bound forces saturation outward and zero inward flow, so
there is no available residual arc leaving the cut. -/
theorem residualClosed_of_value_eq_cutSize {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    {flow : IndexedFlow arcs} {d : ℕ} (hf : IsIndexedFlow net d flow)
    {region : Fin nodes → Bool} (hs : region net.source = true) (ht : region net.sink = false)
    (heq : cutSize net region = d) : ResidualClosed net flow region := by
  let gap (i : Fin arcs) : ℤ :=
    (if region (net.tail i) && !(region (net.head i)) then 1 else 0) -
      (if flow i then (if region (net.tail i) then 1 else 0) -
        (if region (net.head i) then 1 else 0) else 0)
  have hnonneg : ∀ i, 0 ≤ gap i := by
    intro i
    dsimp [gap]
    cases flow i <;> cases region (net.tail i) <;> cases region (net.head i) <;> norm_num
  have hsum : (∑ i : Fin arcs, gap i) = 0 := by
    dsimp [gap]
    rw [Finset.sum_sub_distrib]
    have hcast : (∑ i : Fin arcs,
        if region (net.tail i) && !(region (net.head i)) then (1 : ℤ) else 0) =
        (cutSize net region : ℤ) := by simp [cutSize, Nat.cast_sum]
    rw [hcast]
    change (cutSize net region : ℤ) - cutDivergence net flow region = 0
    rw [cutDivergence_eq_value net hf hs ht, heq, sub_self]
  have hzero : ∀ i, gap i = 0 := by
    intro i
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnonneg j)).mp hsum i (Finset.mem_univ i)
  intro edge ha htail
  have hz := hzero edge.index
  rcases edge with ⟨i, reverse⟩
  dsimp [residualAvailable] at ha
  subst reverse
  cases hflow : flow i <;> cases ht' : region (net.tail i) <;>
    cases hh' : region (net.head i) <;>
    simp [residualTail, residualHead, gap, hflow, ht', hh'] at hz htail ⊢

end STACS2027.Runtimes.Flow

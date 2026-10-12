module

public import Runtimes.Flow.ReverseReach
import Mathlib.Tactic

/-! # A residual source/sink path increases an integral flow -/

@[expose] public section

namespace STACS2027.Runtimes.Flow

/-- A walk in the available residual orientation, retaining occurrence indices. -/
def ResidualWalk {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs) (flow : IndexedFlow arcs)
    (u v : Fin nodes) : List (Fin arcs) → Prop
  | [] => u = v
  | i :: rest => residualTail net (availableEdge flow i) = u ∧
      ResidualWalk net flow (residualHead net (availableEdge flow i)) v rest

private theorem residualWalk_suffix {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    (flow : IndexedFlow arcs) (front suffix : List (Fin arcs)) (u v : Fin nodes)
    (h : ResidualWalk net flow u v (front ++ suffix)) :
    ∃ w, ResidualWalk net flow w v suffix := by
  induction front generalizing u with
  | nil => exact ⟨u, h⟩
  | cons i front ih => exact ih _ h.2

private theorem residualWalk_simplify {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    (flow : IndexedFlow arcs) (indices : List (Fin arcs)) (u v : Fin nodes)
    (h : ResidualWalk net flow u v indices) :
    ∃ simple, simple.Nodup ∧ simple ⊆ indices ∧ ResidualWalk net flow u v simple := by
  induction hn : indices.length using Nat.strong_induction_on generalizing indices u with
  | h n ih =>
    cases indices with
    | nil => exact ⟨[], by simp, by simp, h⟩
    | cons i rest =>
      by_cases hi : i ∈ rest
      · obtain ⟨front, suffix, hsplit⟩ := List.mem_iff_append.mp hi
        obtain ⟨w, hw⟩ := residualWalk_suffix net flow front (i :: suffix) _ v (hsplit ▸ h.2)
        have hshort : (i :: suffix).length < n := by
          simp only [List.length_cons] at hn ⊢
          have hlength : rest.length = front.length + (suffix.length + 1) := by
            rw [hsplit]; simp
          omega
        have hwalk : ResidualWalk net flow u v (i :: suffix) := ⟨h.1, hw.2⟩
        obtain ⟨simple, hnodup, hsubset, hsimple⟩ :=
          ih _ hshort (i :: suffix) u hwalk rfl
        refine ⟨simple, hnodup, ?_, hsimple⟩
        intro j hj
        have hj' := hsubset hj
        apply List.mem_cons.mpr
        exact Or.inr (hsplit ▸ List.mem_append_right front hj')
      · have hshort : rest.length < n := by simp only [List.length_cons] at hn; omega
        obtain ⟨simple, hnodup, hsubset, hsimple⟩ :=
          ih _ hshort rest _ h.2 rfl
        refine ⟨i :: simple, List.nodup_cons.mpr ⟨fun hm => hi (hsubset hm), hnodup⟩,
          ?_, h.1, hsimple⟩
        exact List.cons_subset_cons i hsubset

theorem residualReach_simple_walk {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    (flow : IndexedFlow arcs) {u v : Fin nodes} (h : ResidualReach net flow u v) :
    ∃ indices, indices.Nodup ∧ ResidualWalk net flow u v indices := by
  have hwalk : ∃ indices, ResidualWalk net flow u v indices := by
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl => exact ⟨[], rfl⟩
    | head hstep _ ih =>
      obtain ⟨i, ht, hh⟩ := hstep
      obtain ⟨indices, hi⟩ := ih
      exact ⟨i :: indices, ht, hh ▸ hi⟩
  obtain ⟨indices, hindices⟩ := hwalk
  obtain ⟨simple, hn, _, hs⟩ := residualWalk_simplify net flow indices u v hindices
  exact ⟨simple, hn, hs⟩

/-- Toggle every occurrence of an index-simple residual walk. -/
def augmentFlow {arcs : ℕ} (flow : IndexedFlow arcs) (indices : List (Fin arcs)) : IndexedFlow arcs :=
  fun i => if i ∈ indices then !(flow i) else flow i

private theorem sumOnList {arcs : ℕ} (indices : List (Fin arcs)) (hn : indices.Nodup)
    (term : Fin arcs → ℤ) :
    (∑ i : Fin arcs, if i ∈ indices then term i else 0) = (indices.map term).sum := by
  rw [← List.sum_toFinset term hn]
  calc
    (∑ i : Fin arcs, if i ∈ indices then term i else 0) =
        ∑ i ∈ indices.toFinset, if i ∈ indices then term i else 0 := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      simp only [List.mem_toFinset] at hi
      simp [hi]
    _ = indices.toFinset.sum term := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [List.mem_toFinset] at hi
      simp [hi]

theorem augmentFlow_balance {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    (flow : IndexedFlow arcs) (indices : List (Fin arcs)) (hn : indices.Nodup) (v : Fin nodes) :
    indexedBalance net (augmentFlow flow indices) v = indexedBalance net flow v +
      ((indices.map fun i =>
        (if residualTail net (availableEdge flow i) = v then (1 : ℤ) else 0) -
          (if residualHead net (availableEdge flow i) = v then (1 : ℤ) else 0)).sum) := by
  have hterm : ∀ i : Fin arcs,
      (if augmentFlow flow indices i then
        (if net.tail i = v then (1 : ℤ) else 0) - (if net.head i = v then (1 : ℤ) else 0)
        else 0) =
      (if flow i then
        (if net.tail i = v then (1 : ℤ) else 0) - (if net.head i = v then (1 : ℤ) else 0)
        else 0) +
      (if i ∈ indices then
        (if residualTail net (availableEdge flow i) = v then (1 : ℤ) else 0) -
          (if residualHead net (availableEdge flow i) = v then (1 : ℤ) else 0) else 0) := by
    intro i
    by_cases hi : i ∈ indices <;> cases hf : flow i <;>
      simp [augmentFlow, hi, hf, availableEdge, residualTail, residualHead] <;> omega
  unfold indexedBalance
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, sumOnList indices hn]

theorem residualWalk_balance {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    (flow : IndexedFlow arcs) (indices : List (Fin arcs)) (u v w : Fin nodes)
    (h : ResidualWalk net flow u v indices) :
    ((indices.map fun i =>
      (if residualTail net (availableEdge flow i) = w then (1 : ℤ) else 0) -
        (if residualHead net (availableEdge flow i) = w then (1 : ℤ) else 0)).sum) =
      (if u = w then 1 else 0) - (if v = w then 1 else 0) := by
  induction indices generalizing u with
  | nil => simp only [ResidualWalk] at h; subst v; simp
  | cons i indices ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih _ h.2, h.1]
    omega

/-- Every available residual source/sink path gives a feasible flow of value one larger. -/
theorem residualReach_augments {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    {flow : IndexedFlow arcs} {d : ℕ} (hf : IsIndexedFlow net d flow)
    (hp : ResidualReach net flow net.source net.sink) :
    ∃ better : IndexedFlow arcs, IsIndexedFlow net (d + 1) better := by
  obtain ⟨indices, hn, hw⟩ := residualReach_simple_walk net flow hp
  refine ⟨augmentFlow flow indices, fun v => ?_⟩
  rw [augmentFlow_balance net flow indices hn v,
    residualWalk_balance net flow indices net.source net.sink v hw, hf v]
  by_cases hs : v = net.source
  · subst v
    simp [net.source_ne_sink, Ne.symm net.source_ne_sink]
  · by_cases ht : v = net.sink
    · subst v
      simp [hs, net.source_ne_sink, Ne.symm net.source_ne_sink]
      omega
    · simp [hs, ht, Ne.symm hs, Ne.symm ht]

/-- A maximum integral flow has no residual source/sink path. -/
theorem maximumFlow_no_residualReach {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    {flow : IndexedFlow arcs} {d : ℕ} (hf : IsIndexedFlow net d flow)
    (hmax : ∀ (other : IndexedFlow arcs) (q : ℕ), IsIndexedFlow net q other → q ≤ d) :
    ¬ ResidualReach net flow net.source net.sink := by
  intro hp
  obtain ⟨better, hb⟩ := residualReach_augments net hf hp
  have := hmax better (d + 1) hb
  omega

end STACS2027.Runtimes.Flow

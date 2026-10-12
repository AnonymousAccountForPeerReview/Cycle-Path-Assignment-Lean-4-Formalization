module

public import NPHardness.ExpansionDisjoint
public import NPHardness.OmittedVertex

/-!
Subdivision of edges private to a cycle preserves the overlap interactions
between different cycles. Arbitrary choices on a subdivided cycle can be
normalized to original vertices without increasing these interactions.
-/

@[expose] public section
namespace STACS2027

theorem overlap_eq_intersection_length (p q : List Edge) (hq : q.Nodup) :
    overlap p q = (p.filter q.contains).length := by
  induction p with
  | nil => rfl
  | cons e p ih =>
    rw [overlap_cons_left, hq.count, ih]
    by_cases h : e ∈ q <;> simp [h, Nat.add_comm]

theorem overlap_le_of_intersection_subset {p q r s : List Edge}
    (hp : p.Nodup) (hq : q.Nodup) (hs : s.Nodup)
    (h : ∀ e, e ∈ p → e ∈ q → e ∈ r ∧ e ∈ s) : overlap p q ≤ overlap r s := by
  rw [overlap_eq_intersection_length p q hq, overlap_eq_intersection_length r s hs]
  apply List.Nodup.length_le_of_subset (hp.filter q.contains)
  intro e he
  obtain ⟨hep, heq⟩ := List.mem_filter.mp he
  have heq' : e ∈ q := by simpa using heq
  obtain ⟨her, hes⟩ := h e hep heq'
  exact List.mem_filter.mpr ⟨her, by simpa using hes⟩

theorem overlap_eq_of_intersection_iff {p q r s : List Edge}
    (hp : p.Nodup) (hq : q.Nodup) (hr : r.Nodup) (hs : s.Nodup)
    (h : ∀ e, (e ∈ p ∧ e ∈ q) ↔ (e ∈ r ∧ e ∈ s)) : overlap p q = overlap r s := by
  apply Nat.le_antisymm
  · exact overlap_le_of_intersection_subset hp hq hs (fun e he hf => (h e).mp ⟨he, hf⟩)
  · exact overlap_le_of_intersection_subset hr hs hq (fun e he hf => (h e).mpr ⟨he, hf⟩)

def originalChoice (c : Cycle) (v : Nat) : Nat :=
  if v ∈ c then v else c.head!

theorem originalChoice_mem {g : Graph} {r : Nat} {c : Cycle}
    (hc : IsCycle g r c) (v : Nat) : originalChoice c v ∈ c := by
  unfold originalChoice
  split
  · assumption
  · have hk := hc.1
    have hl := hc.2.1
    cases c with
    | nil => simp at hl; omega
    | cons a cs => exact List.mem_cons_self

theorem originalChoice_avoids {c : Cycle} (v : Nat) {e : Edge}
    (he : e ∈ cycleEdges c) (hv : avoidsVertex (originalChoice c v) e = true) :
    avoidsVertex v e = true := by
  by_cases hvc : v ∈ c
  · simpa [originalChoice, hvc] using hv
  · obtain ⟨h₁, h₂⟩ := cycleEdges_endpoints he
    simp only [avoidsVertex, Bool.and_eq_true, bne_iff_ne]
    exact ⟨fun h => hvc (h ▸ h₁), fun h => hvc (h ▸ h₂)⟩

theorem expanded_cycle_intersection {g : Graph} {r s : Nat} {c d c' d' : Cycle}
    {ss : List SubdivisionStep} (hv : validSubdivision g ss)
    (hc : IsCycle g r c) (hd : IsCycle g s d)
    (hpc : (cycleEdges c').Perm ((cycleEdges c).flatMap (expandedEdge ss)))
    (hpd : (cycleEdges d').Perm ((cycleEdges d).flatMap (expandedEdge ss)))
    (hu : ∀ e ∈ cycleEdges c, e ∈ cycleEdges d → expandedEdge ss e = [e]) (e : Edge) :
    (e ∈ cycleEdges c' ∧ e ∈ cycleEdges d') ↔ (e ∈ cycleEdges c ∧ e ∈ cycleEdges d) := by
  rw [hpc.mem_iff, hpd.mem_iff]
  exact expandedEdge_shared_unchanged hv hc.2.2.2 hd.2.2.2 hu e

theorem expanded_overlap_same_vertices {g h : Graph} {r s k l : Nat} {c d c' d' : Cycle}
    {ss : List SubdivisionStep} (hv : validSubdivision g ss)
    (hc : IsCycle g r c) (hd : IsCycle g s d)
    (hc' : IsCycle h k c') (hd' : IsCycle h l d')
    (hpc : (cycleEdges c').Perm ((cycleEdges c).flatMap (expandedEdge ss)))
    (hpd : (cycleEdges d').Perm ((cycleEdges d).flatMap (expandedEdge ss)))
    (hu : ∀ e ∈ cycleEdges c, e ∈ cycleEdges d → expandedEdge ss e = [e]) (u v : Nat) :
    overlap (selectedAt c u) (selectedAt d v) = overlap (selectedAt c' u) (selectedAt d' v) := by
  apply overlap_eq_of_intersection_iff (selectedAt_nodup hc u) (selectedAt_nodup hd v)
    (selectedAt_nodup hc' u) (selectedAt_nodup hd' v)
  intro e
  have hi := expanded_cycle_intersection hv hc hd hpc hpd hu e
  simp only [selectedAt_mem]
  constructor
  · rintro ⟨⟨hec, hua, hub⟩, ⟨hed, hva, hvb⟩⟩
    obtain ⟨hec', hed'⟩ := hi.mpr ⟨hec, hed⟩
    exact ⟨⟨hec', hua, hub⟩, ⟨hed', hva, hvb⟩⟩
  · rintro ⟨⟨hec, hua, hub⟩, ⟨hed, hva, hvb⟩⟩
    obtain ⟨hec', hed'⟩ := hi.mp ⟨hec, hed⟩
    exact ⟨⟨hec', hua, hub⟩, ⟨hed', hva, hvb⟩⟩

theorem expanded_overlap_normalizes {g h : Graph} {r s k l : Nat} {c d c' d' : Cycle}
    {ss : List SubdivisionStep} (hv : validSubdivision g ss)
    (hc : IsCycle g r c) (hd : IsCycle g s d)
    (_hc' : IsCycle h k c') (hd' : IsCycle h l d')
    (hpc : (cycleEdges c').Perm ((cycleEdges c).flatMap (expandedEdge ss)))
    (hpd : (cycleEdges d').Perm ((cycleEdges d).flatMap (expandedEdge ss)))
    (hu : ∀ e ∈ cycleEdges c, e ∈ cycleEdges d → expandedEdge ss e = [e]) (u v : Nat) :
    overlap (selectedAt c (originalChoice c u)) (selectedAt d (originalChoice d v)) ≤
      overlap (selectedAt c' u) (selectedAt d' v) := by
  apply overlap_le_of_intersection_subset (selectedAt_nodup hc _)
    (selectedAt_nodup hd _) (selectedAt_nodup hd' _)
  intro e hec hed
  obtain ⟨hec, hua⟩ := List.mem_filter.mp hec
  obtain ⟨hed, hva⟩ := List.mem_filter.mp hed
  obtain ⟨hec', hed'⟩ := (expanded_cycle_intersection hv hc hd hpc hpd hu e).mpr ⟨hec, hed⟩
  exact ⟨List.mem_filter.mpr ⟨hec', originalChoice_avoids u hec hua⟩,
    List.mem_filter.mpr ⟨hed', originalChoice_avoids v hed hva⟩⟩

end STACS2027

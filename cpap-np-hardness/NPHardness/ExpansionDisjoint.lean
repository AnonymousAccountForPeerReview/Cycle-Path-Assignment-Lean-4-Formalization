module

public import NPHardness.SubdivisionPrograms

/-! Subdivision preserves distinctness of edges and separates different
original edges. These facts are needed for transporting overlap costs. -/

@[expose] public section
namespace STACS2027

theorem liftEdges_subset_subdivideOnce {g : Graph} {a b z : Nat} {es : List Edge}
    (hs : es ⊆ g) : liftEdges a b z es ⊆ subdivideOnce g a b z := by
  intro e he
  rcases mem_liftEdges.mp he with ⟨he, hne⟩ | ⟨_, rfl | rfl⟩
  · exact mem_subdivideOnce.mpr (Or.inr (Or.inr ⟨hs he, hne⟩))
  · exact mem_subdivideOnce.mpr (Or.inl rfl)
  · exact mem_subdivideOnce.mpr (Or.inr (Or.inl rfl))

theorem expandedEdges_nodup {g : Graph} {ss : List SubdivisionStep}
    (hv : validSubdivision g ss) {es : List Edge} (hn : es.Nodup) (hs : es ⊆ g) :
    (es.flatMap (expandedEdge ss)).Nodup := by
  induction ss generalizing g es with
  | nil => simpa [expandedEdge] using hn
  | cons s ss ih =>
    obtain ⟨hne, _, hf, ht⟩ := hv
    have h := ih ht (liftEdges_nodup hne hf hn (fun _ he => hs he))
      (liftEdges_subset_subdivideOnce hs)
    simpa only [liftEdges, List.flatMap_assoc, expandedEdge] using h

theorem expandedEdge_nonempty (ss : List SubdivisionStep) (e : Edge) :
    expandedEdge ss e ≠ [] := by
  induction ss generalizing e with
  | nil => simp [expandedEdge]
  | cons s ss ih =>
    by_cases h : e = edge s.source s.target
    · simp [expandedEdge, splitEdge, h, ih]
    · simpa [expandedEdge, splitEdge, h] using ih e

theorem expandedEdge_preserves_endpoint (ss : List SubdivisionStep) (e : Edge)
    (v : Nat) (hv : v = e.1 ∨ v = e.2) :
    ∃ f ∈ expandedEdge ss e, v = f.1 ∨ v = f.2 := by
  induction ss generalizing e with
  | nil => exact ⟨e, by simp [expandedEdge], hv⟩
  | cons s ss ih =>
    have hex : ∃ d ∈ splitEdge s.source s.target s.fresh e,
        v = d.1 ∨ v = d.2 := by
      by_cases he : e = edge s.source s.target
      · subst e
        have hab : v = s.source ∨ v = s.target := by
          rcases hv with hv | hv
          · exact ((edge_endpoints s.source s.target).1).imp (hv.trans) (hv.trans)
          · exact ((edge_endpoints s.source s.target).2).imp (hv.trans) (hv.trans)
        rcases hab with rfl | rfl
        · exact ⟨edge s.source s.fresh, by simp [splitEdge], edge_left_endpoint _ _⟩
        · refine ⟨edge s.fresh s.target, by simp [splitEdge], ?_⟩
          simpa only [edge_comm s.fresh s.target] using edge_left_endpoint s.target s.fresh
      · exact ⟨e, by simp [splitEdge, he], hv⟩
    obtain ⟨d, hd, hvd⟩ := hex
    obtain ⟨f, hf, hvf⟩ := ih d hvd
    exact ⟨f, List.mem_flatMap.mpr ⟨d, hd, hf⟩, hvf⟩

theorem expanded_cycle_vertices {g h : Graph} {r k : Nat} {c d : Cycle}
    (hc : IsCycle g r c) (_hd : IsCycle h k d) {ss : List SubdivisionStep}
    (hp : (cycleEdges d).Perm ((cycleEdges c).flatMap (expandedEdge ss))) : c ⊆ d := by
  intro v hv
  obtain ⟨w, _, he⟩ := hc.vertex_incident hv
  obtain ⟨f, hf, hfv⟩ := expandedEdge_preserves_endpoint ss (edge v w) v (edge_left_endpoint v w)
  have hfd : f ∈ cycleEdges d := hp.mem_iff.mpr (List.mem_flatMap.mpr ⟨_, he, hf⟩)
  have hends := cycleEdges_endpoints hfd
  rcases hfv with hfv | hfv
  · exact hfv ▸ hends.1
  · exact hfv ▸ hends.2

theorem expandedEdge_unique_parent {g : Graph} {ss : List SubdivisionStep}
    (hv : validSubdivision g ss) {a b e : Edge} (ha : a ∈ g) (hb : b ∈ g)
    (hea : e ∈ expandedEdge ss a) (heb : e ∈ expandedEdge ss b) : a = b := by
  by_cases hab : a = b
  · exact hab
  have hn : ([a,b] : List Edge).Nodup := by simp [hab]
  have hs : ([a,b] : List Edge) ⊆ g := by
    intro d hd
    rcases (show d = a ∨ d = b from by simpa using hd) with rfl | rfl
    · exact ha
    · exact hb
  have h := expandedEdges_nodup hv hn hs
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at h
  exact False.elim ((List.nodup_append.mp h).2.2 e hea e heb rfl)

theorem expandedEdges_subset_reflect {g : Graph} {ss : List SubdivisionStep}
    (hv : validSubdivision g ss) {as bs : List Edge} (ha : as ⊆ g) (hb : bs ⊆ g)
    (hs : as.flatMap (expandedEdge ss) ⊆ bs.flatMap (expandedEdge ss)) : as ⊆ bs := by
  intro e he
  obtain ⟨f, hf⟩ := List.exists_mem_of_ne_nil _ (expandedEdge_nonempty ss e)
  obtain ⟨d, hd, hfd⟩ := List.mem_flatMap.mp (hs (List.mem_flatMap.mpr ⟨e, he, hf⟩))
  have hed := expandedEdge_unique_parent hv (ha he) (hb hd) hf hfd
  exact hed ▸ hd

theorem expandedEdge_shared_unchanged {g : Graph} {ss : List SubdivisionStep}
    (hv : validSubdivision g ss) {as bs : List Edge} (ha : as ⊆ g) (hb : bs ⊆ g)
    (hu : ∀ e ∈ as, e ∈ bs → expandedEdge ss e = [e]) (e : Edge) :
    (e ∈ as.flatMap (expandedEdge ss) ∧ e ∈ bs.flatMap (expandedEdge ss)) ↔
      e ∈ as ∧ e ∈ bs := by
  constructor
  · rintro ⟨hae, hbe⟩
    obtain ⟨a, hma, hea⟩ := List.mem_flatMap.mp hae
    obtain ⟨b, hmb, heb⟩ := List.mem_flatMap.mp hbe
    have hab := expandedEdge_unique_parent hv (ha hma) (hb hmb) hea heb
    subst b
    rw [hu a hma hmb] at hea
    have he : e = a := by simpa using hea
    subst e
    exact ⟨hma, hmb⟩
  · rintro ⟨hea, heb⟩
    have hm : e ∈ expandedEdge ss e := by rw [hu e hea heb]; simp
    exact ⟨List.mem_flatMap.mpr ⟨e, hea, hm⟩, List.mem_flatMap.mpr ⟨e, heb, hm⟩⟩

theorem linkSteps_zero (next : Nat) (ls : List Link)
    (hb : VerticesBelow (linkEdges ls) next) (hn : (linkEdges ls).Nodup)
    (hp : ∀ l ∈ ls, l.source ≠ l.target) (l : Link) (hl : l ∈ ls)
    (hz : l.subdivisions = 0) :
    expandedEdge (linkSteps next ls) (edge l.source l.target) = [edge l.source l.target] := by
  induction ls generalizing next with
  | nil => simp at hl
  | cons r rs ih =>
    rcases List.mem_cons.mp hl with rfl | hl
    · rw [linkSteps_head next l rs hb hn (hp l (by simp)), hz]
      rfl
    · have hmem : edge l.source l.target ∈ linkEdges rs := List.mem_map.mpr ⟨l, hl, rfl⟩
      have he := hb _ (List.mem_cons_of_mem _ hmem)
      have hne : edge l.source l.target ≠ edge r.source r.target := by
        intro h
        apply (List.nodup_cons.mp hn).1
        change edge r.source r.target ∈ linkEdges rs
        rw [← h]
        exact hmem
      rw [linkSteps_tail next r rs _ he hne]
      apply ih (next + r.subdivisions) ?_ (List.nodup_cons.mp hn).2
        (fun l hl => hp l (by simp [hl])) hl
      intro e he
      have h := hb e (List.mem_cons_of_mem _ he)
      constructor <;> omega

end STACS2027

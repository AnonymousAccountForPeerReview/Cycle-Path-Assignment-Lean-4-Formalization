module

public import Outerplanar.FaceTransport
import Mathlib.Tactic
import Mathlib.Data.List.GetD

/-! Deletion of the root face when it is a weak-dual leaf. The unique child chord bounds
the retained interval; its complementary outer arc is the deleted face path. -/

@[expose] public section

namespace STACS2027

def rootLeafDelete (g : Graph) (p : ℕ × ℕ) : Graph :=
  inducedGraph g (fun v => p.1 ≤ v ∧ v ≤ p.2)

namespace IsPolygon

variable {g : Graph} {n : ℕ}

/-- Every non-root face lies below the unique child of a root leaf. -/
theorem within_unique_root_child (hP : IsPolygon g n) {p t : ℕ × ℕ}
    (_hp : p ∈ segs g n) (_hpc : IsChild g n (0, n - 1) p)
    (hunique : ∀ q ∈ segs g n, IsChild g n (0, n - 1) q → q = p)
    (ht : t ∈ segs g n) (htroot : t ≠ (0, n - 1)) : Within t p := by
  obtain ⟨q, hq, hqc, hwithin⟩ := hP.exists_child hP.root_mem_segs ht (hP.within_root ht) htroot
  exact hunique q hq hqc ▸ hwithin

/-- The internal vertices of the root leaf's complementary outer path are exactly the
original graph vertices outside the unique child interval. -/
theorem root_leaf_face_vertices (hP : IsPolygon g n) {p : ℕ × ℕ}
    (hp : p ∈ segs g n) (hpc : IsChild g n (0, n - 1) p)
    (hunique : ∀ q ∈ segs g n, IsChild g n (0, n - 1) q → q = p) (v : ℕ) :
    v ∈ faceVerts g n (0, n - 1) ↔ v < n ∧ ¬ (p.1 < v ∧ v < p.2) := by
  have hpbound := hP.within_root hp
  have hn := hP.three_le
  rw [mem_faceVerts]
  constructor
  · rintro ⟨_, hv, hf⟩
    exact ⟨by omega, hf p hp hpbound hpc.1⟩
  · rintro ⟨hv, hout⟩
    refine ⟨by omega, by omega, fun t ht _ hne hin => ?_⟩
    have hw := hP.within_unique_root_child hp hpc hunique ht hne
    exact hout ⟨lt_of_le_of_lt hw.1 hin.1, lt_of_lt_of_le hin.2 hw.2⟩

/-- The actual induced root-leaf deletion has an outer Hamiltonian cycle enclosing
exactly the surviving original faces, with their boundaries unchanged and the unique
child chord on the new outer boundary. -/
theorem root_leaf_delete_hamiltonian (hP : IsPolygon g n) {p : ℕ × ℕ}
    (hp : p ∈ segs g n) (hpc : IsChild g n (0, n - 1) p)
    (hunique : ∀ q ∈ segs g n, IsChild g n (0, n - 1) q → q = p) :
    ∃ u, OuterplanarHam (rootLeafDelete g p) u ∧
      encl g n u = (segs g n).erase (0, n - 1) ∧
      (∀ t ∈ (segs g n).erase (0, n - 1),
        ConvexCycle (rootLeafDelete g p) (faceVerts g n t)) ∧ p ∈ cycleEdges u := by
  let S := (segs g n).erase (0, n - 1)
  have hpS : p ∈ S := Finset.mem_erase.mpr ⟨hpc.1, hp⟩
  have hS : IsRooted g n S p := by
    refine ⟨hpS, Finset.erase_subset _ _, fun t ht htp => ?_⟩
    obtain ⟨q, hq, hqc⟩ := hP.exists_parent (Finset.mem_of_mem_erase ht) (Finset.mem_erase.mp ht).1
    have hqroot : q ≠ (0, n - 1) := by
      intro he
      have htp' := hunique t (Finset.mem_of_mem_erase ht) (he ▸ hqc)
      exact htp htp'
    exact ⟨q, Finset.mem_erase.mpr ⟨hqroot, hq⟩, hqc⟩
  have hcS : S.card = (S.card - 1) + 1 := by
    have := Finset.card_pos.mpr ⟨p, hpS⟩
    omega
  obtain ⟨u, hu, hlen, hencl, _⟩ := hP.exists_rpath_of_rooted _ S p hS hcS
  have hpAdj := (hP.mem_segs.mp hp).1
  have hcyc : ConvexCycle g u := ((convexCycle_iff_isRPath hpAdj).mpr ⟨hu, hlen⟩).1
  have hcycle_delete : ∀ v, ConvexCycle g v → (∀ z ∈ v, p.1 ≤ z ∧ z ≤ p.2) →
      ConvexCycle (rootLeafDelete g p) v := by
    intro v hv hr
    refine ⟨hv.1, hv.2.1, fun e he => ?_⟩
    have hend := cycleEdges_endpoints he
    exact List.mem_filter.mpr ⟨hv.2.2 e he, decide_eq_true ⟨hr _ hend.1, hr _ hend.2⟩⟩
  have hcyc' := hcycle_delete u hcyc (fun z hz => hu.bounds hz)
  have hcover : ∀ v, IsVertex (rootLeafDelete g p) v → v ∈ u := by
    intro v hv
    obtain ⟨w, hadj⟩ := hv
    have hr := (adj_inducedGraph.mp hadj).2.2
    by_cases hvlast : v = p.2
    · exact hvlast ▸ hu.last_mem
    have hside : v + 1 < n := by
      have hb := (hP.lt_of_adj hpAdj).2
      omega
    obtain ⟨t, ht, hw, hmin⟩ := hP.exists_own (e := (v, v + 1)) (hP.adj_succ hside) (by omega)
    have htp := hmin p hp ⟨hr.1, by omega⟩
    have htroot : t ≠ (0, n - 1) := by
      intro he
      have hpr := hP.within_root hp
      have heq := Within.antisymm (he ▸ htp) hpr
      exact hpc.1 heq.symm
    have htenc : t ∈ encl g n u := by rw [hencl]; exact Finset.mem_erase.mpr ⟨htroot, ht⟩
    have he := (hP.faces_of_side ht).mpr ⟨hw, hmin⟩
    have hend := cycleEdges_endpoints (List.mem_toFinset.mp he)
    exact (mem_encl.mp htenc).2 v hend.1
  have hham : OuterplanarHam (rootLeafDelete g p) u := by
    refine ⟨hcyc'.isCycle, hcover, fun i j k l hij hjk hkl hl hadj => ?_⟩
    have hi : i < u.length := by omega
    have hj : j < u.length := by omega
    have hk : k < u.length := by omega
    have hIJ := hcyc.1.rel_getElem_of_lt hi hj hij
    have hJK := hcyc.1.rel_getElem_of_lt hj hk hjk
    have hKL := hcyc.1.rel_getElem_of_lt hk hl hkl
    simp only [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj,
      List.getD_eq_getElem _ _ hk, List.getD_eq_getElem _ _ hl] at hadj
    exact hP.noncross hIJ hJK hKL (adj_inducedGraph.mp hadj.1).1 (adj_inducedGraph.mp hadj.2).1
  refine ⟨u, hham, hencl, fun t ht => ?_, ?_⟩
  · have htp := hP.within_unique_root_child hp hpc hunique (Finset.mem_of_mem_erase ht)
      (Finset.mem_erase.mp ht).1
    exact hcycle_delete _ (hP.faceVerts_convexCycle (Finset.mem_of_mem_erase ht))
      (fun z hz => ⟨le_trans htp.1 (mem_faceVerts.mp hz).1,
        le_trans (mem_faceVerts.mp hz).2.1 htp.2⟩)
  · obtain ⟨mid, heq⟩ := hu.eq_cons_snoc (by omega)
    rw [heq, mem_cycleEdges_of_pairwise (heq ▸ hcyc.1)]
    exact Or.inl rfl

theorem root_leaf_delete_twoConnected (hP : IsPolygon g n) {p : ℕ × ℕ}
    (hp : p ∈ segs g n) (hpc : IsChild g n (0, n - 1) p)
    (hunique : ∀ q ∈ segs g n, IsChild g n (0, n - 1) q → q = p) :
    TwoConnected (rootLeafDelete g p) := by
  obtain ⟨u, hu, _⟩ := hP.root_leaf_delete_hamiltonian hp hpc hunique
  exact hamiltonian_cycle_twoConnected hu.1 hu.2.1

theorem root_leaf_delete_outerplanar (hP : IsPolygon g n) {p : ℕ × ℕ}
    (hp : p ∈ segs g n) (hpc : IsChild g n (0, n - 1) p)
    (hunique : ∀ q ∈ segs g n, IsChild g n (0, n - 1) q → q = p) :
    OuterplanarDrawing (rootLeafDelete g p) := by
  obtain ⟨u, hu, _⟩ := hP.root_leaf_delete_hamiltonian hp hpc hunique
  exact hu.outerplanarDrawing

/-- Every edge incident to an internal vertex of the complementary outer path lies on
the root face. This proves the required degree-two property against the actual graph. -/
theorem root_leaf_incident_face (hP : IsPolygon g n) {p : ℕ × ℕ}
    (hp : p ∈ segs g n) (hpc : IsChild g n (0, n - 1) p)
    (hunique : ∀ q ∈ segs g n, IsChild g n (0, n - 1) q → q = p)
    {v w : ℕ} (hout : ¬ (p.1 ≤ v ∧ v ≤ p.2)) (hvw : Adj g v w) :
    edge v w ∈ faceEdges g n (0, n - 1) := by
  have hpAdj := (hP.mem_segs.mp hp).1
  have hbound := hP.lt_of_adj hvw
  have hvout : ¬ (p.1 < v ∧ v < p.2) := by omega
  have hwout : ¬ (p.1 < w ∧ w < p.2) := by
    intro hw
    rcases (show v < p.1 ∨ p.2 < v by omega) with hv | hv
    · exact hP.noncross hv hw.1 hw.2 hvw hpAdj
    · exact hP.noncross hw.1 hw.2 hv hpAdj hvw.symm
  have hvF := (hP.root_leaf_face_vertices hp hpc hunique v).mpr ⟨hbound.1, hvout⟩
  have hwF := (hP.root_leaf_face_vertices hp hpc hunique w).mpr ⟨hbound.2, hwout⟩
  exact List.mem_toFinset.mpr ((hP.face_chordless hP.root_mem_segs).2 v hvF w hwF hvw)

/-- A root-face edge whose endpoints both survive is exactly the unique child chord. -/
theorem root_leaf_retained_face_edge (hP : IsPolygon g n) {p : ℕ × ℕ}
    (hp : p ∈ segs g n) (hpc : IsChild g n (0, n - 1) p)
    (hunique : ∀ q ∈ segs g n, IsChild g n (0, n - 1) q → q = p)
    {v w : ℕ} (he : edge v w ∈ faceEdges g n (0, n - 1))
    (hv : p.1 ≤ v ∧ v ≤ p.2) (hw : p.1 ≤ w ∧ w ≤ p.2) : edge v w = p := by
  have hc := (hP.faceVerts_convexCycle hP.root_mem_segs).isCycle
  have hends := mem_of_mem_cycleEdges (List.mem_toFinset.mp he)
  have hvF := (hP.root_leaf_face_vertices hp hpc hunique v).mp hends.1
  have hwF := (hP.root_leaf_face_vertices hp hpc hunique w).mp hends.2
  have hne : v ≠ w := by
    have hneq := hc.edge_endpoints_ne (List.mem_toFinset.mp he)
    simp only [edge] at hneq
    omega
  ext <;> simp only [edge] <;> omega

/-- The root deletion removes exactly the face's outer path, retaining its unique chord. -/
theorem root_leaf_delete_edges (hP : IsPolygon g n) {p : ℕ × ℕ}
    (hp : p ∈ segs g n) (hpc : IsChild g n (0, n - 1) p)
    (hunique : ∀ q ∈ segs g n, IsChild g n (0, n - 1) q → q = p) (v w : ℕ) :
    Adj (rootLeafDelete g p) v w ↔ Adj g v w ∧
      edge v w ∉ (faceEdges g n (0, n - 1)).erase p := by
  rw [rootLeafDelete, adj_inducedGraph]
  constructor
  · rintro ⟨hadj, hv, hw⟩
    refine ⟨hadj, fun he => ?_⟩
    exact (Finset.mem_erase.mp he).1
      (hP.root_leaf_retained_face_edge hp hpc hunique (Finset.mem_erase.mp he).2 hv hw)
  · rintro ⟨hadj, hnot⟩
    refine ⟨hadj, ?_, ?_⟩
    · by_contra hv
      have he := hP.root_leaf_incident_face hp hpc hunique hv hadj
      have hne : edge v w ≠ p := by
        intro heq
        have hvw := congrArg Prod.fst heq
        have hwv := congrArg Prod.snd heq
        simp only [edge] at hvw hwv
        omega
      exact hnot (Finset.mem_erase.mpr ⟨hne, he⟩)
    · by_contra hw
      have he := hP.root_leaf_incident_face hp hpc hunique hw hadj.symm
      rw [edge_comm] at he
      have hne : edge v w ≠ p := by
        intro heq
        have hvw := congrArg Prod.fst heq
        have hwv := congrArg Prod.snd heq
        simp only [edge] at hvw hwv
        omega
      exact hnot (Finset.mem_erase.mpr ⟨hne, he⟩)

/-- The unique child chord is the root leaf's only chord. -/
theorem root_leaf_unique_chord (hP : IsPolygon g n) {p : ℕ × ℕ}
    (hp : p ∈ segs g n) (hpc : IsChild g n (0, n - 1) p)
    (hunique : ∀ q ∈ segs g n, IsChild g n (0, n - 1) q → q = p) :
    faceEdges g n (0, n - 1) ∩ chords g n = {p} := by
  ext e
  rw [Finset.mem_inter, Finset.mem_singleton]
  constructor
  · rintro ⟨he, hch⟩
    have hch' := Finset.mem_erase.mp hch
    rcases (hP.mem_faceEdges_iff hP.root_mem_segs).mp he with heq | ⟨hes, hec⟩ | ⟨hside, _⟩
    · exact False.elim (hch'.1 heq)
    · exact hunique e hes hec
    · have hlt := (hP.mem_segs.mp hch'.2).2
      omega
  · rintro rfl
    exact ⟨(hP.faces_of_seg hp hP.root_mem_segs).mpr (Or.inr hpc),
      Finset.mem_erase.mpr ⟨hpc.1, hp⟩⟩

/-- Every internal vertex of the root leaf's complementary path has degree two in the
original graph, including the outer-cycle wrap at vertex zero. -/
theorem root_leaf_inner_degree (hP : IsPolygon g n) {p : ℕ × ℕ}
    (hp : p ∈ segs g n) (hpc : IsChild g n (0, n - 1) p)
    (hunique : ∀ q ∈ segs g n, IsChild g n (0, n - 1) q → q = p)
    {v : ℕ} (hvn : v < n) (hout : ¬ (p.1 ≤ v ∧ v ≤ p.2)) :
    degIn (polyEdges g n) v = 2 := by
  have hfilt : (polyEdges g n).filter (fun e => e.1 = v ∨ e.2 = v) =
      (faceEdges g n (0, n - 1)).filter (fun e => e.1 = v ∨ e.2 = v) := by
    ext e
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨he, hv⟩
      have hadj := (hP.mem_polyEdges.mp he).1
      have hlt := (hP.mem_polyEdges.mp he).2
      have hnorm : edge e.1 e.2 = e := by ext <;> simp [edge] <;> omega
      refine ⟨?_, hv⟩
      rcases hv with hv | hv
      · rw [← hnorm]
        exact hP.root_leaf_incident_face hp hpc hunique (hv ▸ hout) hadj
      · rw [← hnorm, edge_comm]
        exact hP.root_leaf_incident_face hp hpc hunique (hv ▸ hout) hadj.symm
    · rintro ⟨he, hv⟩
      exact ⟨hP.mem_polyEdges.mpr (hP.adj_of_mem_faceEdges hP.root_mem_segs he), hv⟩
  have hvface : v ∈ faceVerts g n (0, n - 1) :=
    (hP.root_leaf_face_vertices hp hpc hunique v).mpr ⟨hvn, by omega⟩
  change ((polyEdges g n).filter _).card = 2
  rw [hfilt]
  exact (degIn_cycleEdges (hP.faceVerts_convexCycle hP.root_mem_segs).isCycle v).trans
    (ite_eq_left hvface)

/-- Exact bounded-face transport for deletion of a root leaf. -/
theorem root_leaf_delete_faces (hP : IsPolygon g n) {p : ℕ × ℕ}
    (hp : p ∈ segs g n) (hpc : IsChild g n (0, n - 1) p)
    (hunique : ∀ q ∈ segs g n, IsChild g n (0, n - 1) q → q = p) {F : Finset Edge} :
    BoundedFaceBoundary (rootLeafDelete g p) F ↔
      ∃ t ∈ (segs g n).erase (0, n - 1), F = faceEdges g n t := by
  rw [rootLeafDelete, bounded_face_inducedGraph, hP.bounded_face_boundary_iff]
  constructor
  · rintro ⟨⟨t, ht, rfl⟩, hr⟩
    refine ⟨t, Finset.mem_erase.mpr ⟨?_, ht⟩, rfl⟩
    intro htroot
    subst t
    have hvertices : ∀ v ∈ faceVerts g n (0, n - 1), p.1 ≤ v ∧ v ≤ p.2 := by
      intro v hv
      obtain ⟨w, _, he⟩ := (hP.faceVerts_convexCycle hP.root_mem_segs).isCycle.vertex_incident hv
      have hh := hr _ (List.mem_toFinset.mpr he)
      rcases Nat.le_total v w with h | h
      · simpa only [edge, Nat.min_eq_left h, Nat.max_eq_right h] using hh.1
      · simpa only [edge, Nat.min_eq_right h, Nat.max_eq_left h] using hh.2
    have hn := hP.three_le
    have hleft := hvertices 0 (left_mem_faceVerts (by simp))
    have hright := hvertices (n - 1) (right_mem_faceVerts (by simp))
    have hbounds := hP.within_root hp
    simp only [Within] at hbounds
    exact hpc.1 (Prod.ext (by simp only; omega) (by simp only; omega))
  · rintro ⟨t, ht, rfl⟩
    refine ⟨⟨t, Finset.mem_of_mem_erase ht, rfl⟩, ?_⟩
    have hw := hP.within_unique_root_child hp hpc hunique (Finset.mem_of_mem_erase ht)
      (Finset.mem_erase.mp ht).1
    intro e he
    have hend := cycleEdges_endpoints (List.mem_toFinset.mp he)
    have h1 := mem_faceVerts.mp hend.1
    have h2 := mem_faceVerts.mp hend.2
    exact ⟨⟨le_trans hw.1 h1.1, le_trans h1.2.1 hw.2⟩,
      ⟨le_trans hw.1 h2.1, le_trans h2.2.1 hw.2⟩⟩

theorem root_leaf_delete_face_bijection (hP : IsPolygon g n) {p : ℕ × ℕ}
    (hp : p ∈ segs g n) (hpc : IsChild g n (0, n - 1) p)
    (hunique : ∀ q ∈ segs g n, IsChild g n (0, n - 1) q → q = p) :
    Set.BijOn (faceEdges g n) ((segs g n).erase (0, n - 1) : Set (ℕ × ℕ))
      {F | BoundedFaceBoundary (rootLeafDelete g p) F} := by
  refine ⟨fun t ht => ?_, fun t ht u hu he => ?_, fun F hF => ?_⟩
  · exact (hP.root_leaf_delete_faces hp hpc hunique).mpr ⟨t, ht, rfl⟩
  · exact hP.faceEdges_injective (Finset.mem_of_mem_erase ht) (Finset.mem_of_mem_erase hu) he
  · obtain ⟨t, ht, he⟩ := (hP.root_leaf_delete_faces hp hpc hunique).mp hF
    exact ⟨t, ht, he.symm⟩

theorem root_leaf_delete_weakDual (hP : IsPolygon g n) {p : ℕ × ℕ}
    (hp : p ∈ segs g n) (hpc : IsChild g n (0, n - 1) p)
    (hunique : ∀ q ∈ segs g n, IsChild g n (0, n - 1) q → q = p)
    {t u : ℕ × ℕ} (ht : t ∈ segs g n) (hu : u ∈ segs g n) :
    BoundaryDualAdj (rootLeafDelete g p) (faceEdges g n t) (faceEdges g n u) ↔
      t ≠ (0, n - 1) ∧ u ≠ (0, n - 1) ∧ DualAdj g n t u := by
  have hF : ∀ v ∈ segs g n,
      BoundedFaceBoundary (rootLeafDelete g p) (faceEdges g n v) ↔ v ≠ (0, n - 1) := by
    intro v hv
    rw [hP.root_leaf_delete_faces hp hpc hunique]
    constructor
    · rintro ⟨w, hw, he⟩
      have heq := hP.faceEdges_injective hv (Finset.mem_of_mem_erase hw) he
      exact heq ▸ (Finset.mem_erase.mp hw).1
    · intro hvs
      exact ⟨v, Finset.mem_erase.mpr ⟨hvs, hv⟩, rfl⟩
  have hn : faceEdges g n t ≠ faceEdges g n u ↔ t ≠ u :=
    ⟨fun h he => h (he ▸ rfl), fun h he => h (hP.faceEdges_injective ht hu he)⟩
  simp only [BoundaryDualAdj, hF t ht, hF u hu, DualAdj, hn]
  tauto

end IsPolygon

end STACS2027

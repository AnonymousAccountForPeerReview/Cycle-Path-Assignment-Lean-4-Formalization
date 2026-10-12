module

public import Outerplanar.RootLeaf
import Mathlib.Tactic

/-! Lemma 28 (3) for every weak-dual leaf, including the root face. -/

@[expose] public section

namespace STACS2027

/-- A degree-one vertex of the weak dual, specified by its unique neighbour. -/
def IsDualLeaf (g : Graph) (n : ℕ) (s : ℕ × ℕ) : Prop :=
  s ∈ IsPolygon.segs g n ∧ ∃ p ∈ IsPolygon.segs g n,
    ∀ t ∈ IsPolygon.segs g n, DualAdj g n s t ↔ t = p

/-- Internal vertices of a face path after its unique chord is removed. -/
def leafInterior (g : Graph) (n : ℕ) (s e : ℕ × ℕ) : Finset ℕ :=
  ((faceVerts g n s).toFinset.erase e.1).erase e.2

namespace IsPolygon

variable {g : Graph} {n : ℕ}

/-- Removing any boundary edge of a face leaves a path between its endpoints, with at
least two edges. Applied to the unique chord, this is the path `P` of Lemma 28 (1). -/
theorem face_path_of_edge (hP : IsPolygon g n) {s e : ℕ × ℕ}
    (hs : s ∈ segs g n) (he : e ∈ faceEdges g n s) :
    ∃ a mid b, e = edge b a ∧ IsCycle g (faceVerts g n s).length (a :: (mid ++ [b])) ∧
      (faceVerts g n s).Perm (a :: (mid ++ [b])) ∧
      (faceEdges g n s).erase e = (pathEdges (a :: (mid ++ [b]))).toFinset ∧
      2 ≤ (pathEdges (a :: (mid ++ [b]))).length := by
  have hc := (hP.faceVerts_convexCycle hs).isCycle
  obtain ⟨a, mid, b, hrot, hperm, hsame, heq⟩ := hc.rotate_edge (List.mem_toFinset.mp he)
  have hF : faceEdges g n s = (cycleEdges (a :: (mid ++ [b]))).toFinset := by
    ext e
    simp only [faceEdges, List.mem_toFinset]
    exact ⟨hsame.1 e, hsame.2 e⟩
  have hnd := hrot.edges_nodup
  rw [cycleEdges_snoc] at hnd
  have hnot : edge b a ∉ pathEdges (a :: (mid ++ [b])) := by
    intro he
    exact (List.pairwise_append.mp hnd).2.2 _ he _ (by simp) rfl
  refine ⟨a, mid, b, heq, hrot, hperm, ?_, ?_⟩
  · rw [hF, cycleEdges_snoc, List.toFinset_append, heq]
    simp only [List.toFinset_cons, List.toFinset_nil]
    ext q
    simp only [Finset.mem_erase, Finset.mem_union, Finset.mem_insert, Finset.notMem_empty,
      or_false, List.mem_toFinset]
    constructor
    · rintro ⟨hne, hq | hq⟩
      · exact hq
      · exact False.elim (hne hq)
    · intro hq
      exact ⟨fun he => hnot (he ▸ hq), Or.inl hq⟩
  · have hlen := hrot.2.1
    have hthree := hc.1
    simp only [pathEdges_length, List.length_cons, List.length_append] at *
    omega

theorem dual_leaf_cases (hP : IsPolygon g n) {s : ℕ × ℕ} (hs : IsDualLeaf g n s) :
    (s ≠ (0, n - 1) ∧ ∀ t ∈ segs g n, ¬ IsChild g n s t) ∨
      (s = (0, n - 1) ∧ ∃ p ∈ segs g n, IsChild g n (0, n - 1) p ∧
        ∀ t ∈ segs g n, IsChild g n (0, n - 1) t → t = p) := by
  obtain ⟨hs, p, hp, hleaf⟩ := hs
  by_cases hroot : s = (0, n - 1)
  · right
    subst s
    have hdp := (hleaf p hp).mpr rfl
    rcases (hP.dualAdj_iff.mp hdp).2.2 with hpc | hcp
    · refine ⟨rfl, p, hp, hpc, fun t ht hct => ?_⟩
      exact (hleaf t ht).mp (hP.dualAdj_iff.mpr ⟨hs, ht, Or.inl hct⟩)
    · exact False.elim (hP.not_isChild_root hp hcp)
  · left
    obtain ⟨q, hq, hqs⟩ := hP.exists_parent hs hroot
    have hqp : q = p := (hleaf q hq).mp (hP.dualAdj_iff.mpr ⟨hs, hq, Or.inr hqs⟩)
    refine ⟨hroot, fun t ht hst => ?_⟩
    have htp : t = p := (hleaf t ht).mp (hP.dualAdj_iff.mpr ⟨hs, ht, Or.inl hst⟩)
    have htq : t = q := htp.trans hqp.symm
    have hstq : IsChild g n s q := htq ▸ hst
    exact hqs.1 (Within.antisymm hqs.2.1 hstq.2.1)

theorem leaf_delete_face_edges (hP : IsPolygon g n) {s : ℕ × ℕ} (hs : s ∈ segs g n)
    (hleaf : ∀ t ∈ segs g n, ¬ IsChild g n s t) (v w : ℕ) :
    Adj (leafDelete g s) v w ↔ Adj g v w ∧ edge v w ∉ (faceEdges g n s).erase s := by
  rw [hP.leaf_delete_edges hs hleaf]
  have he : edge v w ∈ (faceEdges g n s).erase s ↔
      min v w + 1 = max v w ∧ s.1 ≤ min v w ∧ max v w ≤ s.2 := by
    rw [Finset.mem_erase, (hP.leaf_face hs hleaf).2.1]
    have hlt := (hP.mem_segs.mp hs).2
    simp only [edge]
    constructor
    · rintro ⟨hne, heq | hside⟩
      · exact False.elim (hne heq)
      · exact ⟨hside.1.symm, hside.2⟩
    · intro hside
      refine ⟨?_, Or.inr ⟨hside.1.symm, hside.2⟩⟩
      intro heq
      have h1 := congrArg Prod.fst heq
      have h2 := congrArg Prod.snd heq
      simp only at h1 h2
      omega
  rw [he]

theorem leaf_delete_interior (hP : IsPolygon g n) {s : ℕ × ℕ} (hs : s ∈ segs g n)
    (hleaf : ∀ t ∈ segs g n, ¬ IsChild g n s t) (v w : ℕ) :
    Adj (leafDelete g s) v w ↔ Adj g v w ∧
      v ∉ leafInterior g n s s ∧ w ∉ leafInterior g n s s := by
  have hw : ∀ v, v ∈ leafInterior g n s s ↔ s.1 < v ∧ v < s.2 := by
    intro v
    simp only [leafInterior, Finset.mem_erase, List.mem_toFinset, (hP.leaf_face hs hleaf).1,
      List.mem_range']
    have hlt := (hP.mem_segs.mp hs).2
    simp only [Nat.one_mul]
    constructor
    · rintro ⟨hne2, hne1, i, hi, heq⟩
      omega
    · rintro ⟨h1, h2⟩
      exact ⟨by omega, by omega, v - s.1, by omega, by omega⟩
  rw [adj_leafDelete, hw, hw]

theorem root_leaf_delete_interior (hP : IsPolygon g n) {p : ℕ × ℕ}
    (hp : p ∈ segs g n) (hpc : IsChild g n (0, n - 1) p)
    (hunique : ∀ q ∈ segs g n, IsChild g n (0, n - 1) q → q = p) (v w : ℕ) :
    Adj (rootLeafDelete g p) v w ↔ Adj g v w ∧
      v ∉ leafInterior g n (0, n - 1) p ∧ w ∉ leafInterior g n (0, n - 1) p := by
  have hw : ∀ v, v < n → (v ∉ leafInterior g n (0, n - 1) p ↔ p.1 ≤ v ∧ v ≤ p.2) := by
    intro v hv
    simp only [leafInterior, Finset.mem_erase, List.mem_toFinset,
      hP.root_leaf_face_vertices hp hpc hunique v]
    have hlt := (hP.mem_segs.mp hp).2
    omega
  rw [rootLeafDelete, adj_inducedGraph]
  constructor
  · rintro ⟨hadj, hv, hw'⟩
    have hb := hP.lt_of_adj hadj
    exact ⟨hadj, (hw v hb.1).mpr hv, (hw w hb.2).mpr hw'⟩
  · rintro ⟨hadj, hv, hw'⟩
    have hb := hP.lt_of_adj hadj
    exact ⟨hadj, (hw v hb.1).mp hv, (hw w hb.2).mp hw'⟩

/-- **Lemma 28 (3)** for every weak-dual leaf. The actual induced deletion removes
precisely the outer face path, is 2-connected and outerplanar, has exactly the other
bounded faces, has the induced weak dual with the leaf removed, and exposes the chord on
its new outer Hamiltonian boundary. -/
theorem leaf_face_deletion (hP : IsPolygon g n) (_hr : 2 ≤ (segs g n).card)
    {s : ℕ × ℕ} (hleaf : IsDualLeaf g n s) :
    ∃ e G' u, e ∈ chords g n ∧ e ∈ faceEdges g n s ∧
      (∀ v w, Adj G' v w ↔ Adj g v w ∧
        v ∉ leafInterior g n s e ∧ w ∉ leafInterior g n s e) ∧
      (∀ v w, Adj G' v w ↔ Adj g v w ∧ edge v w ∉ (faceEdges g n s).erase e) ∧
      TwoConnected G' ∧ OuterplanarDrawing G' ∧ OuterplanarHam G' u ∧ e ∈ cycleEdges u ∧
      Set.BijOn (faceEdges g n) ((segs g n).erase s : Set (ℕ × ℕ))
        {F | BoundedFaceBoundary G' F} ∧
      (∀ t ∈ segs g n, ∀ v ∈ segs g n,
        BoundaryDualAdj G' (faceEdges g n t) (faceEdges g n v) ↔
          t ≠ s ∧ v ≠ s ∧ DualAdj g n t v) := by
  have hs := hleaf.1
  rcases hP.dual_leaf_cases hleaf with ⟨hsroot, hnone⟩ | ⟨hsroot, p, hp, hpc, hunique⟩
  · obtain ⟨u, hu, _, _, he⟩ := hP.leaf_delete_hamiltonian hs hsroot hnone
    refine ⟨s, leafDelete g s, u, Finset.mem_erase.mpr ⟨hsroot, hs⟩, ?_,
      hP.leaf_delete_interior hs hnone, hP.leaf_delete_face_edges hs hnone,
      hP.leaf_delete_twoConnected hs hsroot hnone, hP.leaf_delete_outerplanar s, hu, he,
      hP.leaf_delete_face_bijection hs hsroot hnone, ?_⟩
    · exact (hP.faces_of_seg hs hs).mpr (Or.inl rfl)
    · exact fun t ht v hv => hP.leaf_delete_weakDual hs hsroot hnone ht hv
  · subst s
    obtain ⟨u, hu, _, _, he⟩ := hP.root_leaf_delete_hamiltonian hp hpc hunique
    refine ⟨p, rootLeafDelete g p, u, Finset.mem_erase.mpr ⟨hpc.1, hp⟩, ?_,
      hP.root_leaf_delete_interior hp hpc hunique, hP.root_leaf_delete_edges hp hpc hunique,
      hP.root_leaf_delete_twoConnected hp hpc hunique, hP.root_leaf_delete_outerplanar hp hpc hunique,
      hu, he, hP.root_leaf_delete_face_bijection hp hpc hunique, ?_⟩
    · exact (hP.faces_of_seg hp hP.root_mem_segs).mpr (Or.inr hpc)
    · exact fun t ht v hv => hP.root_leaf_delete_weakDual hp hpc hunique ht hv

end IsPolygon

end STACS2027

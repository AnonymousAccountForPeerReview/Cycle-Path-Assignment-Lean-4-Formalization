module

public import Outerplanar.WeakDualFacts
public import Outerplanar.OuterplanarSym
public import Outerplanar.OuterplanarConstruct
public import Outerplanar.OuterplanarMinorLists
public import Outerplanar.BlockTheory
public import Outerplanar.HypermapEuler
import Mathlib.Tactic
import Mathlib.Data.List.GetD

/-! Genuine graph consequences of deleting the internal vertices of a leaf face. -/

@[expose] public section

namespace STACS2027

/-- All vertices of a walk are mutually reachable within its vertex predicate. -/
theorem WalkWithin.reach_all {g : Graph} {S : ℕ → Prop} :
    ∀ {w : List ℕ}, WalkWithin g S w → ∀ u ∈ w, ∀ v ∈ w, Reach g S u v
  | [], _, _, hu, _, _ => by simp at hu
  | [a], hw, u, hu, v, hv => by
    simp only [List.mem_singleton] at hu hv
    subst u; subst v
    exact .refl hw
  | a :: b :: rest, ⟨ha, hab, hw⟩, u, hu, v, hv => by
    have ih := WalkWithin.reach_all hw
    by_cases hua : u = a
    · subst u
      by_cases hva : v = a
      · subst v; exact .refl ha
      · have hvt := (List.mem_cons.mp hv).resolve_left hva
        exact .step ha hab (ih b List.mem_cons_self v hvt)
    · have hut := (List.mem_cons.mp hu).resolve_left hua
      by_cases hva : v = a
      · subst v
        exact (Reach.step ha hab (ih b List.mem_cons_self u hut)).symm
      · have hvt := (List.mem_cons.mp hv).resolve_left hva
        exact ih u hut v hvt

/-- A Hamiltonian simple cycle proves 2-connectivity. -/
theorem hamiltonian_cycle_twoConnected {g : Graph} {c : List ℕ}
    (hc : IsCycle g c.length c) (hcover : ∀ v, IsVertex g v → v ∈ c) : TwoConnected g := by
  have hlen := hc.1
  have hvertex : ∀ v ∈ c, IsVertex g v := by
    intro v hv
    obtain ⟨w, hne, he⟩ := hc.vertex_incident hv
    exact ⟨w, hne, by simpa only [edge_comm w v] using hc.2.2.2 _ he⟩
  have hconn : ConnectedWithin g (IsVertex g) := by
    rw [connectedWithin_iff]
    intro u v hu hv
    exact (hc.walk.of_mem hvertex).reach_all u (hcover u hu) v (hcover v hv)
  refine ⟨?_, hconn, fun x => ?_⟩
  · rcases c with _ | ⟨a, c⟩
    · simp at hlen
    rcases c with _ | ⟨b, c⟩
    · simp at hlen
    rcases c with _ | ⟨d, rest⟩
    · simp at hlen
    have hnd := hc.2.2.1
    refine ⟨a, b, d, hvertex a (by simp), hvertex b (by simp), hvertex d (by simp), ?_, ?_, ?_⟩
    · exact fun h => (List.nodup_cons.mp hnd).1 (by simp [h])
    · exact fun h => (List.nodup_cons.mp hnd).1 (by simp [h])
    · exact fun h => (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1 (by simp [h])
  · by_cases hx : x ∈ c
    · obtain ⟨rest, hr, _, hperm⟩ := hc.rotate_to_vertex hx
      have hxnot := (List.nodup_cons.mp hr.2.2.1).1
      have hrest : ∀ v, IsVertex g v → v ≠ x → v ∈ rest := by
        intro v hv hne
        have hm := (hperm.mem_iff).mp (hcover v hv)
        rcases List.mem_cons.mp hm with h | h
        · exact False.elim (hne h)
        · exact h
      have hwalk : WalkWithin g (fun v => IsVertex g v ∧ v ≠ x) rest := by
        have hw : WalkWithin g (fun _ => True) rest := hr.walk.right (w1 := [x])
        exact hw.of_mem (fun v hv => ⟨hvertex v (hperm.mem_iff.mpr (List.mem_cons_of_mem _ hv)),
          fun he => hxnot (he ▸ hv)⟩)
      rw [connectedWithin_iff]
      intro u v hu hv
      exact hwalk.reach_all u (hrest u hu.1 hu.2) v (hrest v hv.1 hv.2)
    · rw [connectedWithin_iff]
      intro u v hu hv
      exact ((connectedWithin_iff.mp hconn) u v hu.1 hv.1).mono
        (fun w hw => ⟨hw, fun he => hx (he ▸ hcover w hw)⟩)

/-- Delete the internal vertices of a segment, retaining both segment endpoints. -/
def leafDelete (g : Graph) (s : ℕ × ℕ) : Graph :=
  g.filter fun e => decide (¬ (s.1 < e.1 ∧ e.1 < s.2) ∧ ¬ (s.1 < e.2 ∧ e.2 < s.2))

/-- The deletion is an induced subgraph on the retained vertices. -/
theorem adj_leafDelete {g : Graph} {s : ℕ × ℕ} {u v : ℕ} :
    Adj (leafDelete g s) u v ↔
      Adj g u v ∧ ¬ (s.1 < u ∧ u < s.2) ∧ ¬ (s.1 < v ∧ v < s.2) := by
  unfold Adj leafDelete
  simp only [List.mem_filter, decide_eq_true_eq]
  by_cases h : u ≤ v
  · simp only [edge, Nat.min_eq_left h, Nat.max_eq_right h]
    tauto
  · have hvu : v ≤ u := by omega
    simp only [edge, Nat.min_eq_right hvu, Nat.max_eq_left hvu]
    tauto

namespace IsPolygon

variable {g : Graph} {n : ℕ}

/-- The induced deletion inherits an outerplanar drawing. -/
theorem leaf_delete_outerplanar (hP : IsPolygon g n) (s : ℕ × ℕ) :
    OuterplanarDrawing (leafDelete g s) := by
  have ho : OuterplanarDrawing g := (hP : OuterplanarHam g (List.range n)).outerplanarDrawing
  have hsub : simpleEdges (leafDelete g s) ⊆ simpleEdges g := by
    intro e he
    have hh := mem_simpleEdges.mp he
    exact mem_simpleEdges.mpr ⟨hh.1, (adj_leafDelete.mp hh.2).1⟩
  exact OuterplanarEmbedding.subperm hypermapEuler ((nodup_simpleEdges _).subperm hsub) ho

/-- Deleting the internal vertices removes exactly the outer path edges of the leaf face. -/
theorem leaf_delete_edges (hP : IsPolygon g n) {s : ℕ × ℕ} (hs : s ∈ segs g n)
    (hleaf : ∀ t ∈ segs g n, ¬ IsChild g n s t) (u v : ℕ) :
    Adj (leafDelete g s) u v ↔ Adj g u v ∧
      ¬ ((min u v + 1 = max u v) ∧ s.1 ≤ min u v ∧ max u v ≤ s.2) := by
  rw [adj_leafDelete]
  have hslt := (hP.mem_segs.mp hs).2
  have hdegree := (hP.leaf_face hs hleaf).2.2.2
  constructor
  · rintro ⟨hadj, hu, hv⟩
    refine ⟨hadj, ?_⟩
    intro hpath
    rcases Nat.le_total u v with h | h
    · simp only [Nat.min_eq_left h, Nat.max_eq_right h] at hpath
      omega
    · simp only [Nat.min_eq_right h, Nat.max_eq_left h] at hpath
      omega
  · rintro ⟨hadj, hpath⟩
    refine ⟨hadj, fun hu => ?_, fun hv => ?_⟩
    · have hd := (hdegree u hu.1 hu.2 v).mp hadj
      apply hpath
      rcases Nat.le_total u v with h | h <;>
        simp only [Nat.min_eq_left h, Nat.max_eq_right h, Nat.min_eq_right h, Nat.max_eq_left h] <;>
        omega
    · have hd := (hdegree v hv.1 hv.2 u).mp hadj.symm
      apply hpath
      rcases Nat.le_total u v with h | h <;>
        simp only [Nat.min_eq_left h, Nat.max_eq_right h, Nat.min_eq_right h, Nat.max_eq_left h] <;>
        omega

/-- A retained side has both endpoints on the boundary enclosing all faces other than the
removed leaf. -/
theorem side_vertices_retained {s : ℕ × ℕ} {u : List ℕ} (hP : IsPolygon g n)
    (hencl : encl g n u = (segs g n).erase s) {a : ℕ} (ha : a + 1 < n)
    (houtside : ¬ Within (a, a + 1) s) : a ∈ u ∧ a + 1 ∈ u := by
  obtain ⟨t, ht, hw, hmin⟩ := hP.exists_own (e := (a, a + 1)) (hP.adj_succ ha) (by omega)
  have he : (a, a + 1) ∈ faceEdges g n t := (hP.faces_of_side ht).mpr ⟨hw, hmin⟩
  have hts : t ≠ s := fun heq => houtside (heq ▸ hw)
  have htenc : t ∈ encl g n u := by
    rw [hencl]
    exact Finset.mem_erase.mpr ⟨hts, ht⟩
  have hend := cycleEdges_endpoints (List.mem_toFinset.mp he)
  exact ⟨(mem_encl.mp htenc).2 a hend.1, (mem_encl.mp htenc).2 (a + 1) hend.2⟩

/-- The genuine induced-deletion graph has an outer Hamiltonian cycle whose enclosed faces
in the original embedding are exactly the retained faces. Every retained face boundary is
unchanged, and the leaf's parent chord lies on the new outer cycle. -/
theorem leaf_delete_hamiltonian (hP : IsPolygon g n) {s : ℕ × ℕ} (hs : s ∈ segs g n)
    (hsroot : s ≠ (0, n - 1)) (hleaf : ∀ t ∈ segs g n, ¬ IsChild g n s t) :
    ∃ u, OuterplanarHam (leafDelete g s) u ∧ encl g n u = (segs g n).erase s ∧
      (∀ t ∈ (segs g n).erase s, ConvexCycle (leafDelete g s) (faceVerts g n t)) ∧
      s ∈ cycleEdges u := by
  let S := (segs g n).erase s
  have hr : (0, n - 1) ∈ S := Finset.mem_erase.mpr ⟨hsroot.symm, hP.root_mem_segs⟩
  have hS : IsRooted g n S (0, n - 1) := by
    refine ⟨hr, Finset.erase_subset _ _, fun t ht htr => ?_⟩
    obtain ⟨p, hp, hpc⟩ := hP.exists_parent (Finset.mem_of_mem_erase ht) htr
    have hps : p ≠ s := by
      intro he
      exact hleaf t (Finset.mem_of_mem_erase ht) (he ▸ hpc)
    exact ⟨p, Finset.mem_erase.mpr ⟨hps, hp⟩, hpc⟩
  have hcS : S.card = (S.card - 1) + 1 := by
    have := Finset.card_pos.mpr ⟨(0, n - 1), hr⟩
    omega
  obtain ⟨u, hu, hlen, hencl, _⟩ := hP.exists_rpath_of_rooted _ S (0, n - 1) hS hcS
  have hrootadj := (hP.mem_segs.mp hP.root_mem_segs).1
  have hcyc : ConvexCycle g u := ((convexCycle_iff_isRPath hrootadj).mpr ⟨hu, hlen⟩).1
  have havoid : ∀ z ∈ u, ¬ (s.1 < z ∧ z < s.2) := by
    intro z hz hin
    have he : s ∈ encl g n u := (hP.mem_encl_iff hu hrootadj hs).mpr
      ⟨hP.within_root hs, z, hz, hin.1, hin.2⟩
    rw [hencl] at he
    exact (Finset.mem_erase.mp he).1 rfl
  have hcycle_delete : ∀ v, ConvexCycle g v → (∀ z ∈ v, ¬ (s.1 < z ∧ z < s.2)) →
      ConvexCycle (leafDelete g s) v := by
    intro v hv hnone
    refine ⟨hv.1, hv.2.1, fun e he => ?_⟩
    have hend := cycleEdges_endpoints he
    exact List.mem_filter.mpr ⟨hv.2.2 e he, decide_eq_true ⟨hnone e.1 hend.1, hnone e.2 hend.2⟩⟩
  have hcyc' := hcycle_delete u hcyc havoid
  obtain ⟨p, hp, hpc⟩ := hP.exists_parent hs hsroot
  have hpS : p ∈ encl g n u := by
    rw [hencl]
    exact Finset.mem_erase.mpr ⟨fun he => hpc.1 he.symm, hp⟩
  obtain ⟨hsleft, hsright, _, _⟩ :=
    (infix_pair_iff faceVerts_pairwise).mp (hP.infix_faceVerts_of_child hs hpc)
  have hends : s.1 ∈ u ∧ s.2 ∈ u :=
    ⟨(mem_encl.mp hpS).2 _ hsleft, (mem_encl.mp hpS).2 _ hsright⟩
  have hcover : ∀ v, IsVertex (leafDelete g s) v → v ∈ u := by
    intro v hv
    obtain ⟨w, hadj⟩ := hv
    have hadj' := adj_leafDelete.mp hadj
    have hvn := (hP.lt_of_adj hadj'.1).2
    by_cases hleft : v = s.1
    · exact hleft ▸ hends.1
    by_cases hright : v = s.2
    · exact hright ▸ hends.2
    have hvout : v < s.1 ∨ s.2 < v := by omega
    by_cases hvlast : v + 1 < n
    · exact (hP.side_vertices_retained hencl hvlast (by
        simp only [Within]
        omega)).1
    · have hpred : v - 1 + 1 = v := by
        have hn := hP.three_le
        omega
      have hpout : ¬ Within (v - 1, v - 1 + 1) s := by
        simp only [Within]
        rw [hpred]
        omega
      have hv' := hP.side_vertices_retained hencl (a := v - 1) (by omega) hpout
      simpa [hpred] using hv'.2
  have hham : OuterplanarHam (leafDelete g s) u := by
    refine ⟨hcyc'.isCycle, hcover, fun i j k l hij hjk hkl hl hadj => ?_⟩
    have hi : i < u.length := by omega
    have hj : j < u.length := by omega
    have hk : k < u.length := by omega
    have hIJ := hcyc.1.rel_getElem_of_lt hi hj hij
    have hJK := hcyc.1.rel_getElem_of_lt hj hk hjk
    have hKL := hcyc.1.rel_getElem_of_lt hk hl hkl
    simp only [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj,
      List.getD_eq_getElem _ _ hk, List.getD_eq_getElem _ _ hl] at hadj
    exact hP.noncross hIJ hJK hKL (adj_leafDelete.mp hadj.1).1 (adj_leafDelete.mp hadj.2).1
  refine ⟨u, hham, hencl, fun t ht => ?_, ?_⟩
  · have htenc : t ∈ encl g n u := hencl.symm ▸ ht
    exact hcycle_delete _ (hP.faceVerts_convexCycle (Finset.mem_of_mem_erase ht))
      (fun z hz => havoid z ((mem_encl.mp htenc).2 z hz))
  · have hslt := (hP.mem_segs.mp hs).2
    have hin : [s.1, s.2] <:+: u := (infix_pair_iff hcyc.1).mpr
      ⟨hends.1, hends.2, by omega, fun z hz hin => havoid z hz hin⟩
    have hedge : edge s.1 s.2 = s := by
      ext <;> simp [edge] <;> omega
    rw [← hedge]
    exact pathEdges_subset_cycleEdges u _ (pathEdges_infix hin (by simp [pathEdges]))

/-- The graph obtained by deleting the internal leaf vertices is 2-connected. -/
theorem leaf_delete_twoConnected (hP : IsPolygon g n) {s : ℕ × ℕ} (hs : s ∈ segs g n)
    (hsroot : s ≠ (0, n - 1)) (hleaf : ∀ t ∈ segs g n, ¬ IsChild g n s t) :
    TwoConnected (leafDelete g s) := by
  obtain ⟨u, hu, _⟩ := hP.leaf_delete_hamiltonian hs hsroot hleaf
  exact hamiltonian_cycle_twoConnected hu.1 hu.2.1

end IsPolygon

end STACS2027

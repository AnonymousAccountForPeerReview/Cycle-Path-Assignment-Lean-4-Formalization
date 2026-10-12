module

public import Outerplanar.LeafDelete
public import Outerplanar.Algo.Combine
import Mathlib.Tactic

/-! Bounded face boundaries as chordless cycles, and their transport under induced deletion.
The characterization is proved against the polygon face definition, rather than postulated.
-/

@[expose] public section

namespace STACS2027

/-- A simple cycle with no edge joining nonconsecutive cycle vertices. -/
def ChordlessCycle (g : Graph) (c : List ℕ) : Prop :=
  IsCycle g c.length c ∧ ∀ a ∈ c, ∀ b ∈ c, Adj g a b → edge a b ∈ cycleEdges c

namespace IsPolygon

variable {g : Graph} {n : ℕ}

/-- Every polygon face boundary is chordless in the actual graph. -/
theorem face_chordless (hP : IsPolygon g n) {s : ℕ × ℕ} (hs : s ∈ segs g n) :
    ChordlessCycle g (faceVerts g n s) := by
  refine ⟨(hP.faceVerts_convexCycle hs).isCycle, fun a ha b hb hab => ?_⟩
  have hlt := (hP.mem_segs.mp hs).2
  have key : ∀ a ∈ faceVerts g n s, ∀ b ∈ faceVerts g n s, a < b → Adj g a b →
      edge a b ∈ cycleEdges (faceVerts g n s) := by
    intro a ha b hb hab hAdj
    have hae := mem_faceVerts.mp ha
    have hbe := mem_faceVerts.mp hb
    by_cases he : (a, b) = s
    · have hc := hP.faceVerts_convexCycle hs
      have hn : faceVerts g n s ≠ [] := List.ne_nil_of_mem ha
      have hhead := faceVerts_head? (g := g) (n := n) (s := s) (by omega)
      have hlast := faceVerts_getLast? (g := g) (n := n) (s := s) (by omega)
      have hh : (faceVerts g n s).head hn = s.1 := by simpa [List.head?_eq_some_head hn] using hhead
      have hl : (faceVerts g n s).getLast hn = s.2 := by
        simpa [List.getLast?_eq_some_getLast hn] using hlast
      have hclosing := edge_last_head_mem_cycleEdges hn
      rw [hh, hl, edge_comm] at hclosing
      have hs1 : s.1 = a := (congrArg Prod.fst he).symm
      have hs2 : s.2 = b := (congrArg Prod.snd he).symm
      simpa only [hs1, hs2] using hclosing
    · have hin : [a, b] <:+: faceVerts g n s := by
        apply (infix_pair_iff faceVerts_pairwise).mpr
        refine ⟨ha, hb, hab, fun z hz hzin => ?_⟩
        have hsab : (a, b) ∈ segs g n := hP.mem_segs.mpr ⟨hAdj, by simp only; omega⟩
        exact (mem_faceVerts.mp hz).2.2 (a, b) hsab ⟨hae.1, hbe.2.1⟩ he hzin
      exact pathEdges_subset_cycleEdges _ _ (pathEdges_infix hin (by simp [pathEdges]))
  rcases Nat.lt_or_gt_of_ne hab.1 with h | h
  · exact key a ha b hb h hab
  · rw [edge_comm]
    exact key b hb a ha h hab.symm

/-- A chordless convex cycle is exactly one of the existing polygon faces. -/
theorem chordless_convex_iff_face (hP : IsPolygon g n) {u : List ℕ} (hu : ConvexCycle g u) :
    ChordlessCycle g u ↔ ∃ s ∈ segs g n, u = faceVerts g n s := by
  constructor
  · intro hc
    obtain ⟨a, b, hr, hab, hl⟩ := hP.exists_top hu
    obtain ⟨htop, henc⟩ := hP.top_mem_encl hr hab hl
    refine ⟨(a, b), htop, ?_⟩
    apply hu.1.eq_of_mem_iff faceVerts_pairwise
    intro x
    constructor
    · intro hx
      have hbnd := hr.bounds hx
      apply mem_faceVerts.mpr
      refine ⟨hbnd.1, hbnd.2, fun t ht hwithin hne hinside => ?_⟩
      have htenc : t ∈ encl g n u := (hP.mem_encl_iff hr hab ht).mpr ⟨hwithin, x, hx, hinside⟩
      have htlt := (hP.mem_segs.mp ht).2
      have hta : t.1 ∈ u := (mem_encl.mp htenc).2 _ (left_mem_faceVerts (by omega))
      have htb : t.2 ∈ u := (mem_encl.mp htenc).2 _ (right_mem_faceVerts (by omega))
      have he := hc.2 t.1 hta t.2 htb (hP.mem_segs.mp ht).1
      have henorm : edge t.1 t.2 = t := by ext <;> simp [edge] <;> omega
      rw [henorm] at he
      obtain ⟨mid, heq⟩ := hr.eq_cons_snoc (by omega)
      rw [heq] at he
      rcases (mem_cycleEdges_of_pairwise (heq ▸ hu.1)).mp he with he | ⟨v, w, hin, he⟩
      · exact hne he
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        exact ((infix_pair_iff (heq ▸ hu.1)).mp hin).2.2.2 x (heq ▸ hx) hinside
    · exact (mem_encl.mp henc).2 x
  · rintro ⟨s, hs, rfl⟩
    exact hP.face_chordless hs

/-- Face boundaries are characterized by chordless simple cycles, independent of cycle
starting vertex and orientation. -/
theorem chordless_cycle_iff_face (hP : IsPolygon g n) {c : List ℕ} :
    ChordlessCycle g c ↔ ∃ s ∈ segs g n, IsCycle g c.length c ∧
      (cycleEdges c).toFinset = faceEdges g n s := by
  constructor
  · intro hc
    obtain ⟨hu, hlen, hsame⟩ := hP.convex_of_isCycle hc.1
    let u := c.insertionSort (· ≤ ·)
    have hmem : ∀ x, x ∈ u ↔ x ∈ c := by intro x; simp [u]
    have huc : ChordlessCycle g u := ⟨hu.isCycle, fun a ha b hb hab =>
      hsame.1 _ (hc.2 a ((hmem a).mp ha) b ((hmem b).mp hb) hab)⟩
    obtain ⟨s, hs, heq⟩ := (hP.chordless_convex_iff_face hu).mp huc
    refine ⟨s, hs, hc.1, ?_⟩
    ext e
    simp only [faceEdges, List.mem_toFinset, ← heq]
    exact ⟨hsame.1 e, hsame.2 e⟩
  · rintro ⟨s, hs, hc, heq⟩
    have hf := hP.face_chordless hs
    have hsame : SameCycle c (faceVerts g n s) := by
      constructor <;> intro e he
      · have hh : e ∈ faceEdges g n s := heq ▸ (List.mem_toFinset.mpr he)
        simpa only [faceEdges, List.mem_toFinset] using hh
      · have hh : e ∈ (cycleEdges c).toFinset := heq.symm ▸ (List.mem_toFinset.mpr he)
        simpa only [List.mem_toFinset] using hh
    have hmem : ∀ x, x ∈ c ↔ x ∈ faceVerts g n s := by
      intro x
      constructor
      · intro hx
        obtain ⟨y, _, he⟩ := hc.vertex_incident hx
        exact (mem_of_mem_cycleEdges (hsame.1 _ he)).1
      · intro hx
        obtain ⟨y, _, he⟩ := hf.1.vertex_incident hx
        exact (mem_of_mem_cycleEdges (hsame.2 _ he)).1
    exact ⟨hc, fun a ha b hb hab => hsame.2 _ (hf.2 a ((hmem a).mp ha) b ((hmem b).mp hb) hab)⟩

end IsPolygon

/-- Chordlessness is invariant under cycle starting vertex and orientation. -/
theorem ChordlessCycle.of_sameCycle {g : Graph} {c d : List ℕ} (hc : ChordlessCycle g c)
    (hd : IsCycle g d.length d) (hs : SameCycle d c) : ChordlessCycle g d := by
  have hmem : ∀ x, x ∈ d ↔ x ∈ c := by
    intro x
    constructor
    · intro hx
      obtain ⟨y, _, he⟩ := hd.vertex_incident hx
      exact (mem_of_mem_cycleEdges (hs.1 _ he)).1
    · intro hx
      obtain ⟨y, _, he⟩ := hc.1.vertex_incident hx
      exact (mem_of_mem_cycleEdges (hs.2 _ he)).1
  exact ⟨hd, fun a ha b hb hab => hs.2 _ (hc.2 a ((hmem a).mp ha) b ((hmem b).mp hb) hab)⟩

/-- Bounded face boundary in an outerplanar Hamiltonian embedding. The subsequent theorem
identifies this intrinsic criterion with the existing positional polygon faces. -/
def BoundedFaceBoundary (g : Graph) (F : Finset Edge) : Prop :=
  ∃ c, ChordlessCycle g c ∧ F = (cycleEdges c).toFinset

theorem IsPolygon.bounded_face_boundary_iff (hP : IsPolygon g n) {F : Finset Edge} :
    BoundedFaceBoundary g F ↔ ∃ s ∈ IsPolygon.segs g n, F = faceEdges g n s := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨s, hs, _, he⟩ := hP.chordless_cycle_iff_face.mp hc
    exact ⟨s, hs, he⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨faceVerts g n s, hP.face_chordless hs, rfl⟩

/-- Chordlessness transports through the actual graph/position relabeling. -/
theorem OuterplanarHam.chordless_posGraph {g : Graph} {ham c : List ℕ}
    (h : OuterplanarHam g ham) (hc : IsCycle (posGraph g ham) c.length c) :
    ChordlessCycle (posGraph g ham) c ↔
      ChordlessCycle g (c.map fun i => ham.getD i 0) := by
  let G := posGraph g ham
  let f := fun i => ham.getD i 0
  have hb : VerticesBelow G ham.length := by
    intro e he
    have hh := mem_posGraph.mp he
    exact ⟨by omega, hh.2.1⟩
  have hi : ∀ a, a < ham.length → ∀ b, b < ham.length → f a = f b → a = b := by
    intro a ha b hb he
    exact (h.1.2.2.1.getD_inj ha hb).mp he
  have hv := hc.vertex_bound hb
  have hmap : IsCycle g c.length (c.map f) :=
    Algo.Comb.isCycle_of_edge_iff (posGraph_relabel h) (hc.map f (fun a ha b hb he =>
      hi a (hv a ha) b (hv b hb) he))
  have hmap' : IsCycle g (c.map f).length (c.map f) := by simpa using hmap
  constructor
  · intro hch
    refine ⟨hmap', ?_⟩
    intro a ha b hb hab
    obtain ⟨i, hiC, rfl⟩ := List.mem_map.mp ha
    obtain ⟨j, hjC, rfl⟩ := List.mem_map.mp hb
    have hij : Adj G i j := adj_posGraph.mpr ⟨hv i hiC, hv j hjC, hab⟩
    have he := hch.2 i hiC j hjC hij
    rw [cycleEdges_map]
    exact List.mem_map.mpr ⟨edge i j, he, mapEdge_edge f i j⟩
  · intro hch
    refine ⟨hc, ?_⟩
    intro i hiC j hjC hij
    have he := hch.2 (f i) (List.mem_map_of_mem hiC) (f j) (List.mem_map_of_mem hjC)
      (adj_posGraph.mp hij).2.2
    rw [cycleEdges_map] at he
    obtain ⟨e, heC, he⟩ := List.mem_map.mp he
    have hinj := mapEdge_injective_on hb posGraph_normalized f hi (hc.2.2.2 _ heC) hij.2
    have heq : e = edge i j := hinj (he.trans (mapEdge_edge f i j).symm)
    exact heq ▸ heC

/-- The intrinsic face-boundary criterion is exactly the bounded faces of the positional
polygon of this particular outerplanar Hamiltonian embedding, mapped back to real labels. -/
theorem OuterplanarHam.bounded_face_boundary_iff {g : Graph} {ham : List ℕ}
    (h : OuterplanarHam g ham) {F : Finset Edge} :
    BoundedFaceBoundary g F ↔ ∃ s ∈ IsPolygon.segs (posGraph g ham) ham.length,
      F = (cycleEdges ((faceVerts (posGraph g ham) ham.length s).map
        fun i => ham.getD i 0)).toFinset := by
  let G := posGraph g ham
  let f := fun i => ham.getD i 0
  have hP := isPolygon_posGraph h
  have hb : VerticesBelow G ham.length := by
    intro e he
    have hh := mem_posGraph.mp he
    exact ⟨by omega, hh.2.1⟩
  have hi : ∀ a, a < ham.length → ∀ b, b < ham.length → f a = f b → a = b := by
    intro a ha b hb he
    exact (h.1.2.2.1.getD_inj ha hb).mp he
  constructor
  · rintro ⟨c, hc, rfl⟩
    have hcm := Algo.Comb.isCycle_of_edge_iff
      (fun a b hne => (posGraph_relabel h a b hne).symm) hc.1
    obtain ⟨d, hd, hec⟩ := IsCycle.unmap hb posGraph_normalized f hi hcm
    have hd' : IsCycle G d.length d := by rw [hd.2.1]; exact hd
    have hch : ChordlessCycle G d := (h.chordless_posGraph hd').mpr (by rw [← hec]; exact hc)
    obtain ⟨s, hs, _, hed⟩ := hP.chordless_cycle_iff_face.mp hch
    have hsame : SameCycle d (faceVerts G ham.length s) := by
      constructor <;> intro e he
      · have hh : e ∈ faceEdges G ham.length s := hed ▸ (List.mem_toFinset.mpr he)
        exact List.mem_toFinset.mp hh
      · have hh : e ∈ (cycleEdges d).toFinset := hed.symm ▸ (List.mem_toFinset.mpr he)
        exact List.mem_toFinset.mp hh
    have hsmap := hsame.map f
    refine ⟨s, hs, ?_⟩
    rw [hec]
    ext e
    simp only [List.mem_toFinset]
    exact ⟨hsmap.1 e, hsmap.2 e⟩
  · rintro ⟨s, hs, rfl⟩
    have hface := hP.face_chordless hs
    exact ⟨_, (h.chordless_posGraph hface.1).mp hface, rfl⟩

/-- Actual induced subgraph on the retained vertices. -/
def inducedGraph (g : Graph) (R : ℕ → Prop) [DecidablePred R] : Graph :=
  g.filter fun e => decide (R e.1 ∧ R e.2)

theorem adj_inducedGraph {g : Graph} {R : ℕ → Prop} [DecidablePred R] {a b : ℕ} :
    Adj (inducedGraph g R) a b ↔ Adj g a b ∧ R a ∧ R b := by
  unfold Adj inducedGraph
  simp only [List.mem_filter, decide_eq_true_eq]
  rcases Nat.le_total a b with h | h
  · simp only [edge, Nat.min_eq_left h, Nat.max_eq_right h]
    tauto
  · simp only [edge, Nat.min_eq_right h, Nat.max_eq_left h]
    tauto

theorem isCycle_inducedGraph {g : Graph} {R : ℕ → Prop} [DecidablePred R] {c : List ℕ} :
    IsCycle (inducedGraph g R) c.length c ↔ IsCycle g c.length c ∧ ∀ v ∈ c, R v := by
  constructor
  · intro hc
    refine ⟨hc.graph_mono (fun e he => (List.mem_filter.mp he).1), fun v hv => ?_⟩
    obtain ⟨w, _, he⟩ := hc.vertex_incident hv
    have hh := List.mem_filter.mp (hc.2.2.2 _ he)
    have hr : R (edge v w).1 ∧ R (edge v w).2 := decide_eq_true_eq.mp hh.2
    rcases Nat.le_total v w with h | h
    · simpa only [edge, Nat.min_eq_left h, Nat.max_eq_right h] using hr.1
    · simpa only [edge, Nat.min_eq_right h, Nat.max_eq_left h] using hr.2
  · rintro ⟨hc, hr⟩
    refine ⟨hc.1, hc.2.1, hc.2.2.1, fun e he => ?_⟩
    have hv := cycleEdges_endpoints he
    exact List.mem_filter.mpr ⟨hc.2.2.2 _ he, decide_eq_true ⟨hr _ hv.1, hr _ hv.2⟩⟩

/-- Chordless cycles in an induced subgraph are precisely the surviving original ones. -/
theorem chordless_inducedGraph {g : Graph} {R : ℕ → Prop} [DecidablePred R] {c : List ℕ} :
    ChordlessCycle (inducedGraph g R) c ↔ ChordlessCycle g c ∧ ∀ v ∈ c, R v := by
  constructor
  · intro hc
    obtain ⟨hcg, hr⟩ := isCycle_inducedGraph.mp hc.1
    refine ⟨⟨hcg, fun a ha b hb hab => ?_⟩, hr⟩
    exact hc.2 a ha b hb (adj_inducedGraph.mpr ⟨hab, hr a ha, hr b hb⟩)
  · rintro ⟨hc, hr⟩
    exact ⟨isCycle_inducedGraph.mpr ⟨hc.1, hr⟩,
      fun a ha b hb hab => hc.2 a ha b hb (adj_inducedGraph.mp hab).1⟩

/-- Exact bounded-face transport under an actual induced graph deletion. -/
theorem bounded_face_inducedGraph {g : Graph} {R : ℕ → Prop} [DecidablePred R]
    {F : Finset Edge} :
    BoundedFaceBoundary (inducedGraph g R) F ↔
      BoundedFaceBoundary g F ∧ ∀ e ∈ F, R e.1 ∧ R e.2 := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨hcg, hr⟩ := chordless_inducedGraph.mp hc
    refine ⟨⟨c, hcg, rfl⟩, fun e he => ?_⟩
    have hv := cycleEdges_endpoints (List.mem_toFinset.mp he)
    exact ⟨hr _ hv.1, hr _ hv.2⟩
  · rintro ⟨⟨c, hc, rfl⟩, hr⟩
    refine ⟨c, chordless_inducedGraph.mpr ⟨hc, fun v hv => ?_⟩, rfl⟩
    obtain ⟨w, _, he⟩ := hc.1.vertex_incident hv
    have hh := hr _ (List.mem_toFinset.mpr he)
    rcases Nat.le_total v w with h | h
    · simpa only [edge, Nat.min_eq_left h, Nat.max_eq_right h] using hh.1
    · simpa only [edge, Nat.min_eq_right h, Nat.max_eq_left h] using hh.2

namespace IsPolygon

variable {g : Graph} {n : ℕ}

/-- Distinct polygon faces have distinct boundary edge sets. -/
theorem faceEdges_injective (hP : IsPolygon g n) {s t : ℕ × ℕ}
    (hs : s ∈ segs g n) (ht : t ∈ segs g n) (he : faceEdges g n s = faceEdges g n t) : s = t := by
  have heq := (hP.faceVerts_convexCycle hs).eq_of_edges (hP.faceVerts_convexCycle ht) he
  have hslt := (hP.mem_segs.mp hs).2
  have htlt := (hP.mem_segs.mp ht).2
  apply Prod.ext
  · have hh := congrArg List.head? heq
    rw [faceVerts_head? (by omega), faceVerts_head? (by omega)] at hh
    exact Option.some.inj hh
  · have hh := congrArg List.getLast? heq
    rw [faceVerts_getLast? (by omega), faceVerts_getLast? (by omega)] at hh
    exact Option.some.inj hh

/-- Non-root leaf deletion has exactly the other original bounded face boundaries. -/
theorem leaf_delete_faces (hP : IsPolygon g n) {s : ℕ × ℕ} (hs : s ∈ segs g n)
    (hsroot : s ≠ (0, n - 1)) (hleaf : ∀ t ∈ segs g n, ¬ IsChild g n s t)
    {F : Finset Edge} :
    BoundedFaceBoundary (leafDelete g s) F ↔
      ∃ t ∈ (segs g n).erase s, F = faceEdges g n t := by
  let R := fun v => ¬ (s.1 < v ∧ v < s.2)
  have heq : leafDelete g s = inducedGraph g R := rfl
  rw [heq, bounded_face_inducedGraph, hP.bounded_face_boundary_iff]
  constructor
  · rintro ⟨⟨t, ht, rfl⟩, hr⟩
    refine ⟨t, Finset.mem_erase.mpr ⟨?_, ht⟩, rfl⟩
    intro hts
    subst t
    obtain ⟨v, hv, hv1, hv2⟩ := hP.exists_inner_faceVert hs
    have hc := (hP.faceVerts_convexCycle hs).isCycle
    obtain ⟨w, _, he⟩ := hc.vertex_incident hv
    have hR := hr _ (List.mem_toFinset.mpr he)
    have hvR : R v := by
      rcases Nat.le_total v w with h | h
      · simpa only [edge, Nat.min_eq_left h, Nat.max_eq_right h] using hR.1
      · simpa only [edge, Nat.min_eq_right h, Nat.max_eq_left h] using hR.2
    exact hvR ⟨hv1, hv2⟩
  · rintro ⟨t, ht, rfl⟩
    refine ⟨⟨t, Finset.mem_of_mem_erase ht, rfl⟩, ?_⟩
    obtain ⟨u, _, _, hfaces, _⟩ := hP.leaf_delete_hamiltonian hs hsroot hleaf
    intro e he
    have heG := (hfaces t ht).2.2 e (List.mem_toFinset.mp he)
    exact decide_eq_true_eq.mp (List.mem_filter.mp heG).2

end IsPolygon

/-- The weak dual on actual bounded face boundaries: distinct faces sharing an edge. -/
def BoundaryDualAdj (g : Graph) (F H : Finset Edge) : Prop :=
  BoundedFaceBoundary g F ∧ BoundedFaceBoundary g H ∧ F ≠ H ∧ (F ∩ H).Nonempty

namespace IsPolygon

variable {g : Graph} {n : ℕ}

/-- The old weak dual and the intrinsic boundary weak dual agree. -/
theorem boundary_dual_iff (hP : IsPolygon g n) {s t : ℕ × ℕ}
    (hs : s ∈ segs g n) (ht : t ∈ segs g n) :
    BoundaryDualAdj g (faceEdges g n s) (faceEdges g n t) ↔ DualAdj g n s t := by
  have hn : faceEdges g n s ≠ faceEdges g n t ↔ s ≠ t :=
    ⟨fun h he => h (he ▸ rfl), fun h he => h (hP.faceEdges_injective hs ht he)⟩
  simp only [BoundaryDualAdj, DualAdj, hn]
  have hsF : BoundedFaceBoundary g (faceEdges g n s) :=
    hP.bounded_face_boundary_iff.mpr ⟨s, hs, rfl⟩
  have htF : BoundedFaceBoundary g (faceEdges g n t) :=
    hP.bounded_face_boundary_iff.mpr ⟨t, ht, rfl⟩
  tauto

/-- The surviving original faces biject onto all bounded faces of the actual deleted graph. -/
theorem leaf_delete_face_bijection (hP : IsPolygon g n) {s : ℕ × ℕ} (hs : s ∈ segs g n)
    (hsroot : s ≠ (0, n - 1)) (hleaf : ∀ t ∈ segs g n, ¬ IsChild g n s t) :
    Set.BijOn (faceEdges g n) ((segs g n).erase s : Set (ℕ × ℕ))
      {F | BoundedFaceBoundary (leafDelete g s) F} := by
  refine ⟨fun t ht => ?_, fun t ht u hu he => ?_, fun F hF => ?_⟩
  · exact (hP.leaf_delete_faces hs hsroot hleaf).mpr ⟨t, ht, rfl⟩
  · exact hP.faceEdges_injective (Finset.mem_of_mem_erase ht) (Finset.mem_of_mem_erase hu) he
  · obtain ⟨t, ht, he⟩ := (hP.leaf_delete_faces hs hsroot hleaf).mp hF
    exact ⟨t, ht, he.symm⟩

/-- Exact weak-dual transport: adjacency in the new graph is original adjacency restricted
to the surviving faces. Together with the preceding bijection this is `D' = D - v_f`. -/
theorem leaf_delete_weakDual (hP : IsPolygon g n) {s : ℕ × ℕ} (hs : s ∈ segs g n)
    (hsroot : s ≠ (0, n - 1)) (hleaf : ∀ t ∈ segs g n, ¬ IsChild g n s t)
    {t u : ℕ × ℕ} (ht : t ∈ segs g n) (hu : u ∈ segs g n) :
    BoundaryDualAdj (leafDelete g s) (faceEdges g n t) (faceEdges g n u) ↔
      t ≠ s ∧ u ≠ s ∧ DualAdj g n t u := by
  have hF : ∀ v ∈ segs g n,
      BoundedFaceBoundary (leafDelete g s) (faceEdges g n v) ↔ v ≠ s := by
    intro v hv
    rw [hP.leaf_delete_faces hs hsroot hleaf]
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

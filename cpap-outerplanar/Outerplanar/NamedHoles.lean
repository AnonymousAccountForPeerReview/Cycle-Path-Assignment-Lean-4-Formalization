module

public import Outerplanar.WeakDualCount
import Outerplanar.Algo.PolyPool
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# Cycle-count claims

The proposition constants retain their original names. Both claims used in the proof of
Lemma 35 are proved below. The counting proof uses the sharper generating-function bound
already available for region paths, rather than the manuscript's neighborhood enumeration.
-/

@[expose] public section

namespace STACS2027

/-- For `k ≥ 3`, at most `2^{M_k}` convex `k`-cycles enclose a bounded face, where
`M_k = ∑_{i=0}^{k−3} k^i` (proof of Lemma 35). -/
def EnclosingCycleCountBound : Prop :=
  ∀ (g : Graph) (n : ℕ), IsPolygon g n → ∀ (k : ℕ), 3 ≤ k → ∀ (s : ℕ × ℕ),
    ((convexList g n k).filter fun u => s ∈ encl g n u).length ≤
      2 ^ (∑ i ∈ Finset.range (k - 2), k ^ i)

/-- A convex cycle encloses at most its length minus two bounded faces, and each enclosed
face has perimeter at most that length (proof of Lemma 35). -/
def EnclosedFacesBound : Prop :=
  ∀ (g : Graph) (n : ℕ), IsPolygon g n → ∀ (u : List ℕ), ConvexCycle g u →
    (encl g n u).card + 2 ≤ u.length ∧ ∀ s ∈ encl g n u, (faceVerts g n s).length ≤ u.length

namespace IsPolygon

variable {g : Graph} {n : ℕ}

/-- The subtree dichotomy in Lemma 31(1): if the parent is not enclosed, all enclosed
faces are below the child, or none is. In the polygon model, being below is containment. -/
theorem enclosed_faces_child_dichotomy (hP : IsPolygon g n) {a b : ℕ} {u : List ℕ}
    (hu : IsRPath g a b u) (hab : Adj g a b) (hl : 3 ≤ u.length)
    {s p : ℕ × ℕ} (hs : s ∈ segs g n) (hp : p ∈ segs g n)
    (hc : IsChild g n p s) (hn : p ∉ encl g n u) :
    (∀ t ∈ encl g n u, Within t s) ∨ (∀ t ∈ encl g n u, ¬ Within t s) := by
  have hT := (hP.top_mem_encl hu hab hl).1
  have hst := hP.mem_segs.mp hs
  have htop := hP.mem_segs.mp hT
  by_cases hw : Within (a, b) s
  · left
    intro t ht
    exact (((hP.mem_encl_iff hu hab (encl_subset ht)).mp ht).1).trans hw
  · right
    intro t ht hts
    obtain ⟨htt, z, hz, hz1, hz2⟩ := (hP.mem_encl_iff hu hab (encl_subset ht)).mp ht
    rcases hP.laminar hst.1 hab (by omega) (by omega) with w | w | w | w
    · have hne : s ≠ (a, b) := by
        intro he
        apply hw
        rw [← he]
        exact Within.refl s
      have hwp := hP.parent_within hs hp hT hc w hne
      apply hn
      apply (hP.mem_encl_iff hu hab hp).mpr
      refine ⟨hwp, z, hz, ?_, ?_⟩
      · have hsp := hc.2.1
        simp only [Within] at htt hts hsp
        omega
      · have hsp := hc.2.1
        simp only [Within] at htt hts hsp
        omega
    · exact hw w
    · simp only [Within] at htt hts
      omega
    · simp only [Within] at htt hts
      omega

/-- Lemma 31(2): the top is precisely an enclosed face whose parent is not enclosed. -/
theorem top_face_iff_parent_not_enclosed (hP : IsPolygon g n) {a b : ℕ} {u : List ℕ}
    (hu : IsRPath g a b u) (hab : Adj g a b) (hl : 3 ≤ u.length)
    {s p : ℕ × ℕ} (hp : p ∈ segs g n) (hc : IsChild g n p s) :
    (a, b) = s ↔ s ∈ encl g n u ∧ p ∉ encl g n u := by
  constructor
  · rintro rfl
    refine ⟨(hP.top_mem_encl hu hab hl).2, fun he => ?_⟩
    have hw := ((hP.mem_encl_iff hu hab hp).mp he).1
    exact hc.1 (Within.antisymm hc.2.1 hw)
  · rintro ⟨hs, hn⟩
    by_contra hne
    exact hn (hP.encl_parent hu hab hs (fun h => hne h.symm) hp hc)

/-- Lemma 31(3): a boundary cycle at a nonroot face encloses its parent face. The boundary
is the set used by the proved tree dynamic program. -/
theorem boundary_iff_parent_enclosed (hP : IsPolygon g n) {k : ℕ} (hk : 3 ≤ k)
    {s p : ℕ × ℕ} (hs : s ∈ segs g n) (hp : p ∈ segs g n)
    (hc : IsChild g n p s) (x : CycVar g n k) :
    x ∈ (polygonProblem hP hk).boundary ⟨s, hs⟩ ↔ p ∈ encl g n x.1 := by
  rw [Poly.mem_boundary hP hk s hs x]
  have hcyc := (hP.mem_convexCycles.mp x.2).1
  obtain ⟨a, b, hu, hab, hl⟩ := hP.exists_top hcyc
  have htop := Poly.topOf_of_isRPath hu
  have hT := (hP.top_mem_encl hu hab hl).1
  constructor
  · rintro ⟨hleft, hright, hne⟩
    have hst : Within s (a, b) := ⟨(hu.bounds hleft).1, (hu.bounds hright).2⟩
    have hneq : s ≠ (a, b) := fun he => hne (htop.trans he.symm)
    have hw := hP.parent_within hs hp hT hc hst hneq
    apply (hP.mem_encl_iff hu hab hp).mpr
    refine ⟨hw, ?_⟩
    have hsp := hc.2.1
    by_cases hh : p.1 < s.1
    · exact ⟨s.1, hleft, hh, by
        have hslt := (hP.mem_segs.mp hs).2
        simp only [Within] at hsp
        omega⟩
    · have hh' : s.2 < p.2 := by
        by_contra hge
        apply hc.1
        simp only [Within] at hsp
        exact Prod.ext (by omega) (by omega)
      exact ⟨s.2, hright, by
        have hslt := (hP.mem_segs.mp hs).2
        simp only [Within] at hsp
        omega, hh'⟩
  · intro he
    have hsub := (mem_encl.mp he).2
    obtain ⟨hle, hre, _, _⟩ :=
      (infix_pair_iff faceVerts_pairwise).mp (hP.infix_faceVerts_of_child hs hc)
    refine ⟨hsub _ hle, hsub _ hre, fun hsame => ?_⟩
    have heq : (a, b) = s := htop.symm.trans hsame
    have hw := ((hP.mem_encl_iff hu hab hp).mp he).1
    rw [heq] at hw
    exact hc.1 (Within.antisymm hc.2.1 hw)

/-- Lemma 31(1), including the graph edges: without the parent face, a cycle and its
selected faces lie wholly in the child subtree or are disjoint from it. The edge set of a
polygon subtree consists exactly of edges whose owners are below its root, equivalently
those contained in its interval (`own_within_iff`). -/
theorem cycle_child_dichotomy (hP : IsPolygon g n) {u : List ℕ} (hcyc : ConvexCycle g u)
    {s p : ℕ × ℕ} (hs : s ∈ segs g n) (hp : p ∈ segs g n)
    (hc : IsChild g n p s) (hn : p ∉ encl g n u) :
    ((∀ t ∈ encl g n u, Within t s) ∧
      (∀ e ∈ polyEdges g n, e ∈ cycleEdges u → Within e s)) ∨
    ((∀ t ∈ encl g n u, ¬ Within t s) ∧
      (∀ e ∈ polyEdges g n, e ∈ cycleEdges u → ¬ Within e s)) := by
  obtain ⟨a, b, hu, hab, hl⟩ := hP.exists_top hcyc
  have htop := (hP.top_mem_encl hu hab hl).2
  by_cases hw : Within (a, b) s
  · left
    refine ⟨fun t ht => (((hP.mem_encl_iff hu hab (encl_subset ht)).mp ht).1).trans hw,
      fun e he hec => ?_⟩
    have hends := cycleEdges_endpoints hec
    exact (show Within e (a, b) from ⟨(hu.bounds hends.1).1, (hu.bounds hends.2).2⟩).trans hw
  · right
    have hfaces : ∀ t ∈ encl g n u, ¬ Within t s := by
      rcases hP.enclosed_faces_child_dichotomy hu hab hl hs hp hc hn with h | h
      · exact False.elim (hw (h (a, b) htop))
      · exact h
    refine ⟨hfaces, fun e he hec hew => ?_⟩
    let x : CycVar g n u.length := ⟨u, hP.mem_convexCycles.mpr ⟨hcyc, rfl⟩⟩
    have hne : x ∉ (polygonProblem hP hcyc.2.1).boundary ⟨s, hs⟩ := by
      intro hx
      exact hn ((hP.boundary_iff_parent_enclosed hcyc.2.1 hs hp hc x).mp hx)
    apply hne
    simp only [TreeDP.Problem.boundary, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨?_, e, he, ?_, ?_⟩
    · rw [mem_sub_iff]
      change ¬ Within (u.head (ne_nil_of_mem_convexCycles hcyc.2.1 x.2),
        u.getLast (ne_nil_of_mem_convexCycles hcyc.2.1 x.2)) s
      have hpair : (u.head (ne_nil_of_mem_convexCycles hcyc.2.1 x.2),
          u.getLast (ne_nil_of_mem_convexCycles hcyc.2.1 x.2)) = (a, b) := by
        apply Prod.ext
        · exact Option.some.inj ((List.head?_eq_some_head _).symm.trans hu.1)
        · exact Option.some.inj ((List.getLast?_eq_some_getLast _).symm.trans hu.2.1)
      rw [hpair]
      exact hw

    · rw [mem_sub_iff]
      exact (hP.own_within_iff (hP.mem_polyEdges.mp he).1 (hP.mem_polyEdges.mp he).2 hs).mpr hew
    · simp only [polygonProblem, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hec

/-- The length identity for the subtree enclosed by a particular convex cycle. -/
theorem enclosed_length_identity (hP : IsPolygon g n) {u : List ℕ} (hu : ConvexCycle g u) :
    u.length + 2 * ((encl g n u).card - 1) =
      ∑ s ∈ encl g n u, (faceVerts g n s).length := by
  obtain ⟨v, hv, he, hl⟩ := hP.exists_convex_of_isSubtree (hP.isSubtree_encl hu)
  have huv : u = v := hu.eq_of_edges hv (by
    rw [← hP.bdry_encl hu, ← hP.bdry_encl hv, he])
  subst v
  exact hl

/-- A cycle can enclose at most its length minus two faces, all of smaller or equal
perimeter. -/
theorem enclosed_faces_bound (hP : IsPolygon g n) {u : List ℕ} (hu : ConvexCycle g u) :
    (encl g n u).card + 2 ≤ u.length ∧
      ∀ s ∈ encl g n u, (faceVerts g n s).length ≤ u.length := by
  have hsum : 3 * (encl g n u).card ≤
      ∑ s ∈ encl g n u, (faceVerts g n s).length := by
    calc 3 * (encl g n u).card = ∑ _s ∈ encl g n u, 3 := by simp [Nat.mul_comm]
      _ ≤ _ := Finset.sum_le_sum fun s hs => hP.three_le_length_faceVerts (encl_subset hs)
  have hlen := hP.enclosed_length_identity hu
  have hpos := Finset.card_pos.mpr (hP.isSubtree_encl hu).1
  refine ⟨by omega, fun s hs => ?_⟩
  have hnd : (faceVerts g n s).Nodup := faceVerts_pairwise.imp fun h => Nat.ne_of_lt h
  exact hnd.length_le_of_subset (mem_encl.mp hs).2

/-- A triangle enclosing a face is exactly that face's ordered vertex list. -/
theorem triangle_eq_face (hP : IsPolygon g n) {u : List ℕ} (hu : ConvexCycle g u)
    (hl : u.length = 3) {s : ℕ × ℕ} (hs : s ∈ encl g n u) : u = faceVerts g n s := by
  have hsub := (mem_encl.mp hs).2
  have hnd : (faceVerts g n s).Nodup := faceVerts_pairwise.imp fun h => Nat.ne_of_lt h
  have hlow := hP.three_le_length_faceVerts (encl_subset hs)
  have hhigh := hnd.length_le_of_subset hsub
  have hslist := List.sublist_of_subperm_of_pairwise (hnd.subperm hsub) faceVerts_pairwise hu.1
  exact (hslist.eq_of_length (by omega)).symm

/-- At most one convex triangle encloses a given face. -/
theorem triangle_face_count_bound (hP : IsPolygon g n) (s : ℕ × ℕ) :
    ((convexList g n 3).filter fun u => s ∈ encl g n u).length ≤ 1 := by
  let L := (convexList g n 3).filter fun u => s ∈ encl g n u
  have hsub : L.toFinset ⊆ {faceVerts g n s} := by
    intro u hu
    obtain ⟨hc, he⟩ := List.mem_filter.mp (List.mem_toFinset.mp hu)
    have hh := hP.mem_convexList.mp hc
    exact Finset.mem_singleton.mpr (hP.triangle_eq_face hh.1 hh.2 (of_decide_eq_true he))
  have hcard := Finset.card_le_card hsub
  have hnd : L.Nodup := convexList_nodup.filter _
  rw [List.toFinset_card_of_nodup hnd, Finset.card_singleton] at hcard
  exact hcard

/-- The exponent in the paper bound dominates `2k` for `k ≥ 5`. -/
theorem neighborhood_exponent_bound {k : ℕ} (hk : 5 ≤ k) :
    2 * k ≤ ∑ i ∈ Finset.range (k - 2), k ^ i := by
  have hsub : Finset.range 3 ⊆ Finset.range (k - 2) :=
    Finset.range_mono (by omega)
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
      (f := fun i => k ^ i)
  have hsmall : ∑ i ∈ Finset.range 3, k ^ i = 1 + k + k * k := by
    simp [Finset.sum_range_succ, pow_two]
  rw [hsmall] at hsum
  have hkk : k ≤ k * k := by nlinarith
  omega

/-- The cycle bound used by the paper, proved for all `k ≥ 3`. -/
theorem enclosing_cycle_count_bound (hP : IsPolygon g n) {k : ℕ} (hk : 3 ≤ k)
    (s : ℕ × ℕ) :
    ((convexList g n k).filter fun u => s ∈ encl g n u).length ≤
      2 ^ (∑ i ∈ Finset.range (k - 2), k ^ i) := by
  by_cases hthree : k = 3
  · subst k
    have hh := hP.triangle_face_count_bound s
    norm_num [Finset.sum_range_succ] at ⊢
    omega
  by_cases hfour : k = 4
  · subst k
    have hh := hP.face_cycle_half_bound (by omega) s
    norm_num [Finset.sum_range_succ] at hh ⊢
    omega
  have hkfive : 5 ≤ k := by omega
  have hbound := hP.face_cycle_bound hk s
  have hpow : (4 : ℕ) ^ k = 2 ^ (2 * k) := by rw [pow_mul]; norm_num
  rw [hpow] at hbound
  exact hbound.trans (Nat.pow_le_pow_right (by omega) (neighborhood_exponent_bound hkfive))

end IsPolygon

/-- Proof of the proposition constant retained for the paper alignment. -/
theorem enclosedFacesBound_proved : EnclosedFacesBound := by
  intro g n hP u hu
  exact hP.enclosed_faces_bound hu

/-- Proof of the proposition constant retained for the paper alignment. -/
theorem enclosingCycleCountBound_proved : EnclosingCycleCountBound := by
  intro g n hP k hk s
  exact hP.enclosing_cycle_count_bound hk s

end STACS2027

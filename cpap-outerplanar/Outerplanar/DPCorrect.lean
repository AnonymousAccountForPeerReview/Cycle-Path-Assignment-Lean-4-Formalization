module

public import Outerplanar.Segments
public import Mathlib.Data.List.Sublists
import Mathlib.Tactic

/-!
# Lemma 34: the dynamic program over the weak dual computes the optimum

For a polygon `g` on `0, …, n - 1` (a 2-connected outerplanar graph in the positions of its
outer cycle) and `k ≥ 3`, the cycle-path assignment problem is an instance of the tree
dynamic program of `TreeDP` on the segment tree (the rooted weak dual):

* the variables are the convex `k`-cycles (`convexCycles`), which represent the `k`-cycles
  of `g` once each (`convex_of_isCycle`, `ConvexCycle.eq_of_sameCycle`); a value `j : Fin k`
  omits the `j`-th vertex, leaving the path `selectedAt u u[j]`;
* the top of a cycle is its top segment, the face of least depth it encloses (`top(c)`);
* the factors are the edges, each owned by the deepest face it bounds (`own`, the paper's
  `E_{v_f}`, Lemma 30), with cost `binom(l(e), 2)`;
* a cycle through an edge owned by `s` has its top at `s` or above (`scope_top`), so the
  abstract Lemmas 32 and 33 (`TreeDP.Problem.top_eq_or_mem_boundary`, `boundary_child`)
  apply. The paper derives Lemmas 32 and 33 from Lemma 31 (where the subtree `∂⁻¹(c)` of a
  cycle lies relative to the subtree of a face, and when the face is the top of `c`); here
  that is the containment of segments behind `top` and `scope_top`, and Lemma 31 is not
  stated separately.

`dp_root_optimal`: the value `dp root α` of the dynamic program at the root is the optimum
`C*` of `CPAP(g, k)`. `dp_table_correct`: every table entry `DP[v, α]` is the least cost of
the edges of the subtree of `v` over the assignments extending `α` (the paper's statement
of Lemma 34). The boundary variables are the paper's `B_{v_f}`: the cycles through both
ends of the segment with another top (`Poly.mem_boundary`, `Outerplanar/Algo/PolyPool.lean`).
-/

@[expose] public section

namespace STACS2027

instance (g : Graph) : DecidablePred (ConvexCycle g) := fun u =>
  decidable_of_iff (u.Pairwise (· < ·) ∧ 3 ≤ u.length ∧ ∀ e ∈ cycleEdges u, g.contains e = true)
    (by simp [ConvexCycle])

/-- The convex `k`-cycles of `g` on the positions `0, …, n - 1`, as a list. -/
def convexList (g : Graph) (n k : ℕ) : List (List ℕ) :=
  ((List.range n).sublistsLen k).filter fun u => decide (ConvexCycle g u)

/-- The convex `k`-cycles of `g` on the positions `0, …, n - 1`. -/
def convexCycles (g : Graph) (n k : ℕ) : Finset (List ℕ) := (convexList g n k).toFinset

/-- The edges `(a, b)`, `a < b`, of `g` on the positions `0, …, n - 1`. -/
def polyEdges (g : Graph) (n : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range n) ×ˢ (Finset.range n)).filter fun e => Adj g e.1 e.2 ∧ e.1 < e.2

namespace IsPolygon

variable {g : Graph} {n k : ℕ}

theorem mem_convexList (hP : IsPolygon g n) {u : List ℕ} :
    u ∈ convexList g n k ↔ ConvexCycle g u ∧ u.length = k := by
  simp only [convexList, List.mem_filter, List.mem_sublistsLen, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨-, hl⟩, hc⟩; exact ⟨hc, hl⟩
  · rintro ⟨hc, hl⟩
    refine ⟨⟨?_, hl⟩, hc⟩
    have hlt : ∀ x ∈ u, x ∈ List.range n := by
      intro x hx
      obtain ⟨w, hwx, hw⟩ := hc.isCycle.vertex_incident hx
      have := hc.2.2 _ hw
      have hne : x ≠ w := fun h => hwx h.symm
      simp only [List.mem_range]
      exact (hP.lt_of_adj (⟨hne, this⟩ : Adj g x w)).1
    have hsp : u.Subperm (List.range n) := hc.isCycle.2.2.1.subperm hlt
    exact List.sublist_of_subperm_of_pairwise hsp hc.1 List.pairwise_lt_range

theorem mem_convexCycles (hP : IsPolygon g n) {u : List ℕ} :
    u ∈ convexCycles g n k ↔ ConvexCycle g u ∧ u.length = k := by
  rw [convexCycles, List.mem_toFinset, hP.mem_convexList]

theorem convexList_nodup : (convexList g n k).Nodup :=
  (List.nodup_sublistsLen k List.nodup_range).filter _

theorem mem_polyEdges (hP : IsPolygon g n) {e : ℕ × ℕ} :
    e ∈ polyEdges g n ↔ Adj g e.1 e.2 ∧ e.1 < e.2 := by
  simp only [polyEdges, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  exact ⟨fun h => h.2, fun h => ⟨hP.lt_of_adj h.1, h⟩⟩

theorem ne_nil_of_mem_convexCycles (hk : 3 ≤ k) {u : List ℕ}
    (hu : u ∈ convexCycles g n k) : u ≠ [] := by
  rintro rfl
  simp [convexCycles, convexList, List.mem_sublistsLen] at hu
  omega

end IsPolygon

/-- The cycle variables: the convex `k`-cycles. -/
abbrev CycVar (g : Graph) (n k : ℕ) := {u : List ℕ // u ∈ convexCycles g n k}

/-- The vertex omitted from the cycle `u` by the value `j`. -/
def omitted (u : List ℕ) (j : ℕ) : ℕ := u.getD j 0

/-- The load of the edge `e` under the values `γ`: the number of chosen paths through `e`. -/
def cycLoad {g : Graph} {n k : ℕ} (γ : CycVar g n k → Fin k) (e : ℕ × ℕ) : ℕ :=
  (Finset.univ.filter fun x : CycVar g n k => e ∈ selectedAt x.1 (omitted x.1 (γ x))).card

open TreeDP in
/-- **CPAP on a polygon as a tree dynamic program.** -/
noncomputable def polygonProblem (hP : IsPolygon g n) (hk : 3 ≤ k) :
    Problem (IsPolygon.Seg g n) (CycVar g n k) (ℕ × ℕ) (Fin k) (IsPolygon.segTree hP) where
  top x := ⟨(x.1.head (IsPolygon.ne_nil_of_mem_convexCycles hk x.2),
    x.1.getLast (IsPolygon.ne_nil_of_mem_convexCycles hk x.2)),
    hP.top_mem_segs ((hP.mem_convexCycles.mp x.2).1) _⟩
  factors := polyEdges g n
  own := IsPolygon.own hP
  cost e γ := pairCount (cycLoad γ e)
  scope e := Finset.univ.filter fun x => e ∈ cycleEdges x.1
  cost_congr := by
    intro e γ γ' h
    congr 1
    unfold cycLoad
    congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hx : e ∈ cycleEdges x.1
    · rw [h x (by simp [hx])]
    · constructor <;> intro h' <;> exact absurd (selectedAt_mem.mp h').1 hx
  scope_top := by
    intro e he x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    rw [IsPolygon.mem_sub_iff]
    have he' := hP.mem_polyEdges.mp he
    have hxc := (hP.mem_convexCycles.mp x.2).1
    have hee : edge e.1 e.2 = e := by simp [edge, Nat.min_eq_left he'.2.le, Nat.max_eq_right he'.2.le]
    rw [← hee] at hx
    obtain ⟨h1, h2⟩ := mem_of_mem_cycleEdges hx
    have hu := IsPolygon.ne_nil_of_mem_convexCycles hk x.2
    have hw : Within e (x.1.head hu, x.1.getLast hu) :=
      ⟨(IsPolygon.mem_within_head_last hxc.1 hu h1).1, (IsPolygon.mem_within_head_last hxc.1 hu h2).2⟩
    exact (hP.own_spec he'.1 he'.2).2 _ (hP.top_mem_segs hxc hu) hw

/-! ### The optimum -/

namespace IsPolygon

variable {g : Graph} {n k : ℕ}

theorem load_map_eq_length (cs : List (List ℕ)) (f : List ℕ → List Edge)
    (hf : ∀ c ∈ cs, (f c).Nodup) (e : Edge) :
    load (cs.map f) e = (cs.filter fun c => e ∈ f c).length := by
  induction cs with
  | nil => simp [load]
  | cons c cs ih =>
    have ih' := ih (fun c' hc' => hf c' (List.mem_cons_of_mem _ hc'))
    simp only [load, List.map_cons, List.sum_cons] at ih' ⊢
    rw [ih', List.filter_cons]
    by_cases he : e ∈ f c
    · rw [List.count_eq_one_of_mem (hf c (by simp)) he]
      simp [he]; omega
    · rw [List.count_eq_zero_of_not_mem he]
      simp [he]

/-- The cost of a family assignment of the convex cycles, as a sum over the edges. -/
theorem cost_family (hP : IsPolygon g n) (choose : List ℕ → ℕ) :
    cost ((convexList g n k).map fun c => selectedAt c (choose c)) =
      ∑ e ∈ polyEdges g n, pairCount
        (((convexList g n k).filter fun c => e ∈ selectedAt c (choose c)).length) := by
  have hcyc : ∀ c ∈ convexList g n k, IsCycle g k c := by
    intro c hc
    obtain ⟨h1, h2⟩ := hP.mem_convexList.mp hc
    have := h1.isCycle; rwa [h2] at this
  have hnd : ∀ p ∈ (convexList g n k).map (fun c => selectedAt c (choose c)), p.Nodup := by
    intro p hp
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hp
    exact selectedAt_nodup (hcyc c hc) _
  have hsub : ∀ p ∈ (convexList g n k).map (fun c => selectedAt c (choose c)),
      ∀ e ∈ p, e ∈ (polyEdges g n).toList := by
    intro p hp e he
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hp
    rw [Finset.mem_toList, hP.mem_polyEdges]
    have hce := (selectedAt_mem.mp he).1
    have hg := (hcyc c hc).2.2.2 e hce
    have hne := (hcyc c hc).edge_endpoints_ne hce
    have hnorm := pathEdges_normalized _ e hce
    refine ⟨⟨hne, by rw [hnorm]; exact hg⟩, ?_⟩
    have : e.1 ≤ e.2 := by
      rw [← hnorm]; simp only [edge]; omega
    omega
  rw [cost_eq_load_sum _ _ (Finset.nodup_toList _) hnd hsub, Finset.sum_map_toList]
  apply Finset.sum_congr rfl
  intro e _
  rw [load_map_eq_length _ _ (fun c hc => selectedAt_nodup (hcyc c hc) _)]

/-- The convex `k`-cycles form a complete family of the `k`-cycles of `g`: cycles, with
pairwise different edge sets, one for each `k`-cycle. -/
theorem convexList_complete (hP : IsPolygon g n) :
    (∀ c ∈ convexList g n k, IsCycle g k c) ∧
    (convexList g n k).Pairwise (fun c d => ¬ SameCycle c d) ∧
    (∀ c, IsCycle g k c → ∃ d ∈ convexList g n k, SameCycle c d) := by
  refine ⟨?_, ?_, ?_⟩
  · intro c hc
    obtain ⟨h1, h2⟩ := hP.mem_convexList.mp hc
    have := h1.isCycle; rwa [h2] at this
  · refine (convexList_nodup (g := g) (n := n) (k := k)).imp_of_mem ?_
    intro a b ha hb hab hs
    exact hab ((hP.mem_convexList.mp ha).1.eq_of_sameCycle (hP.mem_convexList.mp hb).1 hs)
  · intro c hc
    obtain ⟨h1, h2, h3⟩ := hP.convex_of_isCycle hc
    exact ⟨_, hP.mem_convexList.mpr ⟨h1, h2⟩, h3⟩

theorem hasAssignment_iff_family (hP : IsPolygon g n) (B : ℕ) :
    HasAssignment g k B ↔ FamilyAssignment (convexList g n k) B :=
  have h := hP.convexList_complete (k := k)
  hasAssignment_iff_complete_family h.1 h.2.1 h.2.2

open Classical in
/-- The omitted vertices of the values `γ`. -/
noncomputable def chooseOf (γ : CycVar g n k → Fin k) (c : List ℕ) : ℕ :=
  if h : c ∈ convexCycles g n k then omitted c (γ ⟨c, h⟩) else 0

theorem chooseOf_mem (hP : IsPolygon g n) (γ : CycVar g n k → Fin k) {c : List ℕ}
    (hc : c ∈ convexList g n k) : chooseOf γ c ∈ c := by
  have hc' : c ∈ convexCycles g n k := List.mem_toFinset.mpr hc
  have hl := (hP.mem_convexList.mp hc).2
  simp only [chooseOf, hc', dite_true, omitted]
  have hj : (γ ⟨c, hc'⟩).1 < c.length := by rw [hl]; exact (γ _).2
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
  exact List.getElem_mem hj

theorem card_filter_cycVar (p : List ℕ → Prop) [DecidablePred p] :
    (Finset.univ.filter fun x : CycVar g n k => p x.1).card =
      ((convexList g n k).filter fun c => decide (p c)).length := by
  have h1 : (Finset.univ.filter fun x : CycVar g n k => p x.1).map
      (Function.Embedding.subtype _) = (convexCycles g n k).filter p := by
    ext c
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Function.Embedding.subtype_apply]
    constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨x.2, hx⟩
    · rintro ⟨hc, hp⟩; exact ⟨⟨c, hc⟩, hp, rfl⟩
  rw [← Finset.card_map (Function.Embedding.subtype _), h1, convexCycles]
  have := List.toFinset_filter (convexList g n k) (fun c => decide (p c))
  simp only [decide_eq_true_eq] at this
  rw [← this, List.toFinset_card_of_nodup (convexList_nodup.filter _)]

theorem total_eq (hP : IsPolygon g n) (hk : 3 ≤ k) (γ : CycVar g n k → Fin k) :
    (polygonProblem hP hk).total γ =
      cost ((convexList g n k).map fun c => selectedAt c (chooseOf γ c)) := by
  rw [hP.cost_family]
  unfold TreeDP.Problem.total
  apply Finset.sum_congr rfl
  intro e _
  simp only [polygonProblem, cycLoad]
  congr 1
  have : (Finset.univ.filter fun x : CycVar g n k => e ∈ selectedAt x.1 (omitted x.1 (γ x))) =
      Finset.univ.filter fun x : CycVar g n k => e ∈ selectedAt x.1 (chooseOf γ x.1) := by
    congr 1
    funext x
    simp only [chooseOf, x.2, dite_true]
  rw [this]
  exact card_filter_cycVar (fun c => e ∈ selectedAt c (chooseOf γ c))

/-- **Lemma 34** (Appendix F): the dynamic program over the weak dual, evaluated at the
root, is the optimum `C*` of `CPAP(g, k)` on a polygon `g` with non-crossing chords. -/
theorem dp_root_optimal (hP : IsPolygon g n) (hk : 3 ≤ k) [NeZero k] (α : CycVar g n k → Fin k) :
    IsMinCost g k ((polygonProblem hP hk).dp (root hP) α) := by
  have hroot := (polygonProblem hP hk).dp_root (r := root hP) (fun x => hP.mem_sub_root _)
    (fun f _ => hP.mem_sub_root _) α
  rw [hroot]
  constructor
  · obtain ⟨γ, -, hγ⟩ := Finset.exists_mem_eq_inf' (s := (Finset.univ : Finset (CycVar g n k → Fin k)))
      Finset.univ_nonempty (polygonProblem hP hk).total
    rw [hγ, hP.hasAssignment_iff_family]
    exact ⟨chooseOf γ, fun c hc => hP.chooseOf_mem γ hc, by rw [hP.total_eq hk]⟩
  · intro B hB
    rw [hP.hasAssignment_iff_family] at hB
    obtain ⟨choose, hch, hcost⟩ := hB
    have hidx : ∀ x : CycVar g n k, (x.1.idxOf (choose x.1)) < k := by
      intro x
      have hx := List.mem_toFinset.mp x.2
      have hl := (hP.mem_convexList.mp hx).2
      have := List.idxOf_lt_length_iff.mpr (hch _ hx)
      omega
    let γ : CycVar g n k → Fin k := fun x => ⟨x.1.idxOf (choose x.1), hidx x⟩
    have hγ : ∀ c ∈ convexList g n k, chooseOf γ c = choose c := by
      intro c hc
      have hc' : c ∈ convexCycles g n k := List.mem_toFinset.mpr hc
      have hlt : c.idxOf (choose c) < c.length := List.idxOf_lt_length_iff.mpr (hch c hc)
      simp only [chooseOf, hc', dite_true, omitted, γ]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some,
        List.getElem_idxOf]
    refine le_trans (Finset.inf'_le _ (Finset.mem_univ γ)) ?_
    rw [hP.total_eq hk]
    refine le_of_eq_of_le ?_ hcost
    congr 1
    apply List.map_congr_left
    intro c hc
    rw [hγ c hc]

/-- **Lemma 34** (every table entry): `DP[v, α]` is the least cost of the edges owned in
the subtree of `v`, over the values of the cycles whose top is in the subtree, the other
cycles taking their values from `α`. -/
theorem dp_table_correct (hP : IsPolygon g n) (hk : 3 ≤ k) [NeZero k] (v : Seg g n)
    (α : CycVar g n k → Fin k) :
    (polygonProblem hP hk).dp v α = (Finset.univ : Finset (CycVar g n k → Fin k)).inf'
      Finset.univ_nonempty fun γ => (polygonProblem hP hk).tot v ((polygonProblem hP hk).ext v α γ) :=
  (polygonProblem hP hk).dp_eq_min v α

end IsPolygon

end STACS2027

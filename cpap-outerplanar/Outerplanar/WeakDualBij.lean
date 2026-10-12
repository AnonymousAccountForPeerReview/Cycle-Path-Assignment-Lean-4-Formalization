module

public import Outerplanar.WeakDual
import Outerplanar.Algo.PolyPool
import Mathlib.Tactic

/-!
# Lemma 29: the boundary map is a bijection between subtrees and cycles

Appendix F, Lemma 29 (`lem:cycle_subtree_map`): the map `ψ(S) = ∂S` is a bijection between
the nonempty subtrees `S` of the weak dual and the simple cycles of `g`, and
`|ψ(S)| = ∑_{f ∈ S} d_f - 2 (|S| - 1)`. In the polygon model (`IsPolygon g n`), the simple
cycles are, up to their edge sets, the convex cycles (`convex_of_isCycle`,
`ConvexCycle.eq_of_sameCycle`), and the inverse of `ψ` is `encl`: a convex cycle `u` encloses
the faces all of whose vertices lie on `u`.

* `mem_encl_iff`: for a convex cycle `u` with top segment `(a, b)` (its first and last entry), a
  segment `s` is enclosed exactly when it lies within `(a, b)` and `u` has an entry strictly
  between the ends of `s` (edges do not cross, `Poly.ends_mem_of_inside_outside`);
* `isRooted_encl`: the enclosed faces form a subtree rooted at the top;
* `bdry_encl`: `∂(encl u)` is the edge set of `u`: an edge of `g` lies on an odd number of the
  enclosed faces exactly when it is an edge of `u`;
* `exists_rpath_of_rooted`: conversely every subtree `S` is `encl u` for a convex cycle `u`
  with `|u| = ∑_{f ∈ S} d_f - 2 (|S| - 1)` (the paper's induction removing a leaf `ℓ` of `S`:
  the face boundary of `ℓ` is spliced into the cycle of `S \ {ℓ}` in place of the chord `ℓ`);
* `cycle_subtree_bij`, `cycle_subtree_bij_simpleCycles`: the bijection.
-/

@[expose] public section

namespace STACS2027

open IsPolygon

variable {g : Graph} {n : ℕ}

theorem mem_encl {u : List ℕ} {s : ℕ × ℕ} :
    s ∈ encl g n u ↔ s ∈ segs g n ∧ ∀ x ∈ faceVerts g n s, x ∈ u := by
  simp [encl]

theorem encl_subset {u : List ℕ} : encl g n u ⊆ segs g n := Finset.filter_subset _ _

/-- Consecutive entries of a region path are increasing and adjacent. -/
theorem IsRPath.adj_of_infix {a b : ℕ} {u : List ℕ} (hu : IsRPath g a b u) {x y : ℕ}
    (h : [x, y] <:+: u) : x < y ∧ Adj g x y := by
  obtain ⟨l₁, l₂, rfl⟩ := h
  have := hu.2.2
  simp only [List.append_assoc, List.cons_append, List.nil_append] at this
  exact (List.isChain_append_cons_cons.mp this).2.1

/-- **Splicing**: replacing two consecutive entries `x, y` of a region path by a region path
from `x` to `y` gives a region path. -/
theorem IsRPath.splice {a b x y : ℕ} {A B q : List ℕ} (h : IsRPath g a b (A ++ [x, y] ++ B))
    (hq : IsRPath g x y q) : IsRPath g a b (A ++ q ++ B) := by
  obtain ⟨q₁, rfl⟩ := List.head?_eq_some_iff.mp hq.1
  obtain ⟨q₂, hq₂⟩ := List.getLast?_eq_some_iff.mp hq.2.1
  refine ⟨?_, ?_, ?_⟩
  · have := h.1
    cases A with
    | nil => simpa using this
    | cons c A => simpa using this
  · have := h.2.1
    rcases List.eq_nil_or_concat B with rfl | ⟨B', c, rfl⟩
    · rw [show A ++ (x :: q₁) ++ [] = (A ++ q₂) ++ [y] by rw [hq₂]; simp]
      simp only [List.append_nil, List.getLast?_append, List.getLast?_cons_cons,
        List.getLast?_singleton, Option.some_or] at this ⊢
      exact this
    · simp only [List.concat_eq_append, ← List.append_assoc, List.getLast?_append,
        List.getLast?_singleton, Option.some_or] at this ⊢
      exact this
  · have hc := h.2.2
    have e1 : A ++ [x, y] ++ B = A ++ x :: y :: B := by simp
    rw [e1, List.isChain_append_cons_cons] at hc
    have e2 : A ++ (x :: q₁) ++ B = A ++ x :: (q₁ ++ B) := by simp
    rw [e2, List.isChain_split]
    refine ⟨hc.1, ?_⟩
    have e3 : x :: (q₁ ++ B) = q₂ ++ y :: B := by
      rw [← List.cons_append, hq₂]; simp
    rw [e3, List.isChain_split, ← hq₂]
    exact ⟨hq.2.2, hc.2.2⟩

/-- In a two-element set, an odd number of entries satisfy `P` exactly when one does. -/
theorem odd_card_filter_pair {α : Type*} [DecidableEq α] {x y : α} (hxy : x ≠ y)
    (P : α → Prop) [DecidablePred P] :
    Odd (({x, y} : Finset α).filter P).card ↔ (P x ↔ ¬ P y) := by
  rw [Finset.filter_insert, Finset.filter_singleton]
  by_cases hx : P x <;> by_cases hy : P y <;> simp [hx, hy, hxy]

namespace IsPolygon

/-! ### The faces enclosed by a convex cycle -/

/-- A segment whose ends lie on a region path `u`, with an entry of `u` strictly between
them, is enclosed by `u`. -/
theorem mem_encl_of_ends (hP : IsPolygon g n) {a b : ℕ} {u : List ℕ} (hu : IsRPath g a b u)
    {s : ℕ × ℕ} (hs : s ∈ segs g n) (h1 : s.1 ∈ u) (h2 : s.2 ∈ u) {z : ℕ} (hz : z ∈ u)
    (hz1 : s.1 < z) (hz2 : z < s.2) : s ∈ encl g n u := by
  refine mem_encl.mpr ⟨hs, fun x hx => ?_⟩
  by_contra hxu
  have hx' := mem_faceVerts.mp hx
  have hx1 : x ≠ s.1 := fun h => hxu (h ▸ h1)
  have hx2 : x ≠ s.2 := fun h => hxu (h ▸ h2)
  have hb1 := hu.bounds h1
  have hb2 := hu.bounds h2
  obtain ⟨c, d, hcd, hc, hd, hside⟩ := Poly.straddle_gap hu (by omega) (by omega) hxu
  have hs1 := hside _ h1
  have hs2 := hside _ h2
  have hzz := hside _ hz
  have hseg : (c, d) ∈ segs g n := hP.mem_segs.mpr ⟨hcd, by simp only; omega⟩
  have hne : (c, d) ≠ s := by
    intro h
    rw [← h] at hz1 hz2
    simp only at hz1 hz2
    omega
  exact hx'.2.2 (c, d) hseg ⟨by simp only; omega, by simp only; omega⟩ hne
    ⟨by simp only; omega, by simp only; omega⟩

/-- **The faces enclosed by a convex cycle**: for a convex cycle `u` with top segment `(a, b)`
(a region path from `a` to `b` closed by the edge `(a, b)`), a segment `s` is enclosed exactly
when it lies within `(a, b)` and `u` has an entry strictly between its ends. -/
theorem mem_encl_iff (hP : IsPolygon g n) {a b : ℕ} {u : List ℕ} (hu : IsRPath g a b u)
    (hab : Adj g a b) {s : ℕ × ℕ} (hs : s ∈ segs g n) :
    s ∈ encl g n u ↔ Within s (a, b) ∧ ∃ z ∈ u, s.1 < z ∧ z < s.2 := by
  have hs' := hP.mem_segs.mp hs
  constructor
  · intro h
    have h' := (mem_encl.mp h).2
    have h1 := hu.bounds (h' _ (left_mem_faceVerts (by omega)))
    have h2 := hu.bounds (h' _ (right_mem_faceVerts (by omega)))
    obtain ⟨z, hz, hz1, hz2⟩ := hP.exists_inner_faceVert hs
    exact ⟨⟨h1.1, h2.2⟩, z, h' z hz, hz1, hz2⟩
  · rintro ⟨hw, z, hz, hz1, hz2⟩
    simp only [Within] at hw
    have hends : s.1 ∈ u ∧ s.2 ∈ u := by
      by_cases h1 : a < s.1
      · exact Poly.ends_mem_of_inside_outside hP hu hab hs'.1 hz hz1 hz2 hu.head_mem (Or.inl h1)
      · by_cases h2 : s.2 < b
        · exact Poly.ends_mem_of_inside_outside hP hu hab hs'.1 hz hz1 hz2 hu.last_mem
            (Or.inr h2)
        · have e1 : s.1 = a := by omega
          have e2 : s.2 = b := by omega
          rw [e1, e2]
          exact ⟨hu.head_mem, hu.last_mem⟩
    exact hP.mem_encl_of_ends hu hs hends.1 hends.2 hz hz1 hz2

/-- A convex cycle encloses its top segment. -/
theorem top_mem_encl (hP : IsPolygon g n) {a b : ℕ} {u : List ℕ} (hu : IsRPath g a b u)
    (hab : Adj g a b) (hl : 3 ≤ u.length) : (a, b) ∈ segs g n ∧ (a, b) ∈ encl g n u := by
  obtain ⟨z, hz, hz1, hz2⟩ := hu.exists_inner hl
  have hseg : (a, b) ∈ segs g n := hP.mem_segs.mpr ⟨hab, by simp only; omega⟩
  exact ⟨hseg, (hP.mem_encl_iff hu hab hseg).mpr ⟨Within.refl _, z, hz, hz1, hz2⟩⟩

/-- The parent of an enclosed face other than the top is enclosed. -/
theorem encl_parent (hP : IsPolygon g n) {a b : ℕ} {u : List ℕ} (hu : IsRPath g a b u)
    (hab : Adj g a b) {s p : ℕ × ℕ} (hs : s ∈ encl g n u) (hne : s ≠ (a, b))
    (hp : p ∈ segs g n) (hc : IsChild g n p s) : p ∈ encl g n u := by
  have hsseg := encl_subset hs
  obtain ⟨hw, z, hz, hz1, hz2⟩ := (hP.mem_encl_iff hu hab hsseg).mp hs
  have hs2 := (hP.mem_segs.mp hsseg).2
  have habseg : (a, b) ∈ segs g n :=
    hP.mem_segs.mpr ⟨hab, by simp only [Within] at hw; simp only; omega⟩
  have hpw := hP.parent_within hsseg hp habseg hc hw hne
  have hsp := hc.2.1
  simp only [Within] at hsp
  exact (hP.mem_encl_iff hu hab hp).mpr ⟨hpw, z, hz, by omega, by omega⟩

/-- **The enclosed faces form a subtree**, rooted at the top segment. -/
theorem isRooted_encl (hP : IsPolygon g n) {a b : ℕ} {u : List ℕ} (hu : IsRPath g a b u)
    (hab : Adj g a b) (hl : 3 ≤ u.length) : IsRooted g n (encl g n u) (a, b) := by
  obtain ⟨hseg, htop⟩ := hP.top_mem_encl hu hab hl
  refine ⟨htop, encl_subset, fun s hs hne => ?_⟩
  have hsseg := encl_subset hs
  have hr : s ≠ (0, n - 1) := by
    intro h
    have hw := ((hP.mem_encl_iff hu hab hsseg).mp hs).1
    rw [h] at hw
    exact hne (h.trans (Within.antisymm hw (hP.within_root hseg)))
  obtain ⟨p, hp, hc⟩ := hP.exists_parent hsseg hr
  exact ⟨p, hP.encl_parent hu hab hs hne hp hc, hc⟩

/-- A convex cycle is a region path of its top segment, an edge. -/
theorem exists_top (hP : IsPolygon g n) {u : List ℕ} (hc : ConvexCycle g u) :
    ∃ a b, IsRPath g a b u ∧ Adj g a b ∧ 3 ≤ u.length := by
  have hu : u ≠ [] := by rintro rfl; have := hc.2.1; simp at this
  exact ⟨_, _, Poly.isRPath_of_convexCycle hP hc hu,
    (hP.mem_segs.mp (hP.top_mem_segs hc hu)).1, hc.2.1⟩

/-! ### The boundary of the enclosed faces -/

/-- **An edge lies on an odd number of the enclosed faces exactly when it is an edge of the
cycle.** -/
theorem mem_cycleEdges_iff_odd (hP : IsPolygon g n) {a b : ℕ} {u : List ℕ}
    (hu : IsRPath g a b u) (hab : Adj g a b) (hl : 3 ≤ u.length) (e : ℕ × ℕ) :
    e ∈ cycleEdges u ↔ Odd ((encl g n u).filter fun s => e ∈ faceEdges g n s).card := by
  obtain ⟨mid, hmid⟩ := hu.eq_cons_snoc (by omega)
  have hpw := hu.pairwise
  have hce : e ∈ cycleEdges u ↔ e = (a, b) ∨ [e.1, e.2] <:+: u := by
    rw [hmid, mem_cycleEdges_of_pairwise (hmid ▸ hpw), ← hmid]
    constructor
    · rintro (h | ⟨x, y, hi, rfl⟩)
      · exact Or.inl h
      · exact Or.inr hi
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr ⟨e.1, e.2, h, rfl⟩
  obtain ⟨hseg, htop⟩ := hP.top_mem_encl hu hab hl
  have hseg' := hP.mem_segs.mp hseg
  obtain ⟨z₀, hz₀, hz₀1, hz₀2⟩ := hu.exists_inner hl
  rw [hce]
  by_cases hE : Adj g e.1 e.2 ∧ e.1 < e.2
  swap
  · -- not an edge: on no face, and not on `u`
    have h0 : (encl g n u).filter (fun s => e ∈ faceEdges g n s) = ∅ := by
      ext s
      simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
      intro hs he
      exact hE (hP.adj_of_mem_faceEdges (encl_subset hs) he)
    rw [h0]
    simp only [Finset.card_empty, Nat.not_odd_zero, iff_false, not_or]
    refine ⟨fun h => hE (h ▸ ⟨hab, by simp only; omega⟩), fun h => hE ?_⟩
    obtain ⟨h1, h2⟩ := hu.adj_of_infix h
    exact ⟨h2, h1⟩
  obtain ⟨hadj, hlt⟩ := hE
  by_cases hside : e.2 = e.1 + 1
  · -- a side: on the face of the smallest segment containing it
    obtain ⟨e1, e2⟩ := e
    simp only at hside hadj hlt
    subst hside
    obtain ⟨o, ho, hoW, homin⟩ := hP.exists_own (e := (e1, e1 + 1)) hadj hlt
    have hF : (encl g n u).filter (fun s => (e1, e1 + 1) ∈ faceEdges g n s) =
        if o ∈ encl g n u then {o} else ∅ := by
      ext s
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hs, he⟩
        have hs' := encl_subset hs
        have h' := (hP.faces_of_side hs').mp he
        have hso : s = o := Within.antisymm (h'.2 o ho hoW) (homin s hs' h'.1)
        subst hso
        simp [hs]
      · intro h
        split_ifs at h with hoe
        · rw [Finset.mem_singleton] at h
          subst h
          exact ⟨hoe, (hP.faces_of_side ho).mpr ⟨hoW, homin⟩⟩
        · simp at h
    have hodd : Odd ((encl g n u).filter (fun s => (e1, e1 + 1) ∈ faceEdges g n s)).card ↔
        o ∈ encl g n u := by
      rw [hF]
      split_ifs with h <;> simp [h]
    rw [hodd]
    have ho2 := (hP.mem_segs.mp ho).2
    simp only [Within] at hoW
    constructor
    · rintro (h | h)
      · simp only [Prod.mk.injEq] at h
        omega
      · obtain ⟨h1, h2, -, -⟩ := (infix_pair_iff hpw).mp h
        have hb1 := hu.bounds h1
        have hb2 := hu.bounds h2
        apply (hP.mem_encl_iff hu hab ho).mpr
        refine ⟨homin (a, b) hseg ⟨hb1.1, hb2.2⟩, ?_⟩
        by_cases hc : o.1 < e1
        · exact ⟨e1, h1, hc, by omega⟩
        · exact ⟨e1 + 1, h2, by omega, by omega⟩
    · intro hoe
      right
      have hsub := (mem_encl.mp hoe).2
      have hi := (hP.side_infix_iff ho).mpr ⟨hoW, homin⟩
      obtain ⟨hx, hy, -, -⟩ := (infix_pair_iff faceVerts_pairwise).mp hi
      exact (infix_pair_iff hpw).mpr ⟨hsub _ hx, hsub _ hy, by omega, fun z _ hz => by omega⟩
  · have hes : e ∈ segs g n := hP.mem_segs.mpr ⟨hadj, by omega⟩
    have hbn := (hP.lt_of_adj hab).2
    by_cases hroot : e = (0, n - 1)
    · -- the root: on the root face only
      have hF : (encl g n u).filter (fun s => e ∈ faceEdges g n s) =
          if e ∈ encl g n u then {e} else ∅ := by
        ext s
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨hs, he⟩
          rcases (hP.faces_of_seg hes (encl_subset hs)).mp he with h | h
          · subst h
            simp [hs]
          · rw [hroot] at h
            exact absurd h (hP.not_isChild_root (encl_subset hs))
        · intro h
          split_ifs at h with hee
          · rw [Finset.mem_singleton] at h
            subst h
            exact ⟨hee, (hP.faces_of_seg hes hes).mpr (Or.inl rfl)⟩
          · simp at h
      have hodd : Odd ((encl g n u).filter (fun s => e ∈ faceEdges g n s)).card ↔
          e ∈ encl g n u := by
        rw [hF]
        split_ifs with h <;> simp [h]
      rw [hodd, hP.mem_encl_iff hu hab hes]
      subst hroot
      simp only [Within]
      constructor
      · intro h
        have hab' : a = 0 ∧ b = n - 1 := by
          rcases h with h | h
          · simp only [Prod.mk.injEq] at h
            omega
          · obtain ⟨h1, h2, -, -⟩ := (infix_pair_iff hpw).mp h
            have := hu.bounds h1
            have := hu.bounds h2
            omega
        exact ⟨⟨by omega, by omega⟩, z₀, hz₀, by omega, by omega⟩
      · rintro ⟨hw, -⟩
        left
        simp only [Prod.mk.injEq]
        omega
    · -- a chord: on its own face and on its parent's
      obtain ⟨p, hp, hc⟩ := hP.exists_parent hes hroot
      have hpe : e ≠ p := hc.1
      have hF : (encl g n u).filter (fun s => e ∈ faceEdges g n s) =
          ({e, p} : Finset (ℕ × ℕ)).filter (· ∈ encl g n u) := by
        ext s
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨hs, he⟩
          rcases (hP.faces_of_seg hes (encl_subset hs)).mp he with h | h
          · exact ⟨Or.inl h, hs⟩
          · exact ⟨Or.inr (hP.parent_unique hes (encl_subset hs) hp h hc), hs⟩
        · rintro ⟨h | h, hs⟩
          · exact ⟨hs, (hP.faces_of_seg hes (encl_subset hs)).mpr (Or.inl h)⟩
          · subst h
            exact ⟨hs, (hP.faces_of_seg hes hp).mpr (Or.inr hc)⟩
      rw [hF, odd_card_filter_pair hpe]
      have hep := hc.2.1
      have hp2 := (hP.mem_segs.mp hp).2
      have hes2 := (hP.mem_segs.mp hes).2
      simp only [Within] at hep
      have hpz : ∃ z, (z = e.1 ∨ z = e.2) ∧ p.1 < z ∧ z < p.2 := by
        by_cases h : p.1 < e.1
        · exact ⟨e.1, Or.inl rfl, h, by omega⟩
        · have : e.2 < p.2 := by
            by_contra h'
            exact hpe (Prod.ext (by omega) (by omega))
          exact ⟨e.2, Or.inr rfl, by omega, this⟩
      by_cases hee : e ∈ encl g n u
      · by_cases heab : e = (a, b)
        · have hpn : p ∉ encl g n u := by
            intro hpe'
            have hw := ((hP.mem_encl_iff hu hab hp).mp hpe').1
            rw [← heab] at hw
            exact hpe (Within.antisymm hc.2.1 hw)
          exact ⟨fun _ => ⟨fun _ => hpn, fun _ => hee⟩, fun _ => Or.inl heab⟩
        · have hpin := hP.encl_parent hu hab hee heab hp hc
          refine ⟨?_, fun h => absurd hpin (h.mp hee)⟩
          rintro (h | hi)
          · exact absurd h heab
          · exfalso
            obtain ⟨-, -, -, hgap⟩ := (infix_pair_iff hpw).mp hi
            obtain ⟨-, z, hz, hz1, hz2⟩ := (hP.mem_encl_iff hu hab hes).mp hee
            exact hgap z hz ⟨hz1, hz2⟩
      · have heab : e ≠ (a, b) := fun h => hee (by rw [h]; exact htop)
        have key : [e.1, e.2] <:+: u ↔ p ∈ encl g n u := by
          constructor
          · intro hi
            obtain ⟨h1, h2, -, -⟩ := (infix_pair_iff hpw).mp hi
            have hb1 := hu.bounds h1
            have hb2 := hu.bounds h2
            have hpw' := hP.parent_within hes hp hseg hc ⟨hb1.1, hb2.2⟩ heab
            obtain ⟨z, hz, hz1, hz2⟩ := hpz
            refine (hP.mem_encl_iff hu hab hp).mpr ⟨hpw', z, ?_, hz1, hz2⟩
            rcases hz with rfl | rfl
            · exact h1
            · exact h2
          · intro hpin
            have hsub := (mem_encl.mp hpin).2
            obtain ⟨h1, h2, -, -⟩ :=
              (infix_pair_iff faceVerts_pairwise).mp (hP.infix_faceVerts_of_child hes hc)
            have h1u := hsub _ h1
            have h2u := hsub _ h2
            have hb1 := hu.bounds h1u
            have hb2 := hu.bounds h2u
            refine (infix_pair_iff hpw).mpr ⟨h1u, h2u, hlt, fun z hz hz' => hee ?_⟩
            exact (hP.mem_encl_iff hu hab hes).mpr ⟨⟨hb1.1, hb2.2⟩, z, hz, hz'.1, hz'.2⟩
        constructor
        · rintro (h | h)
          · exact absurd h heab
          · exact ⟨fun h' => absurd h' hee, fun h' => absurd (key.mp h) h'⟩
        · intro h
          right
          apply key.mpr
          by_contra hpn
          exact hee (h.mpr hpn)

/-- **The boundary of the enclosed faces is the cycle**: `∂(encl u)` is the edge set of the
convex cycle `u`. -/
theorem bdry_encl (hP : IsPolygon g n) {u : List ℕ} (hc : ConvexCycle g u) :
    bdry g n (encl g n u) = (cycleEdges u).toFinset := by
  obtain ⟨a, b, hu, hab, hl⟩ := hP.exists_top hc
  ext e
  rw [mem_bdry, List.mem_toFinset, hP.mem_cycleEdges_iff_odd hu hab hl]

/-- The enclosed faces of a convex cycle form a subtree of the weak dual. -/
theorem isSubtree_encl (hP : IsPolygon g n) {u : List ℕ} (hc : ConvexCycle g u) :
    IsSubtree g n (encl g n u) := by
  obtain ⟨a, b, hu, hab, hl⟩ := hP.exists_top hc
  exact (hP.isSubtree_iff).mpr ⟨_, hP.isRooted_encl hu hab hl⟩

/-! ### Every subtree is enclosed by a cycle -/

/-- **Every subtree is enclosed by a cycle** (the well-definedness part of Lemma 29, by
induction on `|S|`, removing a leaf `ℓ` of `S`): a subtree `S` rooted at `r` with `m + 1`
nodes is the set of faces enclosed by a region path `u` of `r` (a convex cycle with top `r`)
with `|u| + 2 m = ∑_{f ∈ S} d_f`. -/
theorem exists_rpath_of_rooted (hP : IsPolygon g n) : ∀ (m : ℕ) (S : Finset (ℕ × ℕ))
    (r : ℕ × ℕ), IsRooted g n S r → S.card = m + 1 →
      ∃ u, IsRPath g r.1 r.2 u ∧ 3 ≤ u.length ∧ encl g n u = S ∧
        u.length + 2 * m = ∑ s ∈ S, (faceVerts g n s).length
  | 0, S, r, hS, hc => by
    obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hc
    have hSr : S = {r} := by
      have := hS.1
      rw [hx, Finset.mem_singleton] at this
      rw [hx, this]
    subst hSr
    have hr := hS.2.1 (Finset.mem_singleton_self r)
    have hu := hP.faceVerts_isRPath hr
    have hradj := (hP.mem_segs.mp hr).1
    refine ⟨faceVerts g n r, hu, hP.three_le_length_faceVerts hr, ?_, by simp⟩
    ext s
    rw [Finset.mem_singleton]
    constructor
    · intro hs
      have hsseg := encl_subset hs
      obtain ⟨hw, z, hz, hz1, hz2⟩ := (hP.mem_encl_iff hu hradj hsseg).mp hs
      by_contra hne
      exact (mem_faceVerts.mp hz).2.2 s hsseg hw hne ⟨hz1, hz2⟩
    · rintro rfl
      obtain ⟨z, hz, hz1, hz2⟩ := hP.exists_inner_faceVert hr
      exact (hP.mem_encl_iff hu hradj hr).mpr ⟨Within.refl _, z, hz, hz1, hz2⟩
  | m + 1, S, r, hS, hc => by
    have hne : S.Nonempty := ⟨r, hS.1⟩
    obtain ⟨l, hl, hmin⟩ := S.exists_min_image segSize hne
    -- `l` is a leaf of `S` other than the root
    have hlr : l ≠ r := by
      rintro rfl
      have : S = {l} := by
        ext s
        rw [Finset.mem_singleton]
        constructor
        · intro hs
          have hw := hP.rooted_within hS hs
          have h1 := hmin s hs
          have := (hP.mem_segs.mp (hS.2.1 hs)).2
          simp only [segSize] at h1
          simp only [Within] at hw
          exact Prod.ext (by omega) (by omega)
        · rintro rfl
          exact hl
      rw [this] at hc
      simp at hc
    have hleaf : ∀ s ∈ S, ¬ IsChild g n l s := by
      intro s hs hcs
      have := hP.child_size_lt (hS.2.1 hs) hcs
      have := hmin s hs
      omega
    have hS' : IsRooted g n (S.erase l) r := by
      refine ⟨Finset.mem_erase.mpr ⟨hlr.symm, hS.1⟩, (Finset.erase_subset _ _).trans hS.2.1,
        fun s hs hsr => ?_⟩
      obtain ⟨-, hsS⟩ := Finset.mem_erase.mp hs
      obtain ⟨p, hp, hcp⟩ := hS.2.2 s hsS hsr
      have hpl : p ≠ l := fun h => hleaf s hsS (h ▸ hcp)
      exact ⟨p, Finset.mem_erase.mpr ⟨hpl, hp⟩, hcp⟩
    have hc' : (S.erase l).card = m + 1 := by
      rw [Finset.card_erase_of_mem hl, hc]
      rfl
    obtain ⟨u', hu', hl', henc', hlen'⟩ := exists_rpath_of_rooted hP m (S.erase l) r hS' hc'
    have hradj := (hP.mem_segs.mp (hS.2.1 hS.1)).1
    have hlseg := hS.2.1 hl
    have hlseg' := hP.mem_segs.mp hlseg
    -- the parent of `l` is enclosed by `u'`, so the ends of `l` lie on `u'`, consecutive
    obtain ⟨p, hp, hcp⟩ := hS.2.2 l hl hlr
    have hpl : p ≠ l := fun h => hcp.1 h.symm
    have hp' : p ∈ encl g n u' := by
      rw [henc']
      exact Finset.mem_erase.mpr ⟨hpl, hp⟩
    have hl_not : l ∉ encl g n u' := by
      rw [henc']
      simp
    obtain ⟨hl1, hl2, -, -⟩ :=
      (infix_pair_iff faceVerts_pairwise).mp (hP.infix_faceVerts_of_child hlseg hcp)
    have hl1u := (mem_encl.mp hp').2 _ hl1
    have hl2u := (mem_encl.mp hp').2 _ hl2
    have hlW : Within l r := hP.rooted_within hS hl
    have hgap : ∀ z ∈ u', ¬ (l.1 < z ∧ z < l.2) := by
      intro z hz hz'
      exact hl_not ((hP.mem_encl_iff hu' hradj hlseg).mpr ⟨hlW, z, hz, hz'.1, hz'.2⟩)
    obtain ⟨A, B, hAB⟩ := (infix_pair_iff hu'.pairwise).mpr ⟨hl1u, hl2u, by omega, hgap⟩
    subst hAB
    -- splice the face of `l` in place of the chord `l`
    have hu : IsRPath g r.1 r.2 (A ++ faceVerts g n l ++ B) :=
      hu'.splice (hP.faceVerts_isRPath hlseg)
    have hmem : ∀ z, z ∈ A ++ faceVerts g n l ++ B ↔
        z ∈ A ++ [l.1, l.2] ++ B ∨ z ∈ faceVerts g n l := by
      intro z
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
      constructor
      · rintro ((h | h) | h)
        · exact Or.inl (Or.inl (Or.inl h))
        · exact Or.inr h
        · exact Or.inl (Or.inr h)
      · rintro (((h | h | h) | h) | h)
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr (h ▸ left_mem_faceVerts (by omega)))
        · exact Or.inl (Or.inr (h ▸ right_mem_faceVerts (by omega)))
        · exact Or.inr h
        · exact Or.inl (Or.inr h)
    have hd := hP.three_le_length_faceVerts hlseg
    simp only [List.length_append, List.length_cons, List.length_nil] at hl' hlen'
    refine ⟨A ++ faceVerts g n l ++ B, hu, by simp only [List.length_append]; omega, ?_, ?_⟩
    · ext s
      by_cases hs : s ∈ segs g n
      swap
      · exact ⟨fun h => absurd (encl_subset h) hs, fun h => absurd (hS.2.1 h) hs⟩
      have hs' := hP.mem_segs.mp hs
      rw [hP.mem_encl_iff hu hradj hs]
      constructor
      · rintro ⟨hw, z, hz, hz1, hz2⟩
        have hold : z ∈ A ++ [l.1, l.2] ++ B → s ∈ S := by
          intro hz'
          have : s ∈ encl g n (A ++ [l.1, l.2] ++ B) :=
            (hP.mem_encl_iff hu' hradj hs).mpr ⟨hw, z, hz', hz1, hz2⟩
          rw [henc'] at this
          exact Finset.mem_of_mem_erase this
        rcases (hmem z).mp hz with hz' | hz'
        · exact hold hz'
        · by_cases hzu : z ∈ A ++ [l.1, l.2] ++ B
          · exact hold hzu
          · have hzl := mem_faceVerts.mp hz'
            have hz1' : l.1 < z := lt_of_le_of_ne hzl.1 (fun h => hzu (h ▸ hl1u))
            have hz2' : z < l.2 := lt_of_le_of_ne hzl.2.1 (fun h => hzu (h.symm ▸ hl2u))
            by_cases hsl : s = l
            · rw [hsl]
              exact hl
            rcases hP.laminar hs'.1 hlseg'.1 (by omega) (by omega) with w | w | w | w
            · exact absurd ⟨hz1, hz2⟩ (hzl.2.2 s hs w hsl)
            · simp only [Within] at w
              have hz'' : ∃ y ∈ A ++ [l.1, l.2] ++ B, s.1 < y ∧ y < s.2 := by
                by_cases h : s.1 < l.1
                · exact ⟨l.1, hl1u, h, by omega⟩
                · have : l.2 < s.2 := by
                    by_contra h'
                    exact hsl (Prod.ext (by omega) (by omega))
                  exact ⟨l.2, hl2u, by omega, this⟩
              obtain ⟨y, hy, hy1, hy2⟩ := hz''
              have : s ∈ encl g n (A ++ [l.1, l.2] ++ B) :=
                (hP.mem_encl_iff hu' hradj hs).mpr ⟨hw, y, hy, hy1, hy2⟩
              rw [henc'] at this
              exact Finset.mem_of_mem_erase this
            · omega
            · omega
      · intro hsS
        by_cases hsl : s = l
        · subst hsl
          obtain ⟨z, hz, hz1, hz2⟩ := hP.exists_inner_faceVert hlseg
          exact ⟨hlW, z, (hmem z).mpr (Or.inr hz), hz1, hz2⟩
        · have : s ∈ encl g n (A ++ [l.1, l.2] ++ B) := by
            rw [henc']
            exact Finset.mem_erase.mpr ⟨hsl, hsS⟩
          obtain ⟨hw, z, hz, hz1, hz2⟩ := (hP.mem_encl_iff hu' hradj hs).mp this
          exact ⟨hw, z, (hmem z).mpr (Or.inl hz), hz1, hz2⟩
    · rw [← Finset.sum_erase_add S _ hl, ← hlen']
      simp only [List.length_append]
      omega

/-- **Every subtree is enclosed by a convex cycle**, of length `∑_{f ∈ S} d_f - 2 (|S| - 1)`. -/
theorem exists_convex_of_isSubtree (hP : IsPolygon g n) {S : Finset (ℕ × ℕ)}
    (hS : IsSubtree g n S) :
    ∃ u, ConvexCycle g u ∧ encl g n u = S ∧
      u.length + 2 * (S.card - 1) = ∑ s ∈ S, (faceVerts g n s).length := by
  obtain ⟨r, hr⟩ := (hP.isSubtree_iff).mp hS
  have hcard : S.card = (S.card - 1) + 1 := by
    have := Finset.card_pos.mpr ⟨r, hr.1⟩
    omega
  obtain ⟨u, hu, hl, he, hlen⟩ := hP.exists_rpath_of_rooted _ S r hr hcard
  have hradj := (hP.mem_segs.mp (hr.2.1 hr.1)).1
  exact ⟨u, ((convexCycle_iff_isRPath hradj).mpr ⟨hu, hl⟩).1, he, hlen⟩

end IsPolygon

/-! ### The bijection -/

/-- A convex cycle has as many edges as entries. -/
theorem ConvexCycle.card_edges {u : List ℕ} (hc : ConvexCycle g u) :
    (cycleEdges u).toFinset.card = u.length := by
  rw [List.toFinset_card_of_nodup hc.isCycle.edges_nodup]
  have := hc.2.1
  simp only [cycleEdges, pathEdges_length, List.length_append, List.length_take]
  omega

/-- Two convex cycles with the same edge set are equal. -/
theorem ConvexCycle.eq_of_edges {u v : List ℕ} (hu : ConvexCycle g u) (hv : ConvexCycle g v)
    (h : (cycleEdges u).toFinset = (cycleEdges v).toFinset) : u = v := by
  refine hu.eq_of_sameCycle hv ⟨fun e he => ?_, fun e he => ?_⟩
  · rw [← List.mem_toFinset, ← h, List.mem_toFinset]
    exact he
  · rw [← List.mem_toFinset, h, List.mem_toFinset]
    exact he

namespace IsPolygon

/-- **Lemma 29** (`lem:cycle_subtree_map`), in the polygon model: the boundary map
`ψ(S) = ∂S` (`bdry`) is a bijection between the subtrees `S` of the weak dual (`IsSubtree`:
nonempty, connected sets of bounded faces) and the convex cycles (the simple cycles up to
their edge sets), with inverse `encl`, and `|ψ(S)| = ∑_{f ∈ S} d_f - 2 (|S| - 1)`:

1. every convex cycle `u` is `ψ(encl u)`, `encl u` being a subtree (surjectivity);
2. for every subtree `S`, `∂S` is the edge set of exactly one convex cycle, which encloses
   exactly the faces of `S` (well-definedness);
3. every convex cycle with edge set `∂S` encloses exactly the faces of `S`;
4. `ψ` is injective on subtrees;
5. the length formula. -/
theorem cycle_subtree_bij (hP : IsPolygon g n) :
    (∀ u, ConvexCycle g u →
      IsSubtree g n (encl g n u) ∧ bdry g n (encl g n u) = (cycleEdges u).toFinset) ∧
    (∀ S, IsSubtree g n S →
      ∃! u, ConvexCycle g u ∧ (cycleEdges u).toFinset = bdry g n S ∧ encl g n u = S) ∧
    (∀ S u, IsSubtree g n S → ConvexCycle g u → (cycleEdges u).toFinset = bdry g n S →
      encl g n u = S) ∧
    (∀ S S', IsSubtree g n S → IsSubtree g n S' → bdry g n S = bdry g n S' → S = S') ∧
    (∀ S, IsSubtree g n S →
      (bdry g n S).card = ∑ s ∈ S, (faceVerts g n s).length - 2 * (S.card - 1)) := by
  have hex : ∀ S, IsSubtree g n S → ∃ u, ConvexCycle g u ∧ encl g n u = S ∧
      (cycleEdges u).toFinset = bdry g n S ∧
      u.length + 2 * (S.card - 1) = ∑ s ∈ S, (faceVerts g n s).length := by
    intro S hS
    obtain ⟨u, hc, he, hlen⟩ := hP.exists_convex_of_isSubtree hS
    exact ⟨u, hc, he, by rw [← he, hP.bdry_encl hc], hlen⟩
  refine ⟨fun u hc => ⟨hP.isSubtree_encl hc, hP.bdry_encl hc⟩, fun S hS => ?_,
    fun S u hS hc h => ?_, fun S S' hS hS' h => ?_, fun S hS => ?_⟩
  · obtain ⟨u, hc, he, hb, -⟩ := hex S hS
    exact ⟨u, ⟨hc, hb, he⟩, fun v hv => hv.1.eq_of_edges hc (hv.2.1.trans hb.symm)⟩
  · obtain ⟨v, hv, he, hb, -⟩ := hex S hS
    rw [hc.eq_of_edges hv (h.trans hb.symm), he]
  · obtain ⟨u, hc, he, hb, -⟩ := hex S hS
    obtain ⟨u', hc', he', hb', -⟩ := hex S' hS'
    rw [← he, ← he', hc.eq_of_edges hc' (hb.trans (h.trans hb'.symm))]
  · obtain ⟨u, hc, -, hb, hlen⟩ := hex S hS
    rw [← hb, hc.card_edges]
    omega

/-- **Lemma 29 for simple cycles**: `ψ(S) = ∂S` is the edge set of a simple cycle (of length
`|∂S|`) for every subtree `S`, and the edge set of every simple cycle of `g` is `ψ(S)` for
exactly one subtree `S`. -/
theorem cycle_subtree_bij_simpleCycles (hP : IsPolygon g n) :
    (∀ S, IsSubtree g n S →
      ∃ c, IsCycle g (bdry g n S).card c ∧ (cycleEdges c).toFinset = bdry g n S) ∧
    (∀ k c, IsCycle g k c → ∃! S, IsSubtree g n S ∧ bdry g n S = (cycleEdges c).toFinset) := by
  obtain ⟨h1, h2, -, h4, -⟩ := hP.cycle_subtree_bij
  refine ⟨fun S hS => ?_, fun k c hc => ?_⟩
  · obtain ⟨u, ⟨hu, hb, -⟩, -⟩ := h2 S hS
    refine ⟨u, ?_, hb⟩
    rw [← hb, hu.card_edges]
    exact hu.isCycle
  · obtain ⟨hu, -, hsame⟩ := hP.convex_of_isCycle hc
    set u := c.insertionSort (· ≤ ·)
    have hedges : (cycleEdges u).toFinset = (cycleEdges c).toFinset := by
      ext e
      simp only [List.mem_toFinset]
      exact ⟨hsame.2 e, hsame.1 e⟩
    refine ⟨encl g n u, ⟨(h1 u hu).1, (h1 u hu).2.trans hedges⟩, fun S ⟨hS, hb⟩ => ?_⟩
    exact h4 S _ hS (h1 u hu).1 (hb.trans ((h1 u hu).2.trans hedges).symm)

end IsPolygon

end STACS2027

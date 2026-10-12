module

public import Outerplanar.Faces
import Mathlib.Tactic

/-!
# Region paths and the face decomposition (Lemma 29)

A *region path* of an edge `(a, b)`, `a < b`, of a polygon `g` is a strictly increasing list
from `a` to `b` whose consecutive entries are adjacent (`IsRPath`). Closed by the edge
`(b, a)`, the region paths with at least three entries are exactly the convex cycles with
first entry `a` and last entry `b` (`convexCycle_iff_isRPath`): the cycles whose top segment
(Appendix F: `top(c)`) is `(a, b)`.

Our form of the cycle–subtree correspondence of Appendix F, Lemma 29, is the
*decomposition* `IsPolygon.isRPath_iff_joins`: for a segment `s = (a, b)`, a region path of
`s` is either the edge `[a, b]` itself, or it visits every vertex of the face below `s`
(`faceVerts`, see `Faces`) and is the concatenation of region paths between consecutive face
vertices (`Joins`). Between the ends of a side `(x, x + 1)` the only region path is
`[x, x + 1]` (`isRPath_side_iff`); between the ends of a child segment it is again a region
path of that segment, so a cycle with top `s` corresponds to the choice of the subtree of
the weak dual it encloses, recursively, and its length is the sum of the lengths of its
pieces. In particular the boundary of a face is a convex cycle (Lemma 27,
`IsPolygon.faceVerts_convexCycle`).
-/

@[expose] public section

namespace STACS2027

open IsPolygon

/-- `p` is a *region path* from `a` to `b` in `g`: a list with first entry `a` and last
entry `b` whose consecutive entries `x, y` satisfy `x < y` and are adjacent. -/
def IsRPath (g : Graph) (a b : ℕ) (p : List ℕ) : Prop :=
  p.head? = some a ∧ p.getLast? = some b ∧ p.IsChain (fun x y => x < y ∧ Adj g x y)

variable {g : Graph} {n : ℕ}

namespace IsRPath

variable {a b : ℕ} {p : List ℕ}

/-- A region path is strictly increasing. -/
theorem pairwise (h : IsRPath g a b p) : p.Pairwise (· < ·) :=
  List.isChain_iff_pairwise.mp (h.2.2.imp fun _ _ h => h.1)

/-- A region path from `a` visits `a`. -/
theorem head_mem (h : IsRPath g a b p) : a ∈ p := List.mem_of_mem_head? h.1

/-- A region path to `b` visits `b`. -/
theorem last_mem (h : IsRPath g a b p) : b ∈ p := List.mem_of_mem_getLast? h.2.1

/-- Every entry of a region path from `a` to `b` lies in `[a, b]`. -/
theorem bounds (h : IsRPath g a b p) {z : ℕ} (hz : z ∈ p) : a ≤ z ∧ z ≤ b := by
  have hs := h.pairwise
  constructor
  · obtain ⟨t, rfl⟩ := List.head?_eq_some_iff.mp h.1
    rcases List.mem_cons.mp hz with rfl | hz
    · exact le_rfl
    · exact ((List.pairwise_cons.mp hs).1 z hz).le
  · obtain ⟨t, rfl⟩ := List.getLast?_eq_some_iff.mp h.2.1
    rcases List.mem_append.mp hz with hz | hz
    · exact ((List.pairwise_append.mp hs).2.2 z hz b (by simp)).le
    · simp only [List.mem_singleton] at hz; omega

/-- A region path between distinct ends has at least two entries. -/
theorem two_le_length (h : IsRPath g a b p) (hab : a < b) : 2 ≤ p.length := by
  match p, h with
  | [], h => simp [IsRPath] at h
  | [x], h =>
    simp only [IsRPath, List.head?_cons, List.getLast?_singleton, Option.some.injEq] at h
    omega
  | _ :: _ :: _, _ => simp

/-- The only region path from `a` to `a` is `[a]`. -/
theorem eq_singleton (h : IsRPath g a a p) : p = [a] := by
  obtain ⟨t, rfl⟩ := List.head?_eq_some_iff.mp h.1
  cases t with
  | nil => rfl
  | cons c t =>
    have h1 := (List.pairwise_cons.mp h.pairwise).1 c (by simp)
    have h2 := (h.bounds (z := c) (by simp)).2
    omega

end IsRPath

/-- The edge `[a, b]` is a region path exactly when `a < b` are adjacent. -/
theorem isRPath_pair {a b : ℕ} : IsRPath g a b [a, b] ↔ a < b ∧ Adj g a b := by
  simp [IsRPath]

/-- The only region path of a side `(a, a + 1)` is `[a, a + 1]`. -/
theorem isRPath_side_iff {a : ℕ} {p : List ℕ} :
    IsRPath g a (a + 1) p ↔ p = [a, a + 1] ∧ Adj g a (a + 1) := by
  constructor
  · intro h
    have hp : p = [a, a + 1] := by
      obtain ⟨t, rfl⟩ := List.head?_eq_some_iff.mp h.1
      cases t with
      | nil => simp [IsRPath] at h
      | cons c t =>
        have h1 := (List.pairwise_cons.mp h.pairwise).1 c (by simp)
        have h2 := (h.bounds (z := c) (by simp)).2
        obtain rfl : c = a + 1 := by omega
        cases t with
        | nil => rfl
        | cons d t =>
          have h3 := (List.pairwise_cons.mp (List.pairwise_cons.mp h.pairwise).2).1 d (by simp)
          have h4 := (h.bounds (z := d) (by simp)).2
          omega
    subst hp
    exact ⟨rfl, (isRPath_pair.mp h).2⟩
  · rintro ⟨rfl, h⟩
    exact isRPath_pair.mpr ⟨by omega, h⟩

/-- If `x` lies strictly between the first and the last entry of `p` and is not an entry,
two consecutive entries of `p` jump over it. -/
theorem exists_straddle : ∀ {p : List ℕ} {a b x : ℕ}, p.head? = some a → p.getLast? = some b →
    a < x → x < b → x ∉ p → ∃ l₁ u v l₂, p = l₁ ++ u :: v :: l₂ ∧ u < x ∧ x < v
  | [], _, _, _, h, _, _, _, _ => by simp at h
  | [_], _, _, _, h1, h2, _, _, _ => by
    simp only [List.head?_cons, List.getLast?_singleton, Option.some.injEq] at h1 h2
    omega
  | c :: d :: p, a, b, x, h1, h2, hax, hxb, hx => by
    simp only [List.head?_cons, Option.some.injEq] at h1
    subst h1
    have hdx : d ≠ x := fun h => hx (by simp [h])
    rcases Nat.lt_or_gt_of_ne hdx with hd | hd
    · obtain ⟨l₁, u, v, l₂, h, hu, hv⟩ := exists_straddle (p := d :: p) rfl
        (by simpa using h2) hd hxb (fun h => hx (List.mem_cons_of_mem _ h))
      exact ⟨c :: l₁, u, v, l₂, by rw [h]; rfl, hu, hv⟩
    · exact ⟨[], c, d, p, rfl, hax, hd⟩

/-! ### Concatenations along the face vertices -/

/-- `Joins g vs u`: `u` is the concatenation of region paths between consecutive entries of
`vs` (each junction vertex written once): for `vs = [v₀, …, v_d]`, `u = p₁ ++ … ++ p_d`
with the repeated junctions `v₁, …, v_{d-1}` dropped, `p_i` a region path from `v_{i-1}`
to `v_i`. -/
def Joins (g : Graph) : List ℕ → List ℕ → Prop
  | [], _ => False
  | [x], u => u = [x]
  | x :: y :: rest, u => ∃ p q, IsRPath g x y p ∧ Joins g (y :: rest) q ∧ u = p ++ q.tail

/-- A concatenation along `x :: rest` starts at `x`. -/
theorem Joins.head? : ∀ {x : ℕ} {rest u : List ℕ}, Joins g (x :: rest) u → u.head? = some x
  | x, [], u, h => by
    simp only [Joins] at h
    simp [h]
  | _, _ :: _, _, h => by
    obtain ⟨p, q, hp, -, rfl⟩ := h
    obtain ⟨t, rfl⟩ := List.head?_eq_some_iff.mp hp.1
    simp

/-- A concatenation of region paths along `vs` is a region path from the first to the last
entry of `vs`. -/
theorem Joins.isRPath : ∀ {vs u : List ℕ} {a b : ℕ}, Joins g vs u → vs.head? = some a →
    vs.getLast? = some b → IsRPath g a b u
  | [], _, _, _, h, _, _ => h.elim
  | [x], u, a, b, h, h1, h2 => by
    simp only [Joins] at h
    subst h
    simp only [List.head?_cons, List.getLast?_singleton, Option.some.injEq] at h1 h2
    subst h1 h2
    exact ⟨rfl, rfl, List.isChain_singleton _⟩
  | x :: y :: rest, u, a, b, h, h1, h2 => by
    obtain ⟨p, q, hp, hq, rfl⟩ := h
    simp only [List.head?_cons, Option.some.injEq] at h1
    subst h1
    have hq' : IsRPath g y b q := Joins.isRPath hq rfl (by simpa using h2)
    obtain ⟨q₀, rfl⟩ := List.head?_eq_some_iff.mp hq'.1
    obtain ⟨p₀, rfl⟩ := List.getLast?_eq_some_iff.mp hp.2.1
    have he : p₀ ++ [y] ++ (y :: q₀).tail = p₀ ++ y :: q₀ := by simp
    rw [he]
    refine ⟨?_, ?_, List.isChain_split.mpr ⟨hp.2.2, hq'.2.2⟩⟩
    · have := hp.1
      rw [List.head?_append] at this ⊢
      simpa using this
    · rw [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _)]
      exact hq'.2.1

/-- A concatenation along `vs` visits every entry of `vs`. -/
theorem Joins.mem : ∀ {vs u : List ℕ}, Joins g vs u → ∀ z ∈ vs, z ∈ u
  | [], _, h, _, _ => h.elim
  | [_], _, h, _, hz => by
    simp only [Joins] at h
    subst h
    exact hz
  | x :: y :: rest, _, h, z, hz => by
    obtain ⟨p, q, hp, hq, rfl⟩ := h
    obtain ⟨q₀, rfl⟩ := List.head?_eq_some_iff.mp hq.head?
    rcases List.mem_cons.mp hz with rfl | hz
    · exact List.mem_append_left _ hp.head_mem
    · rcases List.mem_cons.mp (Joins.mem hq z hz) with rfl | h
      · exact List.mem_append_left _ hp.last_mem
      · exact List.mem_append_right _ (by simpa using h)

/-- A concatenation along a strictly increasing `vs` has at least as many entries as `vs`. -/
theorem Joins.length_le {vs u : List ℕ} (hs : vs.Pairwise (· < ·)) (h : Joins g vs u) :
    vs.length ≤ u.length :=
  List.Nodup.length_le_of_subset (hs.imp fun h => Nat.ne_of_lt h) (fun z hz => h.mem z hz)

/-- **Slot form of `Joins`**: a concatenation along `x :: rest` is given by one region path
per slot, `qs[i]` from the `i`-th to the `(i + 1)`-th entry, joined at the shared ends. -/
theorem joins_iff_slots : ∀ {x : ℕ} {rest u : List ℕ}, Joins g (x :: rest) u ↔
    ∃ qs : List (List ℕ), qs.length = rest.length ∧
      (∀ i < qs.length,
        IsRPath g ((x :: rest).getD i 0) ((x :: rest).getD (i + 1) 0) (qs.getD i [])) ∧
      u = x :: (qs.map List.tail).flatten
  | x, [], u => by
    simp only [Joins, List.length_nil, List.length_eq_zero_iff]
    constructor
    · rintro rfl
      exact ⟨[], rfl, by simp, by simp⟩
    · rintro ⟨qs, rfl, -, rfl⟩
      simp
  | x, y :: rest, u => by
    simp only [Joins]
    constructor
    · rintro ⟨p, q, hp, hq, rfl⟩
      obtain ⟨qs, hlen, hqs, rfl⟩ := joins_iff_slots.mp hq
      obtain ⟨t, rfl⟩ := List.head?_eq_some_iff.mp hp.1
      refine ⟨(x :: t) :: qs, by simp [hlen], ?_, by simp⟩
      intro i hi
      cases i with
      | zero => simpa using hp
      | succ j => simpa using hqs j (by simpa using hi)
    · rintro ⟨qs, hlen, hqs, rfl⟩
      obtain ⟨p, qs, rfl⟩ : ∃ p qs', qs = p :: qs' := by
        cases qs with
        | nil => simp at hlen
        | cons p qs => exact ⟨p, qs, rfl⟩
      have hp : IsRPath g x y p := by simpa using hqs 0 (by simp)
      obtain ⟨t, rfl⟩ := List.head?_eq_some_iff.mp hp.1
      refine ⟨x :: t, y :: (qs.map List.tail).flatten, hp, joins_iff_slots.mpr
        ⟨qs, by simpa using hlen, fun j hj => by simpa using hqs (j + 1) (by simpa using hj),
          rfl⟩, by simp⟩

/-- **Splitting**: a region path through every entry of a strictly increasing list `vs`, from
its first to its last entry, is a concatenation of region paths along `vs`. -/
theorem joins_of_superset : ∀ {vs : List ℕ}, vs.Pairwise (· < ·) → ∀ {p : List ℕ} {a b : ℕ},
    vs.head? = some a → vs.getLast? = some b → IsRPath g a b p → (∀ z ∈ vs, z ∈ p) →
    Joins g vs p
  | [], _, _, _, _, h, _, _, _ => by simp at h
  | [x], _, _, a, b, h1, h2, hp, _ => by
    simp only [List.head?_cons, List.getLast?_singleton, Option.some.injEq] at h1 h2
    subst h1 h2
    exact hp.eq_singleton
  | x :: y :: rest, hs, p, a, b, h1, h2, hp, hall => by
    simp only [List.head?_cons, Option.some.injEq] at h1
    subst h1
    have hxy : x < y := (List.pairwise_cons.mp hs).1 y (by simp)
    obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem (hall y (by simp))
    have hl₁ : l₁ ≠ [] := by
      rintro rfl
      have := hp.1
      simp only [List.nil_append, List.head?_cons, Option.some.injEq] at this
      omega
    have hch := List.isChain_split.mp hp.2.2
    have hps := hp.pairwise
    refine ⟨l₁ ++ [y], y :: l₂, ⟨?_, by simp, hch.1⟩, ?_, by simp⟩
    · rw [List.head?_append_of_ne_nil _ hl₁]
      have := hp.1
      rwa [List.head?_append_of_ne_nil _ hl₁] at this
    · refine joins_of_superset (List.pairwise_cons.mp hs).2 rfl (by simpa using h2)
        ⟨rfl, ?_, hch.2⟩ ?_
      · have := hp.2.1
        rwa [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _)] at this
      · intro z hz
        rcases List.mem_append.mp (hall z (List.mem_cons_of_mem _ hz)) with h | h
        · exfalso
          have h1 := (List.pairwise_append.mp hps).2.2 z h y (by simp)
          have h2 : y ≤ z := by
            rcases List.mem_cons.mp hz with rfl | hz
            · exact le_rfl
            · exact ((List.pairwise_cons.mp (List.pairwise_cons.mp hs).2).1 z hz).le
          omega
        · exact h

/-! ### Convex cycles and region paths -/

/-- Consecutive entries increasing and adjacent: increasing, and the edges are edges of `g`. -/
theorem isChain_rstep_iff : ∀ {u : List ℕ},
    u.IsChain (fun x y => x < y ∧ Adj g x y) ↔
      u.IsChain (· < ·) ∧ ∀ e ∈ pathEdges u, e ∈ g
  | [] => by simp [pathEdges]
  | [_] => by simp [pathEdges]
  | x :: y :: u => by
    rw [List.isChain_cons_cons, List.isChain_cons_cons, isChain_rstep_iff]
    simp only [pathEdges, List.mem_cons, forall_eq_or_imp]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨⟨h1, h3⟩, h2.2, h4⟩
    · rintro ⟨⟨h1, h3⟩, h2, h4⟩
      exact ⟨⟨h1, by omega, h2⟩, h3, h4⟩

/-- **Cycles with top `(a, b)` are region paths** (Appendix F, `top(c)`): for an edge
`(a, b)`, the convex cycles with first entry `a` and last entry `b` are exactly the region
paths from `a` to `b` with at least three entries. -/
theorem convexCycle_iff_isRPath {a b : ℕ} (hab : Adj g a b) {u : List ℕ} :
    ConvexCycle g u ∧ u.head? = some a ∧ u.getLast? = some b ↔
      IsRPath g a b u ∧ 3 ≤ u.length := by
  constructor
  · rintro ⟨⟨hs, hl, he⟩, h1, h2⟩
    exact ⟨⟨h1, h2, isChain_rstep_iff.mpr ⟨List.isChain_iff_pairwise.mpr hs,
      fun e h => he e (pathEdges_subset_cycleEdges u e h)⟩⟩, hl⟩
  · rintro ⟨hp, hl⟩
    refine ⟨⟨hp.pairwise, hl, ?_⟩, hp.1, hp.2.1⟩
    have hform : ∃ mid, u = a :: (mid ++ [b]) := by
      obtain ⟨t, rfl⟩ := List.head?_eq_some_iff.mp hp.1
      rcases List.eq_nil_or_concat t with rfl | ⟨mid, c, rfl⟩
      · simp at hl
      · obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp hp.2.1
        have h3 : (a :: mid) ++ [c] = ys ++ [b] := by rw [← hys]; simp
        have h4 := (List.append_inj' h3 rfl).2
        simp only [List.cons.injEq, and_true] at h4
        subst h4
        exact ⟨mid, by simp⟩
    obtain ⟨mid, rfl⟩ := hform
    rw [cycleEdges_snoc]
    intro e he
    rcases List.mem_append.mp he with he | he
    · exact (isChain_rstep_iff.mp hp.2.2).2 e he
    · simp only [List.mem_singleton] at he
      subst he
      rw [edge_comm]
      exact hab.2

namespace IsPolygon

/-- **The face decomposition** (our form of Appendix F, Lemma 29): a region path of a
segment `s` is the edge `[s.1, s.2]` itself, or a concatenation of region paths between
consecutive vertices of the face below `s`. -/
theorem isRPath_iff_joins (hP : IsPolygon g n) {s : ℕ × ℕ} (hs : s ∈ segs g n)
    {p : List ℕ} :
    IsRPath g s.1 s.2 p ↔ p = [s.1, s.2] ∨ Joins g (faceVerts g n s) p := by
  have hs' := hP.mem_segs.mp hs
  have hfh := faceVerts_head? (g := g) (n := n) (s := s) (by omega)
  have hfl := faceVerts_getLast? (g := g) (n := n) (s := s) (by omega)
  constructor
  · intro hp
    by_cases hpe : p = [s.1, s.2]
    · exact Or.inl hpe
    right
    refine joins_of_superset faceVerts_pairwise hfh hfl hp ?_
    -- a region path other than the edge visits every face vertex
    intro x hx
    by_contra hxp
    have hx' := mem_faceVerts.mp hx
    have hxa : x ≠ s.1 := fun h => hxp (h ▸ hp.head_mem)
    have hxb : x ≠ s.2 := fun h => hxp (h ▸ hp.last_mem)
    obtain ⟨l₁, u, v, l₂, hsplit, hux, hxv⟩ :=
      exists_straddle hp.1 hp.2.1 (by omega) (by omega) hxp
    have hR : u < v ∧ Adj g u v := by
      have := hp.2.2
      rw [hsplit] at this
      exact (List.isChain_append_cons_cons.mp this).2.1
    have hu := hp.bounds (z := u) (by rw [hsplit]; simp)
    have hv := hp.bounds (z := v) (by rw [hsplit]; simp)
    have hne : (u, v) ≠ s := by
      intro h
      have hu' : u = s.1 := by rw [← h]
      have hv' : v = s.2 := by rw [← h]
      apply hpe
      have hps := hp.pairwise
      rw [hsplit] at hps
      have hl₁ : l₁ = [] := by
        cases l₁ with
        | nil => rfl
        | cons c l₁ =>
          exfalso
          have h1 := hp.1
          rw [hsplit] at h1
          simp only [List.cons_append, List.head?_cons, Option.some.injEq] at h1
          have := (List.pairwise_cons.mp hps).1 u (by simp)
          omega
      have hl₂ : l₂ = [] := by
        cases l₂ with
        | nil => rfl
        | cons c l₂ =>
          exfalso
          have h1 := hp.bounds (z := c) (by rw [hsplit]; simp)
          have h2 := (List.pairwise_append.mp hps).2.1
          have := (List.pairwise_cons.mp (List.pairwise_cons.mp h2).2).1 c (by simp)
          omega
      rw [hsplit, hl₁, hl₂, hu', hv']
      rfl
    exact hx'.2.2 (u, v) (hP.mem_segs.mpr ⟨hR.2, by simp only; omega⟩) ⟨hu.1, hv.2⟩ hne
      ⟨hux, hxv⟩
  · rintro (rfl | h)
    · exact isRPath_pair.mpr ⟨by omega, hs'.1⟩
    · exact h.isRPath hfh hfl

/-- **The face decomposition, slot form**: a region path of a segment `s` other than
`[s.1, s.2]` is given by one region path `qs[i]` for each slot of the face below `s` (from
its `i`-th to its `(i + 1)`-th vertex), joined at the face vertices; and conversely. -/
theorem isRPath_iff_slots (hP : IsPolygon g n) {s : ℕ × ℕ} (hs : s ∈ segs g n)
    {p : List ℕ} :
    IsRPath g s.1 s.2 p ↔ p = [s.1, s.2] ∨
      ∃ qs : List (List ℕ), qs.length = (faceVerts g n s).length - 1 ∧
        (∀ i < qs.length, IsRPath g ((faceVerts g n s).getD i 0)
          ((faceVerts g n s).getD (i + 1) 0) (qs.getD i [])) ∧
        p = s.1 :: (qs.map List.tail).flatten := by
  have hs' := hP.mem_segs.mp hs
  obtain ⟨rest, hrest⟩ := List.head?_eq_some_iff.mp
    (faceVerts_head? (g := g) (n := n) (s := s) (by omega))
  rw [hP.isRPath_iff_joins hs, hrest, joins_iff_slots]
  simp

/-- The boundary of the face below a segment `s`, without the edge `s`, is a region path of
`s`. -/
theorem faceVerts_isRPath (hP : IsPolygon g n) {s : ℕ × ℕ} (hs : s ∈ segs g n) :
    IsRPath g s.1 s.2 (faceVerts g n s) := by
  have hs' := hP.mem_segs.mp hs
  refine ⟨faceVerts_head? (by omega), faceVerts_getLast? (by omega), ?_⟩
  rw [List.isChain_iff_forall_rel_of_append_cons_cons]
  intro x y l₁ l₂ h
  have hi : [x, y] <:+: faceVerts g n s := ⟨l₁, l₂, by rw [h]; simp⟩
  exact ⟨(hP.infix_faceVerts_lt hs hi).2.1, hP.adj_of_infix_faceVerts hs hi⟩

/-- **Lemma 27**: the boundary of the face below a segment is a convex cycle of `g` (closed
by the segment). -/
theorem faceVerts_convexCycle (hP : IsPolygon g n) {s : ℕ × ℕ} (hs : s ∈ segs g n) :
    ConvexCycle g (faceVerts g n s) :=
  ((convexCycle_iff_isRPath (hP.mem_segs.mp hs).1).mpr
    ⟨hP.faceVerts_isRPath hs, hP.three_le_length_faceVerts hs⟩).1

end IsPolygon

end STACS2027

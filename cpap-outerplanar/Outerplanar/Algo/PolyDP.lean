module

public import Outerplanar.Algo.PolyFacts
public import Outerplanar.Algo.Digits
import Mathlib.Tactic

/-!
# The tables of the polygon solver are the tree dynamic program

Given the combinatorial facts `PolyFacts hP hk` about the enumerations of
`Outerplanar.Algo.Poly`, the tables `tabArg` compute the tree dynamic program
`polygonProblem hP hk` of Lemma 34 (`tabArg_spec`).

A value list on pool indices represents values `γ : CycVar pg n k → Fin k` when it is the
list of the values `vOf γ i` of those indices. For a segment `s`:

* the edges owned by `s` are `owned s`, and a cycle through an owned edge is relevant at
  `s` (its top is `s`, or it is a boundary cycle of `s`), so `loadAt` is the load
  `cycLoad` and `localCost` is the local cost `loc` (`loadAt_eq`, `localCost_eq`);
* the children of `s` are `childSegs s`, the boundary cycles of a child are relevant at
  `s`, and `childIdx` encodes their values (`sum_childSegs`, `childIdx_eq`);
* minimizing over all values of the cycles with top `s` is minimizing over the
  configurations `β < k ^ |topIdx s|`, which the fold of `tabArg` does (`argmin_fold`).

`tabArg_spec`: for a configuration `α` of the boundary cycles of `s` that represents `γ`,
the entry `(tabArg fuel s α).2` is `dp s γ` once the fuel exceeds the size of `s`, and its
minimizing configuration `(tabArg fuel s α).1` of the cycles with top `s` attains it: any
values represented by `α` and that configuration have local cost plus children's values
equal to the entry.
-/

@[expose] public section

namespace STACS2027.Poly

open IsPolygon TreeDP

variable {pg : Graph} {n k : ℕ}

/-! ### The cycle pool and the variables -/

/-- The value of the pool cycle `i` under `γ` (`0` if it is not a convex cycle). -/
def vOf (γ : CycVar pg n k → Fin k) (i : ℕ) : ℕ :=
  if h : cyc pg n k i ∈ convexCycles pg n k then (γ ⟨cyc pg n k i, h⟩ : ℕ) else 0

/-- The index in the pool of a convex cycle. -/
def idx (x : CycVar pg n k) : ℕ := (pool pg n k).idxOf x.1

theorem vOf_lt (hk : 0 < k) (γ : CycVar pg n k → Fin k) (i : ℕ) : vOf γ i < k := by
  unfold vOf
  split
  · exact (γ _).2
  · exact hk

theorem vOf_eq (γ : CycVar pg n k → Fin k) {i : ℕ} (h : cyc pg n k i ∈ convexCycles pg n k) :
    vOf γ i = γ ⟨cyc pg n k i, h⟩ := by
  simp [vOf, h]

theorem cyc_eq_getElem {i : ℕ} (hi : i < (pool pg n k).length) :
    cyc pg n k i = (pool pg n k)[i] := by
  simp [cyc, List.getD_eq_getElem?_getD, hi]

section Facts

variable {hP : IsPolygon pg n} {hk : 3 ≤ k}

theorem mem_pool_iff (F : PolyFacts hP hk) {u : List ℕ} :
    u ∈ pool pg n k ↔ u ∈ convexCycles pg n k := by
  rw [F.mem_pool, convexCycles, List.mem_toFinset]

theorem cyc_mem (F : PolyFacts hP hk) {i : ℕ} (hi : i < (pool pg n k).length) :
    cyc pg n k i ∈ convexCycles pg n k := by
  rw [← mem_pool_iff F, cyc_eq_getElem hi]
  exact List.getElem_mem hi

theorem idx_lt (F : PolyFacts hP hk) (x : CycVar pg n k) : idx x < (pool pg n k).length :=
  List.idxOf_lt_length_iff.mpr ((mem_pool_iff F).mpr x.2)

theorem cyc_idx (F : PolyFacts hP hk) (x : CycVar pg n k) : cyc pg n k (idx x) = x.1 := by
  rw [cyc_eq_getElem (idx_lt F x)]
  exact List.getElem_idxOf _

theorem idx_cyc (F : PolyFacts hP hk) {i : ℕ} (hi : i < (pool pg n k).length) :
    idx (⟨cyc pg n k i, cyc_mem F hi⟩ : CycVar pg n k) = i := by
  simp only [idx, cyc_eq_getElem hi]
  exact F.pool_nodup.idxOf_getElem i hi

theorem idx_injective (F : PolyFacts hP hk) : Function.Injective (idx (pg := pg) (n := n) (k := k)) := by
  intro x y h
  apply Subtype.ext
  rw [← cyc_idx F x, ← cyc_idx F y, h]

theorem vOf_idx (F : PolyFacts hP hk) (γ : CycVar pg n k → Fin k) (x : CycVar pg n k) :
    vOf γ (idx x) = γ x := by
  rw [vOf_eq γ (cyc_mem F (idx_lt F x))]
  congr 2
  exact Subtype.ext (cyc_idx F x)

end Facts

theorem topOf_eq_top (hP : IsPolygon pg n) (hk : 3 ≤ k) (x : CycVar pg n k) :
    topOf x.1 = ((polygonProblem hP hk).top x).1 := by
  obtain ⟨u, hu⟩ := x
  have := IsPolygon.ne_nil_of_mem_convexCycles hk hu
  simp only [polygonProblem, topOf]
  cases u with
  | nil => exact absurd rfl this
  | cons a l => simp [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast]

theorem top_eq_iff (hP : IsPolygon pg n) (hk : 3 ≤ k) (x : CycVar pg n k) {s : ℕ × ℕ}
    (hs : s ∈ segs pg n) : (polygonProblem hP hk).top x = ⟨s, hs⟩ ↔ topOf x.1 = s := by
  rw [Subtype.ext_iff, topOf_eq_top hP hk]

/-! ### Boundary cycles and cycles with a given top -/

theorem mem_topIdx {s : ℕ × ℕ} {i : ℕ} :
    i ∈ topIdx pg n k s ↔ i < (pool pg n k).length ∧ topOf (cyc pg n k i) = s := by
  simp [topIdx]

theorem mem_bnd {s : ℕ × ℕ} {i : ℕ} :
    i ∈ bnd pg n k s ↔ i < (pool pg n k).length ∧ s.1 ∈ cyc pg n k i ∧ s.2 ∈ cyc pg n k i ∧
      topOf (cyc pg n k i) ≠ s := by
  simp [bnd]

theorem nodup_topIdx (s : ℕ × ℕ) : (topIdx pg n k s).Nodup := List.nodup_range.filter _

theorem nodup_bnd (s : ℕ × ℕ) : (bnd pg n k s).Nodup := List.nodup_range.filter _

theorem nodup_rel (s : ℕ × ℕ) : (rel pg n k s).Nodup := by
  refine List.nodup_append.mpr ⟨nodup_bnd s, nodup_topIdx s, ?_⟩
  intro a ha b hb hab
  subst hab
  exact (mem_bnd.mp ha).2.2.2 (mem_topIdx.mp hb).2

theorem lt_of_mem_rel {s : ℕ × ℕ} {i : ℕ} (h : i ∈ rel pg n k s) : i < (pool pg n k).length := by
  rcases List.mem_append.mp h with h | h
  · exact (mem_bnd.mp h).1
  · exact (mem_topIdx.mp h).1

section Facts

variable {hP : IsPolygon pg n} {hk : 3 ≤ k}

theorem idx_mem_topIdx_iff (F : PolyFacts hP hk) (x : CycVar pg n k) {s : ℕ × ℕ}
    (hs : s ∈ segs pg n) : idx x ∈ topIdx pg n k s ↔ (polygonProblem hP hk).top x = ⟨s, hs⟩ := by
  rw [mem_topIdx, cyc_idx F, top_eq_iff hP hk x hs]
  exact ⟨fun h => h.2, fun h => ⟨idx_lt F x, h⟩⟩

theorem idx_mem_bnd_iff (F : PolyFacts hP hk) (x : CycVar pg n k) {s : ℕ × ℕ}
    (hs : s ∈ segs pg n) : idx x ∈ bnd pg n k s ↔ x ∈ (polygonProblem hP hk).boundary ⟨s, hs⟩ := by
  rw [mem_bnd, cyc_idx F, F.mem_boundary s hs x]
  exact ⟨fun h => h.2, fun h => ⟨idx_lt F x, h⟩⟩

/-- The values of `upd s γ β`: those of `β` on the cycles with top `s`, of `γ` elsewhere. -/
theorem vOf_upd (F : PolyFacts hP hk) {s : ℕ × ℕ} (hs : s ∈ segs pg n)
    (γ β : CycVar pg n k → Fin k) {i : ℕ} (hi : i < (pool pg n k).length) :
    vOf ((polygonProblem hP hk).upd ⟨s, hs⟩ γ β) i =
      if topOf (cyc pg n k i) = s then vOf β i else vOf γ i := by
  have h := cyc_mem F hi
  simp only [vOf, h, dite_true, Problem.upd]
  by_cases ht : topOf (cyc pg n k i) = s
  · simp [(top_eq_iff hP hk ⟨_, h⟩ hs).mpr ht, ht]
  · have ht' : ¬ (polygonProblem hP hk).top ⟨_, h⟩ = ⟨s, hs⟩ :=
      fun h' => ht ((top_eq_iff hP hk ⟨_, h⟩ hs).mp h')
    simp [ht', ht]

theorem map_bnd_upd (F : PolyFacts hP hk) {s : ℕ × ℕ} (hs : s ∈ segs pg n)
    (γ β : CycVar pg n k → Fin k) :
    (bnd pg n k s).map (vOf ((polygonProblem hP hk).upd ⟨s, hs⟩ γ β)) =
      (bnd pg n k s).map (vOf γ) := by
  apply List.map_congr_left
  intro i hi
  have h := mem_bnd.mp hi
  rw [vOf_upd F hs γ β h.1, ite_eq_right_iff.mpr (fun h' => absurd h' h.2.2.2)]

theorem map_topIdx_upd (F : PolyFacts hP hk) {s : ℕ × ℕ} (hs : s ∈ segs pg n)
    (γ β : CycVar pg n k → Fin k) :
    (topIdx pg n k s).map (vOf ((polygonProblem hP hk).upd ⟨s, hs⟩ γ β)) =
      (topIdx pg n k s).map (vOf β) := by
  apply List.map_congr_left
  intro i hi
  have h := mem_topIdx.mp hi
  rw [vOf_upd F hs γ β h.1, ite_eq_left_iff.mpr (fun h' => absurd h.2 h')]

/-- Every configuration `β` of the cycles with top `s` is that of some values. -/
theorem exists_map_topIdx (F : PolyFacts hP hk) (s : ℕ × ℕ) (β : ℕ) :
    ∃ βv : CycVar pg n k → Fin k,
      (topIdx pg n k s).map (vOf βv) = cfg k (topIdx pg n k s).length β := by
  have hk0 : 0 < k := by omega
  refine ⟨fun x => ⟨β / k ^ ((topIdx pg n k s).idxOf (idx x)) % k, Nat.mod_lt _ hk0⟩, ?_⟩
  apply List.ext_getElem (by simp)
  intro q h1 h2
  have hq : q < (topIdx pg n k s).length := by simpa using h1
  have hi := (mem_topIdx.mp (List.getElem_mem hq)).1
  simp only [List.getElem_map, getElem_cfg]
  rw [vOf_eq _ (cyc_mem F hi)]
  simp only [idx_cyc F hi, (nodup_topIdx s).idxOf_getElem]

/-! ### Loads and local costs -/

/-- Counting convex cycles by pool indices: if every cycle with the property has its index
in `is`, the number of such cycles is the number of indices of `is` with the property. -/
theorem card_filter_eq_countP (F : PolyFacts hP hk) {is : List ℕ} (hnd : is.Nodup)
    (hlt : ∀ i ∈ is, i < (pool pg n k).length) (p : List ℕ → ℕ → Prop)
    [∀ u j, Decidable (p u j)] (γ : CycVar pg n k → Fin k)
    (hcov : ∀ x : CycVar pg n k, p x.1 (γ x) → idx x ∈ is) :
    (Finset.univ.filter fun x : CycVar pg n k => p x.1 (γ x)).card =
      is.countP (fun i => decide (p (cyc pg n k i) (vOf γ i))) := by
  rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup (hnd.filter _),
    ← Finset.card_map ⟨idx, idx_injective F⟩]
  congr 1
  ext i
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, List.mem_toFinset,
    List.mem_filter, decide_eq_true_eq, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨hcov x hx, by rw [cyc_idx F x, vOf_idx F γ x]; exact hx⟩
  · rintro ⟨hi, hp⟩
    refine ⟨⟨cyc pg n k i, cyc_mem F (hlt i hi)⟩, ?_, idx_cyc F (hlt i hi)⟩
    rw [vOf_eq γ (cyc_mem F (hlt i hi))] at hp
    exact hp

theorem countP_zip_map {α β : Type*} (l : List α) (f : α → β) (p : α × β → Bool) :
    (l.zip (l.map f)).countP p = l.countP (fun a => p (a, f a)) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.countP_cons, ih]

/-- A cycle through an edge owned by `s` is relevant at `s`. -/
theorem idx_mem_rel_of_owned (F : PolyFacts hP hk) {s : ℕ × ℕ} (hs : s ∈ segs pg n) {e : Edge}
    (he : e ∈ owned pg n s) {x : CycVar pg n k} (hx : e ∈ cycleEdges x.1) :
    idx x ∈ rel pg n k s := by
  obtain ⟨hep, hown⟩ := (F.mem_owned s hs e).mp he
  have hown' : (polygonProblem hP hk).own e = ⟨s, hs⟩ := Subtype.ext hown
  have hsc : x ∈ (polygonProblem hP hk).scope e := by
    simp only [polygonProblem, Finset.mem_filter, Finset.mem_univ, true_and]; exact hx
  rcases (polygonProblem hP hk).top_eq_or_mem_boundary hep hsc with h | h
  · rw [hown'] at h
    exact List.mem_append_right _ ((idx_mem_topIdx_iff F x hs).mpr h)
  · rw [hown'] at h
    exact List.mem_append_left _ ((idx_mem_bnd_iff F x hs).mpr h)

/-- On the edges owned by `s`, `loadAt` is the load of the represented values. -/
theorem loadAt_eq (F : PolyFacts hP hk) {s : ℕ × ℕ} (hs : s ∈ segs pg n) {e : Edge}
    (he : e ∈ owned pg n s) (γ : CycVar pg n k → Fin k) :
    loadAt pg n k s ((rel pg n k s).map (vOf γ)) e = cycLoad γ e := by
  unfold loadAt cycLoad
  rw [countP_zip_map]
  symm
  exact card_filter_eq_countP F (nodup_rel s) (fun i hi => lt_of_mem_rel hi)
    (fun u j => e ∈ selectedAt u (omitted u j)) γ
    (fun x hx => idx_mem_rel_of_owned F hs he (selectedAt_mem.mp hx).1)

/-- `localCost` is the cost of the factors owned by `s` under the represented values. -/
theorem localCost_eq (F : PolyFacts hP hk) {s : ℕ × ℕ} (hs : s ∈ segs pg n)
    (γ : CycVar pg n k → Fin k) :
    localCost pg n k s ((rel pg n k s).map (vOf γ)) = (polygonProblem hP hk).loc ⟨s, hs⟩ γ := by
  unfold localCost Problem.loc
  have hfil : (polygonProblem hP hk).factors.filter (fun f => (polygonProblem hP hk).own f = ⟨s, hs⟩) =
      (owned pg n s).toFinset := by
    ext e
    rw [Finset.mem_filter, List.mem_toFinset, F.mem_owned s hs e, Subtype.ext_iff]
    rfl
  rw [hfil, List.sum_toFinset _ (F.owned_nodup s hs)]
  congr 1
  apply List.map_congr_left
  intro e he
  rw [loadAt_eq F hs he]
  rfl

/-! ### Children -/

/-- A list sum over `childSegs s` is a sum over the children of `s` in the segment tree. -/
theorem sum_childSegs (F : PolyFacts hP hk) {s : ℕ × ℕ} (hs : s ∈ segs pg n)
    (G : Seg pg n → ℕ) (H : ℕ × ℕ → ℕ)
    (hGH : ∀ w (hw : w ∈ segs pg n), w ∈ childSegs pg n s → H w = G ⟨w, hw⟩) :
    ((childSegs pg n s).map H).sum = ∑ w ∈ (segTree hP).children ⟨s, hs⟩, G w := by
  have hmem : ∀ w : Seg pg n, w ∈ (segTree hP).children ⟨s, hs⟩ ↔ w.1 ∈ childSegs pg n s := by
    intro w
    rw [mem_children_iff, F.mem_childSegs s hs]
    exact ⟨fun h => ⟨w.2, h⟩, fun h => h.2⟩
  have h1 : ∑ w ∈ (segTree hP).children ⟨s, hs⟩, G w =
      ∑ w ∈ (segTree hP).children ⟨s, hs⟩, H w.1 :=
    Finset.sum_congr rfl fun w hw => (hGH w.1 w.2 ((hmem w).mp hw)).symm
  have h2 : ((segTree hP).children ⟨s, hs⟩).map (Function.Embedding.subtype _) =
      (childSegs pg n s).toFinset := by
    ext w
    simp only [Finset.mem_map, Function.Embedding.subtype_apply, List.mem_toFinset]
    constructor
    · rintro ⟨w', hw', rfl⟩; exact (hmem w').mp hw'
    · intro hw
      have hw' := ((F.mem_childSegs s hs w).mp hw).1
      exact ⟨⟨w, hw'⟩, (hmem ⟨w, hw'⟩).mpr hw, rfl⟩
  rw [h1, ← List.sum_toFinset _ (F.childSegs_nodup s), ← h2, Finset.sum_map]
  rfl

/-- The boundary cycles of a child of `s` are relevant at `s`. -/
theorem bnd_child_mem_rel (F : PolyFacts hP hk) {s : ℕ × ℕ} (hs : s ∈ segs pg n) {w : ℕ × ℕ}
    (hw : w ∈ childSegs pg n s) {i : ℕ} (hi : i ∈ bnd pg n k w) : i ∈ rel pg n k s := by
  obtain ⟨hws, hch⟩ := (F.mem_childSegs s hs w).mp hw
  have hlt := (mem_bnd.mp hi).1
  have hidx := idx_cyc F hlt
  have hb : (⟨cyc pg n k i, cyc_mem F hlt⟩ : CycVar pg n k) ∈
      (polygonProblem hP hk).boundary ⟨w, hws⟩ := by
    rw [← idx_mem_bnd_iff F _ hws, hidx]; exact hi
  have hc : (⟨w, hws⟩ : Seg pg n) ∈ (segTree hP).children ⟨s, hs⟩ := by
    rw [mem_children_iff]; exact hch
  rcases (polygonProblem hP hk).boundary_child hc hb with h | h
  · rw [← idx_mem_topIdx_iff F _ hs, hidx] at h
    exact List.mem_append_right _ h
  · rw [← idx_mem_bnd_iff F _ hs, hidx] at h
    exact List.mem_append_left _ h

/-- `childIdx` encodes the values of the boundary cycles of the child. -/
theorem childIdx_eq (F : PolyFacts hP hk) {s : ℕ × ℕ} (hs : s ∈ segs pg n) {w : ℕ × ℕ}
    (hw : w ∈ childSegs pg n s) (γ : CycVar pg n k → Fin k) :
    childIdx pg n k s w ((rel pg n k s).map (vOf γ)) = enc k ((bnd pg n k w).map (vOf γ)) := by
  unfold childIdx
  congr 1
  apply List.map_congr_left
  intro i hi
  have hlt : (rel pg n k s).idxOf i < (rel pg n k s).length :=
    List.idxOf_lt_length_iff.mpr (bnd_child_mem_rel F hs hw hi)
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hlt,
    Option.map_some, Option.getD_some, List.getElem_idxOf]

theorem cfg_enc_map (hk0 : 0 < k) (l : List ℕ) (γ : CycVar pg n k → Fin k) :
    cfg k l.length (enc k (l.map (vOf γ))) = l.map (vOf γ) := by
  have := cfg_enc (k := k) (l.map (vOf γ)) (fun d hd => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hd; exact vOf_lt hk0 γ i)
  rwa [List.length_map] at this

theorem enc_map_lt (hk0 : 0 < k) (l : List ℕ) (γ : CycVar pg n k → Fin k) :
    enc k (l.map (vOf γ)) < k ^ l.length := by
  have := enc_lt hk0 (l.map (vOf γ)) (fun d hd => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hd; exact vOf_lt hk0 γ i)
  rwa [List.length_map] at this

end Facts

/-! ### The tables -/

variable (pg n k) in
/-- The quantity minimized by `tabArg (fuel + 1) s α` over `β`. -/
def stepTotal (fuel : ℕ) (s : ℕ × ℕ) (α β : ℕ) : ℕ :=
  localCost pg n k s (cfg k (bnd pg n k s).length α ++ cfg k (topIdx pg n k s).length β) +
    ((childSegs pg n s).map fun w =>
      (tabArg pg n k fuel w (childIdx pg n k s w
        (cfg k (bnd pg n k s).length α ++ cfg k (topIdx pg n k s).length β))).2).sum

variable (pg n k) in
theorem tabArg_succ (fuel : ℕ) (s : ℕ × ℕ) (α : ℕ) :
    tabArg pg n k (fuel + 1) s α = (List.range' 1 (k ^ (topIdx pg n k s).length - 1)).foldl
      (fun bv β => if stepTotal pg n k fuel s α β < bv.2 then (β, stepTotal pg n k fuel s α β)
        else bv)
      (0, stepTotal pg n k fuel s α 0) := rfl

variable {hP : IsPolygon pg n} {hk : 3 ≤ k}

/-- **The tables compute the tree dynamic program.** For a segment `s` with fuel at least
its size and a configuration `α` of its boundary cycles representing `γ`, the entry
`(tabArg fuel s α).2` is `dp s γ`; and any values represented by `α` and the minimizing
configuration `(tabArg fuel s α).1` of the cycles with top `s` attain it: their local cost
plus the children's values is the entry. -/
theorem tabArg_spec [NeZero k] (F : PolyFacts hP hk) :
    ∀ (fuel : ℕ) (s : ℕ × ℕ) (hs : s ∈ segs pg n), s.2 - s.1 ≤ fuel →
    ∀ (α : ℕ) (γ : CycVar pg n k → Fin k),
      cfg k (bnd pg n k s).length α = (bnd pg n k s).map (vOf γ) →
      (tabArg pg n k fuel s α).2 = (polygonProblem hP hk).dp ⟨s, hs⟩ γ ∧
      ∀ γ' : CycVar pg n k → Fin k,
        cfg k (bnd pg n k s).length α = (bnd pg n k s).map (vOf γ') →
        cfg k (topIdx pg n k s).length (tabArg pg n k fuel s α).1 =
          (topIdx pg n k s).map (vOf γ') →
        (polygonProblem hP hk).loc ⟨s, hs⟩ γ' +
          ∑ w ∈ (segTree hP).children ⟨s, hs⟩, (polygonProblem hP hk).dp w γ' =
            (tabArg pg n k fuel s α).2
  | 0, s, hs, hsz, _, _, _ => by
    have := (hP.mem_segs.mp hs).2; omega
  | fuel + 1, s, hs, hsz, α, γ, hα => by
    have hk0 : 0 < k := by omega
    -- the minimized quantity, for values representing `(α, β)`
    have hL : ∀ (β : ℕ) (γ' : CycVar pg n k → Fin k),
        cfg k (bnd pg n k s).length α = (bnd pg n k s).map (vOf γ') →
        cfg k (topIdx pg n k s).length β = (topIdx pg n k s).map (vOf γ') →
        stepTotal pg n k fuel s α β = (polygonProblem hP hk).loc ⟨s, hs⟩ γ' +
          ∑ w ∈ (segTree hP).children ⟨s, hs⟩, (polygonProblem hP hk).dp w γ' := by
      intro β γ' h1 h2
      have hv : cfg k (bnd pg n k s).length α ++ cfg k (topIdx pg n k s).length β =
          (rel pg n k s).map (vOf γ') := by
        rw [h1, h2, rel, List.map_append]
      unfold stepTotal
      rw [hv, localCost_eq F hs]
      congr 1
      apply sum_childSegs F hs
      intro w hw hws
      have hc := (F.mem_childSegs s hs w).mp hws
      have hsz' : w.2 - w.1 ≤ fuel := by
        have := hP.child_size_lt hw hc.2
        simp only [segSize] at this
        omega
      rw [childIdx_eq F hs hws]
      exact (tabArg_spec F fuel w hw hsz' _ γ' (cfg_enc_map hk0 _ γ')).1
    have hm : 0 < k ^ (topIdx pg n k s).length := pow_pos hk0 _
    obtain ⟨-, heq, hmin⟩ := argmin_fold (stepTotal pg n k fuel s α) hm
    rw [tabArg_succ]
    have hdp : (polygonProblem hP hk).dp ⟨s, hs⟩ γ =
        stepTotal pg n k fuel s α ((List.range' 1 (k ^ (topIdx pg n k s).length - 1)).foldl
          (fun bv β => if stepTotal pg n k fuel s α β < bv.2 then
            (β, stepTotal pg n k fuel s α β) else bv) (0, stepTotal pg n k fuel s α 0)).1 := by
      rw [(polygonProblem hP hk).dp_eq]
      apply le_antisymm
      · obtain ⟨βv, hβv⟩ := exists_map_topIdx F s ((List.range' 1 (k ^ (topIdx pg n k s).length - 1)).foldl
          (fun bv β => if stepTotal pg n k fuel s α β < bv.2 then
            (β, stepTotal pg n k fuel s α β) else bv) (0, stepTotal pg n k fuel s α 0)).1
        refine le_trans (Finset.inf'_le _ (Finset.mem_univ βv)) (le_of_eq ?_)
        refine (hL _ _ (by rw [map_bnd_upd F hs]; exact hα) ?_).symm
        rw [map_topIdx_upd F hs, hβv]
      · obtain ⟨β, -, hβ⟩ := Finset.exists_mem_eq_inf' (s := (Finset.univ : Finset (CycVar pg n k → Fin k)))
          Finset.univ_nonempty (fun β => (polygonProblem hP hk).loc ⟨s, hs⟩
            ((polygonProblem hP hk).upd ⟨s, hs⟩ γ β) + ∑ w ∈ (segTree hP).children ⟨s, hs⟩,
              (polygonProblem hP hk).dp w ((polygonProblem hP hk).upd ⟨s, hs⟩ γ β))
        rw [hβ]
        have h := hL (enc k ((topIdx pg n k s).map (vOf β))) ((polygonProblem hP hk).upd ⟨s, hs⟩ γ β)
          (by rw [map_bnd_upd F hs]; exact hα)
          (by rw [map_topIdx_upd F hs]; exact cfg_enc_map hk0 _ β)
        rw [← h, ← heq]
        exact hmin _ (enc_map_lt hk0 _ β)
    refine ⟨heq.trans hdp.symm, fun γ' h1 h2 => ?_⟩
    rw [heq]
    exact (hL _ γ' h1 h2).symm

end STACS2027.Poly

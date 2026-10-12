module

public import Outerplanar.RAM.R0Spec
public import Outerplanar.RAM.SortSpec
import Mathlib.Tactic

/-!
# First-occurrence identifiers of pairs, abstract side

The module `PairIds.lean` computes, for a list `ps` of pairs of numbers below `N` (stored as
two arrays `PU`, `PV`), in `O(N + |ps|)` time and space and without an `N × N` table:

* `LEAD[q] = ps.idxOf ps[q]`: the first index of the class of `q` (`LEAD[q] = q` iff `q` is a
  first occurrence);
* `EID[q] = ps.eraseDups.idxOf ps[q]`: the index of the pair `q` in the list of the distinct
  pairs, in order of first appearance; `NE = |ps.eraseDups|`; `CNT[e]`: the number of `q`
  with `EID[q] = e`.

This file is the abstract side.

**Leaders** (`gstep`, `grun`, `grun_lead`): the indices are sorted stably by first component
(`bucketIdx`, the counting sort `P1.csort`), then scanned in that order with a timestamped
per-vertex mark array: `STAMP[v] = u + 1` says that the pair `(u, v)` was seen in the current
group (the group of first component `u`), and then `LEADQ[v]` is its first index. Since every
earlier group has a smaller first component, a stale stamp never equals `u + 1`: no unmarking
pass is needed. The invariant (`GInv`) holds along every prefix of an order that is sorted by
`(first component, index)` and complete (`pairwise_bucketIdx`, `mem_bucketIdx`).

**Ranks** (`idxOf_eraseDups_of_not_mem`, `eraseDups_take_succ'`): scanning the indices in
order, `EID[q] := (LEAD[q] = q) ? NE++ : EID[LEAD[q]]` gives the identifiers in order of first
appearance; this part is generic in the type of the elements (it also turns any leader array
into identifiers, e.g. after a sort by labels).
-/

@[expose] public section

namespace STACS2027.RAM.PairIds

open STACS2027.Algo

/-! ### First occurrences in a list -/

section first

variable {α : Type} [BEq α] [LawfulBEq α]

/-- The first index of the element at `q`: `q` itself unless it occurs earlier. -/
theorem idxOf_getElem_eq (ps : List α) {q : ℕ} (hq : q < ps.length) :
    ps.idxOf ps[q] = if ps[q] ∈ ps.take q then (ps.take q).idxOf ps[q] else q := by
  generalize hx : ps[q] = x
  have h1 : ps = ps.take q ++ (x :: ps.drop (q + 1)) := by
    rw [← hx, ← List.drop_eq_getElem_cons hq, List.take_append_drop]
  conv_lhs => rw [h1]
  rw [List.idxOf_append]
  split
  · rfl
  · simp [show q ≤ ps.length by omega]

/-- `q` is the first index of its element iff the element does not occur before `q`. -/
theorem idxOf_getElem_eq_self_iff (ps : List α) {q : ℕ} (hq : q < ps.length) :
    ps.idxOf ps[q] = q ↔ ps[q] ∉ ps.take q := by
  rw [idxOf_getElem_eq ps hq]
  split
  · rename_i h
    have := List.idxOf_lt_length_iff.mpr h
    simp only [List.length_take, show min q ps.length = q by omega] at this
    exact ⟨fun h' => by omega, fun h' => absurd h h'⟩
  · rename_i h
    exact ⟨fun _ => h, fun _ => rfl⟩

/-- The first index of the element at `q` is at most `q`. -/
theorem idxOf_getElem_le (ps : List α) {q : ℕ} (hq : q < ps.length) : ps.idxOf ps[q] ≤ q := by
  rw [idxOf_getElem_eq ps hq]
  split
  · rename_i h
    have := List.idxOf_lt_length_iff.mpr h
    simp only [List.length_take, show min q ps.length = q by omega] at this
    omega
  · exact le_rfl

/-- The element at the first index. -/
theorem getElem_idxOf_getElem (ps : List α) {q : ℕ} (hq : q < ps.length) :
    ps[ps.idxOf ps[q]]'(by have := idxOf_getElem_le ps hq; omega) = ps[q] :=
  List.getElem_idxOf _

/-- The distinct elements of a prefix, one more element. -/
theorem eraseDups_take_succ' (ps : List α) {q : ℕ} (hq : q < ps.length) :
    (ps.take (q + 1)).eraseDups = R0.ext (ps.take q).eraseDups ps[q] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hq, Option.toList_some,
    R0.eraseDups_append_singleton]

/-- The distinct elements of a prefix grow by the first occurrences. -/
theorem eraseDups_take_succ (ps : List α) {q : ℕ} (hq : q < ps.length) :
    (ps.take (q + 1)).eraseDups =
      if ps.idxOf ps[q] = q then (ps.take q).eraseDups ++ [ps[q]] else (ps.take q).eraseDups := by
  rw [eraseDups_take_succ' ps hq]
  split
  · rename_i h
    have h' := (idxOf_getElem_eq_self_iff ps hq).mp h
    exact R0.ext_of_not_mem (fun hm => h' (List.mem_eraseDups.mp hm))
  · rename_i h
    have h' : ps[q] ∈ ps.take q := by
      by_contra hn; exact h ((idxOf_getElem_eq_self_iff ps hq).mpr hn)
    exact R0.ext_of_mem (List.mem_eraseDups.mpr h')

/-- The distinct elements of a prefix are a prefix of the distinct elements. -/
theorem eraseDups_take_prefix (ps : List α) (q : ℕ) : ∃ t, ps.eraseDups = (ps.take q).eraseDups ++ t := by
  refine ⟨((ps.drop q).removeAll (ps.take q)).eraseDups, ?_⟩
  conv_lhs => rw [← List.take_append_drop q ps]
  rw [List.eraseDups_append]

/-- The identifier of a first occurrence: the number of distinct elements before it. -/
theorem idxOf_eraseDups_of_not_mem (ps : List α) {q : ℕ} (hq : q < ps.length)
    (h : ps[q] ∉ ps.take q) : ps.eraseDups.idxOf ps[q] = (ps.take q).eraseDups.length := by
  obtain ⟨t, ht⟩ := eraseDups_take_prefix ps (q + 1)
  have hs := eraseDups_take_succ' ps hq
  rw [R0.ext_of_not_mem (fun hm => h (List.mem_eraseDups.mp hm))] at hs
  have hn : ps[q] ∉ (ps.take q).eraseDups := fun hm => h (List.mem_eraseDups.mp hm)
  rw [ht, hs, List.idxOf_append, List.idxOf_append]
  simp [hn]

/-- The identifier of an element is below the number of distinct elements. -/
theorem idxOf_eraseDups_lt (ps : List α) {q : ℕ} (hq : q < ps.length) :
    ps.eraseDups.idxOf ps[q] < ps.eraseDups.length :=
  List.idxOf_lt_length_iff.mpr (List.mem_eraseDups.mpr (List.getElem_mem hq))

end first

/-! ### Leaders by a timestamped scan in sorted order -/

/-- The pair at `q` (`(0, 0)` beyond the end). -/
abbrev pr (ps : List (ℕ × ℕ)) (q : ℕ) : ℕ × ℕ := ps.getD q (0, 0)

theorem pr_eq (ps : List (ℕ × ℕ)) {q : ℕ} (hq : q < ps.length) : pr ps q = ps[q] :=
  (List.getElem_eq_getD _).symm

theorem getD_map_fst (ps : List (ℕ × ℕ)) (q : ℕ) : (ps.map Prod.fst).getD q 0 = (pr ps q).1 := by
  simp only [pr, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases ps[q]? <;> rfl

theorem getD_map_snd (ps : List (ℕ × ℕ)) (q : ℕ) : (ps.map Prod.snd).getD q 0 = (pr ps q).2 := by
  simp only [pr, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases ps[q]? <;> rfl

/-- The state of the scan: the stamps, the first indices of the stamped pairs, the leaders. -/
structure GS where
  stamp : ℕ → ℕ
  lq : ℕ → ℕ
  lead : ℕ → ℕ

/-- The initial state (fresh zero arrays). -/
def gs0 : GS := ⟨fun _ => 0, fun _ => 0, fun _ => 0⟩

/-- One index `q` of the scan, with `(u, v) = ps[q]`: if `STAMP[v] = u + 1` then
`LEAD[q] := LEADQ[v]`, else `STAMP[v] := u + 1`, `LEADQ[v] := q`, `LEAD[q] := q`. -/
def gstep (ps : List (ℕ × ℕ)) (s : GS) (q : ℕ) : GS :=
  if s.stamp (pr ps q).2 = (pr ps q).1 + 1 then
    { s with lead := Function.update s.lead q (s.lq (pr ps q).2) }
  else ⟨Function.update s.stamp (pr ps q).2 ((pr ps q).1 + 1),
    Function.update s.lq (pr ps q).2 q, Function.update s.lead q q⟩

/-- The scan of the indices `l`, in order. -/
def grun (ps : List (ℕ × ℕ)) (l : List ℕ) : GS := l.foldl (gstep ps) gs0

theorem grun_append_singleton (ps : List (ℕ × ℕ)) (l : List ℕ) (q : ℕ) :
    grun ps (l ++ [q]) = gstep ps (grun ps l) q := by
  simp [grun, List.foldl_append]

/-- The invariant of the scan after the indices `l`. -/
structure GInv (ps : List (ℕ × ℕ)) (l : List ℕ) (s : GS) : Prop where
  stamp : ∀ v, s.stamp v = 0 ∨ ∃ q ∈ l, (pr ps q).2 = v ∧ s.stamp v = (pr ps q).1 + 1 ∧
    s.lq v = ps.idxOf (pr ps q)
  ge : ∀ q ∈ l, (pr ps q).1 + 1 ≤ s.stamp (pr ps q).2
  lead : ∀ q ∈ l, s.lead q = ps.idxOf (pr ps q)

theorem ginv_nil (ps : List (ℕ × ℕ)) : GInv ps [] gs0 :=
  ⟨fun _ => Or.inl rfl, fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil⟩

/-- **One step of the scan**, for an index `q` whose first component is at least those of the
indices scanned so far, and such that every earlier index of the same first component has been
scanned. -/
theorem GInv.step {ps : List (ℕ × ℕ)} {l : List ℕ} {s : GS} (h : GInv ps l s) {q : ℕ}
    (hq : q < ps.length) (hle : ∀ q' ∈ l, (pr ps q').1 ≤ (pr ps q).1)
    (hprev : ∀ q', q' < q → (pr ps q').1 = (pr ps q).1 → q' ∈ l) (hnot : q ∉ l) :
    GInv ps (l ++ [q]) (gstep ps s q) := by
  obtain ⟨u, v, huv⟩ : ∃ u v, pr ps q = (u, v) := ⟨_, _, rfl⟩
  have hu : (pr ps q).1 = u := by rw [huv]
  have hv : (pr ps q).2 = v := by rw [huv]
  rw [hu] at hle hprev
  unfold gstep
  rw [hu, hv]
  by_cases hs : s.stamp v = u + 1
  · simp only [hs, ↓reduceIte]
    rcases h.stamp v with h0 | ⟨q'', hq'', hv'', hst'', hlq''⟩
    · omega
    · have hu'' : (pr ps q'').1 = u := by omega
      have hpr : pr ps q'' = pr ps q := by rw [huv]; exact Prod.ext hu'' hv''
      refine ⟨fun w => ?_, fun q' hq' => ?_, fun q' hq' => ?_⟩ <;> dsimp only
      · rcases h.stamp w with h0 | ⟨q₁, hq₁, h₁⟩
        · exact Or.inl h0
        · exact Or.inr ⟨q₁, List.mem_append_left _ hq₁, h₁⟩
      · rcases List.mem_append.mp hq' with hq' | hq'
        · exact h.ge q' hq'
        · rw [List.mem_singleton.mp hq', hu, hv]; omega
      · rcases List.mem_append.mp hq' with hq' | hq'
        · have : q' ≠ q := fun he => hnot (he ▸ hq')
          rw [Function.update_of_ne this]; exact h.lead q' hq'
        · rw [List.mem_singleton.mp hq', Function.update_self, hlq'', hpr]
  · simp only [hs, ↓reduceIte]
    -- `q` is the first occurrence of its pair
    have hfirst : ps.idxOf (pr ps q) = q := by
      rw [pr_eq ps hq, idxOf_getElem_eq_self_iff ps hq]
      intro hm
      obtain ⟨j, hj, hjq⟩ := List.mem_take_iff_getElem.mp hm
      have hjq' : pr ps j = pr ps q := by
        rw [pr_eq ps (by omega), pr_eq ps hq]; exact hjq
      have hjl : j ∈ l := hprev j (by omega) (by rw [hjq', hu])
      have hge := h.ge j hjl
      rw [hjq', hu, hv] at hge
      rcases h.stamp v with h0 | ⟨q₁, hq₁, _, hst₁, _⟩
      · omega
      · have := hle q₁ hq₁
        omega
    refine ⟨fun w => ?_, fun q' hq' => ?_, fun q' hq' => ?_⟩ <;> dsimp only
    · by_cases hw : w = v
      · rw [hw]
        refine Or.inr ⟨q, List.mem_append_right _ (List.mem_singleton_self _), hv, ?_, ?_⟩
        · rw [Function.update_self, hu]
        · rw [Function.update_self, hfirst]
      · rw [Function.update_of_ne hw, Function.update_of_ne hw]
        rcases h.stamp w with h0 | ⟨q₁, hq₁, h₁⟩
        · exact Or.inl h0
        · exact Or.inr ⟨q₁, List.mem_append_left _ hq₁, h₁⟩
    · rcases List.mem_append.mp hq' with hq' | hq'
      · by_cases hw : (pr ps q').2 = v
        · rw [hw, Function.update_self]
          have := hle q' hq'
          omega
        · rw [Function.update_of_ne hw]; exact h.ge q' hq'
      · rw [List.mem_singleton.mp hq', hv, Function.update_self, hu]
    · rcases List.mem_append.mp hq' with hq' | hq'
      · have : q' ≠ q := fun he => hnot (he ▸ hq')
        rw [Function.update_of_ne this]; exact h.lead q' hq'
      · rw [List.mem_singleton.mp hq', Function.update_self, hfirst]

/-! ### The order of the counting sort -/

/-- The order of a stable sort by key: by key, then by index. -/
def KeyLt (keys : List ℕ) (a b : ℕ) : Prop :=
  keys.getD a 0 < keys.getD b 0 ∨ (keys.getD a 0 = keys.getD b 0 ∧ a < b)

theorem pairwise_bkt (keys : List ℕ) (i k : ℕ) : (P1.bkt keys i k).Pairwise (KeyLt keys) := by
  unfold P1.bkt
  refine (List.pairwise_lt_range.filter _).imp_of_mem ?_
  intro a b ha hb hab
  simp only [List.mem_filter, decide_eq_true_eq] at ha hb
  exact Or.inr ⟨by rw [ha.2, hb.2], hab⟩

/-- **The counting sort orders by key, then by index.** -/
theorem pairwise_bucketIdx (keys : List ℕ) (K : ℕ) : (P1.bucketIdx keys K).Pairwise (KeyLt keys) := by
  unfold P1.bucketIdx
  rw [List.pairwise_flatMap]
  refine ⟨fun k _ => pairwise_bkt keys _ k, ?_⟩
  refine List.pairwise_lt_range.imp_of_mem ?_
  intro k₁ k₂ _ _ hk x hx y hy
  rw [P1.mem_bkt] at hx hy
  exact Or.inl (by rw [hx.2, hy.2]; exact hk)

theorem mem_bucketIdx {keys : List ℕ} {K q : ℕ} :
    q ∈ P1.bucketIdx keys K ↔ q < keys.length ∧ keys.getD q 0 < K := by
  simp only [P1.bucketIdx, List.mem_flatMap, List.mem_range, P1.mem_bkt]
  constructor
  · rintro ⟨k, hk, hq, rfl⟩; exact ⟨hq, hk⟩
  · rintro ⟨hq, hk⟩; exact ⟨_, hk, hq, rfl⟩

/-- An order that is sorted by `(key, index)`: the entry at `p` and the entries before it. -/
theorem keyLt_split {keys : List ℕ} {ord : List ℕ} (hs : ord.Pairwise (KeyLt keys)) {p : ℕ}
    (hp : p < ord.length) :
    (∀ a ∈ ord.take p, KeyLt keys a ord[p]) ∧ (∀ b ∈ ord.drop (p + 1), KeyLt keys ord[p] b) := by
  have h : ord = ord.take p ++ (ord[p] :: ord.drop (p + 1)) := by simp
  rw [h, List.pairwise_append, List.pairwise_cons] at hs
  exact ⟨fun a ha => hs.2.2 a ha _ (List.mem_cons_self ..), hs.2.1.1⟩

theorem keyLt_irrefl (keys : List ℕ) (a : ℕ) : ¬ KeyLt keys a a := by
  unfold KeyLt; omega

/-! ### The scan in the order of the counting sort -/

section scan

variable (ps : List (ℕ × ℕ)) (K : ℕ)

/-- The order of the scan: the indices sorted stably by first component. -/
def ordOf : List ℕ := P1.bucketIdx (ps.map Prod.fst) K

variable {ps K}

theorem pairwise_ordOf : (ordOf ps K).Pairwise (KeyLt (ps.map Prod.fst)) :=
  pairwise_bucketIdx _ K

theorem lt_of_mem_ordOf {q : ℕ} (hq : q ∈ ordOf ps K) : q < ps.length := by
  simpa using P1.lt_of_mem_bucketIdx hq

theorem length_ordOf (hK : ∀ p ∈ ps, p.1 < K) : (ordOf ps K).length = ps.length := by
  rw [ordOf, P1.length_bucketIdx _ K (by simpa using hK), List.length_map]

theorem mem_ordOf (hK : ∀ p ∈ ps, p.1 < K) {q : ℕ} (hq : q < ps.length) : q ∈ ordOf ps K := by
  rw [ordOf, mem_bucketIdx, getD_map_fst, pr_eq ps hq]
  exact ⟨by simpa using hq, hK _ (List.getElem_mem hq)⟩

theorem grun_take_succ {p : ℕ} (hp : p < (ordOf ps K).length) :
    grun ps ((ordOf ps K).take (p + 1)) = gstep ps (grun ps ((ordOf ps K).take p)) (ordOf ps K)[p] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hp, Option.toList_some, grun_append_singleton]

/-- The invariant along the order of the counting sort. -/
theorem ginv_take (hK : ∀ p ∈ ps, p.1 < K) :
    ∀ p, p ≤ (ordOf ps K).length → GInv ps ((ordOf ps K).take p) (grun ps ((ordOf ps K).take p))
  | 0, _ => by simpa [grun] using ginv_nil ps
  | p + 1, hp => by
    have ih := ginv_take hK p (by omega)
    have hlt : p < (ordOf ps K).length := by omega
    obtain ⟨hbef, haft⟩ := keyLt_split pairwise_ordOf hlt
    rw [grun_take_succ hlt, List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some]
    have hq := lt_of_mem_ordOf (List.getElem_mem hlt)
    refine ih.step hq (fun q' hq' => ?_) (fun q' hq' hk => ?_) (fun hm => ?_)
    · have := hbef q' hq'
      unfold KeyLt at this
      rw [getD_map_fst, getD_map_fst] at this
      omega
    · have hq'L : q' < ps.length := by omega
      have hm := mem_ordOf hK hq'L
      have hsplit : ordOf ps K = (ordOf ps K).take p ++ ((ordOf ps K)[p] :: (ordOf ps K).drop (p + 1)) := by
        simp
      rw [hsplit] at hm
      rcases List.mem_append.mp hm with hm | hm
      · exact hm
      · rcases List.mem_cons.mp hm with hm | hm
        · omega
        · have := haft q' hm
          unfold KeyLt at this
          rw [getD_map_fst, getD_map_fst] at this
          omega
    · exact keyLt_irrefl _ _ (hbef _ hm)

/-- **The leaders**: after the scan of all indices in the order of the counting sort,
`lead q` is the first index of the pair at `q`. -/
theorem grun_lead (hK : ∀ p ∈ ps, p.1 < K) {q : ℕ} (hq : q < ps.length) :
    (grun ps (ordOf ps K)).lead q = ps.idxOf ps[q] := by
  have h := ginv_take hK _ le_rfl
  rw [List.take_length] at h
  rw [h.lead q (mem_ordOf hK hq), pr_eq ps hq]

end scan

end STACS2027.RAM.PairIds

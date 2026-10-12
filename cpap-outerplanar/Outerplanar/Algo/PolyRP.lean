module

public import Outerplanar.Algo.PolyEnum
import Mathlib.Tactic

/-!
# The polygon solver: region paths by folding over the face slots

`rpF pg n k fuel a b L` (in `Outerplanar.Algo.Poly`) lists the region paths of the edge
`(a, b)` with `L` entries: `[a, b]` for `L = 2`, and for a segment the concatenations of
region paths of the slots of its face, built by a left fold over the slots (`extendParts`)
from the partial path `[a]`, with at most `k` edges in all.

* `mem_foldl_sound`, `mem_foldl_complete`: the fold over the consecutive pairs of `y :: rest`
  extends each partial path by exactly the concatenations along `y :: rest` (`Joins`),
  within the budget of `k` edges;
* `sound_rpF`: every member of `rpF` is a region path from `a` to `b` with `L` entries (any
  fuel, any graph);
* `mem_rpF`: with fuel at least `b - a`, for `2 ≤ L ≤ k + 1`, the members are exactly these
  region paths (on a polygon, by the face decomposition `isRPath_iff_joins`);
* `rpF_nodup`: each is listed once;
* `rpF_fuel`: with fuel at least `b - a`, the fuel does not matter;
* `length_rpF_le`: at most `rpathBound L` members;
* `foldl_rpF_bound`: the intermediate lists of the fold have at most `partsBound k`
  members, each with at most `k` edges.
-/

@[expose] public section

namespace STACS2027.Poly

open IsPolygon

variable {pg : Graph} {n k : ℕ}

/-! ### One step of the fold -/

/-- The partial paths after one slot `(x, y)`: each earlier one extended by a slot path. -/
theorem mem_extendParts {rp : ℕ → ℕ → ℕ → List (List ℕ)} {parts : List (List ℕ × ℕ)}
    {x y : ℕ} {pe : List ℕ × ℕ} :
    pe ∈ extendParts k rp parts x y ↔ ∃ pe0 ∈ parts, ∃ L', (2 ≤ L' ∧ L' < 2 + (k - pe0.2)) ∧
      ∃ q ∈ rp x y L', (pe0.1 ++ q.tail, pe0.2 + (L' - 1)) = pe := by
  simp only [extendParts, List.mem_flatMap, List.mem_map, List.mem_range'_1]

/-- A list obtained from a list of slots by `Joins` is not empty. -/
theorem joins_ne_nil {y : ℕ} {rest q : List ℕ} (h : Joins pg (y :: rest) q) : q ≠ [] := by
  have := h.head?
  rintro rfl
  simp at this

/-- **Soundness of the fold**: every partial path after the slots of `y :: rest` extends a
starting one by a concatenation along `y :: rest`. -/
theorem mem_foldl_sound (rp : ℕ → ℕ → ℕ → List (List ℕ))
    (hrp : ∀ x y L' q, q ∈ rp x y L' → IsRPath pg x y q ∧ q.length = L') :
    ∀ (rest : List ℕ) (y : ℕ) (parts : List (List ℕ × ℕ)) (pe : List ℕ × ℕ),
      pe ∈ (pairs (y :: rest)).foldl (fun parts t => extendParts k rp parts t.1 t.2) parts →
      ∃ pe0 ∈ parts, ∃ q, Joins pg (y :: rest) q ∧
        pe = (pe0.1 ++ q.tail, pe0.2 + (q.length - 1))
  | [], y, parts, pe, h => by
    simp only [pairs, List.foldl_nil] at h
    exact ⟨pe, h, [y], by simp [Joins], by simp⟩
  | z :: rest, y, parts, pe, h => by
    simp only [pairs, List.foldl_cons] at h
    obtain ⟨pe1, h1, q', hq', rfl⟩ := mem_foldl_sound rp hrp rest z _ pe h
    obtain ⟨pe0, h0, L', hL', p, hp, rfl⟩ := mem_extendParts.mp h1
    obtain ⟨hpr, hpl⟩ := hrp y z L' p hp
    have hpne : p ≠ [] := by rintro rfl; simp at hpl; omega
    have hq'1 := List.length_pos_of_ne_nil (joins_ne_nil hq')
    refine ⟨pe0, h0, p ++ q'.tail, ⟨p, q', hpr, hq', rfl⟩, ?_⟩
    rw [List.tail_append_of_ne_nil hpne]
    simp only [List.append_assoc, List.length_append, List.length_tail, Prod.mk.injEq, true_and]
    omega

/-- **Completeness of the fold**: every extension of a starting partial path by a
concatenation along `y :: rest` within the budget is found. -/
theorem mem_foldl_complete (rp : ℕ → ℕ → ℕ → List (List ℕ)) :
    ∀ (rest : List ℕ) (y : ℕ), (y :: rest).Pairwise (· < ·) →
      (∀ x z, [x, z] <:+: y :: rest → ∀ L', 2 ≤ L' → L' ≤ k + 1 → ∀ q, IsRPath pg x z q →
        q.length = L' → q ∈ rp x z L') →
      ∀ (parts : List (List ℕ × ℕ)) (pe0 : List ℕ × ℕ) (q : List ℕ), pe0 ∈ parts →
        Joins pg (y :: rest) q → pe0.2 + (q.length - 1) ≤ k →
        (pe0.1 ++ q.tail, pe0.2 + (q.length - 1)) ∈
          (pairs (y :: rest)).foldl (fun parts t => extendParts k rp parts t.1 t.2) parts
  | [], y, _, _, parts, pe0, q, h0, hq, _ => by
    simp only [Joins] at hq
    subst hq
    simpa [pairs] using h0
  | z :: rest, y, hs, hrp, parts, pe0, q, h0, hq, hk => by
    obtain ⟨p, q', hp, hq', rfl⟩ := hq
    have hyz : y < z := (List.pairwise_cons.mp hs).1 z (by simp)
    have hp2 := hp.two_le_length hyz
    have hpne : p ≠ [] := by rintro rfl; simp at hp2
    have hq'1 := List.length_pos_of_ne_nil (joins_ne_nil hq')
    simp only [List.length_append, List.length_tail] at hk
    simp only [pairs, List.foldl_cons]
    have hmem : (pe0.1 ++ p.tail, pe0.2 + (p.length - 1)) ∈ extendParts k rp parts y z := by
      rw [mem_extendParts]
      exact ⟨pe0, h0, p.length, ⟨hp2, by omega⟩, p,
        hrp y z (infix_pair_head y z rest) _ hp2 (by omega) p hp rfl, rfl⟩
    have := mem_foldl_complete rp rest z (List.pairwise_cons.mp hs).2
      (fun x w h => hrp x w (List.infix_cons h)) _ _ q' hmem hq' (by simp only; omega)
    convert this using 2
    · rw [List.tail_append_of_ne_nil hpne, List.append_assoc]
    · simp only [List.length_append, List.length_tail]
      omega

/-- One step of the fold keeps the partial paths distinct, if they end at or below `y`. -/
theorem nodup_extendParts (rp : ℕ → ℕ → ℕ → List (List ℕ))
    (hrp : ∀ x y L' q, q ∈ rp x y L' → IsRPath pg x y q ∧ q.length = L')
    (hnd : ∀ x y L', (rp x y L').Nodup) {parts : List (List ℕ × ℕ)} {y z : ℕ}
    (hparts : parts.Nodup) (hle : ∀ pe ∈ parts, ∀ v ∈ pe.1, v ≤ y) :
    (extendParts k rp parts y z).Nodup := by
  -- the tail of a slot path lies above `y`
  have htail : ∀ L' q, q ∈ rp y z L' → q = y :: q.tail ∧ ∀ v ∈ q.tail, y < v := by
    intro L' q hq
    obtain ⟨t, rfl⟩ := List.head?_eq_some_iff.mp (hrp _ _ _ q hq).1.1
    have hpw := (hrp _ _ _ _ hq).1.pairwise
    exact ⟨rfl, fun v hv => (List.pairwise_cons.mp hpw).1 v hv⟩
  have hfilter : ∀ pe ∈ parts, ∀ L' q, q ∈ rp y z L' →
      (pe.1 ++ q.tail).filter (fun v => decide (v ≤ y)) = pe.1 := by
    intro pe hpe L' q hq
    rw [List.filter_append, List.filter_eq_self.mpr (fun v hv => by simpa using hle pe hpe v hv),
      List.filter_eq_nil_iff.mpr (fun v hv => by simpa using (htail L' q hq).2 v hv),
      List.append_nil]
  unfold extendParts
  rw [List.nodup_flatMap]
  refine ⟨fun pe0 _ => ?_, ?_⟩
  · rw [List.nodup_flatMap]
    refine ⟨fun L' _ => ?_, ?_⟩
    · refine List.Nodup.map_on ?_ (hnd y z L')
      intro q hq q' hq' he
      simp only [Prod.mk.injEq, List.append_cancel_left_eq, and_true] at he
      rw [(htail L' q hq).1, (htail L' q' hq').1, he]
    · refine List.Pairwise.imp_of_mem ?_ List.nodup_range'
      intro L₁ L₂ h₁ h₂ hne w hw₁ hw₂
      simp only [List.mem_map] at hw₁ hw₂
      obtain ⟨q₁, -, rfl⟩ := hw₁
      obtain ⟨q₂, -, he⟩ := hw₂
      simp only [Prod.mk.injEq] at he
      rw [List.mem_range'_1] at h₁ h₂
      omega
  · refine List.Pairwise.imp_of_mem ?_ hparts
    intro pe₁ pe₂ h₁ h₂ hne w hw₁ hw₂
    simp only [List.mem_flatMap, List.mem_map, List.mem_range'_1] at hw₁ hw₂
    obtain ⟨L₁, hL₁, q₁, hq₁, rfl⟩ := hw₁
    obtain ⟨L₂, hL₂, q₂, hq₂, he⟩ := hw₂
    simp only [Prod.mk.injEq] at he
    have e1 : pe₂.1 = pe₁.1 := by
      rw [← hfilter pe₂ h₂ L₂ q₂ hq₂, ← hfilter pe₁ h₁ L₁ q₁ hq₁, he.1]
    rw [e1, List.append_cancel_left_eq] at he
    have hl : q₂.length = q₁.length := by
      rw [(htail L₂ q₂ hq₂).1, (htail L₁ q₁ hq₁).1, he.1]
    rw [(hrp _ _ _ _ hq₂).2, (hrp _ _ _ _ hq₁).2] at hl
    subst hl
    exact hne (Prod.ext e1.symm (by omega))

/-- The fold keeps the partial paths distinct. -/
theorem nodup_foldl (rp : ℕ → ℕ → ℕ → List (List ℕ))
    (hrp : ∀ x y L' q, q ∈ rp x y L' → IsRPath pg x y q ∧ q.length = L')
    (hnd : ∀ x y L', (rp x y L').Nodup) :
    ∀ (rest : List ℕ) (y : ℕ) (parts : List (List ℕ × ℕ)), parts.Nodup →
      (∀ pe ∈ parts, ∀ v ∈ pe.1, v ≤ y) →
      ((pairs (y :: rest)).foldl (fun parts t => extendParts k rp parts t.1 t.2) parts).Nodup
  | [], y, parts, h, _ => by simpa [pairs] using h
  | z :: rest, y, parts, h, hle => by
    simp only [pairs, List.foldl_cons]
    refine nodup_foldl rp hrp hnd rest z _ (nodup_extendParts rp hrp hnd h hle) ?_
    intro pe hpe v hv
    obtain ⟨pe0, h0, L', -, q, hq, rfl⟩ := mem_extendParts.mp hpe
    have hqr := (hrp y z L' q hq).1
    have hyz := (hqr.bounds hqr.head_mem).2
    rcases List.mem_append.mp hv with hv | hv
    · have := hle pe0 h0 v hv
      omega
    · exact (hqr.bounds (List.mem_of_mem_tail hv)).2

/-! ### The region paths -/

/-- `rpF` with two entries: the edge itself. -/
theorem rpF_two (fuel a b : ℕ) :
    rpF pg n k fuel a b 2 = if a < b ∧ Adj pg a b then [[a, b]] else [] :=
  rpF.eq_1 _ _ _ _ _ _

/-- `rpF` without fuel and other than two entries: nothing. -/
theorem rpF_zero {a b L : ℕ} (hL : L ≠ 2) : rpF pg n k 0 a b L = [] :=
  rpF.eq_2 _ _ _ _ _ _ hL

/-- `rpF` with fuel and other than two entries: the fold over the slots. -/
theorem rpF_succ {fuel a b L : ℕ} (hL : L ≠ 2) :
    rpF pg n k (fuel + 1) a b L =
      if (a, b) ∈ segEnum pg n then
        (((slots pg n (a, b)).foldl (fun parts t => extendParts k (rpF pg n k fuel) parts t.1 t.2)
          [([a], 0)]).filter fun pe => decide (pe.2 + 1 = L)).map Prod.fst
      else [] :=
  rpF.eq_3 _ _ _ _ _ _ _ hL

/-- The face of a segment `(a, b)` starts at `a`. -/
theorem faceVerts_eq_cons {a b : ℕ} (hab : a ≤ b) :
    ∃ rest, faceVerts pg n (a, b) = a :: rest :=
  List.head?_eq_some_iff.mp (faceVerts_head? (g := pg) (n := n) (s := (a, b)) hab)

/-- **Soundness**: the members of `rpF` are region paths from `a` to `b` with `L`
entries. -/
theorem sound_rpF {fuel : ℕ} : ∀ {a b L : ℕ} {u : List ℕ}, u ∈ rpF pg n k fuel a b L →
    IsRPath pg a b u ∧ u.length = L := by
  induction fuel with
  | zero =>
    intro a b L u h
    by_cases hL : L = 2
    · subst hL
      rw [rpF_two] at h
      split_ifs at h with hc
      · simp only [List.mem_singleton] at h
        subst h
        exact ⟨isRPath_pair.mpr hc, rfl⟩
      · simp at h
    · rw [rpF_zero hL] at h
      simp at h
  | succ fuel ih =>
    intro a b L u h
    by_cases hL : L = 2
    · subst hL
      rw [rpF_two] at h
      split_ifs at h with hc
      · simp only [List.mem_singleton] at h
        subst h
        exact ⟨isRPath_pair.mpr hc, rfl⟩
      · simp at h
    · rw [rpF_succ hL] at h
      split_ifs at h with hs
      · simp only [List.mem_map, List.mem_filter, decide_eq_true_eq] at h
        obtain ⟨pe, ⟨hpe, hlen⟩, rfl⟩ := h
        have hs' := (of_mem_segs (mem_segEnum.mp hs)).2
        simp only at hs'
        obtain ⟨rest, hrest⟩ := faceVerts_eq_cons (pg := pg) (n := n) (show a ≤ b by omega)
        rw [slots, hrest] at hpe
        obtain ⟨pe0, h0, q, hq, rfl⟩ :=
          mem_foldl_sound _ (fun _ _ _ _ h => ih h) rest a _ pe hpe
        simp only [List.mem_singleton] at h0
        subst h0
        have hql : 0 < q.length := List.length_pos_of_ne_nil (joins_ne_nil hq)
        obtain ⟨t, rfl⟩ := List.head?_eq_some_iff.mp hq.head?
        have hlast : (a :: rest).getLast? = some b := by
          rw [← hrest]; exact faceVerts_getLast? (by simp only; omega)
        refine ⟨hq.isRPath rfl hlast, ?_⟩
        simp only [List.tail_cons, List.singleton_append, List.length_cons] at hlen ⊢
        omega
      · simp at h

/-- **Enumeration of region paths by the fold**: with fuel at least `b - a`, for
`2 ≤ L ≤ k + 1`, the members of `rpF pg n k fuel a b L` are exactly the region paths from `a`
to `b` with `L` entries. -/
theorem mem_rpF (hP : IsPolygon pg n) {fuel : ℕ} : ∀ {a b L : ℕ} {u : List ℕ},
    b - a ≤ fuel → Adj pg a b → a < b → 2 ≤ L → L ≤ k + 1 →
    (u ∈ rpF pg n k fuel a b L ↔ IsRPath pg a b u ∧ u.length = L) := by
  induction fuel with
  | zero => intro a b L u hf _ hab; omega
  | succ fuel ih =>
    intro a b L u hf hadj hab hL hLk
    refine ⟨sound_rpF, ?_⟩
    rintro ⟨hu, hl⟩
    by_cases hL2 : L = 2
    · subst hL2
      rw [rpF_two, ite_eq_left ⟨hab, hadj⟩, List.mem_singleton]
      match u, hu, hl with
      | [x, y], hu, _ =>
        simp only [IsRPath, List.head?_cons, Option.some.injEq, List.getLast?_cons_cons,
          List.getLast?_singleton] at hu
        rw [hu.1, hu.2.1]
    · rw [rpF_succ hL2]
      by_cases hs : (a, b) ∈ segEnum pg n
      · rw [ite_eq_left hs]
        have hs' := mem_segEnum.mp hs
        obtain ⟨rest, hrest⟩ := faceVerts_eq_cons (pg := pg) (n := n) hab.le
        rcases (hP.isRPath_iff_joins hs').mp hu with h | h
        · subst h
          simp at hl
          omega
        · rw [hrest] at h
          have hpw : (a :: rest).Pairwise (· < ·) := hrest ▸ faceVerts_pairwise
          have hmem := mem_foldl_complete (k := k) (rpF pg n k fuel) rest a hpw
            (by
              intro x z hxz L' hL' hL'k q hq hql
              rw [← hrest] at hxz
              have hlt := hP.infix_faceVerts_lt hs' hxz
              simp only at hlt
              exact (ih (by omega) (hP.adj_of_infix_faceVerts hs' hxz) hlt.2.1 hL' hL'k).mpr
                ⟨hq, hql⟩)
            [([a], 0)] ([a], 0) u (List.mem_singleton_self _) h (by simp only; omega)
          rw [slots, hrest]
          simp only [List.mem_map, List.mem_filter, decide_eq_true_eq]
          refine ⟨_, ⟨hmem, by simp only; omega⟩, ?_⟩
          obtain ⟨t, rfl⟩ := List.head?_eq_some_iff.mp h.head?
          rfl
      · exfalso
        have hb : b = a + 1 := by
          by_contra h
          exact hs (mem_segEnum.mpr (hP.mem_segs.mpr ⟨hadj, by simp only; omega⟩))
        subst hb
        obtain ⟨rfl, -⟩ := isRPath_side_iff.mp hu
        simp at hl
        omega

/-- **The fold lists each region path once.** -/
theorem rpF_nodup (fuel : ℕ) : ∀ (a b L : ℕ), (rpF pg n k fuel a b L).Nodup := by
  induction fuel with
  | zero =>
    intro a b L
    by_cases hL : L = 2
    · subst hL
      rw [rpF_two]
      split_ifs <;> simp
    · rw [rpF_zero hL]
      simp
  | succ fuel ih =>
    intro a b L
    by_cases hL : L = 2
    · subst hL
      rw [rpF_two]
      split_ifs <;> simp
    · rw [rpF_succ hL]
      split_ifs with hs
      · have hs' := (of_mem_segs (mem_segEnum.mp hs)).2
        simp only at hs'
        obtain ⟨rest, hrest⟩ := faceVerts_eq_cons (pg := pg) (n := n) (show a ≤ b by omega)
        rw [slots, hrest]
        refine List.Nodup.map_on ?_ ((nodup_foldl (k := k) _ (fun _ _ _ _ h => sound_rpF h)
          ih rest a _ (by simp) (by simp)).filter _)
        intro pe hpe pe' hpe' he
        simp only [List.mem_filter, decide_eq_true_eq] at hpe hpe'
        exact Prod.ext he (by omega)
      · simp

/-! ### Fuel and size -/

/-- The fold depends only on the slot paths of the slots it visits. -/
theorem foldl_extendParts_congr {rp rp' : ℕ → ℕ → ℕ → List (List ℕ)} :
    ∀ (ts : List (ℕ × ℕ)) (parts : List (List ℕ × ℕ)),
      (∀ t ∈ ts, ∀ L', rp t.1 t.2 L' = rp' t.1 t.2 L') →
      ts.foldl (fun parts t => extendParts k rp parts t.1 t.2) parts =
        ts.foldl (fun parts t => extendParts k rp' parts t.1 t.2) parts
  | [], _, _ => rfl
  | t :: ts, parts, h => by
    simp only [List.foldl_cons]
    have : extendParts k rp parts t.1 t.2 = extendParts k rp' parts t.1 t.2 := by
      simp only [extendParts, h t List.mem_cons_self]
    rw [this]
    exact foldl_extendParts_congr ts _ (fun t' ht' => h t' (List.mem_cons_of_mem _ ht'))

/-- **Enough fuel**: `rpF` does not depend on the fuel once it is at least `b - a`. -/
theorem rpF_fuel (hP : IsPolygon pg n) {fuel : ℕ} : ∀ {fuel' a b L : ℕ}, b - a ≤ fuel →
    b - a ≤ fuel' → rpF pg n k fuel a b L = rpF pg n k fuel' a b L := by
  induction fuel with
  | zero =>
    intro fuel' a b L _ _
    by_cases hL : L = 2
    · subst hL
      rw [rpF_two, rpF_two]
    · rw [rpF_zero hL]
      cases fuel' with
      | zero => rw [rpF_zero hL]
      | succ f' =>
        rw [rpF_succ hL, ite_eq_right]
        intro hs
        have := (of_mem_segs (mem_segEnum.mp hs)).2
        simp only at this
        omega
  | succ fuel ih =>
    intro fuel' a b L hf hf'
    by_cases hL : L = 2
    · subst hL
      rw [rpF_two, rpF_two]
    · cases fuel' with
      | zero =>
        rw [rpF_zero hL, rpF_succ hL, ite_eq_right]
        intro hs
        have := (of_mem_segs (mem_segEnum.mp hs)).2
        simp only at this
        omega
      | succ f' =>
        rw [rpF_succ hL, rpF_succ hL]
        split_ifs with hs
        · have hs' := mem_segEnum.mp hs
          rw [foldl_extendParts_congr]
          intro t ht L'
          have hlt := hP.infix_faceVerts_lt hs' (mem_slots.mp ht)
          simp only at hlt
          exact ih (by omega) (by omega)
        · rfl

/-- `rpF` is empty unless `(a, b)` is an edge with `a < b`. -/
theorem rpF_eq_nil {fuel a b L : ℕ} (h : ¬ (a < b ∧ Adj pg a b)) : rpF pg n k fuel a b L = [] := by
  by_cases hL : L = 2
  · subst hL
    rw [rpF_two, ite_eq_right h]
  · cases fuel with
    | zero => exact rpF_zero hL
    | succ fuel =>
      rw [rpF_succ hL, ite_eq_right]
      intro hs
      have := of_mem_segs (mem_segEnum.mp hs)
      exact h ⟨by simp only at this; omega, this.1⟩

/-- **Size of `rpF`**: at most `rpathBound L` region paths with `L` entries. -/
theorem length_rpF_le (hP : IsPolygon pg n) (fuel a b L : ℕ) :
    (rpF pg n k fuel a b L).length ≤ rpathBound L := by
  by_cases h : a < b ∧ Adj pg a b
  · refine le_trans (List.Subperm.length_le (List.subperm_of_subset (rpF_nodup fuel a b L) ?_))
      (hP.length_rpaths_le a b L)
    intro u hu
    exact (hP.mem_rpaths h.2 h.1).mpr (sound_rpF hu)
  · rw [rpF_eq_nil h]
    exact Nat.zero_le _

/-- The bound on the number of partial paths during the fold of `rpF`: each slot multiplies
their number by at most `k * rpathBound (k + 1)`, and adds at least one edge, so that after
`k` slots none is left. -/
def partsBound (k : ℕ) : ℕ := (k * rpathBound (k + 1) + 1) ^ k

/-- One step of the fold multiplies the number of partial paths by at most
`k * rpathBound (k + 1)`. -/
theorem length_extendParts_le (hP : IsPolygon pg n) (fuel x y : ℕ)
    (parts : List (List ℕ × ℕ)) :
    (extendParts k (rpF pg n k fuel) parts x y).length ≤
      parts.length * (k * rpathBound (k + 1)) := by
  simp only [extendParts, List.length_flatMap, List.length_map]
  apply sum_map_le_mul
  intro pe _
  calc _ ≤ (List.range' 2 (k - pe.2)).length * rpathBound (k + 1) := by
        apply sum_map_le_mul
        intro L' hL'
        rw [List.mem_range'_1] at hL'
        exact (length_rpF_le hP fuel x y L').trans (rpathBound_mono (by omega))
    _ ≤ k * rpathBound (k + 1) := by
        apply Nat.mul_le_mul_right
        simp

/-- The invariant of the fold: after `j` slots, every partial path has between `j` and `k`
edges, one entry more than edges, and there are at most `(k * rpathBound (k + 1)) ^ j` of
them. -/
theorem foldl_extendParts_inv (hP : IsPolygon pg n) (fuel : ℕ) :
    ∀ (ts : List (ℕ × ℕ)) (parts : List (List ℕ × ℕ)) (j : ℕ),
      (∀ pe ∈ parts, j ≤ pe.2 ∧ pe.2 ≤ k ∧ pe.1.length = pe.2 + 1) →
      parts.length ≤ (k * rpathBound (k + 1)) ^ j →
      (∀ pe ∈ ts.foldl (fun parts t => extendParts k (rpF pg n k fuel) parts t.1 t.2) parts,
          j + ts.length ≤ pe.2 ∧ pe.2 ≤ k ∧ pe.1.length = pe.2 + 1) ∧
        (ts.foldl (fun parts t => extendParts k (rpF pg n k fuel) parts t.1 t.2) parts).length ≤
          (k * rpathBound (k + 1)) ^ (j + ts.length)
  | [], parts, j, hinv, hlen => by
    simp only [List.foldl_nil, List.length_nil, Nat.add_zero]
    exact ⟨hinv, hlen⟩
  | t :: ts, parts, j, hinv, hlen => by
    simp only [List.foldl_cons, List.length_cons]
    have := foldl_extendParts_inv hP fuel ts (extendParts k (rpF pg n k fuel) parts t.1 t.2)
      (j + 1) ?_ ?_
    · rw [show j + (ts.length + 1) = j + 1 + ts.length by omega]
      exact this
    · intro pe hpe
      obtain ⟨pe0, h0, L', hL', q, hq, rfl⟩ := mem_extendParts.mp hpe
      have hql := (sound_rpF hq).2
      obtain ⟨h1, h2, h3⟩ := hinv pe0 h0
      simp only [List.length_append, List.length_tail]
      omega
    · calc _ ≤ parts.length * (k * rpathBound (k + 1)) := length_extendParts_le hP fuel _ _ parts
        _ ≤ (k * rpathBound (k + 1)) ^ j * (k * rpathBound (k + 1)) :=
          Nat.mul_le_mul_right _ hlen
        _ = _ := by ring

/-- **The intermediate lists of the fold in `rpF`**: from `[([a], 0)]`, over any list of
slots, at most `partsBound k` partial paths, each with at most `k` edges and one entry more
than edges. -/
theorem foldl_rpF_bound (hP : IsPolygon pg n) (fuel a : ℕ) (ts : List (ℕ × ℕ)) :
    (ts.foldl (fun parts t => extendParts k (rpF pg n k fuel) parts t.1 t.2)
        [([a], 0)]).length ≤ partsBound k ∧
      ∀ pe ∈ ts.foldl (fun parts t => extendParts k (rpF pg n k fuel) parts t.1 t.2) [([a], 0)],
        pe.2 ≤ k ∧ pe.1.length = pe.2 + 1 := by
  obtain ⟨hinv, hlen⟩ := foldl_extendParts_inv hP fuel ts [([a], 0)] 0 (by simp) (by simp)
  refine ⟨?_, fun pe hpe => (hinv pe hpe).2⟩
  by_cases hts : ts.length ≤ k
  · calc _ ≤ (k * rpathBound (k + 1)) ^ (0 + ts.length) := hlen
      _ ≤ (k * rpathBound (k + 1) + 1) ^ (0 + ts.length) := Nat.pow_le_pow_left (Nat.le_succ _) _
      _ ≤ partsBound k := Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
  · have : ts.foldl (fun parts t => extendParts k (rpF pg n k fuel) parts t.1 t.2) [([a], 0)] =
        [] := List.eq_nil_iff_forall_not_mem.mpr (fun pe hpe => by
          have := hinv pe hpe
          omega)
    rw [this]
    exact Nat.zero_le _

end STACS2027.Poly

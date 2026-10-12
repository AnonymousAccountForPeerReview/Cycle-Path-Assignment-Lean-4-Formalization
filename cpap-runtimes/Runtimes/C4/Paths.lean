module

public import Runtimes.C4.Peel
import Mathlib.Tactic

/-!
# Four-cycle listing: the inserted 2-paths

For any ranking `pos` injective on the vertices:

* `mem_outL`, `nodup_outL`; the index pairs `pairsOf` of a duplicate-free list: membership
  (`mem_pairsOf`), no repetitions (`nodup_pairsOf`), never both `(x, y)` and `(y, x)`
  (`pairsOf_asymm`), and one of them for any two distinct entries (`pairsOf_total`);
* **P1** `mem_ins`: `((x, y), z)` is inserted iff `x < y` and `z` is an admissible centre for
  `x, y` (`Adm`): every 2-path whose centre is not the latest of its vertices is inserted, and
  nothing else (the direction `mem_ins_imp` and the bounds `lt_of_mem_ins` hold for any
  ranking);
* **P2** `nodup_ins`: no 2-path is inserted twice;
* **P3** `numPaths_eq`: the number of inserted 2-paths is the sum computed by the machine's
  SIZE phase, `Σ_{v<N} Σ_{a<|out v|} (|out (out v)[a]| + a)` (per vertex: `length_wedges1`,
  `length_wedges2`, `numPaths_eq_sum`);
* **5.2** `numPaths_le_degen`: if every out-degree is at most `D`, at most `4 D |E|` 2-paths
  are inserted.
-/

@[expose] public section

namespace STACS2027.Runtimes.C4

open STACS2027 STACS2027.Algo Finset

variable {g : Graph} {pos : ℕ → ℕ}

/-! ### Out-lists -/

theorem mem_outL {v u : ℕ} : u ∈ outL g pos v ↔ u ∈ nb g v ∧ pos v < pos u := by
  simp [outL]

theorem nodup_outL (g : Graph) (pos : ℕ → ℕ) (v : ℕ) : (outL g pos v).Nodup :=
  (nodup_nb g v).filter _

theorem lt_of_mem_outL {v u : ℕ} (h : u ∈ outL g pos v) : u < numV g :=
  (nbOk g).lt v u (mem_outL.mp h).1

theorem length_outL_le (g : Graph) (pos : ℕ → ℕ) (v : ℕ) :
    (outL g pos v).length ≤ (nb g v).length := List.length_filter_le _ _

/-! ### Index pairs -/

theorem getD_eq_getElem' {l : List ℕ} {a : ℕ} (h : a < l.length) : l.getD a 0 = l[a] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem mem_pairsOf {l : List ℕ} {x y : ℕ} :
    (x, y) ∈ pairsOf l ↔ ∃ a b, a < b ∧ b < l.length ∧ l.getD a 0 = x ∧ l.getD b 0 = y := by
  simp only [pairsOf, List.mem_flatMap, List.mem_range, List.mem_map, List.mem_range'_1,
    Prod.mk.injEq]
  constructor
  · rintro ⟨a, ha, b, ⟨hb1, hb2⟩, hx, hy⟩
    exact ⟨a, b, by omega, by omega, hx, hy⟩
  · rintro ⟨a, b, hab, hb, hx, hy⟩
    exact ⟨a, by omega, b, ⟨by omega, by omega⟩, hx, hy⟩

theorem getD_inj {l : List ℕ} (hl : l.Nodup) {a b : ℕ} (ha : a < l.length) (hb : b < l.length)
    (h : l.getD a 0 = l.getD b 0) : a = b := by
  rw [getD_eq_getElem' ha, getD_eq_getElem' hb] at h
  exact (hl.getElem_inj_iff).mp h

theorem pairsOf_ne {l : List ℕ} (hl : l.Nodup) {x y : ℕ} (h : (x, y) ∈ pairsOf l) : x ≠ y := by
  obtain ⟨a, b, hab, hb, rfl, rfl⟩ := mem_pairsOf.mp h
  intro e
  have := getD_inj hl (by omega) hb e
  omega

theorem mem_of_mem_pairsOf {l : List ℕ} {x y : ℕ} (h : (x, y) ∈ pairsOf l) : x ∈ l ∧ y ∈ l := by
  obtain ⟨a, b, hab, hb, rfl, rfl⟩ := mem_pairsOf.mp h
  rw [getD_eq_getElem' (by omega), getD_eq_getElem' hb]
  exact ⟨List.getElem_mem _, List.getElem_mem _⟩

theorem pairsOf_asymm {l : List ℕ} (hl : l.Nodup) {x y : ℕ} (h : (x, y) ∈ pairsOf l) :
    (y, x) ∉ pairsOf l := by
  intro h'
  obtain ⟨a, b, hab, hb, rfl, rfl⟩ := mem_pairsOf.mp h
  obtain ⟨a', b', hab', hb', h1, h2⟩ := mem_pairsOf.mp h'
  have e1 := getD_inj hl (by omega) hb h1
  have e2 := getD_inj hl hb' (by omega) h2
  omega

theorem pairsOf_total {l : List ℕ} {x y : ℕ} (hx : x ∈ l) (hy : y ∈ l) (hxy : x ≠ y) :
    (x, y) ∈ pairsOf l ∨ (y, x) ∈ pairsOf l := by
  obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem hx
  obtain ⟨b, hb, rfl⟩ := List.getElem_of_mem hy
  have hab : a ≠ b := fun e => hxy (by subst e; rfl)
  rcases Nat.lt_or_gt_of_ne hab with h | h
  · exact Or.inl (mem_pairsOf.mpr ⟨a, b, h, hb, getD_eq_getElem' ha, getD_eq_getElem' hb⟩)
  · exact Or.inr (mem_pairsOf.mpr ⟨b, a, h, ha, getD_eq_getElem' hb, getD_eq_getElem' ha⟩)

theorem nodup_pairsOf {l : List ℕ} (hl : l.Nodup) : (pairsOf l).Nodup := by
  unfold pairsOf
  rw [List.nodup_flatMap]
  refine ⟨fun a ha => ?_, ?_⟩
  · refine List.Nodup.map_on ?_ List.nodup_range'
    intro b hb b' hb' h
    simp only [List.mem_range'_1] at hb hb'
    simp only [Prod.mk.injEq] at h
    exact getD_inj hl (by omega) (by omega) h.2
  · refine List.Pairwise.imp_of_mem ?_ List.nodup_range
    intro a a' ha ha' hne
    simp only [Function.onFun]
    intro p hp hp'
    simp only [List.mem_map, List.mem_range'_1] at hp hp'
    obtain ⟨b, -, rfl⟩ := hp
    obtain ⟨b', -, h⟩ := hp'
    simp only [Prod.mk.injEq] at h
    exact hne (getD_inj hl (List.mem_range.mp ha') (List.mem_range.mp ha) h.1).symm

/-! ### P1: the inserted entries -/

theorem key_eq {x y : ℕ} (h : x < y) : key x y = (x, y) := by
  simp [key, Nat.min_eq_left h.le, Nat.max_eq_right h.le]

theorem key_comm (x y : ℕ) : key x y = key y x := by
  simp [key, Nat.min_comm, Nat.max_comm]

theorem key_lt {x y : ℕ} (h : x ≠ y) : (key x y).1 < (key x y).2 := by
  simp only [key]; omega

theorem key_eq_iff {x y x' y' : ℕ} :
    key x y = key x' y' ↔ (x = x' ∧ y = y') ∨ (x = y' ∧ y = x') := by
  simp only [key, Prod.mk.injEq]; omega

theorem mem_wedges1 {v x z y : ℕ} :
    (x, z, y) ∈ wedges1 g pos v ↔ x = v ∧ z ∈ outL g pos v ∧ y ∈ outL g pos z := by
  simp only [wedges1, List.mem_flatMap, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨j, hj, k, hk, rfl, rfl, rfl⟩; exact ⟨rfl, hj, hk⟩
  · rintro ⟨rfl, hz, hy⟩; exact ⟨z, hz, y, hy, rfl, rfl, rfl⟩

theorem mem_wedges2 {v x z y : ℕ} :
    (x, z, y) ∈ wedges2 g pos v ↔ z = v ∧ (x, y) ∈ pairsOf (outL g pos v) := by
  simp only [wedges2, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨j, k⟩, h, rfl, rfl, rfl⟩; exact ⟨rfl, h⟩
  · rintro ⟨rfl, h⟩; exact ⟨(x, y), h, rfl, rfl, rfl⟩

theorem mem_ins_iff {e : (ℕ × ℕ) × ℕ} :
    e ∈ ins g pos ↔ ∃ v < numV g, ∃ w ∈ wedges g pos v, entry w = e := by
  simp [ins, List.mem_flatMap, List.mem_map]

/-- **P1**, first half (for any ranking): an inserted entry is an admissible 2-path keyed by
its ordered endpoints. -/
theorem mem_ins_imp {x y z : ℕ} (h : ((x, y), z) ∈ ins g pos) : x < y ∧ Adm g pos x z y := by
  have hok := nbOk g
  revert h
  rw [mem_ins_iff]
  rintro ⟨v, hv, ⟨a, c, b⟩, hw, he⟩
  simp only [entry, Prod.mk.injEq] at he
  obtain ⟨hk, rfl⟩ := he
  rcases List.mem_append.mp hw with hw | hw
  · obtain ⟨rfl, hc, hb⟩ := mem_wedges1.mp hw
    obtain ⟨hc1, hc2⟩ := mem_outL.mp hc
    obtain ⟨hb1, hb2⟩ := mem_outL.mp hb
    have hbN := hok.lt _ _ hb1
    have hne : a ≠ b := by rintro rfl; omega
    have := key_lt hne
    rw [hk] at this
    refine ⟨this, ?_⟩
    simp only [key, Prod.mk.injEq] at hk
    obtain ⟨rfl, rfl⟩ := hk
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · rw [Nat.min_eq_left h.le, Nat.max_eq_right h.le]
      exact ⟨by omega, by omega, by omega, hc1, hb1, by omega⟩
    · rw [Nat.min_eq_right h.le, Nat.max_eq_left h.le]
      exact ⟨by omega, by omega, by omega, hok.symm _ _ hb1, hok.symm _ _ hc1, by omega⟩
  · obtain ⟨rfl, hab⟩ := mem_wedges2.mp hw
    have hne := pairsOf_ne (nodup_outL g pos _) hab
    obtain ⟨ha, hb⟩ := mem_of_mem_pairsOf hab
    obtain ⟨ha1, ha2⟩ := mem_outL.mp ha
    obtain ⟨hb1, hb2⟩ := mem_outL.mp hb
    have haN := hok.lt _ _ ha1
    have hbN := hok.lt _ _ hb1
    have := key_lt hne
    rw [hk] at this
    refine ⟨this, ?_⟩
    simp only [key, Prod.mk.injEq] at hk
    obtain ⟨rfl, rfl⟩ := hk
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · rw [Nat.min_eq_left h.le, Nat.max_eq_right h.le]
      exact ⟨by omega, by omega, by omega, hok.symm _ _ ha1, hb1, by omega⟩
    · rw [Nat.min_eq_right h.le, Nat.max_eq_left h.le]
      exact ⟨by omega, by omega, by omega, hok.symm _ _ hb1, ha1, by omega⟩

/-- Bounds on the entries of the insertion list (for any ranking). -/
theorem lt_of_mem_ins {e : (ℕ × ℕ) × ℕ} (h : e ∈ ins g pos) :
    e.1.1 < e.1.2 ∧ e.1.2 < numV g ∧ e.2 < numV g := by
  obtain ⟨⟨x, y⟩, z⟩ := e
  obtain ⟨hxy, hx, hy, -, hz, -, -⟩ := mem_ins_imp h
  exact ⟨hxy, hy, (nbOk g).lt _ _ hz⟩

/-- **P1.** The inserted entries are exactly the admissible 2-paths, keyed by their ordered
endpoints. -/
theorem mem_ins (hpos : Set.InjOn pos (Set.Iio (numV g))) {x y z : ℕ} :
    ((x, y), z) ∈ ins g pos ↔ x < y ∧ Adm g pos x z y := by
  have hok := nbOk g
  constructor
  · exact mem_ins_imp
  · rintro ⟨hxy, hx, hy, hne, hz, hyz, hp⟩
    have hzN := hok.lt _ _ hz
    have hzx : z ≠ x := fun e => hok.noloop x (e ▸ hz)
    have hzy : z ≠ y := fun e => hok.noloop z (e ▸ hyz)
    have hxz : x ∈ nb g z := hok.symm _ _ hz
    have hzy' : z ∈ nb g y := hok.symm _ _ hyz
    have hpxy : pos x ≠ pos y := fun e => hne (hpos hx hy e)
    have hpzx : pos z ≠ pos x := fun e => hzx (hpos hzN hx e)
    have hpzy : pos z ≠ pos y := fun e => hzy (hpos hzN hy e)
    rw [mem_ins_iff]
    -- `lo`, `hi`: the endpoints ordered by position
    rcases Nat.lt_or_gt_of_ne hpxy with hxy' | hxy'
    · -- lo = x, hi = y
      rcases Nat.lt_or_gt_of_ne hpzx with hzx' | hzx'
      · -- type 2 at z
        refine ⟨z, hzN, ?_⟩
        have hxo : x ∈ outL g pos z := mem_outL.mpr ⟨hxz, by omega⟩
        have hyo : y ∈ outL g pos z := mem_outL.mpr ⟨hyz, by omega⟩
        rcases pairsOf_total hxo hyo hne with h | h
        · exact ⟨(x, z, y), List.mem_append_right _ (mem_wedges2.mpr ⟨rfl, h⟩),
            by simp [entry, key_eq hxy]⟩
        · exact ⟨(y, z, x), List.mem_append_right _ (mem_wedges2.mpr ⟨rfl, h⟩),
            by simp [entry, key_comm y x, key_eq hxy]⟩
      · -- type 1 at x
        refine ⟨x, hx, (x, z, y), List.mem_append_left _ (mem_wedges1.mpr ⟨rfl, ?_, ?_⟩),
          by simp [entry, key_eq hxy]⟩
        · exact mem_outL.mpr ⟨hz, hzx'⟩
        · exact mem_outL.mpr ⟨hyz, by omega⟩
    · -- lo = y, hi = x
      rcases Nat.lt_or_gt_of_ne hpzy with hzy'' | hzy''
      · refine ⟨z, hzN, ?_⟩
        have hxo : x ∈ outL g pos z := mem_outL.mpr ⟨hxz, by omega⟩
        have hyo : y ∈ outL g pos z := mem_outL.mpr ⟨hyz, by omega⟩
        rcases pairsOf_total hxo hyo hne with h | h
        · exact ⟨(x, z, y), List.mem_append_right _ (mem_wedges2.mpr ⟨rfl, h⟩),
            by simp [entry, key_eq hxy]⟩
        · exact ⟨(y, z, x), List.mem_append_right _ (mem_wedges2.mpr ⟨rfl, h⟩),
            by simp [entry, key_comm y x, key_eq hxy]⟩
      · refine ⟨y, hy, (y, z, x), List.mem_append_left _ (mem_wedges1.mpr ⟨rfl, ?_, ?_⟩),
          by simp [entry, key_comm y x, key_eq hxy]⟩
        · exact mem_outL.mpr ⟨hzy', hzy''⟩
        · exact mem_outL.mpr ⟨hxz, by omega⟩

/-! ### P2: no repetitions -/

/-- The vertex `v` generating an entry is the earliest of its three vertices. -/
def Gen (pos : ℕ → ℕ) (v : ℕ) (e : (ℕ × ℕ) × ℕ) : Prop :=
  (v = e.1.1 ∨ v = e.1.2 ∨ v = e.2) ∧ pos v ≤ pos e.1.1 ∧ pos v ≤ pos e.1.2 ∧ pos v ≤ pos e.2

theorem gen_of_mem {v : ℕ} {e : (ℕ × ℕ) × ℕ} (h : e ∈ (wedges g pos v).map entry) :
    Gen pos v e := by
  obtain ⟨⟨a, c, b⟩, hw, rfl⟩ := List.mem_map.mp h
  simp only [Gen, entry, key]
  rcases List.mem_append.mp hw with hw | hw
  · obtain ⟨rfl, hc, hb⟩ := mem_wedges1.mp hw
    have h1 := (mem_outL.mp hc).2
    have h2 := (mem_outL.mp hb).2
    refine ⟨?_, ?_, ?_, by omega⟩
    · rcases Nat.le_total a b with h | h
      · left; rw [Nat.min_eq_left h]
      · right; left; rw [Nat.max_eq_left h]
    · rcases Nat.le_total a b with h | h
      · rw [Nat.min_eq_left h]
      · rw [Nat.min_eq_right h]; omega
    · rcases Nat.le_total a b with h | h
      · rw [Nat.max_eq_right h]; omega
      · rw [Nat.max_eq_left h]
  · obtain ⟨rfl, hab⟩ := mem_wedges2.mp hw
    obtain ⟨ha, hb⟩ := mem_of_mem_pairsOf hab
    have h1 := (mem_outL.mp ha).2
    have h2 := (mem_outL.mp hb).2
    refine ⟨Or.inr (Or.inr rfl), ?_, ?_, le_rfl⟩
    · rcases Nat.le_total a b with h | h
      · rw [Nat.min_eq_left h]; omega
      · rw [Nat.min_eq_right h]; omega
    · rcases Nat.le_total a b with h | h
      · rw [Nat.max_eq_right h]; omega
      · rw [Nat.max_eq_left h]; omega

theorem gen_unique (hpos : Set.InjOn pos (Set.Iio (numV g))) {v v' : ℕ} (hv : v < numV g)
    (hv' : v' < numV g) {e : (ℕ × ℕ) × ℕ} (h : Gen pos v e) (h' : Gen pos v' e) : v = v' := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  obtain ⟨h0', h1', h2', h3'⟩ := h'
  apply hpos hv hv'
  rcases h0 with rfl | rfl | rfl <;> rcases h0' with rfl | rfl | rfl <;> omega

theorem nodup_wedges1_map (v : ℕ) : ((wedges1 g pos v).map entry).Nodup := by
  have hw : (wedges1 g pos v).map entry =
      (outL g pos v).flatMap fun j => (outL g pos j).map fun k => (key v k, j) := by
    simp only [wedges1, List.map_flatMap, List.map_map]; rfl
  rw [hw, List.nodup_flatMap]
  refine ⟨fun j hj => ?_, ?_⟩
  · refine List.Nodup.map_on ?_ (nodup_outL g pos j)
    intro k hk k' hk' h
    simp only [Prod.mk.injEq, key_eq_iff] at h
    have h1 := (mem_outL.mp hj).2
    have h2 := (mem_outL.mp hk).2
    have h3 := (mem_outL.mp hk').2
    rcases h.1 with ⟨-, h⟩ | ⟨h4, h5⟩
    · exact h
    · subst h4; omega
  · refine List.Pairwise.imp_of_mem ?_ (nodup_outL g pos v)
    intro j j' _ _ hne
    simp only [Function.onFun]
    intro p hp hp'
    simp only [List.mem_map] at hp hp'
    obtain ⟨k, -, rfl⟩ := hp
    obtain ⟨k', -, h⟩ := hp'
    simp only [Prod.mk.injEq] at h
    exact hne h.2.symm

theorem nodup_wedges2_map (v : ℕ) : ((wedges2 g pos v).map entry).Nodup := by
  have hw : (wedges2 g pos v).map entry =
      (pairsOf (outL g pos v)).map fun jk => (key jk.1 jk.2, v) := by
    simp [wedges2, entry]
  rw [hw]
  have hl := nodup_outL g pos v
  refine List.Nodup.map_on ?_ (nodup_pairsOf hl)
  rintro ⟨a, b⟩ hab ⟨a', b'⟩ hab' h
  simp only [Prod.mk.injEq, key_eq_iff] at h
  rcases h.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact absurd hab' (pairsOf_asymm hl hab)

theorem nodup_wedges_map (v : ℕ) : ((wedges g pos v).map entry).Nodup := by
  rw [wedges, List.map_append]
  refine List.nodup_append.mpr ⟨nodup_wedges1_map v, nodup_wedges2_map v, ?_⟩
  intro e h1 e' h2 he
  subst he
  obtain ⟨⟨a, c, b⟩, hw1, rfl⟩ := List.mem_map.mp h1
  obtain ⟨⟨a', c', b'⟩, hw2, h⟩ := List.mem_map.mp h2
  obtain ⟨rfl, hc, -⟩ := mem_wedges1.mp hw1
  obtain ⟨rfl, -⟩ := mem_wedges2.mp hw2
  simp only [entry, Prod.mk.injEq] at h
  have := (mem_outL.mp hc).2
  rw [h.2] at this
  omega

/-- **P2.** No 2-path is inserted twice. -/
theorem nodup_ins (hpos : Set.InjOn pos (Set.Iio (numV g))) : (ins g pos).Nodup := by
  unfold ins
  rw [List.nodup_flatMap]
  refine ⟨fun v _ => nodup_wedges_map v, ?_⟩
  refine List.Pairwise.imp_of_mem ?_ List.nodup_range
  intro v v' hv hv' hne
  simp only [Function.onFun]
  intro e h h'
  exact hne (gen_unique hpos (List.mem_range.mp hv) (List.mem_range.mp hv') (gen_of_mem h)
    (gen_of_mem h'))

/-! ### P3: the number of inserted 2-paths -/

theorem sum_map_range (n : ℕ) (f : ℕ → ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, sum_range_succ]; simp

theorem sum_map_eq_getD (l : List ℕ) (f : ℕ → ℕ) :
    (l.map f).sum = ∑ a ∈ range l.length, f (l.getD a 0) := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.map_cons, List.sum_cons, ih, List.length_cons, sum_range_succ']
    simp [Nat.add_comm]

theorem length_pairsOf (l : List ℕ) : (pairsOf l).length = ∑ a ∈ range l.length, a := by
  unfold pairsOf
  rw [List.length_flatMap, sum_map_range]
  simp only [List.length_map, List.length_range']
  rw [← sum_range_reflect]
  refine sum_congr rfl fun a ha => ?_
  simp only [mem_range] at ha
  omega

theorem length_wedges1 (g : Graph) (pos : ℕ → ℕ) (v : ℕ) :
    (wedges1 g pos v).length =
      ∑ a ∈ range (outL g pos v).length, (outL g pos ((outL g pos v).getD a 0)).length := by
  rw [wedges1, List.length_flatMap, sum_map_eq_getD]
  simp

theorem length_wedges2 (g : Graph) (pos : ℕ → ℕ) (v : ℕ) :
    (wedges2 g pos v).length = ∑ a ∈ range (outL g pos v).length, a := by
  rw [wedges2, List.length_map, length_pairsOf]

/-- The number of inserted 2-paths, vertex by vertex. -/
theorem numPaths_eq_sum (g : Graph) (pos : ℕ → ℕ) :
    numPaths g pos =
      ∑ v ∈ range (numV g), ((wedges1 g pos v).length + (wedges2 g pos v).length) := by
  unfold numPaths ins
  rw [List.length_flatMap, sum_map_range]
  simp [wedges]

/-- **P3.** The number of inserted 2-paths, as the SIZE phase sums it. -/
theorem numPaths_eq (g : Graph) (pos : ℕ → ℕ) :
    numPaths g pos = ∑ v ∈ range (numV g), ∑ a ∈ range (outL g pos v).length,
      ((outL g pos ((outL g pos v).getD a 0)).length + a) := by
  rw [numPaths_eq_sum]
  refine sum_congr rfl fun v _ => ?_
  rw [length_wedges1, length_wedges2, sum_add_distrib]

/-! ### 5.2: the bound by the out-degree -/

/-- **5.2.** If every out-degree is at most `D`, at most `4 D |E|` 2-paths are inserted. -/
theorem numPaths_le_degen (g : Graph) (pos : ℕ → ℕ) {D : ℕ}
    (hD : ∀ v < numV g, (outL g pos v).length ≤ D) :
    numPaths g pos ≤ 4 * (D * (idEdges g).length) := by
  rw [numPaths_eq]
  calc ∑ v ∈ range (numV g), ∑ a ∈ range (outL g pos v).length,
        ((outL g pos ((outL g pos v).getD a 0)).length + a)
      ≤ ∑ v ∈ range (numV g), ∑ _a ∈ range (outL g pos v).length, (D + D) := by
        refine sum_le_sum fun v hv => sum_le_sum fun a ha => ?_
        simp only [mem_range] at hv ha
        have hm : (outL g pos v).getD a 0 ∈ outL g pos v := by
          rw [getD_eq_getElem' ha]; exact List.getElem_mem _
        have h1 := hD _ (lt_of_mem_outL hm)
        have h2 := hD v hv
        omega
    _ = 2 * D * ∑ v ∈ range (numV g), (outL g pos v).length := by
        rw [mul_sum]; refine sum_congr rfl fun v _ => ?_
        simp only [sum_const, card_range, smul_eq_mul]; ring
    _ ≤ 2 * D * ∑ v ∈ range (numV g), (nb g v).length := by
        gcongr with v; exact length_outL_le g pos v
    _ = 4 * (D * (idEdges g).length) := by rw [sum_length_nb]; ring

end STACS2027.Runtimes.C4

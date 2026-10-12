module

public import Outerplanar.RAM.Poly2Bnd
import Mathlib.Tactic

/-!
# Phase P2 of the polygon solver: the grouped pass (keys of the triples)

The triples `(x, y, i)` of the pair scan (`trip`, stored as three arrays) have been sorted
stably by `x` (indices `ORDT`, group starts `OFFT`), and the segments of `segOrder` by their first
end (indices `ORDS`, group starts `OFFS`). For `x = 0, …, n - 1` the grouped pass

* marks the second ends `b` of the segments `(x, b)`: `STAMP[b] := x + 1`, `SVAL[b] :=` the index
  of `(x, b)` in `segOrder` (`stBody`; the stamps of earlier groups are at most `x`, so no
  clearing is needed, `StA`, `StB`);
* pushes, for every triple `(x, y, i)` of the group, its key: `SVAL[y]` if `STAMP[y] = x + 1`,
  else `|segOrder|` (`scBody`, `key_eq`).

The stream of keys is `(tripX …).map (keyOf …)` (`grpPass_spec`). Memory: `STAMP`, `SVAL`
(`n` cells each) from the free address `F₀`, then the keys (`|trip|` cells): the pass ends at
`F₀ + 2 n + |trip|`, and the triples are bounded (`HTB S`) for `S` at or above this end. Cost
`O(n + |segOrder| + |trip|)`. No table is indexed by pairs.
-/

@[expose] public section

namespace STACS2027.RAM.P2

open STACS2027.Poly P1

/-! ### Registers and program -/

/-- Base of the second entries `y` of the triples. -/
abbrev rGTY : ℕ := 162
/-- Base of the triple indices sorted by `x`. -/
abbrev rGOT : ℕ := 163
/-- Base of the group starts of the triples. -/
abbrev rGFT : ℕ := 164
/-- Base of the segment indices sorted by first end. -/
abbrev rGOS : ℕ := 165
/-- Base of the group starts of the segments. -/
abbrev rGFS : ℕ := 166
/-- Base of `STAMP`. -/
abbrev rGST : ℕ := 167
/-- Base of `SVAL`. -/
abbrev rGSV : ℕ := 168
/-- The group `x`. -/
abbrev rGX : ℕ := 169
/-- `x + 1`. -/
abbrev rGX1 : ℕ := 170
/-- The position in a group. -/
abbrev rGJ : ℕ := 171
/-- The start of a group. -/
abbrev rGLo : ℕ := 172
/-- The end of a group. -/
abbrev rGHi : ℕ := 173
/-- A segment or triple index. -/
abbrev rGT : ℕ := 174
/-- The second entry `y`. -/
abbrev rGY : ℕ := 175
/-- A value. -/
abbrev rGV : ℕ := 176

/-- Allocate `STAMP` and `SVAL` (`n` cells each). -/
def gpAlloc : Stmt := .seq (alloc rGST gPN) (alloc rGSV gPN)
/-- The range of the segments of the group `x`. -/
def gpHead : Stmt := .seq (addc rGX1 rGX 1) (.seq (ld rGLo rGFS rGX) (ld rGHi rGFS rGX1))
/-- Mark the segment `ORDS[j] = t`, `(x, y)`: `STAMP[y] := x + 1`, `SVAL[y] := t`. -/
def stBody : Stmt :=
  .seq (ld rGT rGOS rGJ) (.seq (ld rGY gSB rGT) (.seq (st rGST rGY rGX1) (st rGSV rGY rGT)))
/-- The range of the triples of the group `x`. -/
def gpMid : Stmt := .seq (ld rGLo rGFT rGX) (ld rGHi rGFT rGX1)
/-- The key of the triple `ORDT[j] = p`, `(x, y, i)`. -/
def scRead : Stmt :=
  .seq (ld rGT rGOT rGJ) (.seq (ld rGY rGTY rGT) (.seq (ld rGV rGST rGY)
    (ifEq rGV rGX1 (ld rGV rGSV rGY) (mov rGV gNS))))
/-- Push the key of the triple `ORDT[j]`. -/
def scBody : Stmt := .seq scRead (push rGV)
/-- One group. -/
def gpBody : Stmt :=
  .seq gpHead (.seq (forRange rGJ rGLo rGHi stBody) (.seq gpMid (forRange rGJ rGLo rGHi scBody)))
/-- **The grouped pass.** -/
def grpPass : Stmt := .seq gpAlloc (forUp rGX gPN gpBody)

variable {pg : Graph} {n k : ℕ}

/-! ### Abstract side -/

section Defs

variable (pg : Graph) (n k : ℕ)

/-- All triples. -/
abbrev tAll : List (ℕ × ℕ × ℕ) := trip pg n k (pool pg n k).length
/-- The first entries of the triples (the keys of their sort). -/
abbrev tkeys : List ℕ := (tAll pg n k).map Prod.fst
/-- The first ends of the segments (the keys of their sort). -/
abbrev skeys : List ℕ := (segOrder pg n).map Prod.fst
/-- The segments with first end `x` (indices in `segOrder`). -/
abbrev gS (x : ℕ) : List ℕ := bkt (skeys pg n) (skeys pg n).length x
/-- The triples with first entry `x` (indices in `tAll`). -/
abbrev gT (x : ℕ) : List ℕ := bkt (tkeys pg n k) (tkeys pg n k).length x
/-- The triples with first entry `x`. -/
abbrev tGrp (x : ℕ) : List (ℕ × ℕ × ℕ) := (tAll pg n k).filter fun p => p.1 = x

/-- The keys of the groups before `x` and of the first `r` triples of the group `x`. -/
def keysPre (x r : ℕ) : List ℕ :=
  ((List.range x).flatMap fun x' => (tGrp pg n k x').map (keyOf pg n)) ++
    ((tGrp pg n k x).take r).map (keyOf pg n)

end Defs

theorem keysPre_zero_succ (x : ℕ) :
    keysPre pg n k (x + 1) 0 = keysPre pg n k x (tGrp pg n k x).length := by
  rw [keysPre, keysPre, List.range_succ, List.flatMap_append, List.flatMap_singleton, List.take_zero,
    List.map_nil, List.append_nil, List.take_length]

theorem keysPre_full : keysPre pg n k n 0 = (tripX pg n k).map (keyOf pg n) := by
  simp [keysPre, tripX, List.map_flatMap]

theorem keysPre_succ (x : ℕ) {r : ℕ} (hr : r < (tGrp pg n k x).length) :
    keysPre pg n k x (r + 1) = keysPre pg n k x r ++ [keyOf pg n (tGrp pg n k x)[r]] := by
  rw [keysPre, keysPre, take_succ_eq hr, List.map_append, List.map_singleton, List.append_assoc]

theorem length_keysPre (x r : ℕ) (hr : r ≤ (tGrp pg n k x).length) :
    (keysPre pg n k x r).length = offOf (tkeys pg n k) x + r := by
  rw [keysPre, List.length_append, List.length_map, List.length_take, min_eq_left hr,
    List.length_flatMap]
  congr 1
  unfold offOf
  congr 1
  apply List.map_congr_left
  intro x' _
  rw [List.length_map, List.length_map, length_bkt_map (tAll pg n k) (0, 0, 0) Prod.fst x']

theorem gT_eq (x : ℕ) : gT pg n k x = bkt ((tAll pg n k).map Prod.fst) (tAll pg n k).length x := by
  simp only [gT, tkeys, List.length_map]

theorem length_gT (x : ℕ) : (gT pg n k x).length = (tGrp pg n k x).length := by
  rw [gT_eq, length_bkt_map (tAll pg n k) (0, 0, 0) Prod.fst x]

theorem length_gS (x : ℕ) : (gS pg n x).length = offOf (skeys pg n) (x + 1) - offOf (skeys pg n) x := by
  have := offOf_succ (skeys pg n) x
  dsimp only [gS] at *
  omega

theorem offOf_tkeys_succ (x : ℕ) :
    offOf (tkeys pg n k) (x + 1) = offOf (tkeys pg n k) x + (tGrp pg n k x).length := by
  rw [offOf_succ, ← length_gT]

/-- A segment of the group `x`. -/
theorem gS_mem {x t : ℕ} (ht : t ∈ gS pg n x) :
    t < (segOrder pg n).length ∧ ((segOrder pg n).getD t (0, 0)).1 = x := by
  rw [mem_bkt, List.length_map] at ht
  refine ⟨ht.1, ?_⟩
  rw [← ht.2, getD_map_lt ht.1 (0, 0)]

/-- The segments of the group `x` are listed once. -/
theorem gS_nodup (x : ℕ) : (gS pg n x).Nodup := List.nodup_range.filter _

/-- Every segment `(x, y)` is in the group `x`. -/
theorem mem_gS {x y : ℕ} (h : (x, y) ∈ segOrder pg n) :
    (segOrder pg n).idxOf (x, y) ∈ gS pg n x := by
  have hi := List.idxOf_lt_length_iff.mpr h
  rw [mem_bkt, List.length_map]
  refine ⟨hi, ?_⟩
  rw [getD_map_lt hi (0, 0), getD_of_lt hi, List.getElem_idxOf]

/-- Reading the segment group `x` off the sorted indices. -/
theorem read_gS {m : ℕ → ℕ} {b : ℕ} (h : Arr m b (bucketIdx (skeys pg n) n)) {x r : ℕ}
    (hx : x < n) (hr : r < (gS pg n x).length) :
    m (b + (offOf (skeys pg n) x + r)) = (gS pg n x)[r] := by
  have := arr_flatMap_get (bkt (skeys pg n) (skeys pg n).length) n h x hx
  rw [← Nat.add_assoc]
  exact this.get hr

/-- Reading the triple group `x` off the sorted indices. -/
theorem read_gT {m : ℕ → ℕ} {b : ℕ} (h : Arr m b (bucketIdx (tkeys pg n k) n)) {x r : ℕ}
    (hx : x < n) (hr : r < (gT pg n k x).length) :
    m (b + (offOf (tkeys pg n k) x + r)) = (gT pg n k x)[r] := by
  have := arr_flatMap_get (bkt (tkeys pg n k) (tkeys pg n k).length) n h x hx
  rw [← Nat.add_assoc]
  exact this.get hr

/-- The triple read through the group `x`. -/
theorem getD_gT {x r : ℕ} (hr : r < (gT pg n k x).length) (g : ℕ × ℕ × ℕ → ℕ) :
    ((tAll pg n k).map g).getD (gT pg n k x)[r] 0 =
      g ((tGrp pg n k x)[r]'(by rw [← length_gT]; exact hr)) := by
  have h := map_bkt (tAll pg n k) (0, 0, 0) Prod.fst g x
  rw [← gT_eq] at h
  have := List.getElem_of_eq h (by simpa using hr)
  simpa only [List.getElem_map] using this

/-- The triples have their first entry as group, entries below `n`. -/
theorem tGrp_mem {x : ℕ} {p : ℕ × ℕ × ℕ} (hp : p ∈ tGrp pg n k x) : p.1 = x ∧ p.2.1 < n := by
  rw [List.mem_filter] at hp
  exact ⟨by simpa using hp.2, (trip_lt le_rfl hp.1).2.1⟩

/-! ### The stamps -/

section Stamps

variable (pg : Graph) (n : ℕ)

/-- Every stamp is at most `x` or a stamp of the group `x` (`x + 1`, with its segment). -/
def StA (F₀ x : ℕ) (m : ℕ → ℕ) : Prop :=
  ∀ y, y < n → m (F₀ + y) ≤ x ∨
    (m (F₀ + y) = x + 1 ∧ (x, y) ∈ segOrder pg n ∧ m (F₀ + n + y) = (segOrder pg n).idxOf (x, y))

/-- The first `r` segments of the group `x` are stamped. -/
def StB (F₀ x r : ℕ) (m : ℕ → ℕ) : Prop :=
  ∀ t ∈ (gS pg n x).take r, m (F₀ + ((segOrder pg n).getD t (0, 0)).2) = x + 1 ∧
    m (F₀ + n + ((segOrder pg n).getD t (0, 0)).2) = t

end Stamps

/-- Before the group `x`: the stamps are at most `x`. -/
theorem stA_zero {F₀ x : ℕ} {m : ℕ → ℕ} (h : ∀ y, y < n → m (F₀ + y) ≤ x) : StA pg n F₀ x m :=
  fun y hy => Or.inl (h y hy)

theorem stB_zero (F₀ x : ℕ) (m : ℕ → ℕ) : StB pg n F₀ x 0 m := by simp [StB]

/-- After the group `x`: the stamps are at most `x + 1`. -/
theorem StA.le {F₀ x : ℕ} {m : ℕ → ℕ} (h : StA pg n F₀ x m) : ∀ y, y < n → m (F₀ + y) ≤ x + 1 :=
  fun y hy => by rcases h y hy with h | h <;> omega

theorem StA.upd {F₀ x a v : ℕ} {m : ℕ → ℕ} (h : StA pg n F₀ x m) (ha : F₀ + 2 * n ≤ a) :
    StA pg n F₀ x (RAM.upd m a v) := fun y hy => by
  rw [upd_ne _ _ (by omega), upd_ne _ _ (by omega)]; exact h y hy

theorem StB.upd {F₀ x r a v : ℕ} {m : ℕ → ℕ} (h : StB pg n F₀ x r m) (ha : F₀ + 2 * n ≤ a)
    (hlt : ∀ t ∈ (gS pg n x).take r, ((segOrder pg n).getD t (0, 0)).2 < n) :
    StB pg n F₀ x r (RAM.upd m a v) := fun t ht => by
  have := hlt t ht
  rw [upd_ne _ _ (by omega), upd_ne _ _ (by omega)]; exact h t ht

theorem snd_lt_of_gS {x t : ℕ} (ht : t ∈ gS pg n x) : ((segOrder pg n).getD t (0, 0)).2 < n := by
  have := (gS_mem ht).1
  rw [getD_of_lt this]
  exact (lt_of_mem_segOrder (List.getElem_mem this)).2

/-- **Stamping the segment `r` of the group `x`.** -/
theorem stamp_step {F₀ x r : ℕ} {m : ℕ → ℕ} (hA : StA pg n F₀ x m) (hB : StB pg n F₀ x r m)
    (hr : r < (gS pg n x).length) :
    StA pg n F₀ x (RAM.upd (RAM.upd m (F₀ + ((segOrder pg n).getD (gS pg n x)[r] (0, 0)).2) (x + 1))
        (F₀ + n + ((segOrder pg n).getD (gS pg n x)[r] (0, 0)).2) (gS pg n x)[r]) ∧
      StB pg n F₀ x (r + 1) (RAM.upd (RAM.upd m
        (F₀ + ((segOrder pg n).getD (gS pg n x)[r] (0, 0)).2) (x + 1))
        (F₀ + n + ((segOrder pg n).getD (gS pg n x)[r] (0, 0)).2) (gS pg n x)[r]) := by
  set t := (gS pg n x)[r] with htdef
  have htm : t ∈ gS pg n x := List.getElem_mem hr
  obtain ⟨htl, htx⟩ := gS_mem htm
  set y0 := ((segOrder pg n).getD t (0, 0)).2 with hy0
  have hy0n : y0 < n := snd_lt_of_gS htm
  have hseg : (segOrder pg n).getD t (0, 0) = (x, y0) := by rw [← htx]
  have hmem : (x, y0) ∈ segOrder pg n := by rw [← hseg, getD_of_lt htl]; exact List.getElem_mem _
  have hidx : (segOrder pg n).idxOf (x, y0) = t := by
    rw [← hseg, getD_of_lt htl, segOrder_nodup.idxOf_getElem]
  refine ⟨fun y hy => ?_, fun t' ht' => ?_⟩
  · by_cases hyy : y = y0
    · rw [hyy]
      right
      rw [upd_ne _ _ (show F₀ + y0 ≠ F₀ + n + y0 by omega), upd_same, upd_same]
      exact ⟨rfl, hmem, hidx.symm⟩
    · rw [upd_ne _ _ (show F₀ + y ≠ F₀ + n + y0 by omega),
        upd_ne _ _ (show F₀ + y ≠ F₀ + y0 by omega),
        upd_ne _ _ (show F₀ + n + y ≠ F₀ + n + y0 by omega),
        upd_ne _ _ (show F₀ + n + y ≠ F₀ + y0 by omega)]
      exact hA y hy
  · rw [take_succ_eq hr, List.mem_append, List.mem_singleton] at ht'
    rcases ht' with ht' | rfl
    · have ht'm : t' ∈ gS pg n x := List.mem_of_mem_take ht'
      have hne : t' ≠ t := by
        intro he
        rw [he] at ht'
        rw [List.mem_iff_getElem] at ht'
        obtain ⟨i, hi, hie⟩ := ht'
        simp only [List.length_take] at hi
        rw [List.getElem_take] at hie
        have := (gS_nodup (pg := pg) (n := n) x).getElem_inj_iff.mp hie
        omega
      have hy' : ((segOrder pg n).getD t' (0, 0)).2 ≠ y0 := by
        intro he
        obtain ⟨htl', htx'⟩ := gS_mem ht'm
        apply hne
        have h1 : (segOrder pg n).getD t' (0, 0) = (segOrder pg n).getD t (0, 0) :=
          Prod.ext (htx'.trans htx.symm) he
        rw [getD_of_lt htl', getD_of_lt htl] at h1
        exact segOrder_nodup.getElem_inj_iff.mp h1
      have hy'n := snd_lt_of_gS ht'm
      set y' := ((segOrder pg n).getD t' (0, 0)).2
      rw [upd_ne _ _ (show F₀ + y' ≠ F₀ + n + y0 by omega),
        upd_ne _ _ (show F₀ + y' ≠ F₀ + y0 by omega),
        upd_ne _ _ (show F₀ + n + y' ≠ F₀ + n + y0 by omega),
        upd_ne _ _ (show F₀ + n + y' ≠ F₀ + y0 by omega)]
      exact hB t' ht'
    · rw [upd_ne _ _ (show F₀ + y0 ≠ F₀ + n + y0 by omega), upd_same, upd_same]
      exact ⟨rfl, rfl⟩

/-- **The key of a triple of the group `x`**, read off the stamps of the group. -/
theorem key_eq {F₀ x : ℕ} {m : ℕ → ℕ} (hA : StA pg n F₀ x m)
    (hB : StB pg n F₀ x (gS pg n x).length m) {y : ℕ} (hy : y < n) (i : ℕ) :
    (if m (F₀ + y) = x + 1 then m (F₀ + n + y) else (segOrder pg n).length) =
      keyOf pg n (x, y, i) := by
  unfold keyOf
  simp only
  by_cases hs : (x, y) ∈ segOrder pg n
  · obtain ⟨h1, h2⟩ := hB _ (by rw [List.take_length]; exact mem_gS hs)
    have hg : (segOrder pg n).getD ((segOrder pg n).idxOf (x, y)) (0, 0) = (x, y) := by
      rw [getD_of_lt (List.idxOf_lt_length_iff.mpr hs), List.getElem_idxOf]
    rw [hg] at h1 h2
    rw [ite_eq_left h1, ite_eq_left hs, h2]
  · rw [ite_eq_right hs]
    rcases hA y hy with h | ⟨_, h, _⟩
    · rw [ite_eq_right (by omega)]
    · exact absurd h hs

/-! ### The state of the pass -/

/-- The constant registers and data of the grouped pass (data in the memory `m₀` before the pass,
below `F₀`). -/
@[mk_iff] structure GPre (pg : Graph) (n k F₀ : ℕ) (m₀ : ℕ → ℕ) (c : Config) : Prop where
  pn : c.reg gPN = n
  ns : c.reg gNS = (segOrder pg n).length
  ty : Arr m₀ (c.reg rGTY) ((tAll pg n k).map (·.2.1))
  bty : c.reg rGTY + (tAll pg n k).length ≤ F₀
  ot : Arr m₀ (c.reg rGOT) (bucketIdx (tkeys pg n k) n)
  bot : c.reg rGOT + (tAll pg n k).length ≤ F₀
  ft : Tab m₀ (c.reg rGFT) (n + 1) (offOf (tkeys pg n k))
  bft : c.reg rGFT + (n + 1) ≤ F₀
  sb : Arr m₀ (c.reg gSB) ((segOrder pg n).map Prod.snd)
  bsb : c.reg gSB + (segOrder pg n).length ≤ F₀
  os : Arr m₀ (c.reg rGOS) (bucketIdx (skeys pg n) n)
  bos : c.reg rGOS + (segOrder pg n).length ≤ F₀
  fs : Tab m₀ (c.reg rGFS) (n + 1) (offOf (skeys pg n))
  bfs : c.reg rGFS + (n + 1) ≤ F₀

/-- The state of the pass: the keys `keys` pushed (from `F₀ + 2 n`), the stamps (`STAMP` at `F₀`,
`SVAL` at `F₀ + n`) satisfying `Q`. -/
def GSt (pg : Graph) (n k F₀ : ℕ) (m₀ : ℕ → ℕ) (keys : List ℕ) (Q : (ℕ → ℕ) → Prop)
    (c : Config) : Prop :=
  (GPre pg n k F₀ m₀ c ∧ c.reg rGST = F₀ ∧ c.reg rGSV = F₀ + n) ∧ SameOn (· < F₀) m₀ c.mem ∧
    Strm (F₀ + 2 * n) keys c ∧ Q c.mem

theorem GSt.indep (F₀ : ℕ) (m₀ : ℕ → ℕ) (keys : List ℕ) (Q : (ℕ → ℕ) → Prop) :
    Indep [rT, rGX1, rGJ, rGLo, rGHi, rGT, rGY, rGV] (GSt pg n k F₀ m₀ keys Q) := by
  indep [GSt, gPre_iff, Strm]

theorem GSt.rd {F₀ : ℕ} {m₀ : ℕ → ℕ} {keys : List ℕ} {Q : (ℕ → ℕ) → Prop} {c : Config}
    (h : GSt pg n k F₀ m₀ keys Q c) {a : ℕ} (ha : a < F₀) : c.mem a = m₀ a := h.2.1 a ha

/-- The offset of the segment group `x`. -/
abbrev offS (pg : Graph) (n x : ℕ) : ℕ := offOf (skeys pg n) x
/-- The offset of the triple group `x`. -/
abbrev offT (pg : Graph) (n k x : ℕ) : ℕ := offOf (tkeys pg n k) x

/-- The invariant of the groups, before the group `x`. -/
def OInv (pg : Graph) (n k F₀ : ℕ) (m₀ : ℕ → ℕ) (x : ℕ) (c : Config) : Prop :=
  GSt pg n k F₀ m₀ (keysPre pg n k x 0) (fun m => ∀ y, y < n → m (F₀ + y) ≤ x) c

/-- The invariant of the marks of the group `x`, at the position `j`. -/
def SInv (pg : Graph) (n k F₀ : ℕ) (m₀ : ℕ → ℕ) (x j : ℕ) (c : Config) : Prop :=
  GSt pg n k F₀ m₀ (keysPre pg n k x 0)
    (fun m => StA pg n F₀ x m ∧ StB pg n F₀ x (j - offS pg n x) m) c ∧
    c.reg rGX = x ∧ c.reg rGX1 = x + 1

/-- The invariant of the keys of the group `x`, at the position `j`. -/
def KInv (pg : Graph) (n k F₀ : ℕ) (m₀ : ℕ → ℕ) (x j : ℕ) (c : Config) : Prop :=
  GSt pg n k F₀ m₀ (keysPre pg n k x (j - offT pg n k x))
    (fun m => StA pg n F₀ x m ∧ StB pg n F₀ x (gS pg n x).length m) c ∧
    c.reg rGX = x ∧ c.reg rGX1 = x + 1

/-- Stores into the marks keep the state of the pass (with new marks). -/
theorem GSt.stamp {F₀ : ℕ} {m₀ : ℕ → ℕ} {keys : List ℕ} {Q Q' : (ℕ → ℕ) → Prop} {c c' : Config}
    (h : GSt pg n k F₀ m₀ keys Q c) (hreg : ∀ r, r ∉ [rT, rGT, rGY] → c'.reg r = c.reg r)
    {y0 v1 v2 : ℕ} (hy0 : y0 < n)
    (hmem : c'.mem = RAM.upd (RAM.upd c.mem (F₀ + y0) v1) (F₀ + n + y0) v2)
    (hout : c'.out = c.out)
    (hQ : Q' (RAM.upd (RAM.upd c.mem (F₀ + y0) v1) (F₀ + n + y0) v2)) :
    GSt pg n k F₀ m₀ keys Q' c' := by
  have _ := hout
  obtain ⟨hG, hSm, ⟨hA, hF, hZ⟩, -⟩ := h
  refine ⟨(show RegIndep [rT, rGT, rGY] (fun c => GPre pg n k F₀ m₀ c ∧ c.reg rGST = F₀ ∧
    c.reg rGSV = F₀ + n) by indep [gPre_iff]) c c' hreg hG, ?_, ⟨?_, ?_, ?_⟩, by rw [hmem]; exact hQ⟩
  · rw [hmem]; exact (hSm.upd_of_ge (by omega) _).upd_of_ge (by omega) _
  · rw [hmem]; exact (hA.upd_of_disjoint (by omega)).upd_of_disjoint (by omega)
  · rw [hreg _ (by decide)]; exact hF
  · rw [hmem, hreg _ (by decide)]; exact (hZ.upd (by omega)).upd (by omega)

/-- The segment groups end within `|segOrder|`. -/
theorem offS_le {x : ℕ} (hx : x ≤ n) : offS pg n x ≤ (segOrder pg n).length := by
  have h1 := offOf_mono (skeys pg n) hx
  rw [offOf_eq_length _ n (by
    intro z hz; obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hz; have := lt_of_mem_segOrder hs; omega),
    List.length_map] at h1
  exact h1

/-- The triple groups end within `|trip|`. -/
theorem offT_le {x : ℕ} (hx : x ≤ n) : offT pg n k x ≤ (tAll pg n k).length := by
  have h1 := offOf_mono (tkeys pg n k) hx
  rw [offOf_eq_length _ n (by
    intro z hz; obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hz; exact (trip_lt le_rfl hp).1),
    List.length_map] at h1
  exact h1

theorem stBody_run {c : Config} {t y0 : ℕ} (ht : c.mem (c.reg rGOS + c.reg rGJ) = t)
    (hy : c.mem (c.reg gSB + t) = y0) :
    (RAM.run stBody c).mem = RAM.upd (RAM.upd c.mem (c.reg rGST + y0) (c.reg rGX1))
      (c.reg rGSV + y0) t ∧ (∀ r, r ∉ [rT, rGT, rGY] → (RAM.run stBody c).reg r = c.reg r) ∧
      (RAM.run stBody c).out = c.out := by
  have hw : ∀ r ∈ wregs stBody, r ∈ [rT, rGT, rGY] := by decide
  refine ⟨?_, fun r hr => run_reg_of_not_mem (by decide) (fun h => hr (hw r h)) c,
    run_out_of_writes (by decide) (by decide) c⟩
  simp +decide only [stBody, run_seq', run_ld, run_st (show rGX1 ≠ rT by decide),
    run_st (show rGT ≠ rT by decide), setReg_reg, ↓reduceIte, setReg_mem, setMem_mem_upd,
    setMem_reg, ht, hy]

theorem stBody_spec {S : ℕ} (F₀ : ℕ) (m₀ : ℕ → ℕ) (hSz : F₀ + 2 * n + (tAll pg n k).length ≤ S)
    {x : ℕ} (hx : x < n) (j : ℕ) (hj1 : offS pg n x ≤ j) (hj2 : j < offS pg n (x + 1)) :
    HTB S stBody (fun c => SInv pg n k F₀ m₀ x j c ∧ c.reg rGJ = j ∧ c.reg rGHi = offS pg n (x + 1))
      (fun c => SInv pg n k F₀ m₀ x (j + 1) c ∧ c.reg rGJ = j ∧
        c.reg rGHi = offS pg n (x + 1)) 10 := by
  refine HTB.run_le (by decide) (by decide) fun c ⟨⟨hS, hX, hX1⟩, hJ, hH⟩ => ?_
  have hgl := length_gS (pg := pg) (n := n) x
  have hle := offS_le (pg := pg) (n := n) (show x + 1 ≤ n by omega)
  obtain ⟨r, rfl⟩ : ∃ r, j = offS pg n x + r := ⟨j - offS pg n x, by omega⟩
  have hr : r < (gS pg n x).length := by dsimp only [offS] at *; omega
  have hG := hS.1.1
  have hB := hS.2.2.2.2
  have hA := hS.2.2.2.1
  rw [show offS pg n x + r - offS pg n x = r by omega] at hB
  set t := (gS pg n x)[r] with htdef
  have htm : t ∈ gS pg n x := List.getElem_mem hr
  have htl := (gS_mem htm).1
  have hy0n : ((segOrder pg n).getD t (0, 0)).2 < n := snd_lt_of_gS htm
  have e1 : c.mem (c.reg rGOS + c.reg rGJ) = t := by
    rw [hJ, hS.rd (by have := hG.bos; omega), read_gS hG.os hx hr]
  have e2 : c.mem (c.reg gSB + t) = ((segOrder pg n).getD t (0, 0)).2 := by
    rw [hS.rd (by have := hG.bsb; omega), hG.sb.getD (by simpa using htl),
      getD_map_lt htl (0, 0)]
  have := hG.bos; have := hG.bsb
  refine ⟨by addr_ok [stBody, e1, e2, hS.1.2.1, hS.1.2.2], ?_⟩
  obtain ⟨hmem, hreg, hout⟩ := stBody_run e1 e2
  rw [hS.1.2.1, hS.1.2.2, hX1] at hmem
  have hst := stamp_step hA hB hr
  refine ⟨⟨hS.stamp hreg hy0n hmem hout ⟨hst.1, ?_⟩, by rw [hreg _ (by decide), hX],
    by rw [hreg _ (by decide), hX1]⟩, by rw [hreg _ (by decide), hJ], by rw [hreg _ (by decide), hH]⟩
  rw [show offS pg n x + r + 1 - offS pg n x = r + 1 by omega]
  exact hst.2

/-! ### The keys of the triples of a group -/

theorem scRead_run {c : Config} {p y : ℕ} (hp : c.mem (c.reg rGOT + c.reg rGJ) = p)
    (hy : c.mem (c.reg rGTY + p) = y) :
    (RAM.run scRead c).reg rGV = (if c.mem (c.reg rGST + y) = c.reg rGX1 then
      c.mem (c.reg rGSV + y) else c.reg gNS) ∧ Agree [rT, rGT, rGY, rGV] c (RAM.run scRead c) := by
  refine ⟨?_, agree_run (by decide) rfl rfl (by decide) c⟩
  simp only [scRead, run_seq', run_ld]
  rw [run_ifEq (by decide) (by decide)]
  simp +decide only [setReg_reg, ↓reduceIte, setReg_mem, hp, hy]
  split_ifs <;> simp +decide [run_mov]

theorem scBody_spec {S : ℕ} (F₀ : ℕ) (m₀ : ℕ → ℕ) (hSz : F₀ + 2 * n + (tAll pg n k).length ≤ S)
    {x : ℕ} (hx : x < n) (j : ℕ) (hj1 : offT pg n k x ≤ j) (hj2 : j < offT pg n k (x + 1)) :
    HTB S scBody
      (fun c => KInv pg n k F₀ m₀ x j c ∧ c.reg rGJ = j ∧ c.reg rGHi = offT pg n k (x + 1))
      (fun c => KInv pg n k F₀ m₀ x (j + 1) c ∧ c.reg rGJ = j ∧
        c.reg rGHi = offT pg n k (x + 1)) 20 := by
  refine HTB.run_le (by decide) (by decide) fun c ⟨⟨hS, hX, hX1⟩, hJ, hH⟩ => ?_
  have hgl := offOf_tkeys_succ (pg := pg) (n := n) (k := k) x
  have hle := offT_le (pg := pg) (n := n) (k := k) (show x + 1 ≤ n by omega)
  obtain ⟨r, rfl⟩ : ∃ r, j = offT pg n k x + r := ⟨j - offT pg n k x, by omega⟩
  have hr : r < (tGrp pg n k x).length := by dsimp only [offT] at *; omega
  have hr' : r < (gT pg n k x).length := by rw [length_gT]; exact hr
  have hG := hS.1.1
  rw [show offT pg n k x + r - offT pg n k x = r by omega] at hS
  set p := (gT pg n k x)[r] with hpdef
  have hpl : p < (tAll pg n k).length := by
    have := (mem_bkt.mp (List.getElem_mem hr')).1
    simpa using this
  obtain ⟨y, hydef⟩ : ∃ y, ((tGrp pg n k x)[r]).2.1 = y := ⟨_, rfl⟩
  have hyn : y < n := hydef ▸ (tGrp_mem (List.getElem_mem hr)).2
  have e1 : c.mem (c.reg rGOT + c.reg rGJ) = p := by
    rw [hJ, hS.rd (by have := hG.bot; omega), read_gT hG.ot hx hr']
  have e2 : c.mem (c.reg rGTY + p) = y := by
    rw [hS.rd (by have := hG.bty; omega), hG.ty.getD (by simpa using hpl), getD_gT hr', hydef]
  have hA₁ : AddrOK S scRead c := by
    have := hG.bot; have := hG.bty
    addr_ok [scRead, e1, e2, hS.1.2.1, hS.1.2.2]
  obtain ⟨hv, hag⟩ := scRead_run e1 e2
  rw [hS.1.2.1, hS.1.2.2, hX1, hG.ns] at hv
  have hkey := key_eq hS.2.2.2.1 hS.2.2.2.2 hyn ((tGrp pg n k x)[r]).2.2
  rw [← hv] at hkey
  have hS₁ : GSt pg n k F₀ m₀ (keysPre pg n k x r)
      (fun m => StA pg n F₀ x m ∧ StB pg n F₀ x (gS pg n x).length m) (RAM.run scRead c) :=
    ((GSt.indep F₀ m₀ _ _).mono (by decide)) c _ hag hS
  -- the push
  have hrun : RAM.run scBody c = RAM.run (push rGV) (RAM.run scRead c) := rfl
  obtain ⟨⟨hG₁, hst₁, hsv₁⟩, hSm₁, hStr₁, hQ₁⟩ := hS₁
  have hp1 := hStr₁.2.1
  have hlk := length_keysPre (pg := pg) (n := n) (k := k) x r hr.le
  refine ⟨AddrOK.seq (s := scRead) (t := push rGV) hA₁ ((addrOK_push _ _).mpr (by
    rw [hp1, hlk]; dsimp only [offT] at *; omega)), ?_⟩
  have hStr₂ := push_strm hStr₁ rGV
  rw [hkey] at hStr₂
  have hpk : keyOf pg n (x, y, ((tGrp pg n k x)[r]).2.2) = keyOf pg n (tGrp pg n k x)[r] := by
    have hq : (tGrp pg n k x)[r] = (x, y, ((tGrp pg n k x)[r]).2.2) :=
      Prod.ext (tGrp_mem (List.getElem_mem hr)).1 (Prod.ext hydef rfl)
    exact congrArg (keyOf pg n) hq.symm
  rw [hpk, ← keysPre_succ x hr] at hStr₂
  have hreg : ∀ r', r' ≠ rT → r' ≠ rFREE →
      (RAM.run scBody c).reg r' = (RAM.run scRead c).reg r' := fun r' h1 h2 => by
    rw [hrun]; exact push_reg _ _ h1 h2
  have hmem : (RAM.run scBody c).mem = RAM.upd (RAM.run scRead c).mem
      ((RAM.run scRead c).reg rFREE) ((RAM.run scRead c).reg rGV) := by
    rw [hrun, run_push]; simp
  have hF₀ : F₀ + 2 * n ≤ (RAM.run scRead c).reg rFREE := by omega
  unfold KInv
  rw [show offT pg n k x + r + 1 - offT pg n k x = r + 1 by omega]
  refine ⟨⟨⟨⟨?_, ?_, ?_⟩, ?_, by rw [hrun]; exact hStr₂, ?_⟩, ?_, ?_⟩, ?_, ?_⟩
  · exact (show RegIndep [rT, rFREE] (GPre pg n k F₀ m₀) by indep [gPre_iff])
      _ _ (fun r' hr' => hreg r' (by simp at hr'; exact hr'.1) (by simp at hr'; exact hr'.2)) hG₁
  · rw [hreg _ (by decide) (by decide), hst₁]
  · rw [hreg _ (by decide) (by decide), hsv₁]
  · rw [hmem]; exact hSm₁.upd_of_ge (by omega) _
  · rw [hmem]
    exact ⟨hQ₁.1.upd hF₀, hQ₁.2.upd hF₀ fun t ht => snd_lt_of_gS (List.mem_of_mem_take ht)⟩
  · rw [hreg _ (by decide) (by decide), hag.reg _ (by decide), hX]
  · rw [hreg _ (by decide) (by decide), hag.reg _ (by decide), hX1]
  · rw [hreg _ (by decide) (by decide), hag.reg _ (by decide), hJ]
  · rw [hreg _ (by decide) (by decide), hag.reg _ (by decide), hH]

/-! ### One group and the pass -/

/-- The bound of the group with `a` segments and `b` triples. -/
def tGp (a b : ℕ) : ℕ := a * 14 + b * 24 + 30

theorem gpBody_spec {S : ℕ} (F₀ : ℕ) (m₀ : ℕ → ℕ) (hSz : F₀ + 2 * n + (tAll pg n k).length ≤ S)
    {x : ℕ} (hx : x < n) :
    HTB S gpBody (fun c => OInv pg n k F₀ m₀ x c ∧ c.reg rGX = x ∧ c.reg gPN = n)
      (fun c => OInv pg n k F₀ m₀ (x + 1) c ∧ c.reg rGX = x ∧ c.reg gPN = n)
      (tGp (gS pg n x).length (tGrp pg n k x).length) := by
  have hSs := offOf_succ (skeys pg n) x
  have hTs := offOf_tkeys_succ (pg := pg) (n := n) (k := k) x
  -- the range of the segments of the group
  have h₁ : HTB S gpHead (fun c => OInv pg n k F₀ m₀ x c ∧ c.reg rGX = x ∧ c.reg gPN = n)
      (fun c => SInv pg n k F₀ m₀ x (offS pg n x) c ∧ c.reg rGLo = offS pg n x ∧
        c.reg rGHi = offS pg n (x + 1) ∧ offS pg n x ≤ offS pg n (x + 1)) 6 := by
    refine HTB.run_le (by decide) (by decide) fun c ⟨hO, hX, hN⟩ => ?_
    have hG := hO.1.1
    have := hG.bfs
    refine ⟨by addr_ok [gpHead, hX], ?_⟩
    have hag : Agree [rT, rGX1, rGLo, rGHi] c (RAM.run gpHead c) :=
      agree_run (by decide) rfl rfl (by decide) c
    have e1 : c.mem (c.reg rGFS + x) = offS pg n x := by
      rw [hO.rd (by have := hG.bfs; omega), hG.fs.get (by omega)]
    have e2 : c.mem (c.reg rGFS + (x + 1)) = offS pg n (x + 1) := by
      rw [hO.rd (by have := hG.bfs; omega), hG.fs.get (by omega)]
    have hO' := ((GSt.indep (pg := pg) (n := n) (k := k) F₀ m₀ _ _).mono (by decide)) c _ hag hO
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, by dsimp only [offS]; omega⟩
    · obtain ⟨h1, h2, h3, h4⟩ := hO'
      exact ⟨h1, h2, h3, stA_zero h4, by rw [Nat.sub_self]; exact stB_zero _ _ _⟩
    · rw [hag.reg _ (by decide), hX]
    all_goals simp +decide only [gpHead, run_seq', run_ld, run_addc (show rGX ≠ rT by decide),
      setReg_reg, ↓reduceIte, setReg_mem, hX, e1, e2]
  have h₂ := HTB.forRange (S := S) (i := rGJ) (a := rGLo) (n := rGHi) (A := offS pg n x)
    (N := offS pg n (x + 1)) (body := stBody) (SInv pg n k F₀ m₀ x) (fun _ => 10)
    (by decide) (by decide) (by decide) (by decide)
    (fun j => by unfold SInv; exact ((GSt.indep F₀ m₀ _ _).mono (by decide)).and (by indep))
    (fun j hj1 hj2 => stBody_spec F₀ m₀ hSz hx j hj1 hj2)
  -- the range of the triples of the group
  have h₃ : HTB S gpMid (fun c => SInv pg n k F₀ m₀ x (offS pg n (x + 1)) c ∧
        c.reg rGJ = offS pg n (x + 1) ∧ c.reg rGHi = offS pg n (x + 1))
      (fun c => KInv pg n k F₀ m₀ x (offT pg n k x) c ∧ c.reg rGLo = offT pg n k x ∧
        c.reg rGHi = offT pg n k (x + 1) ∧ offT pg n k x ≤ offT pg n k (x + 1)) 4 := by
    refine HTB.run_le (by decide) (by decide) fun c ⟨⟨hS, hX, hX1⟩, _, _⟩ => ?_
    have hG := hS.1.1
    have := hG.bft
    refine ⟨by addr_ok [gpMid, hX, hX1], ?_⟩
    have hag : Agree [rT, rGLo, rGHi] c (RAM.run gpMid c) :=
      agree_run (by decide) rfl rfl (by decide) c
    have e1 : c.mem (c.reg rGFT + x) = offT pg n k x := by
      rw [hS.rd (by have := hG.bft; omega), hG.ft.get (by omega)]
    have e2 : c.mem (c.reg rGFT + (x + 1)) = offT pg n k (x + 1) := by
      rw [hS.rd (by have := hG.bft; omega), hG.ft.get (by omega)]
    have hS' := ((GSt.indep (pg := pg) (n := n) (k := k) F₀ m₀ _ _).mono (by decide)) c _ hag hS
    refine ⟨⟨?_, by rw [hag.reg _ (by decide), hX], by rw [hag.reg _ (by decide), hX1]⟩, ?_, ?_,
      by dsimp only [offT]; omega⟩
    · obtain ⟨h1, h2, h3, h4, h5⟩ := hS'
      rw [Nat.sub_self]
      refine ⟨h1, h2, h3, h4, ?_⟩
      rw [length_gS]
      exact h5
    all_goals simp +decide only [gpMid, run_seq', run_ld, setReg_reg, ↓reduceIte, setReg_mem, hX,
      hX1, e1, e2]
  have h₄ := HTB.forRange (S := S) (i := rGJ) (a := rGLo) (n := rGHi) (A := offT pg n k x)
    (N := offT pg n k (x + 1)) (body := scBody) (KInv pg n k F₀ m₀ x) (fun _ => 20)
    (by decide) (by decide) (by decide) (by decide)
    (fun j => by unfold KInv; exact ((GSt.indep F₀ m₀ _ _).mono (by decide)).and (by indep))
    (fun j hj1 hj2 => scBody_spec F₀ m₀ hSz hx j hj1 hj2)
  refine (h₁.seq (h₂.seq (h₃.seq h₄))).mono (fun _ h => h) ?_ ?_
  · rintro c ⟨⟨⟨hG, hSm, hStr, hA, -⟩, hX, -⟩, -, -⟩
    refine ⟨⟨hG, hSm, ?_, hA.le⟩, hX, hG.1.pn⟩
    rw [show offT pg n k (x + 1) - offT pg n k x = (tGrp pg n k x).length by
      dsimp only [offT] at *; omega, ← keysPre_zero_succ] at hStr
    exact hStr
  · simp only [Finset.sum_const, Nat.card_Ico, smul_eq_mul]
    have := length_gS (pg := pg) (n := n) x
    dsimp only [offS, offT, gS] at *
    unfold tGp
    rw [hTs, hSs]
    omega

/-- The groups sum to all the segments and all the triples. -/
theorem sum_groups :
    ∑ x ∈ Finset.range n, (tGp (gS pg n x).length (tGrp pg n k x).length + 4) =
      14 * (segOrder pg n).length + 24 * (tAll pg n k).length + 34 * n := by
  have h1 := sum_bkt (skeys pg n) n (by
    intro z hz; obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hz; have := lt_of_mem_segOrder hs; omega)
    (skeys pg n).length le_rfl
  have h2 := sum_bkt (tkeys pg n k) n (by
    intro z hz; obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hz; exact (trip_lt le_rfl hp).1)
    (tkeys pg n k).length le_rfl
  rw [← sum_range_eq] at h1 h2
  have e : ∀ x ∈ Finset.range n, tGp (gS pg n x).length (tGrp pg n k x).length + 4 =
      (gS pg n x).length * 14 + (gT pg n k x).length * 24 + 34 := by
    intro x _; rw [length_gT]; unfold tGp; omega
  rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul,
    ← Finset.sum_mul]
  simp only [gS, gT] at h1 h2 ⊢
  rw [h1, h2]
  simp; ring

/-- **The grouped pass**: from the free address `F₀`, the keys of the grouped triples, pushed
from `F₀ + 2 n` (after `STAMP` and `SVAL`). -/
theorem grpPass_spec {S : ℕ} (F₀ : ℕ) (m₀ : ℕ → ℕ)
    (hSz : F₀ + 2 * n + (tAll pg n k).length ≤ S) :
    HTB S grpPass (fun c => GPre pg n k F₀ m₀ c ∧ c.reg rFREE = F₀ ∧ c.mem = m₀ ∧ ZeroFrom m₀ F₀)
      (fun c => GPre pg n k F₀ m₀ c ∧ SameOn (· < F₀) m₀ c.mem ∧
        Strm (F₀ + 2 * n) ((tripX pg n k).map (keyOf pg n)) c)
      (14 * (segOrder pg n).length + 24 * (tAll pg n k).length + 34 * n + 10) := by
  have h₀ : HTB S gpAlloc (fun c => GPre pg n k F₀ m₀ c ∧ c.reg rFREE = F₀ ∧ c.mem = m₀ ∧
        ZeroFrom m₀ F₀)
      (fun c => OInv pg n k F₀ m₀ 0 c ∧ c.reg gPN = n) 6 := by
    refine HTB.run_le (by decide) (by decide) fun c ⟨hG, hF, hm, hZ⟩ => ?_
    refine ⟨by addr_ok [gpAlloc], ?_⟩
    have hmem : (RAM.run gpAlloc c).mem = c.mem := run_mem_of_stores (by decide) rfl c
    have hrr : ∀ r, r ∉ [rT, rGST, rGSV, rFREE] → (RAM.run gpAlloc c).reg r = c.reg r := by
      have hw : ∀ r ∈ wregs gpAlloc, r ∈ [rT, rGST, rGSV, rFREE] := by decide
      exact fun r hr => run_reg_of_not_mem (by decide) (fun h => hr (hw r h)) c
    have hv : (RAM.run gpAlloc c).reg rGST = F₀ ∧ (RAM.run gpAlloc c).reg rGSV = F₀ + n ∧
        (RAM.run gpAlloc c).reg rFREE = F₀ + 2 * n := by
      simp only [gpAlloc, run_seq']
      rw [run_alloc (by decide) (by decide), run_alloc (by decide) (by decide)]
      simp +decide [hF, hG.pn]
      omega
    refine ⟨⟨⟨(show RegIndep [rT, rGST, rGSV, rFREE] (GPre pg n k F₀ m₀) by indep [gPre_iff])
      c _ hrr hG, hv.1, hv.2.1⟩, by rw [hmem, hm]; exact SameOn.refl _ _, ⟨by simp [keysPre],
      by rw [hv.2.2]; simp [keysPre], by rw [hmem, hv.2.2, hm]; exact hZ.mono (by omega)⟩,
      fun y hy => by rw [hmem, hm, hZ _ (by omega)]⟩, by rw [hrr _ (by decide), hG.pn]⟩
  have hl := HTB.forUp (S := S) (i := rGX) (n := gPN) (N := n) (body := gpBody) (OInv pg n k F₀ m₀)
    (fun x => tGp (gS pg n x).length (tGrp pg n k x).length) (by decide) (by decide) (by decide)
    (fun x => by indep [OInv, GSt, gPre_iff, Strm])
    (fun x hx => gpBody_spec F₀ m₀ hSz hx)
  refine (h₀.seq hl).mono (fun _ h => h) ?_ ?_
  · rintro c ⟨⟨⟨hG, -, -⟩, hSm, hStr, -⟩, -, -⟩
    rw [keysPre_full] at hStr
    exact ⟨hG, hSm, hStr⟩
  · rw [sum_groups]; omega

end STACS2027.RAM.P2

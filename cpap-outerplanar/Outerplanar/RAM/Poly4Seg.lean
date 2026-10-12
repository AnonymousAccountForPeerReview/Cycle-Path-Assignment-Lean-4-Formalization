module

public import Outerplanar.RAM.Poly4Sub
import Mathlib.Tactic

/-!
# Phase P4 of the polygon solver: the state of the backtracking and one slot

The backtracking runs from the initial state `c₀` of phase P4 (`Poly3Post pg n k omap c₀`),
whose free pointer is `F₀`. It allocates the configurations `A` passed to the segments at `F₀`
(`NS` cells), the values of the pool cycles at `F₀ + NS` (`NP` cells), and the digits of `α`
of every segment above `F₁ = F₀ + NS + NP`.

* `Fix c₀ c`: the registers holding their values during P4 (register-only: it survives every
  sub-program not writing them, by `RegIndep` and the tactic `indep [fix_iff]`);
* `BtMem c₀ fA fB m mem`: the memory below `F₀` is that of `c₀`, `A` representing `fA` on
  `segOrder`, and the values `valAt fB` of the cycles from `tst m` on;
* reading the interface arrays of `c₀` through such a memory: `rd_boff`, `rd_bidx`, `rd_tst`,
  `rd_toff`, `rd_arg`, `rd_foff`, `rd_fv`, `rd_fsid`, `rd_pool`, `rd_omap`, at addresses below the
  free pointer of `c₀` (`lt_boff`, …);
* `slotBody`: one slot `(x, y)` of the face of the segment `segOrder[m]`: for a child
  (`x + 2 ≤ y`), its configuration `childIdx` stored in `A` (`slotBody_spec`; the digits found
  by `lookup` are those of the configuration of the segment, `dig_eq`), so that after `q`
  slots `A` represents `fPart … q`.
-/

@[expose] public section

namespace STACS2027.RAM.P4

open STACS2027.Poly

/-! ### The state -/

/-- The registers holding their values during P4 (after the allocations). -/
@[mk_iff] structure Fix (pg : Graph) (n k : ℕ) (c₀ c : Config) : Prop where
  pn : c.reg gPN = n
  ns : c.reg gNS = (segOrder pg n).length
  np : c.reg gNP = (pool pg n k).length
  fsid : c.reg gFSID = c₀.reg gFSID
  foff : c.reg gFOFF = c₀.reg gFOFF
  fv : c.reg gFV = c₀.reg gFV
  pl : c.reg gPOOL = c₀.reg gPOOL
  tst : c.reg gTST = c₀.reg gTST
  boff : c.reg gBOFF = c₀.reg gBOFF
  bidx : c.reg gBIDX = c₀.reg gBIDX
  toff : c.reg gTOFF = c₀.reg gTOFF
  arg : c.reg gARG = c₀.reg gARG
  om : c.reg gOMAP = c₀.reg gOMAP
  k : c.reg rK = k
  a : c.reg rA = c₀.reg rFREE
  val : c.reg rVAL = c₀.reg rFREE + (segOrder pg n).length

/-- The memory during the backtracking: the configurations `fA` in `A`, the values of the
cycles from `tst m` on under `fB`. -/
structure BtMem (pg : Graph) (n k : ℕ) (c₀ : Config) (fA fB : ℕ × ℕ → ℕ) (m : ℕ)
    (mem : ℕ → ℕ) : Prop where
  same : SameOn (· < c₀.reg rFREE) c₀.mem mem
  a : ∀ j (hj : j < (segOrder pg n).length), mem (c₀.reg rFREE + j) = fA (segOrder pg n)[j]
  val : ∀ i, tst pg n k m ≤ i → i < (pool pg n k).length →
    mem (c₀.reg rFREE + (segOrder pg n).length + i) = valAt pg n k fB i

/-- The end of the arrays of P4 (the digits of `α` are allocated above it). -/
abbrev F₁ (pg : Graph) (n k : ℕ) (c₀ : Config) : ℕ :=
  c₀.reg rFREE + (segOrder pg n).length + (pool pg n k).length

/-- Stores at or above `F₁` keep `BtMem`. -/
theorem BtMem.wr_above {pg : Graph} {n k : ℕ} {c₀ : Config} {fA fB : ℕ × ℕ → ℕ} {m : ℕ}
    {mem : ℕ → ℕ} (h : BtMem pg n k c₀ fA fB m mem) {b : ℕ} (hb : F₁ pg n k c₀ ≤ b)
    (l : List ℕ) : BtMem pg n k c₀ fA fB m (wr mem b l) where
  same := sameOn_wr h.same (by simp only [F₁] at hb; omega) l
  a j hj := by rw [wr_of_lt l (by simp only [F₁] at hb; omega)]; exact h.a j hj
  val i hi hp := by rw [wr_of_lt l (by simp only [F₁] at hb; omega)]; exact h.val i hi hp

/-! ### Offsets -/

section Offsets

variable (pg : Graph) (n k : ℕ)

/-- The offset of the boundary list of `segOrder[j]`. -/
def bOff (j : ℕ) : ℕ := (((segOrder pg n).take j).map fun t => (bnd pg n k t).length).sum
/-- The offset of the table of `segOrder[j]`. -/
def tOff (j : ℕ) : ℕ := (((segOrder pg n).take j).map fun t => k ^ (bnd pg n k t).length).sum
/-- The offset of the face of `segOrder[j]`. -/
def fOf (j : ℕ) : ℕ := (((segOrder pg n).take j).map fun t => (faceVerts pg n t).length).sum

end Offsets

theorem sum_take_succ {α : Type*} (S : List α) (f : α → ℕ) {j : ℕ} (hj : j < S.length) :
    ((S.take (j + 1)).map f).sum = ((S.take j).map f).sum + f S[j] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, List.map_append,
    List.sum_append]
  simp

theorem sum_take_le {α : Type*} (S : List α) (f : α → ℕ) (j : ℕ) :
    ((S.take j).map f).sum ≤ (S.map f).sum := by
  rw [← List.sum_take_add_sum_drop (S.map f) j, List.map_take]
  omega

/-! ### Reading the interface arrays -/

section Read

variable {pg : Graph} {n k : ℕ} {omap : List ℕ} {c₀ : Config} {mem : ℕ → ℕ}

theorem lt_boff (hc : Poly3Post pg n k omap c₀) {j : ℕ} (hj : j ≤ (segOrder pg n).length) :
    c₀.reg gBOFF + j < c₀.reg rFREE := by
  have hb := hc.p2.below.2.2.1; omega

theorem rd_boff (hc : Poly3Post pg n k omap c₀) (hs : SameOn (· < c₀.reg rFREE) c₀.mem mem)
    {j : ℕ} (hj : j ≤ (segOrder pg n).length) : mem (c₀.reg gBOFF + j) = bOff pg n k j := by
  rw [hs _ (lt_boff hc hj)]
  exact arr_prefixSums_get hc.p2.boff hj

theorem bOff_succ {j : ℕ} (hj : j < (segOrder pg n).length) :
    bOff pg n k (j + 1) = bOff pg n k j + (bnd pg n k (segOrder pg n)[j]).length :=
  sum_take_succ _ _ hj

theorem lt_bidx (hc : Poly3Post pg n k omap c₀) {j : ℕ} (hj : j < (segOrder pg n).length) {p : ℕ}
    (hp : p < (bnd pg n k (segOrder pg n)[j]).length) :
    c₀.reg gBIDX + (bOff pg n k j + p) < c₀.reg rFREE := by
  have hb := hc.p2.below.2.2.2
  have hl : bOff pg n k j + (bnd pg n k (segOrder pg n)[j]).length ≤ (bndCat pg n k).length := by
    rw [← bOff_succ hj, bndCat, List.length_flatMap]; exact sum_take_le _ _ _
  omega

theorem rd_bidx (hc : Poly3Post pg n k omap c₀) (hs : SameOn (· < c₀.reg rFREE) c₀.mem mem)
    {j : ℕ} (hj : j < (segOrder pg n).length) {p : ℕ} (hp : p < (bnd pg n k (segOrder pg n)[j]).length) :
    mem (c₀.reg gBIDX + (bOff pg n k j + p)) = (bnd pg n k (segOrder pg n)[j])[p] := by
  have h := arr_flatMap_part (bnd pg n k) hc.p2.bidx hj
  rw [hs _ (lt_bidx hc hj hp), ← Nat.add_assoc]
  exact h p hp

theorem lt_tst (hc : Poly3Post pg n k omap c₀) {j : ℕ} (hj : j ≤ (segOrder pg n).length) :
    c₀.reg gTST + j < c₀.reg rFREE := by
  have hb := hc.p2.below.2.1; omega

theorem rd_tst (hc : Poly3Post pg n k omap c₀) (hs : SameOn (· < c₀.reg rFREE) c₀.mem mem)
    {j : ℕ} (hj : j ≤ (segOrder pg n).length) : mem (c₀.reg gTST + j) = tst pg n k j := by
  rw [hs _ (lt_tst hc hj)]
  exact arr_prefixSums_get hc.p2.tst hj

theorem lt_toff (hc : Poly3Post pg n k omap c₀) {j : ℕ} (hj : j ≤ (segOrder pg n).length) :
    c₀.reg gTOFF + j < c₀.reg rFREE := by
  have hb := hc.below.1; omega

theorem rd_toff (hc : Poly3Post pg n k omap c₀) (hs : SameOn (· < c₀.reg rFREE) c₀.mem mem)
    {j : ℕ} (hj : j ≤ (segOrder pg n).length) : mem (c₀.reg gTOFF + j) = tOff pg n k j := by
  rw [hs _ (lt_toff hc hj)]
  exact arr_prefixSums_get hc.toff hj

theorem lt_arg (hc : Poly3Post pg n k omap c₀) {j : ℕ} (hj : j < (segOrder pg n).length) {α : ℕ}
    (hα : α < k ^ (bnd pg n k (segOrder pg n)[j]).length) :
    c₀.reg gARG + (tOff pg n k j + α) < c₀.reg rFREE := by
  have hb := hc.below.2.2
  have hl : tOff pg n k j + k ^ (bnd pg n k (segOrder pg n)[j]).length ≤ (argCat pg n k).length := by
    rw [tOff, ← sum_take_succ _ (fun t => k ^ (bnd pg n k t).length) hj, argCat, List.length_flatMap]
    simpa using sum_take_le (segOrder pg n) (fun t => k ^ (bnd pg n k t).length) (j + 1)
  omega

theorem rd_arg (hc : Poly3Post pg n k omap c₀) (hs : SameOn (· < c₀.reg rFREE) c₀.mem mem)
    {j : ℕ} (hj : j < (segOrder pg n).length) {α : ℕ}
    (hα : α < k ^ (bnd pg n k (segOrder pg n)[j]).length) :
    mem (c₀.reg gARG + (tOff pg n k j + α)) = argTab pg n k (segOrder pg n)[j] α := by
  have h := arr_flatMap_part (fun s => (List.range (k ^ (bnd pg n k s).length)).map
    (argTab pg n k s)) hc.ag hj
  simp only [List.length_map, List.length_range] at h
  rw [hs _ (lt_arg hc hj hα), ← Nat.add_assoc]
  have := h α (by simpa using hα)
  simpa [tOff] using this

theorem lt_foff (hc : Poly3Post pg n k omap c₀) {j : ℕ} (hj : j ≤ (segOrder pg n).length) :
    c₀.reg gFOFF + j < c₀.reg rFREE := by
  have hb := hc.p2.p1.below.2.2.2.1; omega

theorem rd_foff (hc : Poly3Post pg n k omap c₀) (hs : SameOn (· < c₀.reg rFREE) c₀.mem mem)
    {j : ℕ} (hj : j ≤ (segOrder pg n).length) : mem (c₀.reg gFOFF + j) = fOf pg n j := by
  rw [hs _ (lt_foff hc hj)]
  exact arr_prefixSums_get hc.p2.p1.foff hj

theorem fOf_succ {j : ℕ} (hj : j < (segOrder pg n).length) :
    fOf pg n (j + 1) = fOf pg n j + (faceVerts pg n (segOrder pg n)[j]).length :=
  sum_take_succ _ _ hj

theorem lt_fv (hc : Poly3Post pg n k omap c₀) {j : ℕ} (hj : j < (segOrder pg n).length) {q : ℕ}
    (hq : q < (faceVerts pg n (segOrder pg n)[j]).length) :
    c₀.reg gFV + (fOf pg n j + q) < c₀.reg rFREE := by
  have hb := hc.p2.p1.below.2.2.2.2
  have hl : fOf pg n j + (faceVerts pg n (segOrder pg n)[j]).length ≤ (faceCat pg n).length := by
    rw [← fOf_succ hj, faceCat, List.length_flatMap]; exact sum_take_le _ _ _
  omega

theorem rd_fv (hc : Poly3Post pg n k omap c₀) (hs : SameOn (· < c₀.reg rFREE) c₀.mem mem)
    {j : ℕ} (hj : j < (segOrder pg n).length) {q : ℕ}
    (hq : q < (faceVerts pg n (segOrder pg n)[j]).length) :
    mem (c₀.reg gFV + (fOf pg n j + q)) = (faceVerts pg n (segOrder pg n)[j])[q] := by
  have h := arr_flatMap_part (faceVerts pg n) hc.p2.p1.fv hj
  rw [hs _ (lt_fv hc hj hq), ← Nat.add_assoc]
  exact h q hq

theorem fOf_eq_fOff (j : ℕ) : fOf pg n j = P1.fOff pg n j := by
  rw [fOf, P1.fOff, List.length_flatMap]

theorem lt_fsidCat {j : ℕ} (hj : j < (segOrder pg n).length) {q : ℕ}
    (hq : q < (faceVerts pg n (segOrder pg n)[j]).length) :
    fOf pg n j + q < (fsidCat pg n).length := by
  rw [P1.length_fsidCat, fOf_eq_fOff]
  have := P1.fOff_succ (pg := pg) (n := n) hj
  have := P1.fOff_le_faceCat (pg := pg) (n := n) (j + 1)
  omega

theorem lt_fsid (hc : Poly3Post pg n k omap c₀) {j : ℕ} (hj : j < (segOrder pg n).length) {q : ℕ}
    (hq : q < (faceVerts pg n (segOrder pg n)[j]).length) :
    c₀.reg gFSID + (fOf pg n j + q) < c₀.reg rFREE := by
  have hb := hc.p2.p1.below.2.2.1
  have hl := lt_fsidCat hj hq
  omega

theorem rd_fsid (hc : Poly3Post pg n k omap c₀) (hs : SameOn (· < c₀.reg rFREE) c₀.mem mem)
    {j : ℕ} (hj : j < (segOrder pg n).length) {q : ℕ}
    (hq : q < (faceVerts pg n (segOrder pg n)[j]).length) :
    mem (c₀.reg gFSID + (fOf pg n j + q)) = segId pg n ((faceVerts pg n (segOrder pg n)[j]).getD q 0,
      (faceVerts pg n (segOrder pg n)[j]).getD (q + 1) 0) := by
  rw [hs _ (lt_fsid hc hj hq), hc.p2.p1.fsid.getD (lt_fsidCat hj hq), fOf_eq_fOff,
    P1.fsidCat_getD hj hq]

theorem lt_pool (hP : IsPolygon pg n) (hk : 3 ≤ k) (hc : Poly3Post pg n k omap c₀) {i : ℕ}
    (hi : i < (pool pg n k).length) {t : ℕ} (ht : t < k) :
    c₀.reg gPOOL + k * i + t < c₀.reg rFREE := by
  have hb := hc.p2.below.1
  have hlen : (pool pg n k).flatten.length = k * (pool pg n k).length := by
    rw [List.length_flatten, List.map_congr_left (fun u hu => length_of_mem_pool hP hk hu),
      List.map_const', List.sum_replicate, smul_eq_mul, mul_comm]
  have : k * i + t < k * (pool pg n k).length := by
    calc k * i + t < k * i + k := by omega
      _ = k * (i + 1) := by ring
      _ ≤ k * (pool pg n k).length := Nat.mul_le_mul_left _ hi
  omega

theorem rd_pool (hP : IsPolygon pg n) (hk : 3 ≤ k) (hc : Poly3Post pg n k omap c₀)
    (hs : SameOn (· < c₀.reg rFREE) c₀.mem mem) {i : ℕ} (hi : i < (pool pg n k).length) {t : ℕ}
    (ht : t < k) : mem (c₀.reg gPOOL + k * i + t) = (cyc pg n k i).getD t 0 := by
  have h := arr_pool hP hk hc.p2.pl hi
  rw [hs _ (lt_pool hP hk hc hi ht), h.getD (by rw [length_cyc hP hk hi]; exact ht)]

theorem lt_omap (hc : Poly3Post pg n k omap c₀) {x : ℕ} (hx : x < n) :
    c₀.reg gOMAP + x < c₀.reg rFREE := by
  have hb := hc.p2.p1.base.below.2.2
  have hl := hc.p2.p1.base.omap_len
  omega

theorem rd_omap (hc : Poly3Post pg n k omap c₀) (hs : SameOn (· < c₀.reg rFREE) c₀.mem mem)
    {x : ℕ} (hx : x < n) : mem (c₀.reg gOMAP + x) = omap.getD x 0 := by
  have hl := hc.p2.p1.base.omap_len
  rw [hs _ (lt_omap hc hx), hc.p2.p1.base.om.getD (by omega)]

end Read

/-! ### One slot -/

/-- The slot `q` of the current face: `rX`, `rY` its ends, `rTN = rX + 2`. -/
def slotHead : Stmt :=
  .seq (.add rX rFO rQ) (.seq (ld rX gFV rX) (.seq (.add rY rFO rQ) (.seq (inc rY)
    (.seq (ld rY gFV rY) (addc rTN rX 2)))))

/-- **One slot**: a child gets its configuration. -/
def slotBody : Stmt := .seq slotHead (ifLe rTN rY child .skip)

/-- The bound of `child`. -/
def Tch (k : ℕ) : ℕ := Lk k * (16 * Lk k + 10 * k + 34) + 21

/-- The bound of `slotBody`. -/
def Tsl (k : ℕ) : ℕ := Tch k + 12

/-- The registers of the current segment `s = segOrder[m]` (digits of `α` at `F`). -/
@[mk_iff] structure SegRegs (pg : Graph) (n k : ℕ) (c₀ : Config) (m F : ℕ) (s : ℕ × ℕ)
    (c : Config) : Prop where
  fix : Fix pg n k c₀ c
  bo : c.reg rBO = bOff pg n k m
  nb : c.reg rNB = (bnd pg n k s).length
  ts : c.reg rTS = tst pg n k m
  te : c.reg rTE = tst pg n k (m + 1)
  fo : c.reg rFO = fOf pg n m
  ad : c.reg rAD = F
  free : F + (bnd pg n k s).length ≤ c.reg rFREE

/-- The invariant of the slot loop of `s = segOrder[m]` after `q` slots. -/
def SlInv (pg : Graph) (n k : ℕ) (c₀ : Config) (m F : ℕ) (s : ℕ × ℕ) (α β : ℕ)
    (fA fB : ℕ × ℕ → ℕ) (q : ℕ) (c : Config) : Prop :=
  SegRegs pg n k c₀ m F s c ∧ BtMem pg n k c₀ (fPart pg n k s α β fA q) fB m c.mem ∧
    Arr c.mem F (cfg k (bnd pg n k s).length α) ∧ ZeroFrom c.mem (c.reg rFREE) ∧
    c.out = c₀.out

theorem lkp_congr {l ds : List ℕ} {ts te : ℕ} {vv vv' : ℕ → ℕ}
    (h : ∀ x, ts ≤ x → x < te → vv x = vv' x) (i : ℕ) : lkp l ds ts te vv i = lkp l ds ts te vv' i := by
  unfold lkp
  split
  · rfl
  · split
    · next h' => exact h i h'.1 h'.2
    · rfl

/-- The slots of a face, by index. -/
theorem getElem_slots (pg : Graph) (n : ℕ) (s : ℕ × ℕ) {q : ℕ} (hq : q < (slots pg n s).length) :
    (slots pg n s)[q] = ((faceVerts pg n s).getD q 0, (faceVerts pg n s).getD (q + 1) 0) := by
  simp only [slots, pairs_eq, List.getElem_map, List.getElem_range]

theorem length_slots (pg : Graph) (n : ℕ) (s : ℕ × ℕ) :
    (slots pg n s).length = (faceVerts pg n s).length - 1 := P1.length_pairs _

section Slot

variable {pg : Graph} {n k : ℕ} {omap : List ℕ} {c₀ : Config}

/-- Storing the configuration of the segment `segOrder[jw]` in `A`. -/
theorem BtMem.upd_a {fA fB : ℕ × ℕ → ℕ} {m : ℕ} {mem : ℕ → ℕ}
    (h : BtMem pg n k c₀ fA fB m mem) {jw : ℕ} (hjw : jw < (segOrder pg n).length) (v : ℕ) :
    BtMem pg n k c₀ (Function.update fA (segOrder pg n)[jw] v) fB m
      (upd mem (c₀.reg rFREE + jw) v) where
  same := h.same.upd_of_ge (by omega) v
  a j hj := by
    by_cases hj' : j = jw
    · subst hj'; simp
    · have hne : (segOrder pg n)[j] ≠ (segOrder pg n)[jw] := fun he =>
        hj' (((segOrder_nodup (pg := pg) (n := n)).getElem_inj_iff).mp he)
      rw [upd_ne _ _ (by omega), Function.update_of_ne hne]; exact h.a j hj
  val i hi hp := by rw [upd_ne _ _ (by omega)]; exact h.val i hi hp

/-- The digits found by `lookup` at the segment `segOrder[m]` are those of its configuration. -/
theorem dig_eq {m : ℕ} (hm : m < (segOrder pg n).length)
    {α β F : ℕ} {fA : ℕ × ℕ → ℕ} {mem : ℕ → ℕ}
    (hB : BtMem pg n k c₀ fA (abAt pg n k m).2 m mem)
    (hβ : β = argTab pg n k (segOrder pg n)[m] ((abAt pg n k (m + 1)).1 (segOrder pg n)[m]))
    (i : ℕ) :
    LkEnv.dig ⟨c₀.reg gBIDX, bOff pg n k m, F, tst pg n k m, tst pg n k (m + 1),
      c₀.reg rFREE + (segOrder pg n).length, bnd pg n k (segOrder pg n)[m],
      cfg k (bnd pg n k (segOrder pg n)[m]).length α⟩ mem i =
      (valsOf pg n k (segOrder pg n)[m] α β).getD ((rel pg n k (segOrder pg n)[m]).idxOf i) 0 := by
  have hrel : rel pg n k (segOrder pg n)[m] = bnd pg n k (segOrder pg n)[m] ++
      List.range' (tst pg n k m) (rpLen pg n k (segOrder pg n)[m]) := by
    rw [rel, topIdx_tst hm]
  rw [valsOf, hrel, length_topIdx hm, getD_idxOf_rel, LkEnv.dig, ← tst_succ hm]
  apply lkp_congr
  intro x h1 h2
  have hx := (mem_tst hm).mp ⟨h1, h2⟩
  simp only
  rw [hB.val x h1 hx.1, abAt_succ_snd hm, valAt_update_self hm _ ⟨h1, h2⟩, ← hβ]

/-- **One slot** of the face of `s = segOrder[m]`. -/
theorem slotBody_spec {S : ℕ} (hP : IsPolygon pg n) (hk : 3 ≤ k) (hc : Poly3Post pg n k omap c₀)
    {m : ℕ} (hm : m < (segOrder pg n).length) {α β F : ℕ}
    (hα : α = (abAt pg n k (m + 1)).1 (segOrder pg n)[m])
    (hβ : β = argTab pg n k (segOrder pg n)[m] α) (hF : F₁ pg n k c₀ ≤ F)
    (hFS : F + (bnd pg n k (segOrder pg n)[m]).length ≤ S)
    (q : ℕ) (hq : q < (slots pg n (segOrder pg n)[m]).length) :
    HTB S slotBody (fun c => SlInv pg n k c₀ m F (segOrder pg n)[m] α β (abAt pg n k (m + 1)).1
        (abAt pg n k m).2 q c ∧ c.reg rQ = q ∧
        c.reg rNSL = (slots pg n (segOrder pg n)[m]).length)
      (fun c => SlInv pg n k c₀ m F (segOrder pg n)[m] α β (abAt pg n k (m + 1)).1
        (abAt pg n k m).2 (q + 1) c ∧ c.reg rQ = q ∧
        c.reg rNSL = (slots pg n (segOrder pg n)[m]).length) (Tsl k) := by
  have hq1 : q + 1 < (faceVerts pg n (segOrder pg n)[m]).length := by
    rw [length_slots] at hq; omega
  have hslot := getElem_slots pg n (segOrder pg n)[m] hq
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq1, Option.getD_some] at hslot
  obtain ⟨x, hxd⟩ : ∃ x, (faceVerts pg n (segOrder pg n)[m])[q] = x := ⟨_, rfl⟩
  obtain ⟨y, hyd⟩ : ∃ y, (faceVerts pg n (segOrder pg n)[m])[q + 1] = y := ⟨_, rfl⟩
  rw [hxd, hyd] at hslot
  -- the slot head
  have hF₁ : c₀.reg rFREE + (segOrder pg n).length + (pool pg n k).length ≤ F := hF
  have hHead : HTB S slotHead (fun c => SlInv pg n k c₀ m F (segOrder pg n)[m] α β
        (abAt pg n k (m + 1)).1 (abAt pg n k m).2 q c ∧ c.reg rQ = q ∧
        c.reg rNSL = (slots pg n (segOrder pg n)[m]).length)
      (fun c => (SlInv pg n k c₀ m F (segOrder pg n)[m] α β (abAt pg n k (m + 1)).1
        (abAt pg n k m).2 q c ∧ c.reg rQ = q ∧ c.reg rNSL = (slots pg n (segOrder pg n)[m]).length) ∧
        c.reg rX = x ∧ c.reg rY = y ∧ c.reg rTN = x + 2) 10 :=
    HTB.run_le (by decide) (by decide) fun c hc' => by
      have l1 := lt_fv hc hm (q := q) (by omega)
      have l2 := lt_fv hc hm (q := q + 1) hq1
      have hfo := hc'.1.1.fo
      have hfv := hc'.1.1.fix.fv
      have hQ0 := hc'.2.1
      refine ⟨by addr_ok [slotHead, hfo, hQ0, hfv], ?_⟩
      have hI : Indep (wregs slotHead) (fun c => SlInv pg n k c₀ m F (segOrder pg n)[m] α β
          (abAt pg n k (m + 1)).1 (abAt pg n k m).2 q c ∧ c.reg rQ = q ∧
          c.reg rNSL = (slots pg n (segOrder pg n)[m]).length) := by
        indep [SlInv, segRegs_iff, fix_iff]
      refine ⟨hI.run (by decide) (by decide) (by decide) hc', ?_⟩
      obtain ⟨⟨hR, hB, -, -, -⟩, hQ, -⟩ := hc'
      have h1 := rd_fv hc hB.same hm (q := q) (by omega)
      have h2 := rd_fv hc hB.same hm (q := q + 1) hq1
      rw [show fOf pg n m + (q + 1) = fOf pg n m + q + 1 by omega, hyd] at h2
      rw [hxd] at h1
      simp +decide only [slotHead, run_seq', run_add, run_ld, run_inc (show rY ≠ rT by decide),
        run_addc (show rX ≠ rT by decide), setReg_reg, ↓reduceIte, setReg_mem, hR.fo, hQ,
        hR.fix.fv, h1, h2, and_true]
  have hb₁ := hc.p2.p1.base.below
  -- a child
  have hChild : HTB S child (fun c => ((SlInv pg n k c₀ m F (segOrder pg n)[m] α β
        (abAt pg n k (m + 1)).1 (abAt pg n k m).2 q c ∧ c.reg rQ = q ∧
        c.reg rNSL = (slots pg n (segOrder pg n)[m]).length) ∧
        c.reg rX = x ∧ c.reg rY = y ∧ c.reg rTN = x + 2) ∧ c.reg rTN ≤ c.reg rY)
      (fun c => SlInv pg n k c₀ m F (segOrder pg n)[m] α β (abAt pg n k (m + 1)).1
        (abAt pg n k m).2 (q + 1) c ∧ c.reg rQ = q ∧
        c.reg rNSL = (slots pg n (segOrder pg n)[m]).length) (Tch k) := by
    intro c ⟨⟨⟨⟨hR, hB, hAD, hZ, hO⟩, hQ, hN⟩, hx, hy, ht⟩, hle⟩
    have hxy : x + 2 ≤ y := by omega
    have hw : (x, y) ∈ childSegs pg n (segOrder pg n)[m] := by
      rw [childSegs, List.mem_filter]
      refine ⟨?_, by simpa using hxy⟩
      rw [← hslot]; exact List.getElem_mem hq
    obtain ⟨hwS, -, -⟩ := mem_childSegs' hP hw
    have hjw : (segOrder pg n).idxOf (x, y) < (segOrder pg n).length :=
      List.idxOf_lt_length_iff.mpr hwS
    have hSjw : (segOrder pg n)[(segOrder pg n).idxOf (x, y)] = (x, y) := List.getElem_idxOf hjw
    have hM : LkMem ⟨c₀.reg gBIDX, bOff pg n k m, F, tst pg n k m, tst pg n k (m + 1),
        c₀.reg rFREE + (segOrder pg n).length, bnd pg n k (segOrder pg n)[m],
        cfg k (bnd pg n k (segOrder pg n)[m]).length α⟩ c.mem :=
      ⟨nodup_bnd _, fun p hp => rd_bidx hc hB.same hm hp, fun p hp => hAD.getD (by simpa using hp)⟩
    have hβ' : β = argTab pg n k (segOrder pg n)[m] ((abAt pg n k (m + 1)).1 (segOrder pg n)[m]) := by
      rw [hβ, hα]
    have hdig := dig_eq hm (F := F) (α := α) (β := β) hB hβ'
    have hfs : c.mem (c₀.reg gFSID + (fOf pg n m + q)) = (segOrder pg n).idxOf (x, y) + 1 := by
      rw [rd_fsid hc hB.same hm (by omega), List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by omega), Option.getD_some, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hq1, Option.getD_some, hxd, hyd, P1.segId_of_mem hwS]
    have hBnd : LkBnd S ⟨c₀.reg gBIDX, bOff pg n k m, F, tst pg n k m, tst pg n k (m + 1),
        c₀.reg rFREE + (segOrder pg n).length, bnd pg n k (segOrder pg n)[m],
        cfg k (bnd pg n k (segOrder pg n)[m]).length α⟩ := by
      have htN : tst pg n k (m + 1) ≤ (pool pg n k).length := by
        rw [← tst_length]; exact tst_mono hm
      refine ⟨fun p hp => ?_, hFS, by simp only; omega⟩
      have := lt_bidx hc hm hp; simp only at hp ⊢; omega
    obtain ⟨c', t, e, hmem, ht'⟩ := child_spec (S := S) (k := k) (fo := fOf pg n m) (q := q)
      (fsid := c₀.reg gFSID) (jw := (segOrder pg n).idxOf (x, y)) (boff := c₀.reg gBOFF)
      (bw := bOff pg n k ((segOrder pg n).idxOf (x, y))) (a := c₀.reg rFREE)
      (lw := bnd pg n k (segOrder pg n)[(segOrder pg n).idxOf (x, y)]) hM hBnd hfs
      (rd_boff hc hB.same hjw.le) (by rw [rd_boff hc hB.same hjw, bOff_succ hjw])
      (fun q hq => rd_bidx hc hB.same hjw hq)
      (fun q hq => by have := lt_bidx hc hjw hq; simp only; omega)
      (by have := lt_fsid hc hm (q := q) (by omega); omega)
      (by have := lt_boff hc (j := (segOrder pg n).idxOf (x, y) + 1) hjw; omega) (by omega)
      (fun i _ => by
        rw [hdig i]
        exact getD_lt (by omega) (fun d hd => by
          rcases List.mem_append.mp hd with h' | h' <;> exact cfg_lt (by omega) _ _ d h') _)
      c ⟨⟨hR.fix.bidx, hR.bo, hR.nb, hR.ad, hR.ts, hR.te, hR.fix.val⟩, hR.fix.k, hR.fo, hQ,
        hR.fix.fsid, hR.fix.boff, hR.fix.a, rfl⟩
    have hval : enc k ((bnd pg n k (segOrder pg n)[(segOrder pg n).idxOf (x, y)]).map
        (LkEnv.dig ⟨c₀.reg gBIDX, bOff pg n k m, F, tst pg n k m, tst pg n k (m + 1),
          c₀.reg rFREE + (segOrder pg n).length, bnd pg n k (segOrder pg n)[m],
          cfg k (bnd pg n k (segOrder pg n)[m]).length α⟩ c.mem)) =
        childIdx pg n k (segOrder pg n)[m] (x, y) (valsOf pg n k (segOrder pg n)[m] α β) := by
      rw [childIdx, hSjw]
      congr 1
      exact List.map_congr_left fun i _ => hdig i
    rw [hval] at hmem
    have hRI : RegIndep (wregs child) (fun c => SegRegs pg n k c₀ m F (segOrder pg n)[m] c ∧
        c.reg rQ = q ∧ c.reg rNSL = (slots pg n (segOrder pg n)[m]).length) := by
      indep [segRegs_iff, fix_iff]
    obtain ⟨hR', hQ', hN'⟩ := hRI.execB e ⟨hR, hQ, hN⟩
    have hjF : c₀.reg rFREE + (segOrder pg n).idxOf (x, y) < F₁ pg n k c₀ := by
      simp only [F₁]; omega
    have hFree : c'.reg rFREE = c.reg rFREE := e.frame.reg rFREE (by decide)
    refine ⟨c', t, e, ⟨⟨hR', ?_, ?_, ?_, ?_⟩, hQ', hN'⟩, ht'.trans ?_⟩
    · rw [fPart_succ_child _ _ _ _ hq (by rw [hslot]; exact hxy), hslot, hmem]
      have := hB.upd_a hjw (childIdx pg n k (segOrder pg n)[m] (x, y)
        (valsOf pg n k (segOrder pg n)[m] α β))
      rwa [hSjw] at this
    · rw [hmem]; exact hAD.upd_of_disjoint (Or.inl (by omega))
    · rw [hmem, hFree]; exact hZ.upd (by have := hR.free; omega)
    · rw [e.frame.out (by decide), hO]
    · have h1 := length_bnd_le' (k := k) hP hwS
      have h2 := length_bnd_le' (k := k) hP (List.getElem_mem hm)
      rw [hSjw]
      unfold Tch
      simp only
      have := Nat.mul_le_mul h1 (show 16 * (bnd pg n k (segOrder pg n)[m]).length + 10 * k + 34 ≤
        16 * Lk k + 10 * k + 34 by omega)
      omega
  -- a side
  have hSide : HTB S .skip (fun c => ((SlInv pg n k c₀ m F (segOrder pg n)[m] α β
        (abAt pg n k (m + 1)).1 (abAt pg n k m).2 q c ∧ c.reg rQ = q ∧
        c.reg rNSL = (slots pg n (segOrder pg n)[m]).length) ∧
        c.reg rX = x ∧ c.reg rY = y ∧ c.reg rTN = x + 2) ∧ c.reg rY < c.reg rTN)
      (fun c => SlInv pg n k c₀ m F (segOrder pg n)[m] α β (abAt pg n k (m + 1)).1
        (abAt pg n k m).2 (q + 1) c ∧ c.reg rQ = q ∧
        c.reg rNSL = (slots pg n (segOrder pg n)[m]).length) (Tch k) := by
    refine (HTB.skip.mono (fun c h => h) ?_ (by unfold Tch; omega))
    rintro c ⟨⟨⟨⟨hR, hB, hAD, hZ, hO⟩, hQ, hN⟩, hx, hy, ht⟩, hlt⟩
    refine ⟨⟨hR, ?_, hAD, hZ, hO⟩, hQ, hN⟩
    rw [fPart_succ_side _ _ _ _ hq (by rw [hslot]; omega)]
    exact hB
  exact (hHead.seq (HTB.ifLe (by decide) (by decide) (by indep [SlInv, segRegs_iff, fix_iff])
    hChild hSide)).weaken (by unfold Tsl; omega)

end Slot

end STACS2027.RAM.P4

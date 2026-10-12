module

public import Outerplanar.RAM.Poly1Face
import Mathlib.Tactic

/-!
# Phase P1 of the polygon solver, stage F: the slot ids

Stage F (`stageF`) writes, parallel to the face vertices `gFV`, the slot ids `fsidCat` at
`gFSID` (`|faceCat|` fresh cells, read off `FOFF[NS]`): for the face vertex `q` of the face of
`s = (a, b)` (the segment `t` of `segOrder`), `1 +` the index in `segOrder` of the slot from `q`
to the next face vertex, or `0` for a side and for the last face vertex. No table is indexed by
pairs of positions:

* the first slot `(a, predNb a b)` is, if `a + 2 ≤ predNb a b`, the segment enumerated before
  `s`, whose enumeration id is the index `e = ORD3[t]` of `s` in `segEnum` (`enumId_pred`);
* every other slot `(x, y)` but the last has `y = lastNb x` (`faceVerts_next`), whose
  enumeration id is `LSEG[x]` (stage B);
* enumeration ids become segment ids by the table `POS` of stage D (`posId_enumId`);
* the last face vertex keeps the `0` of the fresh memory (`segId_last_slot`).

Layout: `FSID` from the free address `F₀`, ending at `F₀ + |faceCat|` (`stageF_core`).
Cost `O(|segOrder| + |faceCat|)`.
-/

@[expose] public section

namespace STACS2027.RAM.P1

open STACS2027.Poly

/-! ### Registers and program -/

/-- The segment counter `t`. -/
abbrev rST : ℕ := 147
/-- The first end `a` of the segment. -/
abbrev rSA0 : ℕ := 148
/-- The index `e` of the segment in `segEnum`. -/
abbrev rSE : ℕ := 149
/-- The face vertex after `a`. -/
abbrev rSP : ℕ := 150
/-- The face offset of the segment. -/
abbrev rSO : ℕ := 151
/-- The counter over the face vertices. -/
abbrev rSQ : ℕ := 152
/-- The end of the middle face vertices. -/
abbrev rSH : ℕ := 153
/-- Temporary. -/
abbrev rSX : ℕ := 154
/-- The start of the middle face vertices. -/
abbrev rSL : ℕ := 155
/-- `|faceCat|`. -/
abbrev rSN : ℕ := 156
/-- `a + 2`. -/
abbrev rSA2 : ℕ := 157

/-- Allocate `FSID` (`FOFF[NS] = |faceCat|` cells). -/
def fsAlloc : Stmt := .seq (ld rSN gFOFF gNS) (alloc gFSID rSN)
/-- Read the segment `t`: `a`, `e`, the face vertex after `a`, the range of its face. -/
def fsHead : Stmt :=
  .seq (ld rSA0 gSA rST) (.seq (ld rSE rORD3 rST) (.seq (ld rSP rSEP rSE) (.seq (ld rSO gFOFF rST)
    (.seq (addc rSH rST 1) (.seq (ld rSH gFOFF rSH) (.seq (dec rSH) (.seq (addc rSL rSO 1)
      (addc rSA2 rSA0 2))))))))
/-- The first slot: `FSID[off] := POS[a + 2 ≤ pred ? e : 0]`. -/
def fsFirst : Stmt :=
  .seq (ifLe rSA2 rSP (mov rSX rSE) (.const rSX 0)) (.seq (ld rSX rPOS rSX) (st gFSID rSO rSX))
/-- A middle face vertex `x = FV[q]`: `FSID[q] := POS[LSEG[x]]`. -/
def fsMid : Stmt :=
  .seq (ld rSX gFV rSQ) (.seq (ld rSX rLSEG rSX) (.seq (ld rSX rPOS rSX) (st gFSID rSQ rSX)))
/-- One segment. -/
def fsBody : Stmt := .seq fsHead (.seq fsFirst (forRange rSQ rSL rSH fsMid))
/-- **Stage F**: the slot ids. -/
def stageF : Stmt := .seq fsAlloc (forUp rST gNS fsBody)

/-- The registers written by stage F. -/
abbrev WF : List ℕ := wregs stageF

/-- The result of stage F. -/
def SlotSt (pg : Graph) (n : ℕ) (c : Config) : Prop := ArrAt gFSID (fsidCat pg n) c

variable {pg : Graph} {n : ℕ} {S : ℕ}

/-! ### Abstract side -/

/-- A part of a concatenation over the segments. -/
theorem arr_segOrder_part {m : ℕ → ℕ} {b : ℕ} {f : ℕ × ℕ → List ℕ}
    (h : Arr m b ((segOrder pg n).flatMap f)) {t : ℕ} (ht : t < (segOrder pg n).length) :
    Arr m (b + (((segOrder pg n).take t).flatMap f).length) (f (segOrder pg n)[t]) := by
  have hS : segOrder pg n = (segOrder pg n).take t ++ (segOrder pg n)[t] ::
      (segOrder pg n).drop (t + 1) := by
    rw [← List.drop_eq_getElem_cons ht, List.take_append_drop]
  rw [hS, List.flatMap_append, List.flatMap_cons, arr_append] at h
  exact h.2.prefix

theorem faceOffs_get {t : ℕ} (ht : t < (segOrder pg n).length + 1) :
    (faceOffs pg n)[t]'(by simp [faceOffs, prefixSums]; omega) = fOff pg n t := by
  simp only [← map_fOff, List.getElem_map, List.getElem_range]

theorem faceSids_take_succ {s : ℕ × ℕ} {r : ℕ} (hr : r < (faceVerts pg n s).length) :
    (faceSids pg n s).take (r + 1) = (faceSids pg n s).take r ++
      [segId pg n ((faceVerts pg n s).getD r 0, (faceVerts pg n s).getD (r + 1) 0)] := by
  rw [List.take_add_one, List.getElem?_eq_getElem (by rw [length_faceSids]; exact hr)]
  simp [faceSids]

/-- The slot ids of a face end with the `0` of the last face vertex. -/
theorem faceSids_eq_last {s : ℕ × ℕ} (h : 1 ≤ (faceVerts pg n s).length) :
    faceSids pg n s = (faceSids pg n s).take ((faceVerts pg n s).length - 1) ++ [0] := by
  have e : faceSids pg n s = (faceSids pg n s).take ((faceVerts pg n s).length - 1 + 1) :=
    (List.take_of_length_le (by rw [length_faceSids]; omega)).symm
  rw [faceSids_take_succ (by omega), segId_last_slot] at e
  exact e

theorem enumId_le (p : ℕ × ℕ) : enumId pg n p ≤ (segEnum pg n).length := by
  unfold enumId
  split_ifs with h
  · have := List.idxOf_lt_length_iff.mpr h; omega
  · omega

/-! ### The state -/

/-- The constant registers and data of stage F (arrays in the memory `m₀` before it, below
`F₀`; `FSID` at `F₀`). -/
@[mk_iff] structure FsCtx (pg : Graph) (n F₀ : ℕ) (m₀ : ℕ → ℕ) (c : Config) : Prop where
  ns : c.reg gNS = (segOrder pg n).length
  fsid : c.reg gFSID = F₀
  free : c.reg rFREE = F₀ + (faceCat pg n).length
  sa : Arr m₀ (c.reg gSA) ((segOrder pg n).map Prod.fst)
  bsa : c.reg gSA + (segOrder pg n).length ≤ F₀
  ord : Arr m₀ (c.reg rORD3) (ord3 pg n)
  bord : c.reg rORD3 + (segOrder pg n).length ≤ F₀
  sep : Arr m₀ (c.reg rSEP) ((segEnum pg n).map (predOf pg n))
  bsep : c.reg rSEP + (segOrder pg n).length ≤ F₀
  foff : Arr m₀ (c.reg gFOFF) (faceOffs pg n)
  bfoff : c.reg gFOFF + ((segOrder pg n).length + 1) ≤ F₀
  fv : Arr m₀ (c.reg gFV) (faceCat pg n)
  bfv : c.reg gFV + (faceCat pg n).length ≤ F₀
  lseg : Tab m₀ (c.reg rLSEG) n (fun x => enumId pg n (x, lastNb pg n x))
  blseg : c.reg rLSEG + n ≤ F₀
  pos : Tab m₀ (c.reg rPOS) ((segOrder pg n).length + 1) (posId pg n)
  bpos : c.reg rPOS + ((segOrder pg n).length + 1) ≤ F₀

/-- The state of stage F with the slot ids `l` written. -/
def FsSt (pg : Graph) (n F₀ : ℕ) (m₀ : ℕ → ℕ) (l : List ℕ) (c : Config) : Prop :=
  FsCtx pg n F₀ m₀ c ∧ SameOn (· < F₀) m₀ c.mem ∧ Arr c.mem F₀ l ∧ ZeroFrom c.mem (F₀ + l.length)

theorem FsSt.indep (F₀ : ℕ) (m₀ : ℕ → ℕ) (l : List ℕ) :
    Indep [rT, rST, rSA0, rSE, rSP, rSO, rSQ, rSH, rSX, rSL, rSA2] (FsSt pg n F₀ m₀ l) := by
  indep [FsSt, fsCtx_iff]

/-- Storing the next slot id. -/
theorem FsSt.push {F₀ : ℕ} {m₀ : ℕ → ℕ} {l : List ℕ} {c : Config} (h : FsSt pg n F₀ m₀ l c)
    (v : ℕ) : FsSt pg n F₀ m₀ (l ++ [v]) (c.setMem (F₀ + l.length) v) := by
  obtain ⟨hC, hS, hA, hZ⟩ := h
  refine ⟨(show RegIndep [] (FsCtx pg n F₀ m₀) by indep [fsCtx_iff]).setMem _ _ hC, ?_, ?_, ?_⟩
  · simp only [setMem_mem_upd]; exact hS.upd_of_ge (by omega) _
  · simp only [setMem_mem_upd]; exact hA.upd_snoc rfl
  · simp only [setMem_mem_upd, List.length_append, List.length_singleton]
    exact (hZ.mono (by omega)).upd (by omega)

/-- Reading below `F₀`. -/
theorem FsSt.rd {F₀ : ℕ} {m₀ : ℕ → ℕ} {l : List ℕ} {c : Config} (h : FsSt pg n F₀ m₀ l c)
    {a : ℕ} (ha : a < F₀) : c.mem a = m₀ a := h.2.1 a ha

/-! ### One segment -/

/-- The registers set by the head of the segment `t`. -/
def HeadR (pg : Graph) (n t : ℕ) (c : Config) : Prop :=
  c.reg rST = t ∧ c.reg rSE = (ord3 pg n).getD t 0 ∧
    c.reg rSP = predNb pg n ((segOrder pg n).getD t (0, 0)).1 ((segOrder pg n).getD t (0, 0)).2 ∧
    c.reg rSO = fOff pg n t ∧ c.reg rSH = fOff pg n (t + 1) - 1 ∧ c.reg rSL = fOff pg n t + 1 ∧
    c.reg rSA2 = ((segOrder pg n).getD t (0, 0)).1 + 2 ∧ c.reg gNS = (segOrder pg n).length

theorem fsHead_spec (F₀ : ℕ) (m₀ : ℕ → ℕ) (hB : F₀ + (faceCat pg n).length ≤ S) (t : ℕ)
    (ht : t < (segOrder pg n).length) :
    HTB S fsHead (fun c => FsSt pg n F₀ m₀ (doneS pg n t) c ∧ c.reg rST = t ∧
        c.reg gNS = (segOrder pg n).length)
      (fun c => FsSt pg n F₀ m₀ (doneS pg n t) c ∧ HeadR pg n t c) 18 := by
  refine HTB.run_le (by decide) (by decide) fun c ⟨hS, hT, hN⟩ => ?_
  have hC := hS.1
  have hag : Agree [rT, rST, rSA0, rSE, rSP, rSO, rSQ, rSH, rSX, rSL, rSA2] c (RAM.run fsHead c) :=
    agree_run (by decide) rfl rfl (by decide) c
  have hlo := length_ord3 (pg := pg) (n := n)
  have hle := length_segOrder (pg := pg) (n := n)
  have hst : (segOrder pg n).getD t (0, 0) = (segOrder pg n)[t] := getD_of_lt ht _
  have e1 : c.mem (c.reg gSA + t) = (segOrder pg n)[t].1 := by
    rw [hS.rd (by have := hC.bsa; omega), hC.sa.get (by simpa using ht)]; simp
  have e2 : c.mem (c.reg rORD3 + t) = (ord3 pg n).getD t 0 := by
    rw [hS.rd (by have := hC.bord; omega), hC.ord.getD (by omega)]
  have hel : (ord3 pg n).getD t 0 < (segEnum pg n).length := lt_of_mem_ord3 (getD_ord3_mem ht)
  have e3 : c.mem (c.reg rSEP + (ord3 pg n).getD t 0) =
      predNb pg n (segOrder pg n)[t].1 (segOrder pg n)[t].2 := by
    rw [hS.rd (by have := hC.bsep; omega), hC.sep.getD (by simpa using hel),
      getD_map_lt hel (0, 0), getD_segEnum_ord3 ht]
    rfl
  have e4 : c.mem (c.reg gFOFF + t) = fOff pg n t := by
    rw [hS.rd (by have := hC.bfoff; omega), hC.foff.get (by simp [faceOffs, prefixSums]; omega),
      faceOffs_get (by omega)]
  have e5 : c.mem (c.reg gFOFF + (t + 1)) = fOff pg n (t + 1) := by
    rw [hS.rd (by have := hC.bfoff; omega), hC.foff.get (by simp [faceOffs, prefixSums]; omega),
      faceOffs_get (by omega)]
  refine ⟨by
    have := hC.bsa; have := hC.bord; have := hC.bsep; have := hC.bfoff
    addr_ok [fsHead, hT, e2], (FsSt.indep F₀ m₀ (doneS pg n t)) c _ hag hS, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  all_goals simp +decide only [fsHead, run_seq', run_ld, run_addc (show rST ≠ rT by decide),
    run_addc (show rSO ≠ rT by decide), run_addc (show rSA0 ≠ rT by decide),
    run_dec (show rSH ≠ rT by decide), setReg_reg, ↓reduceIte, setReg_mem, hT, hN, e1, e2, e3, e4,
    e5, hst]

theorem fsFirst_spec (hP : IsPolygon pg n) (F₀ : ℕ) (m₀ : ℕ → ℕ)
    (hB : F₀ + (faceCat pg n).length ≤ S) (t : ℕ) (ht : t < (segOrder pg n).length) :
    HTB S fsFirst (fun c => FsSt pg n F₀ m₀ (doneS pg n t) c ∧ HeadR pg n t c)
      (fun c => FsSt pg n F₀ m₀ (doneS pg n t ++ (faceSids pg n (segOrder pg n)[t]).take 1) c ∧
        HeadR pg n t c) 12 := by
  refine HTB.run_le (by decide) (by decide) fun c ⟨hS, hR⟩ => ?_
  obtain ⟨hT, hE, hSP, hSO, hSH, hSL, hA2, hN⟩ := hR
  have hst : (segOrder pg n).getD t (0, 0) = (segOrder pg n)[t] := getD_of_lt ht _
  rw [hst] at hSP hA2
  obtain ⟨s, hsdef⟩ : ∃ s, (segOrder pg n)[t] = s := ⟨_, rfl⟩
  rw [hsdef] at hSP hA2
  have hsS : s ∈ segOrder pg n := hsdef ▸ List.getElem_mem ht
  have hsE : s ∈ segEnum pg n := mem_segOrder_iff_segEnum.mp hsS
  have hss : s ∈ IsPolygon.segs pg n := mem_segOrder.mp hsS
  have hel : (ord3 pg n).getD t 0 < (segEnum pg n).length := lt_of_mem_ord3 (getD_ord3_mem ht)
  have hidx : (segEnum pg n).idxOf s = (ord3 pg n).getD t 0 := by
    have := getD_segEnum_ord3 (pg := pg) (n := n) ht
    rw [hsdef] at this
    rw [← this, getD_of_lt hel, segEnum_nodup.idxOf_getElem]
  have h3 := hP.three_le_length_faceVerts hss
  -- the enumeration id of the first slot
  set id0 := if s.1 + 2 ≤ predNb pg n s.1 s.2 then (ord3 pg n).getD t 0 else 0 with hid0
  have hid : id0 = enumId pg n (s.1, predNb pg n s.1 s.2) := by rw [enumId_pred hsE, hidx]
  have hidle : id0 < (segOrder pg n).length + 1 := by
    rw [hid]; have := enumId_le (pg := pg) (n := n) (s.1, predNb pg n s.1 s.2)
    rw [length_segOrder]; omega
  have hval : posId pg n id0 =
      segId pg n ((faceVerts pg n s).getD 0 0, (faceVerts pg n s).getD (0 + 1) 0) := by
    obtain ⟨h0, h1⟩ := faceVerts_start hP hss
    rw [hid, posId_enumId, Nat.zero_add, h0, h1]
  have hC := hS.1
  have hpos : c.mem (c.reg rPOS + id0) = posId pg n id0 := by
    rw [hS.rd (by have := hC.bpos; omega), hC.pos.get hidle]
  refine ⟨?_, ?_⟩
  · have := hC.bpos
    have hfs := fOff_succ (pg := pg) (n := n) ht
    rw [hsdef] at hfs
    have := fOff_le_faceCat (pg := pg) (n := n) (t + 1)
    have hle' := length_segOrder (pg := pg) (n := n)
    addr_ok [fsFirst, hA2, hSP, hE, hSO, hC.fsid]
  -- the run
  have hmem : (RAM.run fsFirst c).mem = upd c.mem (F₀ + fOff pg n t) (posId pg n id0) := by
    by_cases hle : s.1 + 2 ≤ predNb pg n s.1 s.2
    · have e : id0 = (ord3 pg n).getD t 0 := by rw [hid0, ite_eq_left hle]
      rw [← e] at hE
      simp +decide only [fsFirst, run_seq', run_ifLe, hA2, hSP, hle, ↓reduceIte,
        run_mov (show rSE ≠ rT by decide), run_ld, run_st (show rSX ≠ rT by decide), setReg_reg,
        setReg_mem, hE, hpos, hC.fsid, hSO, setMem_mem_upd]
    · have e : id0 = 0 := by rw [hid0, ite_eq_right hle]
      have hpos' : c.mem (c.reg rPOS + 0) = posId pg n id0 := by rw [← e]; exact hpos
      simp +decide only [fsFirst, run_seq', run_ifLe, hA2, hSP, hle, ↓reduceIte, run_const,
        run_ld, run_st (show rSX ≠ rT by decide), setReg_reg, setReg_mem, hpos', hC.fsid, hSO,
        setMem_mem_upd]
  have hw : ∀ r ∈ wregs fsFirst, r ∈ [rT, rSX] := by decide
  have hrr : ∀ r, r ∉ [rT, rSX] → (RAM.run fsFirst c).reg r = c.reg r :=
    fun r hr => run_reg_of_not_mem (by decide) (fun h => hr (hw r h)) c
  have hAg : Agree [rT, rSX] (c.setMem (F₀ + (doneS pg n t).length) (posId pg n id0))
      (RAM.run fsFirst c) :=
    ⟨fun r hr => by rw [hrr r hr]; simp, by rw [hmem, length_doneS]; simp,
      by rw [run_out_of_writes (by decide) (by decide) c]; simp⟩
  have hS' := ((FsSt.indep F₀ m₀ _).mono (by decide)) _ _ hAg (hS.push (posId pg n id0))
  refine ⟨?_, ?_⟩
  · rw [hsdef, List.take_one, List.head?_eq_getElem?, List.getElem?_eq_getElem
      (by rw [length_faceSids]; omega), Option.toList_some]
    convert hS' using 3
    simp only [faceSids, List.getElem_map, List.getElem_range]
    exact hval.symm
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals rw [hrr _ (by decide)]
    all_goals simp only [hT, hE, hSO, hSH, hSL, hN, hst, hsdef, hSP, hA2]

/-- The invariant of the middle face vertices of the segment `t`, at the position `q`. -/
def MidInv (pg : Graph) (n F₀ : ℕ) (m₀ : ℕ → ℕ) (t q : ℕ) (c : Config) : Prop :=
  FsSt pg n F₀ m₀ (doneS pg n t ++
    (faceSids pg n ((segOrder pg n).getD t (0, 0))).take (q - fOff pg n t)) c ∧ HeadR pg n t c

theorem fsMid_spec (hP : IsPolygon pg n) (F₀ : ℕ) (m₀ : ℕ → ℕ)
    (hB : F₀ + (faceCat pg n).length ≤ S) (t : ℕ)
    (ht : t < (segOrder pg n).length) (q : ℕ) (hq1 : fOff pg n t + 1 ≤ q)
    (hq2 : q < fOff pg n (t + 1) - 1) :
    HTB S fsMid (fun c => MidInv pg n F₀ m₀ t q c ∧ c.reg rSQ = q ∧
        c.reg rSH = fOff pg n (t + 1) - 1)
      (fun c => MidInv pg n F₀ m₀ t (q + 1) c ∧ c.reg rSQ = q ∧
        c.reg rSH = fOff pg n (t + 1) - 1) 10 := by
  refine HTB.run_le (by decide) (by decide) fun c ⟨⟨hS, hR⟩, hQ, hH⟩ => ?_
  have hst : (segOrder pg n).getD t (0, 0) = (segOrder pg n)[t] := getD_of_lt ht _
  rw [hst] at hS
  unfold MidInv
  rw [hst]
  obtain ⟨s, hsdef⟩ : ∃ s, (segOrder pg n)[t] = s := ⟨_, rfl⟩
  rw [hsdef] at hS ⊢
  have hsS : s ∈ segOrder pg n := hsdef ▸ List.getElem_mem ht
  have hss : s ∈ IsPolygon.segs pg n := mem_segOrder.mp hsS
  have hsn := (lt_of_mem_segOrder hsS).2
  have hfs := fOff_succ (pg := pg) (n := n) ht
  rw [hsdef] at hfs
  obtain ⟨r, rfl⟩ : ∃ r, q = fOff pg n t + r := ⟨q - fOff pg n t, by omega⟩
  have hr1 : 1 ≤ r := by omega
  have hr2 : r + 1 < (faceVerts pg n s).length := by omega
  rw [show fOff pg n t + r - fOff pg n t = r by omega] at hS
  have hC := hS.1
  -- the face vertex
  have hx : c.mem (c.reg gFV + (fOff pg n t + r)) = (faceVerts pg n s).getD r 0 := by
    have hpart := arr_segOrder_part hC.fv ht
    rw [hsdef] at hpart
    have hpart' : Arr m₀ (c.reg gFV + fOff pg n t) (faceVerts pg n s) := hpart
    rw [hS.rd (by have := hC.bfv; have := fOff_le_faceCat (pg := pg) (n := n) (t + 1); omega),
      ← Nat.add_assoc, hpart'.getD (by omega)]
  set x := (faceVerts pg n s).getD r 0 with hxdef
  have hxn : x < n := by
    have hxm : x ∈ faceVerts pg n s := by rw [hxdef, getD_of_lt (by omega)]; exact List.getElem_mem _
    have := (mem_faceVerts.mp hxm).2.1
    omega
  have hl : c.mem (c.reg rLSEG + x) = enumId pg n (x, lastNb pg n x) := by
    rw [hS.rd (by have := hC.blseg; omega), hC.lseg.get hxn]
  have hle := enumId_le (pg := pg) (n := n) (x, lastNb pg n x)
  have hp : c.mem (c.reg rPOS + enumId pg n (x, lastNb pg n x)) = segId pg n (x, lastNb pg n x) := by
    rw [hS.rd (by have := hC.bpos; rw [length_segOrder] at this; omega),
      hC.pos.get (by rw [length_segOrder]; omega), posId_enumId]
  have hnext := faceVerts_next hP hss hr1 hr2
  rw [← hxdef] at hnext
  refine ⟨?_, ?_⟩
  · have := hC.bfv; have := hC.blseg; have := hC.bpos
    have := fOff_le_faceCat (pg := pg) (n := n) (t + 1)
    have hle' := length_segOrder (pg := pg) (n := n)
    addr_ok [fsMid, hQ, hx, hl, hC.fsid]
  have hlen : (doneS pg n t ++ (faceSids pg n s).take r).length = fOff pg n t + r := by
    rw [List.length_append, length_doneS, List.length_take, length_faceSids]; omega
  have hmem : (RAM.run fsMid c).mem = upd c.mem (F₀ + (fOff pg n t + r)) (segId pg n (x, lastNb pg n x)) := by
    simp +decide only [fsMid, run_seq', run_ld, run_st (show rSX ≠ rT by decide), setReg_reg,
      ↓reduceIte, setReg_mem, setMem_mem_upd, hQ, hx, hl, hp, hC.fsid]
  have hw : ∀ r ∈ wregs fsMid, r ∈ [rT, rSX] := by decide
  have hrr : ∀ r, r ∉ [rT, rSX] → (RAM.run fsMid c).reg r = c.reg r :=
    fun r hr => run_reg_of_not_mem (by decide) (fun h => hr (hw r h)) c
  have hAg : Agree [rT, rSX] (c.setMem (F₀ + (doneS pg n t ++ (faceSids pg n s).take r).length)
      (segId pg n (x, lastNb pg n x))) (RAM.run fsMid c) :=
    ⟨fun r hr => by rw [hrr r hr]; simp, by rw [hmem, hlen]; simp,
      by rw [run_out_of_writes (by decide) (by decide) c]; simp⟩
  have hS' := ((FsSt.indep F₀ m₀ _).mono (by decide)) _ _ hAg (hS.push _)
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [show fOff pg n t + r + 1 - fOff pg n t = r + 1 by omega, faceSids_take_succ (by omega),
      ← List.append_assoc, hnext]
    exact hS'
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hR
    exact ⟨by rw [hrr _ (by decide), h1], by rw [hrr _ (by decide), h2], by rw [hrr _ (by decide), h3],
      by rw [hrr _ (by decide), h4], by rw [hrr _ (by decide), h5], by rw [hrr _ (by decide), h6],
      by rw [hrr _ (by decide), h7], by rw [hrr _ (by decide), h8]⟩
  · rw [hrr _ (by decide), hQ]
  · rw [hrr _ (by decide), hH]

/-- The bound of one segment. -/
def tFs (L : ℕ) : ℕ := 14 * L + 34

theorem fsBody_spec (hP : IsPolygon pg n) (F₀ : ℕ) (m₀ : ℕ → ℕ)
    (hB : F₀ + (faceCat pg n).length ≤ S) (t : ℕ) (ht : t < (segOrder pg n).length) :
    HTB S fsBody (fun c => FsSt pg n F₀ m₀ (doneS pg n t) c ∧ c.reg rST = t ∧
        c.reg gNS = (segOrder pg n).length)
      (fun c => FsSt pg n F₀ m₀ (doneS pg n (t + 1)) c ∧ c.reg rST = t ∧
        c.reg gNS = (segOrder pg n).length)
      (tFs (faceVerts pg n ((segOrder pg n).getD t (0, 0))).length) := by
  have hst : (segOrder pg n).getD t (0, 0) = (segOrder pg n)[t] := getD_of_lt ht _
  have hsS : (segOrder pg n)[t] ∈ segOrder pg n := List.getElem_mem ht
  have h3 := hP.three_le_length_faceVerts (mem_segOrder.mp hsS)
  have hfs := fOff_succ (pg := pg) (n := n) ht
  have hl := HTB.forRange (i := rSQ) (a := rSL) (n := rSH) (A := fOff pg n t + 1)
    (N := fOff pg n (t + 1) - 1) (body := fsMid) (MidInv pg n F₀ m₀ t) (fun _ => 10)
    (by decide) (by decide) (by decide) (by decide)
    (fun q => by unfold MidInv HeadR; exact ((FsSt.indep F₀ m₀ _).mono (by decide)).and (by indep))
    (fun q hq1 hq2 => fsMid_spec hP F₀ m₀ hB t ht q hq1 hq2)
  refine ((fsHead_spec F₀ m₀ hB t ht).seq ((fsFirst_spec hP F₀ m₀ hB t ht).seq
    (hl.pre fun c ⟨hS, hR⟩ => ⟨⟨by
      rw [hst, show fOff pg n t + 1 - fOff pg n t = 1 by omega]; exact hS,
      hR⟩, hR.2.2.2.2.2.1, hR.2.2.2.2.1, by omega⟩))).mono (fun _ h => h) ?_ ?_
  · rintro c ⟨⟨hS, hR⟩, -, -⟩
    rw [hst, show fOff pg n (t + 1) - 1 - fOff pg n t =
      (faceVerts pg n (segOrder pg n)[t]).length - 1 by omega] at hS
    refine ⟨?_, hR.1, hR.2.2.2.2.2.2.2⟩
    have htake := faceSids_eq_last (pg := pg) (n := n) (s := (segOrder pg n)[t]) (by omega)
    obtain ⟨hC, hSm, hA, hZ⟩ := hS
    have hlen : (doneS pg n t ++ (faceSids pg n (segOrder pg n)[t]).take
        ((faceVerts pg n (segOrder pg n)[t]).length - 1)).length =
          fOff pg n t + ((faceVerts pg n (segOrder pg n)[t]).length - 1) := by
      rw [List.length_append, length_doneS, List.length_take, length_faceSids]; omega
    rw [doneS_succ ht, htake, ← List.append_assoc]
    refine ⟨hC, hSm, hA.snoc (hZ _ le_rfl), ?_⟩
    simp only [List.length_append, List.length_singleton] at hZ ⊢
    exact hZ.mono (by omega)
  · rw [getD_of_lt ht]
    simp only [Finset.sum_const, Nat.card_Ico, smul_eq_mul]
    unfold tFs; omega

/-! ### Stage F -/

/-- The state before stage F. -/
def FsIn (pg : Graph) (n : ℕ) (c : Config) : Prop :=
  (FaceSt pg n c ∧ Zf c) ∧ OrdSt pg n c ∧ EnumSt pg n c ∧ PosSt pg n c

theorem fsAlloc_spec (F₀ : ℕ) (m₀ : ℕ → ℕ) (hB : F₀ ≤ S) :
    HTB S fsAlloc (fun c => FsIn pg n c ∧ c.reg rFREE = F₀ ∧ c.mem = m₀)
      (fun c => FsSt pg n F₀ m₀ (doneS pg n 0) c ∧ c.reg gNS = (segOrder pg n).length) 6 := by
  refine HTB.run_le (by decide) (by decide) fun c ⟨⟨⟨hF, hZ⟩, hO, hE, hP⟩, hFr, hm⟩ => ?_
  subst hm
  have hns : c.reg gNS = (segOrder pg n).length := by rw [hE.1, length_segOrder]
  refine ⟨by
    have := hF.1.2
    simp only [faceOffs, prefixSums, List.length_map, List.length_range] at this
    addr_ok [fsAlloc, hns], ?_⟩
  have hfo : c.mem (c.reg gFOFF + c.reg gNS) = (faceCat pg n).length := by
    rw [hns, hF.1.1.get (by simp [faceOffs, prefixSums]), faceOffs_get (by omega), fOff_full]
  have hw : ∀ r ∈ wregs fsAlloc, r ∈ [rT, rSN, gFSID, rFREE] := by decide
  have hreg : ∀ r, r ∉ [rT, rSN, gFSID, rFREE] → (RAM.run fsAlloc c).reg r = c.reg r :=
    fun r hr => run_reg_of_not_mem (by decide) (fun h => hr (hw r h)) c
  have hmem : (RAM.run fsAlloc c).mem = c.mem := run_mem_of_stores (by decide) rfl c
  have hfs : (RAM.run fsAlloc c).reg gFSID = F₀ := by
    simp only [fsAlloc, run_seq', run_ld]
    rw [run_alloc (by decide) (by decide)]
    simp +decide [hFr]
  have hfr : (RAM.run fsAlloc c).reg rFREE = F₀ + (faceCat pg n).length := by
    simp only [fsAlloc, run_seq', run_ld]
    rw [run_alloc (by decide) (by decide)]
    simp +decide [hFr, hfo]
  have hlo := length_ord3 (pg := pg) (n := n)
  have hle := length_segOrder (pg := pg) (n := n)
  have b1 := hO.2.1.2
  have b2 := hO.1.2
  have b3 := hE.2.2.2.1.2
  have b4 := hF.1.2
  have b5 := hF.2.2
  have b6 := hE.2.2.2.2.2.2.2
  have b7 := hP.2
  simp only [List.length_map, faceOffs, prefixSums, List.length_range] at b1 b2 b3 b4 b5
  unfold Zf at hZ
  refine ⟨⟨⟨?_, hfs, hfr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_⟩
  all_goals try rw [hreg _ (by decide)]
  all_goals try omega
  · exact hO.2.1.1
  · exact hO.1.1
  · exact hE.2.2.2.1.1
  · exact hF.1.1
  · exact hF.2.1
  · exact hE.2.2.2.2.2.2.1
  · exact hP.1
  · rw [hmem]; exact SameOn.refl _ _
  · simp [doneS]
  · rw [hmem]; simp only [doneS, List.take_zero, List.flatMap_nil, List.length_nil, Nat.add_zero]
    rw [hFr] at hZ; exact hZ

/-- **Stage F** (with its layout): the slot ids at `F₀`, `|faceCat|` cells. -/
theorem stageF_core (hP : IsPolygon pg n) (F₀ : ℕ) (m₀ : ℕ → ℕ)
    (hB : F₀ + (faceCat pg n).length ≤ S) :
    HTB S stageF (fun c => FsIn pg n c ∧ c.reg rFREE = F₀ ∧ c.mem = m₀)
      (fun c => (SlotSt pg n c ∧ Zf c) ∧ SameOn (· < F₀) m₀ c.mem ∧ F₀ ≤ c.reg rFREE ∧
        c.reg rFREE = F₀ + (faceCat pg n).length)
      (14 * (faceCat pg n).length + 38 * (segOrder pg n).length + 9) := by
  have hl := HTB.forUp (i := rST) (n := gNS) (N := (segOrder pg n).length) (body := fsBody)
    (fun t => FsSt pg n F₀ m₀ (doneS pg n t))
    (fun t => tFs (faceVerts pg n ((segOrder pg n).getD t (0, 0))).length)
    (by decide) (by decide) (by decide) (fun t => (FsSt.indep F₀ m₀ _).mono (by decide))
    (fun t ht => fsBody_spec hP F₀ m₀ hB t ht)
  refine ((fsAlloc_spec F₀ m₀ (by omega)).seq hl).mono (fun _ h => h) ?_ ?_
  · rintro c ⟨⟨hC, hSm, hA, hZ⟩, -, -⟩
    rw [doneS_full] at hA hZ
    refine ⟨⟨⟨by rw [hC.fsid]; exact hA, by rw [hC.fsid, hC.free, length_fsidCat]⟩, ?_⟩, hSm,
      by rw [hC.free]; omega, hC.free⟩
    unfold Zf; rw [hC.free, ← length_fsidCat]; exact hZ
  · have hsum := sum_range_getD (fun s => tFs (faceVerts pg n s).length + 4) (0, 0) (segOrder pg n)
    have hcat : ((segOrder pg n).map fun s => tFs (faceVerts pg n s).length + 4).sum =
        14 * (faceCat pg n).length + 38 * (segOrder pg n).length := by
      rw [faceCat, List.length_flatMap]
      unfold tFs
      rw [List.sum_map_add, List.sum_map_add, List.sum_map_mul_left]
      simp; ring
    rw [hsum, hcat]; omega

/-- **Stage F**: the slot ids (growth triple). -/
theorem stageF_spec (hP : IsPolygon pg n) :
    HGMB S stageF WF (FsIn pg n) (fun c => SlotSt pg n c ∧ Zf c) (66 * pg.length + 9)
      (2 * pg.length) := by
  refine HGMB.ofGhost (by decide) (fun _ h => h) fun F₀ m₀ hS => ?_
  have h1 := length_faceCat_le (pg := pg) (n := n) hP
  have h2 := length_segOrder (pg := pg) (n := n)
  have h3 := length_segEnum_le (pg := pg) (n := n)
  refine (stageF_core hP F₀ m₀ (by omega)).mono (fun _ h => h)
    (fun _ h => ⟨h.1, h.2.1, h.2.2.1, by rw [h.2.2.2]; omega⟩) ?_
  omega

end STACS2027.RAM.P1

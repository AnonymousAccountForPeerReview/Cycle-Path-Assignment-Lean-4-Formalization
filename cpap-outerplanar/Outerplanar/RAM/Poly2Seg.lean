module

public import Outerplanar.RAM.Poly2Ext
import Mathlib.Tactic

/-!
# Phase P2 of the polygon solver: the slots of a face

For the segment `s = (segOrder pg n)[t]`, the machine folds `extendParts` over the slots of
its face (`finPre_succ`, `extendParts_eq`): the slot `j` is read off the face vertices
(`gFV`, from the offset `fOff t`), its child segment is the slot id at the same position
(`gFSID`, `fsidCat_getD`), and the child's final partial paths, stored earlier (`FinOK`), are
scanned by `peLoop`. The current partial paths are at `rP` (`rPN` of them); the new ones are pushed at the
free pointer.

* `RCtx`, `LayOK`: the constant registers and data (addresses in a ghost layout `Lay`);
* `FinOK t`: the final partial paths of the segments before `t`, through the tables at `L.fb`
  (addresses) and `L.fc` (numbers);
* `slotBody_spec`, `slotLoop_spec`: one slot, all slots of a face (bounded triples: the
  lists of partial paths of the face, `encB k` cells per slot, end at or below `S`).
-/

@[expose] public section

namespace STACS2027.RAM.P2

open STACS2027.Poly P1

/-! ### Registers -/

/-- The first end `x` of the slot. -/
abbrev rX : ℕ := 135
/-- The segment id of the slot. -/
abbrev rCH : ℕ := 136
/-- Start of the new partial paths. -/
abbrev rQ : ℕ := 137
/-- Address of the current partial paths. -/
abbrev rP : ℕ := 138
/-- The slot counter. -/
abbrev rSj : ℕ := 140
/-- The number of slots. -/
abbrev rNSL : ℕ := 141
/-- The face offset of the segment. -/
abbrev rOFF : ℕ := 142
/-- The segment counter. -/
abbrev rSt : ℕ := 143
/-- The first end of the segment. -/
abbrev rSA : ℕ := 144

/-! ### Programs -/

/-- Read the slot id and the second vertex `y` of the slot. -/
def slRdA : Stmt :=
  .seq (.add rW rOFF rSj) (.seq (ld rCH gFSID rW) (.seq (addc rW rW 1) (ld rY gFV rW)))
/-- Find the child's records (none for a side). -/
def slRdB : Stmt :=
  .ifz rCH (.seq (.const rCN 0) (.const rCB 0))
    (.seq (subc rW rCH 1) (.seq (ld rCB rFB rW) (ld rCN rFC rW)))
/-- Read the slot. -/
def slRd : Stmt := .seq slRdA slRdB
/-- Start the new partial paths. -/
def slInit : Stmt := .seq (mov rQ rFREE) (.seq (.const rQN 0) (mov rPP rP))
/-- The new partial paths become the current ones. -/
def slFin : Stmt := .seq (mov rP rQ) (mov rPN rQN)
/-- **One slot.** -/
def slotBody : Stmt := .seq slRd (.seq slInit (.seq peLoop slFin))
/-- **All slots of a face.** -/
def slotLoop : Stmt := forUp rSj rNSL slotBody

/-- Steps for one slot. -/
def TSl (k : ℕ) : ℕ := TPL k + 30

/-! ### Layout and contexts -/

/-- The addresses of the data of stage R (ghosts). -/
structure Lay where
  /-- The second ends of the segments. -/
  sb : ℕ
  /-- The slot ids. -/
  fsid : ℕ
  /-- The face vertices. -/
  fv : ℕ
  /-- The face offsets. -/
  foff : ℕ
  /-- The first ends of the segments. -/
  sa : ℕ
  /-- The table of the addresses of the final partial paths. -/
  fb : ℕ
  /-- The table of the numbers of final partial paths. -/
  fc : ℕ
  /-- The start of the region of the partial paths. -/
  fr : ℕ

/-- The layout: the data below the tables, the tables below the region of the paths. -/
structure LayOK (pg : Graph) (n : ℕ) (L : Lay) : Prop where
  sb : L.sb + (segOrder pg n).length ≤ L.fb
  fsid : L.fsid + (faceCat pg n).length ≤ L.fb
  fv : L.fv + (faceCat pg n).length ≤ L.fb
  foff : L.foff + ((segOrder pg n).length + 1) ≤ L.fb
  sa : L.sa + (segOrder pg n).length ≤ L.fb
  fc : L.fb + (segOrder pg n).length ≤ L.fc
  fr : L.fc + (segOrder pg n).length ≤ L.fr

/-- The constant registers and data of stage R. -/
@[mk_iff] structure RCtx (pg : Graph) (n k : ℕ) (L : Lay) (c : Config) : Prop where
  rk : c.reg rK = k
  pn : c.reg gPN = n
  ns : c.reg gNS = (segOrder pg n).length
  rsb : c.reg gSB = L.sb
  rfsid : c.reg gFSID = L.fsid
  rfv : c.reg gFV = L.fv
  rfoff : c.reg gFOFF = L.foff
  rsa : c.reg gSA = L.sa
  rfb : c.reg rFB = L.fb
  rfc : c.reg rFC = L.fc
  sb : Arr c.mem L.sb ((segOrder pg n).map Prod.snd)
  fsid : Arr c.mem L.fsid (fsidCat pg n)
  fv : Arr c.mem L.fv (faceCat pg n)
  foff : Arr c.mem L.foff (faceOffs pg n)
  sa : Arr c.mem L.sa ((segOrder pg n).map Prod.fst)
  fr : L.fr ≤ c.reg rFREE

variable {pg : Graph} {n k : ℕ}

theorem RCtx.stable {L : Lay} (hL : LayOK pg n L) {W : List ℕ}
    (hW : ∀ r ∈ [rK, gPN, gNS, gSB, gFSID, gFV, gFOFF, gSA, rFB, rFC], r ∉ W) :
    Stable W (RCtx pg n k L) := fun c c' h hg => by
  have hm : ∀ a, a < L.fb → c'.mem a = c.mem a := fun a ha =>
    hg.mem a (show a < c.reg rFREE by have := h.fr; have := hL.fc; have := hL.fr; omega)
  have hS : SameOn (· < L.fb) c.mem c'.mem := fun a ha => hm a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hW
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hg.reg _ hW.1]; exact h.rk
  · rw [hg.reg _ hW.2.1]; exact h.pn
  · rw [hg.reg _ hW.2.2.1]; exact h.ns
  · rw [hg.reg _ hW.2.2.2.1]; exact h.rsb
  · rw [hg.reg _ hW.2.2.2.2.1]; exact h.rfsid
  · rw [hg.reg _ hW.2.2.2.2.2.1]; exact h.rfv
  · rw [hg.reg _ hW.2.2.2.2.2.2.1]; exact h.rfoff
  · rw [hg.reg _ hW.2.2.2.2.2.2.2.1]; exact h.rsa
  · rw [hg.reg _ hW.2.2.2.2.2.2.2.2.1]; exact h.rfb
  · rw [hg.reg _ hW.2.2.2.2.2.2.2.2.2]; exact h.rfc
  · exact h.sb.of_below hS (by simpa using hL.sb)
  · exact h.fsid.of_below hS (by rw [length_fsidCat]; exact hL.fsid)
  · exact h.fv.of_below hS hL.fv
  · exact h.foff.of_below hS (by simpa [faceOffs, prefixSums] using hL.foff)
  · exact h.sa.of_below hS (by simpa using hL.sa)
  · exact h.fr.trans hg.free

/-- The final partial paths of the segments before `t`. -/
def FinOK (pg : Graph) (n k : ℕ) (L : Lay) (t : ℕ) (c : Config) : Prop :=
  L.fr ≤ c.reg rFREE ∧ ∀ t', t' < t → ∀ (ht : t' < (segOrder pg n).length),
    L.fr ≤ c.mem (L.fb + t') ∧ Bel (c.mem (L.fb + t')) (enc (fin pg n k (segOrder pg n)[t'])) c ∧
    c.mem (L.fc + t') = (fin pg n k (segOrder pg n)[t']).length

theorem FinOK.stable {L : Lay} (hL : LayOK pg n L) (W : List ℕ) (t : ℕ) :
    Stable W (FinOK pg n k L t) := fun c c' h hg => by
  have hm : ∀ a, a < L.fr → c'.mem a = c.mem a := fun a ha =>
    hg.mem a (show a < c.reg rFREE by have := h.1; omega)
  refine ⟨h.1.trans hg.free, fun t' ht' hts => ?_⟩
  obtain ⟨h1, h2, h3⟩ := h.2 t' ht' hts
  have e1 : c'.mem (L.fb + t') = c.mem (L.fb + t') := hm _ (by have := hL.fc; have := hL.fr; omega)
  have e2 : c'.mem (L.fc + t') = c.mem (L.fc + t') := hm _ (by have := hL.fr; omega)
  rw [e1, e2]
  exact ⟨h1, stable_bel W _ _ c c' h2 hg, h3⟩

/-! ### Facts about faces -/

theorem fOff_le_length (t : ℕ) : fOff pg n t ≤ (faceCat pg n).length := by
  have h := congrArg List.length (List.take_append_drop t (segOrder pg n))
  rw [fOff, faceCat]
  conv_rhs => rw [← List.take_append_drop t (segOrder pg n)]
  rw [List.flatMap_append, List.length_append]
  omega

/-- The face vertex `j` of the segment `t`. -/
theorem faceCat_getD {t j : ℕ} (ht : t < (segOrder pg n).length)
    (hj : j < (faceVerts pg n (segOrder pg n)[t]).length) :
    (faceCat pg n).getD (fOff pg n t + j) 0 = (faceVerts pg n (segOrder pg n)[t])[j] := by
  have h := Poly.getD_flatMap (faceVerts pg n) 0 (segOrder pg n) t (segOrder pg n)[t]
    (List.getElem?_eq_getElem ht) j hj
  rw [getD_of_lt hj 0] at h
  rw [← h, faceCat, fOff, List.length_flatMap]

theorem fOff_add_lt {t j : ℕ} (ht : t < (segOrder pg n).length)
    (hj : j < (faceVerts pg n (segOrder pg n)[t]).length) :
    fOff pg n t + j < (faceCat pg n).length := by
  have h1 := fOff_succ (pg := pg) (n := n) ht
  have h2 := fOff_le_length (pg := pg) (n := n) (t + 1)
  omega

theorem faceOffs_getElem {t : ℕ} (ht : t < (segOrder pg n).length + 1) :
    (faceOffs pg n)[t]'(by simp [faceOffs, prefixSums]; omega) = fOff pg n t := by
  simp only [← map_fOff, List.getElem_map, List.getElem_range]

/-- The slot `j` of the segment `t`: its ends are adjacent, increasing, positions. -/
theorem slot_facts (hP : IsPolygon pg n) {t j : ℕ} (ht : t < (segOrder pg n).length)
    (hj : j < (slots pg n (segOrder pg n)[t]).length) :
    ∃ (h1 : j < (faceVerts pg n (segOrder pg n)[t]).length)
      (h2 : j + 1 < (faceVerts pg n (segOrder pg n)[t]).length),
      (slots pg n (segOrder pg n)[t])[j] = ((faceVerts pg n (segOrder pg n)[t])[j],
        (faceVerts pg n (segOrder pg n)[t])[j + 1]) ∧
      (faceVerts pg n (segOrder pg n)[t])[j] < (faceVerts pg n (segOrder pg n)[t])[j + 1] ∧
      (faceVerts pg n (segOrder pg n)[t])[j + 1] < n ∧
      Adj pg (faceVerts pg n (segOrder pg n)[t])[j] (faceVerts pg n (segOrder pg n)[t])[j + 1] := by
  have hl : (slots pg n (segOrder pg n)[t]).length = (faceVerts pg n (segOrder pg n)[t]).length - 1 :=
    length_pairs _
  have h1 : j < (faceVerts pg n (segOrder pg n)[t]).length := by omega
  have h2 : j + 1 < (faceVerts pg n (segOrder pg n)[t]).length := by omega
  have hs := mem_segOrder.mp (List.getElem_mem ht)
  have he := getElem_pairs (faceVerts pg n (segOrder pg n)[t]) j hj
  have hmem := mem_slots.mp (List.getElem_mem hj)
  rw [show (slots pg n (segOrder pg n)[t])[j] = (pairs (faceVerts pg n (segOrder pg n)[t]))[j] from rfl,
    he] at hmem
  have hlt := hP.infix_faceVerts_lt hs hmem
  have hsn := (lt_of_mem_segOrder (List.getElem_mem ht)).2
  exact ⟨h1, h2, he, hlt.2.1, by omega, hP.adj_of_infix_faceVerts hs hmem⟩

/-! ### Reading a slot -/

theorem slRdA_run (hP : IsPolygon pg n) {L : Lay} {t j : ℕ} (ht : t < (segOrder pg n).length)
    (hj : j < (slots pg n (segOrder pg n)[t]).length) (h1 : j < (faceVerts pg n (segOrder pg n)[t]).length)
    (h2 : j + 1 < (faceVerts pg n (segOrder pg n)[t]).length) {c : Config} (hR : RCtx pg n k L c)
    (hoff : c.reg rOFF = fOff pg n t) (hsj : c.reg rSj = j) :
    (RAM.run slRdA c).reg rY = (faceVerts pg n (segOrder pg n)[t])[j + 1] ∧
      (RAM.run slRdA c).reg rCH = segId pg n ((faceVerts pg n (segOrder pg n)[t])[j],
        (faceVerts pg n (segOrder pg n)[t])[j + 1]) ∧
      Agree [rT, rW, rX, rY, rCH] c (RAM.run slRdA c) := by
  have _ := hP
  have _ := hj
  have hy : c.mem (L.fv + (fOff pg n t + j + 1)) = (faceVerts pg n (segOrder pg n)[t])[j + 1] := by
    rw [Nat.add_assoc, hR.fv.getD (fOff_add_lt ht h2), faceCat_getD ht h2]
  have hid : c.mem (L.fsid + (fOff pg n t + j)) = segId pg n ((faceVerts pg n (segOrder pg n)[t])[j],
      (faceVerts pg n (segOrder pg n)[t])[j + 1]) := by
    rw [hR.fsid.getD (by rw [length_fsidCat]; exact fOff_add_lt ht h1), fsidCat_getD ht h1,
      getD_of_lt h1, getD_of_lt h2]
  refine ⟨?_, ?_, agree_run (by decide) rfl rfl (by decide) c⟩
  · simp +decide only [slRdA, run_seq', run_add, run_ld, run_addc (show rW ≠ rT by decide),
      setReg_reg, ↓reduceIte, setReg_mem, hoff, hsj, hR.rfv, hy]
  · simp +decide only [slRdA, run_seq', run_add, run_ld, run_addc (show rW ≠ rT by decide),
      setReg_reg, ↓reduceIte, setReg_mem, hoff, hsj, hR.rfsid, hid]

theorem slRd_run (hP : IsPolygon pg n) {L : Lay} {t j : ℕ}
    (ht : t < (segOrder pg n).length) (hj : j < (slots pg n (segOrder pg n)[t]).length)
    (h1 : j < (faceVerts pg n (segOrder pg n)[t]).length)
    (h2 : j + 1 < (faceVerts pg n (segOrder pg n)[t]).length) {c : Config} (hR : RCtx pg n k L c)
    (hF : FinOK pg n k L t c) (hoff : c.reg rOFF = fOff pg n t) (hsj : c.reg rSj = j) :
    (∃ cb, SCtx k (faceVerts pg n (segOrder pg n)[t])[j + 1] cb
      (cfin pg n k (faceVerts pg n (segOrder pg n)[t])[j] (faceVerts pg n (segOrder pg n)[t])[j + 1])
      (RAM.run slRd c)) ∧ Agree [rT, rW, rX, rY, rCH, rCN, rCB] c (RAM.run slRd c) := by
  obtain ⟨_, _, hsl, hxy, hyn, _⟩ := slot_facts hP ht hj
  obtain ⟨hY, hCH, hA⟩ := slRdA_run hP ht hj h1 h2 hR hoff hsj
  have hslm := List.getElem_mem hj
  rw [hsl] at hslm
  set x := (faceVerts pg n (segOrder pg n)[t])[j] with hxdef
  set y := (faceVerts pg n (segOrder pg n)[t])[j + 1] with hydef
  have hAll : Agree [rT, rW, rX, rY, rCH, rCN, rCB] c (RAM.run slRd c) :=
    agree_run (by decide) rfl rfl (by decide) c
  refine ⟨?_, hAll⟩
  have hrun : RAM.run slRd c = RAM.run slRdB (RAM.run slRdA c) := rfl
  have hk : (RAM.run slRd c).reg rK = k := by rw [hAll.reg _ (by decide)]; exact hR.rk
  have hy' : (RAM.run slRd c).reg rY = y := by
    rw [hrun]; simp only [slRdB, run_ifz']; split_ifs <;> simp +decide [run_subc, hY]
  have hmem : (RAM.run slRd c).mem = c.mem := hAll.mem
  have hfree : (RAM.run slRd c).reg rFREE = c.reg rFREE := hAll.reg _ (by decide)
  unfold segId at hCH
  by_cases hs : (x, y) ∈ segOrder pg n
  · -- a child segment
    rw [ite_eq_left hs] at hCH
    set i := (segOrder pg n).idxOf (x, y) with hidef
    have hi : i < (segOrder pg n).length := List.idxOf_lt_length_iff.mpr hs
    have hit : i < t := child_idx_lt hP ht hslm hs
    have hget : (segOrder pg n)[i] = (x, y) := List.getElem_idxOf hi
    obtain ⟨-, hb, hc⟩ := hF.2 i hit hi
    rw [hget] at hb hc
    have hcf : cfin pg n k x y = fin pg n k (x, y) := by
      rw [cfin, ite_eq_left (mem_segEnum.mpr (mem_segOrder.mp hs))]
    refine ⟨c.mem (L.fb + i), hk, hy', ?_, ?_, ?_⟩
    · rw [hrun]; simp +decide [slRdB, run_subc, hCH]
      rw [hA.mem, hA.reg _ (by decide), hR.rfb]
    · rw [hrun]; simp +decide [slRdB, run_subc, hCH]
      rw [hA.mem, hA.reg _ (by decide), hR.rfc, hc, hcf]
    · rw [hcf]; exact hb.mono hmem (by rw [hfree])
  · -- a side
    rw [ite_eq_right hs] at hCH
    have hcf : cfin pg n k x y = [] := by
      rw [cfin, ite_eq_right (fun h => hs (mem_segOrder.mpr (mem_segEnum.mp h)))]
    refine ⟨0, hk, hy', ?_, ?_, ?_⟩
    · rw [hrun]; simp [slRdB, hCH]
    · rw [hrun, hcf]; simp [slRdB, hCH]
    · rw [hcf]; exact ⟨by simp, by simp⟩

theorem segId_le (p : ℕ × ℕ) : segId pg n p ≤ (segOrder pg n).length := by
  unfold segId
  split_ifs with h
  · exact List.idxOf_lt_length_iff.mpr h
  · exact Nat.zero_le _

/-- Reading a slot reads the tables below `L.fr`. -/
theorem slRd_addrOK (hP : IsPolygon pg n) {L : Lay} (hL : LayOK pg n L) {t j : ℕ}
    (ht : t < (segOrder pg n).length) (hj : j < (slots pg n (segOrder pg n)[t]).length)
    (h1 : j < (faceVerts pg n (segOrder pg n)[t]).length)
    (h2 : j + 1 < (faceVerts pg n (segOrder pg n)[t]).length) {c : Config} (hR : RCtx pg n k L c)
    (hoff : c.reg rOFF = fOff pg n t) (hsj : c.reg rSj = j) {S : ℕ} (hS : L.fr ≤ S) :
    AddrOK S slRd c := by
  obtain ⟨-, hCH, hA⟩ := slRdA_run hP ht hj h1 h2 hR hoff hsj
  have hid : (RAM.run slRdA c).reg rCH ≤ (segOrder pg n).length := by rw [hCH]; exact segId_le _
  have hfb : (RAM.run slRdA c).reg rFB = L.fb := by rw [hA.reg _ (by decide)]; exact hR.rfb
  have hfc : (RAM.run slRdA c).reg rFC = L.fc := by rw [hA.reg _ (by decide)]; exact hR.rfc
  have hlt := fOff_add_lt ht h2
  have := hL.fsid; have := hL.fv; have := hL.fc; have := hL.fr
  refine AddrOK.seq (s := slRdA) (t := slRdB) ?_ ?_
  · addr_ok [slRdA, hoff, hsj, hR.rfsid, hR.rfv]
  · addr_ok [slRdB, hfb, hfc]

/-! ### One slot -/

/-- The state of stage R kept through the slots: the constant data, the final partial paths of
the segments before `t`, the memory below the tables. -/
def RSt (pg : Graph) (n k : ℕ) (L : Lay) (m₁ : ℕ → ℕ) (t : ℕ) (c : Config) : Prop :=
  RCtx pg n k L c ∧ FinOK pg n k L t c ∧ SameOn (· < L.fb) m₁ c.mem

theorem RSt.stable {L : Lay} (hL : LayOK pg n L) {W : List ℕ}
    (hW : ∀ r ∈ [rK, gPN, gNS, gSB, gFSID, gFV, gFOFF, gSA, rFB, rFC], r ∉ W) (m₁ : ℕ → ℕ)
    (t : ℕ) : Stable W (RSt pg n k L m₁ t) := fun c c' h hg =>
  ⟨RCtx.stable hL hW c c' h.1 hg, FinOK.stable hL W t c c' h.2.1 hg,
    hg.sameOn h.2.2 (by have := h.1.fr; have := hL.fc; have := hL.fr; omega)⟩

/-- A bound of the encoding of the partial paths: at most `partsBound k` of them, each with at
most `k + 2` entries. -/
def encB (k : ℕ) : ℕ := partsBound k * (k + 2)

theorem length_enc_le {l : List (List ℕ × ℕ)} (hl : l.length ≤ partsBound k)
    (h : ∀ pe ∈ l, pe.2 ≤ k ∧ pe.1.length = pe.2 + 1) : (enc l).length ≤ encB k := by
  have e : (enc l).length = (l.map fun pe => pe.1.length + 1).sum := by
    simp [enc, List.length_flatMap]
  rw [e]
  calc _ ≤ l.length * (k + 2) := sum_map_le_mul _ _ _ fun pe hpe => by have := h pe hpe; omega
    _ ≤ _ := Nat.mul_le_mul_right _ hl

theorem two_le_encB : 2 ≤ encB k := by
  unfold encB partsBound
  have := Nat.one_le_pow k (k * rpathBound (k + 1) + 1) (by omega)
  nlinarith

/-- The bound of the free pointer after `j` slots of the segment `t`: every current list of
partial paths so far, at most `encB k` cells each, lies above `L.fr`. -/
def FrB (pg : Graph) (n k : ℕ) (L : Lay) (t j : ℕ) (c : Config) : Prop :=
  c.reg rFREE ≤ L.fr + encB k * (fOff pg n t + j + 1)

/-- The invariant of the slots of the segment `t`, after `j` slots. -/
def SlInv (pg : Graph) (n k : ℕ) (L : Lay) (m₁ : ℕ → ℕ) (t j : ℕ) (c : Config) : Prop :=
  RSt pg n k L m₁ t c ∧ c.reg rOFF = fOff pg n t ∧ c.reg rSt = t ∧ L.fr ≤ c.reg rP ∧
    Bel (c.reg rP) (enc (finPre pg n k ((segOrder pg n).getD t (0, 0)) j)) c ∧
    c.reg rPN = (finPre pg n k ((segOrder pg n).getD t (0, 0)) j).length ∧ Zf c

theorem slInv_iff {L : Lay} {m₁ : ℕ → ℕ} {t j : ℕ} (ht : t < (segOrder pg n).length) {c : Config} :
    SlInv pg n k L m₁ t j c ↔ RSt pg n k L m₁ t c ∧ c.reg rOFF = fOff pg n t ∧ c.reg rSt = t ∧
      L.fr ≤ c.reg rP ∧ Bel (c.reg rP) (enc (finPre pg n k (segOrder pg n)[t] j)) c ∧
      c.reg rPN = (finPre pg n k (segOrder pg n)[t] j).length ∧ Zf c := by
  rw [SlInv, getD_of_lt ht]

theorem SlInv.indep (L : Lay) (m₁ : ℕ → ℕ) (t j : ℕ) :
    Indep [rT, rSj, rW, rX, rY, rCH, rCN, rCB, rQ, rQN, rPP] (SlInv pg n k L m₁ t j) := by
  indep [SlInv, RSt, rCtx_iff, FinOK, Bel, Zf]

theorem slotBody_spec {S : ℕ} (hP : IsPolygon pg n) {L : Lay} (hL : LayOK pg n L) (m₁ : ℕ → ℕ)
    {t : ℕ} (ht : t < (segOrder pg n).length) (N j : ℕ)
    (hj : j < (slots pg n (segOrder pg n)[t]).length)
    (hSz : L.fr + encB k * (fOff pg n t + j + 2) ≤ S) :
    HGB S slotBody (wregs slotLoop)
      (fun c => (SlInv pg n k L m₁ t j c ∧ FrB pg n k L t j c) ∧ c.reg rSj = j ∧ c.reg rNSL = N)
      (fun c => (SlInv pg n k L m₁ t (j + 1) c ∧ FrB pg n k L t (j + 1) c) ∧ c.reg rSj = j ∧
        c.reg rNSL = N) (TSl k) := by
  obtain ⟨h1, h2, hsl, hxy, hyn, hadj⟩ := slot_facts hP ht hj
  have hPb := finPre_bound (k := k) hP (segOrder pg n)[t] j
  have hcfb := cfin_bound (k := k) hP (faceVerts pg n (segOrder pg n)[t])[j]
    (faceVerts pg n (segOrder pg n)[t])[j + 1]
  -- the new partial paths
  have hnext : (finPre pg n k (segOrder pg n)[t] j).flatMap (fun pe => extPe k pe
      (faceVerts pg n (segOrder pg n)[t])[j + 1] (cfin pg n k (faceVerts pg n (segOrder pg n)[t])[j]
        (faceVerts pg n (segOrder pg n)[t])[j + 1])) = finPre pg n k (segOrder pg n)[t] (j + 1) := by
    rw [finPre_succ hj, hsl, extendParts_eq hP hxy hyn hadj]
  set x := (faceVerts pg n (segOrder pg n)[t])[j] with hxdef
  set y := (faceVerts pg n (segOrder pg n)[t])[j + 1] with hydef
  set P := finPre pg n k (segOrder pg n)[t] j with hPdef
  set cf := cfin pg n k x y with hcfdef
  refine HGB.ghost (fun c => (c.reg rP, c.reg rFREE)) fun bq => ?_
  obtain ⟨b, q⟩ := bq
  refine HGB.of_pre (fun c h => show L.fr ≤ q ∧ q ≤ L.fr + encB k * (fOff pg n t + j + 1) by
    have h1 := h.1.1.1.1.1.fr
    have h2 := h.1.1.2
    simp only [Prod.mk.injEq, FrB] at h h2
    rw [← h.2.2]; exact ⟨h1, h2⟩) fun ⟨hfrq, hqB⟩ => ?_
  have hB2 : encB k * (fOff pg n t + j + 2) = encB k * (fOff pg n t + j + 1) + encB k := by ring
  refine HGB.pre (P := fun c => (SlInv pg n k L m₁ t j c ∧ c.reg rSj = j ∧ c.reg rNSL = N) ∧
    (c.reg rP, c.reg rFREE) = (b, q)) ?_ fun c ⟨⟨⟨hI, _⟩, hs, hn⟩, hbq⟩ => ⟨⟨hI, hs, hn⟩, hbq⟩
  -- reading the slot
  have h₁ : HGB S slRd (wregs slotLoop)
      (fun c => (SlInv pg n k L m₁ t j c ∧ c.reg rSj = j ∧ c.reg rNSL = N) ∧
        (c.reg rP, c.reg rFREE) = (b, q))
      (fun c => ∃ cb, SCtx k y cb cf c ∧ (SlInv pg n k L m₁ t j c ∧ c.reg rSj = j ∧
        c.reg rNSL = N ∧ c.reg rP = b ∧ c.reg rFREE = q)) 21 := by
    refine (HGB.runR (s := slRd) (by decide) (by decide) (by decide) (by decide) (by decide)
      fun c hc => ?_).mono (by decide) (fun _ h => h) (fun _ h => h) le_rfl
    obtain ⟨⟨hI, hsj, hN⟩, hbq⟩ := hc
    simp only [Prod.mk.injEq] at hbq
    refine ⟨slRd_addrOK hP hL ht hj h1 h2 hI.1.1 hI.2.1 hsj (by omega), ?_⟩
    obtain ⟨hex, hA⟩ := slRd_run hP ht hj h1 h2 hI.1.1 hI.1.2.1 hI.2.1 hsj
    obtain ⟨cb, hcb⟩ := hex
    refine ⟨cb, hcb, ?_, ?_, ?_, ?_, ?_⟩
    · have := (SlInv.indep (pg := pg) (n := n) (k := k) L m₁ t j).mono (W' := [rT, rW, rX, rY, rCH, rCN, rCB])
        (by decide) c _ hA
      exact this hI
    · rw [hA.reg _ (by decide), hsj]
    · rw [hA.reg _ (by decide), hN]
    · rw [hA.reg _ (by decide), hbq.1]
    · rw [hA.reg _ (by decide), hbq.2]
  refine (h₁.seq (b₂ := TPL k + 9) (HGB.exists_pre fun cb => ?_)).weaken (by unfold TSl; omega)
  -- the frame of the scan
  let F : Config → Prop := fun c => RSt pg n k L m₁ t c ∧ (c.reg rOFF = fOff pg n t ∧ c.reg rSt = t ∧
    c.reg rSj = j ∧ c.reg rNSL = N ∧ c.reg rQ = q ∧ c.reg rP = b)
  have hFs : Stable (wregs peLoop) F := (RSt.stable hL (by decide) m₁ t).and (by stab)
  -- starting the new partial paths
  have h₂ : HGB S slInit (wregs slotLoop)
      (fun c => SCtx k y cb cf c ∧ (SlInv pg n k L m₁ t j c ∧ c.reg rSj = j ∧ c.reg rNSL = N ∧
        c.reg rP = b ∧ c.reg rFREE = q))
      (fun c => (PeInv k y cb cf b P q 0 c ∧ c.reg rPN = P.length) ∧ F c) 5 := by
    refine (HGB.runM (s := slInit) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) fun c hc => ?_).mono (by decide) (fun _ h => h) (fun _ h => h) le_rfl
    have hA : Agree [rT, rQ, rQN, rPP] c (RAM.run slInit c) :=
      agree_run (by decide) rfl rfl (by decide) c
    have hG := grow_of_agree (W := [rT, rQ, rQN, rPP]) hA (by decide) (by decide)
    obtain ⟨hC, hI, hsj, hN, hb, hq⟩ := hc
    obtain ⟨hR, hoff, hst, -, hB, hpn, hZ⟩ := (slInv_iff ht).mp hI
    rw [hb] at hB
    refine ⟨⟨⟨SCtx.stable (by decide) _ _ _ _ c _ hC hG, stable_bel _ _ _ c _ hB hG, ?_, ?_, ?_⟩,
      by rw [hA.reg _ (by decide), hpn]⟩, RSt.stable hL (by decide) m₁ t c _ hR hG, ?_, ?_, ?_, ?_,
      ?_, ?_⟩
    · simp +decide [slInit, run_mov, hb, encOff]
    · refine ⟨by simp, ?_, ?_⟩
      · rw [hA.reg _ (by decide), hq]; simp
      · rw [hA.reg _ (by decide), hA.mem]; exact hZ
    · simp +decide [slInit, run_mov]
    · rw [hA.reg _ (by decide), hoff]
    · rw [hA.reg _ (by decide), hst]
    · rw [hA.reg _ (by decide), hsj]
    · rw [hA.reg _ (by decide), hN]
    · simp +decide [slInit, run_mov, hq]
    · rw [hA.reg _ (by decide), hb]
  have he : extJ k P y cf P.length = finPre pg n k (segOrder pg n)[t] (j + 1) := by
    rw [extJ, List.take_length, ← hnext]
  have hPb' := finPre_bound (k := k) hP (segOrder pg n)[t] (j + 1)
  have hlen := length_enc_le hPb'.1 hPb'.2
  have h₃ := HGB.frame (peLoop_spec (S := S) k y cb cf b P q (fun pe hpe => hPb.2 pe hpe) hPb.1
    hcfb.2 hcfb.1 (by rw [he]; omega)) (F := F) hFs
  -- the new partial paths become the current ones
  have h₄ : HGB S slFin (wregs slotLoop)
      (fun c => (PeInv k y cb cf b P q P.length c ∧ c.reg rPJ = P.length ∧ c.reg rPN = P.length) ∧
        F c)
      (fun c => (SlInv pg n k L m₁ t (j + 1) c ∧ FrB pg n k L t (j + 1) c) ∧ c.reg rSj = j ∧
        c.reg rNSL = N) 4 := by
    refine (HGB.runM (s := slFin) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) fun c hc => ?_).mono (by decide) (fun _ h => h) (fun _ h => h) le_rfl
    have hA : Agree [rT, rP, rPN] c (RAM.run slFin c) :=
      agree_run (by decide) rfl rfl (by decide) c
    have hG := grow_of_agree (W := [rT, rP, rPN]) hA (by decide) (by decide)
    obtain ⟨⟨⟨-, -, -, hS, hn⟩, -, -⟩, hR, hoff, hst, hsj, hN, hq, -⟩ := hc
    rw [he] at hS hn
    have hS' := strm_agree hA (by decide) hS
    have hrp : (RAM.run slFin c).reg rP = q := by simp +decide [slFin, run_mov, hq]
    refine ⟨⟨(slInv_iff ht).mpr ⟨RSt.stable hL (by decide) m₁ t c _ hR hG,
      by rw [hA.reg _ (by decide), hoff], by rw [hA.reg _ (by decide), hst], by rw [hrp]; exact hfrq,
      ?_, ?_, hS'.2.2⟩, ?_⟩,
      by rw [hA.reg _ (by decide), hsj], by rw [hA.reg _ (by decide), hN]⟩
    · rw [hrp]; exact hS'.bel
    · rw [← hn]; simp +decide [slFin, run_mov]
    · unfold FrB; rw [hS'.2.1]
      have : encB k * (fOff pg n t + (j + 1) + 1) = encB k * (fOff pg n t + j + 2) := by ring
      omega
  exact (h₂.seq ((h₃.mono (by decide) (fun _ h => h) (fun _ h => h) le_rfl).seq h₄)).weaken
    (by omega)

/-- **All slots of the face of the segment `t`.** -/
theorem slotLoop_spec {S : ℕ} (hP : IsPolygon pg n) {L : Lay} (hL : LayOK pg n L)
    (m₁ : ℕ → ℕ) {t : ℕ} (ht : t < (segOrder pg n).length)
    (hSz : L.fr + encB k * (faceCat pg n).length ≤ S) :
    HGB S slotLoop (wregs slotLoop)
      (fun c => (SlInv pg n k L m₁ t 0 c ∧ FrB pg n k L t 0 c) ∧
        c.reg rNSL = (slots pg n (segOrder pg n)[t]).length)
      (fun c => (SlInv pg n k L m₁ t (slots pg n (segOrder pg n)[t]).length c ∧
        FrB pg n k L t (slots pg n (segOrder pg n)[t]).length c) ∧
        c.reg rSj = (slots pg n (segOrder pg n)[t]).length ∧
        c.reg rNSL = (slots pg n (segOrder pg n)[t]).length)
      ((slots pg n (segOrder pg n)[t]).length * (TSl k + 4) + 3) :=
  HGB.forUpC (W := wregs slotLoop) (i := rSj) (n := rNSL) (body := slotBody)
    (fun j c => SlInv pg n k L m₁ t j c ∧ FrB pg n k L t j c) (TSl k) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (fun j => ((SlInv.indep L m₁ t j).mono (by decide)).and (by unfold FrB; indep))
    (fun j hj => slotBody_spec hP hL m₁ ht _ j hj (by
      have h1 := fOff_succ (pg := pg) (n := n) ht
      have h2 := fOff_le_length (pg := pg) (n := n) (t + 1)
      have h3 := length_pairs (faceVerts pg n (segOrder pg n)[t])
      have h4 : (slots pg n (segOrder pg n)[t]).length =
          (faceVerts pg n (segOrder pg n)[t]).length - 1 := h3
      have := Nat.mul_le_mul_left (encB k) (show fOff pg n t + j + 2 ≤ (faceCat pg n).length by
        omega)
      omega))

end STACS2027.RAM.P2

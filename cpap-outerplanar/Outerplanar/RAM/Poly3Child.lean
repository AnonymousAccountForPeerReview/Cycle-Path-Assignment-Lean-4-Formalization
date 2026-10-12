module

public import Outerplanar.RAM.Poly3Sel
import Mathlib.Tactic

/-!
# Phase P3 of the polygon solver: the table entries of the children

`childCost` adds `table w (childIdx s w vals)` to `rTOT` for a child `w = (x, y)` of the
current segment `s` (`childCost_spec`):

* `ccPre`: the index `j'` of `w` in `segOrder` from the slot id `FSID[fOff s + q]` of the slot
  `q` of `w` (`fsidCat_getD`), the offset and the number of its boundary cycles from `gBOFF`;
* the digit loop (`encBody_spec`): for each boundary cycle `i` of `w`, its digit
  `digit s vals i` is found by a scan of the relevant cycles of `s` (`scan_spec`), and
  `acc += pw * d; pw *= k`, so that `acc` is the code `childIdx s w vals` at the end
  (`childIdx_eq`);
* `ccPost`: the entry `TAB[toff j' + acc]`, an entry of the tables of the earlier segments
  (`getD_tabDone`, `idxOf_child_lt`).
-/

@[expose] public section

namespace STACS2027.RAM.P3

open STACS2027.Poly STACS2027.RAM.P1

variable {pg : Graph} {n k : ℕ}

/-! ### The scan -/

/-- The scan loop. -/
abbrev scanL : Stmt := forUp rR2 rNR scanBody

theorem run_scanBody (c : Config) : (RAM.run scanBody c).reg rDI =
    if c.mem (c.reg rREL + c.reg rR2) = c.reg rIX then c.mem (c.reg rVAL + c.reg rR2)
    else c.reg rDI := by
  simp only [scanBody, run_seq']
  rw [run_ifEq (by decide) (by decide)]
  by_cases h : c.mem (c.reg rREL + c.reg rR2) = c.reg rIX <;>
    simp +decide [h]

/-- The value of the scan after `r` relevant cycles. -/
def scanV (l vals : List ℕ) (i r : ℕ) : ℕ := if i ∈ l.take r then vals.getD (l.idxOf i) 0 else 0

/-- **The scan** finds the digit of the cycle `i`. -/
theorem scan_spec {S j : ℕ} {vals : List ℕ} {i : ℕ} (G : Config → Prop)
    (hG : Indep (wregs scanL) G)
    (hGr : ∀ c, G c → Rd S pg n k j vals c ∧ c.reg rIX = i) (hP : IsPolygon pg n)
    (hj : j < (segOrder pg n).length) (hvl : vals.length = (rel pg n k (sg pg n j)).length) :
    HTB S scanL (fun c => G c ∧ c.reg rDI = 0)
      (fun c => G c ∧ c.reg rDI = digit pg n k (sg pg n j) vals i) (2 * Rb k * 14 + 3) := by
  set l := rel pg n k (sg pg n j)
  have hl := HTB.forUpC (S := S) (i := rR2) (n := rNR) (N := l.length) (body := scanBody)
    (fun r c => G c ∧ c.reg rDI = scanV l vals i r) 10 (by decide) (by decide) (by decide)
    (fun r => by indepG hG) (fun r hr => by
      refine HTB.run_le (by decide) (by decide) fun c ⟨⟨hg, hd⟩, hr2, hnr⟩ => ?_
      obtain ⟨hR, hix⟩ := hGr c hg
      have h1 : c.reg rREL + l.length ≤ S := hR.brl
      have h2 := hR.bvl
      refine ⟨by addr_ok [scanBody, hr2], ?_⟩
      have hag : Agree (wregs scanL) c (RAM.run scanBody c) :=
        agree_run (by decide) rfl rfl (by decide) c
      refine ⟨⟨hG c _ hag hg, ?_⟩, ?_, ?_⟩
      · rw [run_scanBody, hr2, hR.rl.getD hr, hR.vl.getD (by omega), hix]
        exact scan_step (nodup_rel _) i hr _ hd
      · rw [run_reg_of_not_mem (by decide) (by decide) c]; exact hr2
      · rw [run_reg_of_not_mem (by decide) (by decide) c]; exact hnr)
  have hrel := length_rel_le (k := k) hP (sg_mem hj)
  refine hl.mono (fun c ⟨hg, hd⟩ => ⟨⟨hg, by rw [hd]; simp [scanV]⟩, (hGr c hg).1.nr⟩) ?_ ?_
  · rintro c ⟨⟨hg, hd⟩, -, -⟩
    exact ⟨hg, by rw [hd]; exact scan_done hvl i⟩
  · have : l.length * (10 + 4) ≤ 2 * Rb k * 14 := Nat.mul_le_mul hrel le_rfl
    omega

/-! ### The digits of the child configuration -/

/-- The code of the first `t` digits of the child configuration. -/
def encT (pg : Graph) (n k j : ℕ) (vals : List ℕ) (w : ℕ × ℕ) (t : ℕ) : ℕ :=
  enc k ((List.range t).map fun t' => digit pg n k (sg pg n j) vals ((bnd pg n k w).getD t' 0))

/-- The digit loop. -/
abbrev encL : Stmt := forUp rT2 rBL encBody

/-- The bound of one digit. -/
def tEnc (k : ℕ) : ℕ := 2 * Rb k * 14 + 10 * k + 20

theorem encBody_spec {S j : ℕ} {vals : List ℕ} {w : ℕ × ℕ} {wb : ℕ} (G : Config → Prop)
    (hG : Indep (wregs encL) G)
    (hGr : ∀ c, G c → Rd S pg n k j vals c ∧ c.reg rWB = wb ∧
      ∀ t < (bnd pg n k w).length, c.mem (c.reg gBIDX + (wb + t)) = (bnd pg n k w).getD t 0)
    (hwb : ∀ t < (bnd pg n k w).length, wb + t < (bndCat pg n k).length)
    (hP : IsPolygon pg n) (hj : j < (segOrder pg n).length) (hk : 0 < k)
    (hvk : ∀ x ∈ vals, x < k) (hvl : vals.length = (rel pg n k (sg pg n j)).length)
    (t : ℕ) (ht : t < (bnd pg n k w).length) :
    HTB S encBody
      (fun c => (G c ∧ c.reg rACC = encT pg n k j vals w t ∧ c.reg rPW = k ^ t) ∧
        c.reg rT2 = t ∧ c.reg rBL = (bnd pg n k w).length)
      (fun c => (G c ∧ c.reg rACC = encT pg n k j vals w (t + 1) ∧ c.reg rPW = k ^ (t + 1)) ∧
        c.reg rT2 = t ∧ c.reg rBL = (bnd pg n k w).length) (tEnc k) := by
  set it := (bnd pg n k w).getD t 0
  set dt := digit pg n k (sg pg n j) vals it
  have hdt : dt < k := digit_lt hk hvk it
  -- the frame of the scan: everything but `rDI`
  let Q : Config → Prop := fun c => (G c ∧ c.reg rACC = encT pg n k j vals w t ∧
    c.reg rPW = k ^ t) ∧ c.reg rT2 = t ∧ c.reg rBL = (bnd pg n k w).length
  have h₁ : HTB S encRd Q
      (fun c => (Q c ∧ c.reg rIX = it) ∧ c.reg rDI = 0) 4 := by
    refine HTB.run_le (by decide) (by decide) fun c hc => ?_
    have hag : Agree (wregs encL) c (RAM.run encRd c) :=
      agree_run (by decide) rfl rfl (by decide) c
    obtain ⟨⟨hg, ha, hp⟩, ht2, hbl⟩ := hc
    obtain ⟨hR, hwbr, hbidx⟩ := hGr c hg
    have := hR.bbidx
    have := hwb t ht
    refine ⟨by addr_ok [encRd, hwbr, ht2], ?_⟩
    refine ⟨⟨⟨⟨hG c _ hag hg, ?_, ?_⟩, ?_, ?_⟩, ?_⟩, ?_⟩
    all_goals simp +decide only [encRd, run_seq', run_add, run_ld, run_const, setReg_reg,
      ↓reduceIte, setReg_mem, ha, hp, ht2, hbl, hwbr]
    exact hbidx t ht
  have h₂ := scan_spec (pg := pg) (j := j) (vals := vals) (i := it)
    (fun c => Q c ∧ c.reg rIX = it) (by indepG hG)
    (fun c hc => ⟨(hGr c hc.1.1.1).1, hc.2⟩) hP hj hvl
  have h₃ := HTB.mul (S := S) (P := fun c => (Q c ∧ c.reg rIX = it) ∧ c.reg rDI = dt) (d := rM)
    (a := rPW)
    (b := rDI) (k := rMK) (x := k ^ t) (y := dt) (by decide) (by indepG hG)
    (fun c hc => hc.1.1.1.2.2) (fun c hc => hc.2)
  have h₄ : HTB S (.add rACC rACC rM)
      (fun c => ((Q c ∧ c.reg rIX = it) ∧ c.reg rDI = dt) ∧ c.reg rM = k ^ t * dt)
      (fun c => (G c ∧ c.reg rACC = encT pg n k j vals w (t + 1) ∧ c.reg rPW = k ^ t) ∧
        c.reg rT2 = t ∧ c.reg rBL = (bnd pg n k w).length) 1 := by
    refine HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c hc => ?_
    obtain ⟨⟨⟨⟨⟨hg, ha, hp⟩, ht2, hbl⟩, -⟩, -⟩, hm⟩ := hc
    have hag : Agree (wregs encL) c (RAM.run (.add rACC rACC rM) c) :=
      agree_run (by decide) rfl rfl (by decide) c
    refine ⟨⟨hG c _ hag hg, ?_, ?_⟩, ?_, ?_⟩
    all_goals simp +decide only [run_add, setReg_reg, ↓reduceIte, ha, hp, ht2, hbl, hm]
    rw [encT, encT, enc_range_succ]
  have h₅ := HTB.mul (S := S) (P := fun c => (G c ∧ c.reg rACC = encT pg n k j vals w (t + 1) ∧
      c.reg rPW = k ^ t) ∧ c.reg rT2 = t ∧ c.reg rBL = (bnd pg n k w).length) (d := rM) (a := rPW)
    (b := rK) (k := rMK) (x := k ^ t) (y := k) (by decide) (by indepG hG)
    (fun c hc => hc.1.2.2) (fun c hc => (hGr c hc.1.1).1.kk)
  have h₆ : HTB S (mov rPW rM)
      (fun c => ((G c ∧ c.reg rACC = encT pg n k j vals w (t + 1) ∧ c.reg rPW = k ^ t) ∧
        c.reg rT2 = t ∧ c.reg rBL = (bnd pg n k w).length) ∧ c.reg rM = k ^ t * k)
      (fun c => (G c ∧ c.reg rACC = encT pg n k j vals w (t + 1) ∧ c.reg rPW = k ^ (t + 1)) ∧
        c.reg rT2 = t ∧ c.reg rBL = (bnd pg n k w).length) 2 := by
    refine HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c hc => ?_
    obtain ⟨⟨⟨hg, ha, -⟩, ht2, hbl⟩, hm⟩ := hc
    have hag : Agree (wregs encL) c (RAM.run (mov rPW rM) c) :=
      agree_run (by decide) rfl rfl (by decide) c
    refine ⟨⟨hG c _ hag hg, ?_, ?_⟩, ?_, ?_⟩
    all_goals simp +decide only [run_mov, setReg_reg, ↓reduceIte, ha, ht2, hbl, hm, pow_succ]
  have h₃' := h₃.weaken (show 5 * dt + 4 ≤ 5 * k + 4 by omega)
  have := h₁.seq (h₂.seq (h₃'.seq (h₄.seq (h₅.seq h₆))))
  refine this.weaken ?_
  unfold tEnc; omega

/-! ### The child -/

/-- The bound of `childCost`. -/
def tCC (k : ℕ) : ℕ := Rb k * (tEnc k + 4) + 25

theorem rd_bnd {S j : ℕ} {vals : List ℕ} {c : Config} (hR : Rd S pg n k j vals c) {j' : ℕ}
    (hj' : j' < (segOrder pg n).length) :
    c.mem (c.reg gBOFF + j') = (((segOrder pg n).take j').map fun t => (bnd pg n k t).length).sum ∧
      c.mem (c.reg gBOFF + (j' + 1)) = (((segOrder pg n).take j').map fun t =>
        (bnd pg n k t).length).sum + (bnd pg n k (segOrder pg n)[j']).length ∧
      ∀ t < (bnd pg n k (segOrder pg n)[j']).length,
        c.mem (c.reg gBIDX + ((((segOrder pg n).take j').map fun t => (bnd pg n k t).length).sum + t)) =
          (bnd pg n k (segOrder pg n)[j']).getD t 0 := by
  refine ⟨arr_prefixSums_seg_read _ hR.boff hj'.le, ?_, fun t ht => arr_flatMap_seg_read _ hR.bidx hj' ht⟩
  rw [arr_prefixSums_seg_read _ hR.boff hj', take_succ_segOrder hj', List.map_append, List.sum_append]
  simp

/-- **The table entry of a child**: `childCost` adds `table w (childIdx s w vals)` to `rTOT`
for the child `w = (x, y)` of the segment `j`. -/
theorem childCost_spec {S j : ℕ} {vals : List ℕ} {x y q t0 : ℕ} (G : Config → Prop)
    (hG : Indep (wregs childCost) G)
    (hGr : ∀ c, G c → Rd S pg n k j vals c ∧ c.reg rQ = q)
    (hP : IsPolygon pg n) (hj : j < (segOrder pg n).length) (hk : 0 < k)
    (hvk : ∀ x ∈ vals, x < k) (hvl : vals.length = (rel pg n k (sg pg n j)).length)
    (hq : q < (faceVerts pg n (sg pg n j)).length)
    (hxq : (faceVerts pg n (sg pg n j)).getD q 0 = x)
    (hyq : (faceVerts pg n (sg pg n j)).getD (q + 1) 0 = y)
    (hw : (x, y) ∈ childSegs pg n (sg pg n j)) :
    HTB S childCost (fun c => G c ∧ c.reg rTOT = t0)
      (fun c => G c ∧ c.reg rTOT = t0 + table pg n k (x, y) (childIdx pg n k (sg pg n j) (x, y) vals))
      (tCC k) := by
  have hws : (x, y) ∈ IsPolygon.segs pg n := ((mem_childSegs hP _ (x, y)).mp hw).1
  have hwS : (x, y) ∈ segOrder pg n := mem_segOrder.mpr hws
  set j' := (segOrder pg n).idxOf (x, y)
  have hj' : j' < (segOrder pg n).length := List.idxOf_lt_length_iff.mpr hwS
  have hSj' : (segOrder pg n)[j'] = (x, y) := List.getElem_idxOf hj'
  have hj'j : j' < j := by
    have := idxOf_child_lt hP hj (w := (x, y)) (by rw [← sg_eq hj]; exact hw)
    exact this
  set wb := (((segOrder pg n).take j').map fun t => (bnd pg n k t).length).sum
  let G' : Config → Prop := fun c => G c ∧ c.reg rTOT = t0 ∧ c.reg rWI = j' ∧ c.reg rWB = wb
  have hq2 : q < (faceVerts pg n (segOrder pg n)[j]).length := by rw [← sg_eq hj]; exact hq
  have hlt : fOff pg n j + q < (fsidCat pg n).length := by
    have := fOff_succ (pg := pg) (n := n) hj
    have := fOff_le_faceCat (pg := pg) (n := n) (j + 1)
    rw [length_fsidCat]; omega
  have hbo : (bndOffs pg n k).length = (segOrder pg n).length + 1 := by
    rw [bndOffs, length_prefixSums, List.length_map]
  have h₁ : HTB S ccPre (fun c => G c ∧ c.reg rTOT = t0)
      (fun c => (G' c ∧ c.reg rACC = encT pg n k j vals (x, y) 0 ∧ c.reg rPW = k ^ 0) ∧
        c.reg rBL = (bnd pg n k (x, y)).length) 16 := by
    refine HTB.run_le (by decide) (by decide) fun c ⟨hg, ht⟩ => ?_
    obtain ⟨hR, hq'⟩ := hGr c hg
    have hag : Agree (wregs childCost) c (RAM.run ccPre c) :=
      agree_run (by decide) rfl rfl (by decide) c
    have hfs : c.mem (c.reg gFSID + (fOff pg n j + q)) = j' + 1 := by
      rw [hR.fsid.getD hlt, fsidCat_getD hj hq2, ← sg_eq hj, hxq, hyq, segId_of_mem hwS]
    have := hR.bfsid
    have := hR.bboff
    refine ⟨by addr_ok [ccPre, hq', hR.fo, hfs], ?_⟩
    obtain ⟨hb0, hb1, -⟩ := rd_bnd hR hj'
    rw [hSj'] at hb1
    refine ⟨⟨⟨hG c _ hag hg, ?_, ?_, ?_⟩, ?_, ?_⟩, ?_⟩
    all_goals simp +decide only [ccPre, run_seq', run_ld, run_add, run_dec, run_addc, run_sub,
      run_const, setReg_reg, ↓reduceIte, setReg_mem, ht, hq', hR.fo, hfs, Nat.add_sub_cancel,
      hb0, hb1, encT, List.range_zero, List.map_nil, pow_zero]
    · rfl
    · rfl
    · exact Nat.add_sub_cancel_left _ _
  have hR' : ∀ c, G' c → Rd S pg n k j vals c ∧ c.reg rWB = wb ∧
      ∀ t < (bnd pg n k (x, y)).length, c.mem (c.reg gBIDX + (wb + t)) = (bnd pg n k (x, y)).getD t 0 := by
    intro c hc
    obtain ⟨-, -, h3⟩ := rd_bnd (hGr c hc.1).1 hj'
    rw [hSj'] at h3
    exact ⟨(hGr c hc.1).1, hc.2.2.2, h3⟩
  have hwb : ∀ t < (bnd pg n k (x, y)).length, wb + t < (bndCat pg n k).length := fun t ht => by
    have := lt_length_flatMap_seg (pg := pg) (n := n) (bnd pg n k) hj' (i := t)
      (by rw [hSj']; exact ht)
    rwa [bndCat]
  have h₂ := HTB.forUpC (S := S) (i := rT2) (n := rBL) (N := (bnd pg n k (x, y)).length)
    (body := encBody)
    (fun t c => G' c ∧ c.reg rACC = encT pg n k j vals (x, y) t ∧ c.reg rPW = k ^ t) (tEnc k)
    (by decide) (by decide) (by decide) (fun t => by indepG hG)
    (fun t ht => encBody_spec G' (by indepG hG) hR' hwb hP hj hk hvk hvl t ht)
  have hcl := childIdx_lt (pg := pg) (n := n) (s := sg pg n j) (w := (x, y)) hk hvk
  have hjS : j ≤ (segOrder pg n).length := hj.le
  have hlt2 :
      childIdx pg n k (sg pg n j) (x, y) vals < k ^ (bnd pg n k (segOrder pg n)[j']).length := by
    rw [hSj']; exact hcl
  have hidx := toffAt_add_lt (pg := pg) (n := n) (k := k) hj'j hj' hlt2
  have h₃ : HTB S ccPost
      (fun c => ((G' c ∧ c.reg rACC = encT pg n k j vals (x, y) (bnd pg n k (x, y)).length ∧
        c.reg rPW = k ^ (bnd pg n k (x, y)).length) ∧ c.reg rT2 = (bnd pg n k (x, y)).length ∧
        c.reg rBL = (bnd pg n k (x, y)).length))
      (fun c => G c ∧ c.reg rTOT = t0 + table pg n k (x, y) (childIdx pg n k (sg pg n j) (x, y) vals)) 6 := by
    refine HTB.run_le (by decide) (by decide) fun c ⟨⟨⟨hg, ht, hwi, _⟩, ha, _⟩, _, _⟩ => ?_
    have hR := (hGr c hg).1
    have hag : Agree (wregs childCost) c (RAM.run ccPost c) :=
      agree_run (by decide) rfl rfl (by decide) c
    have ha' : c.reg rACC = childIdx pg n k (sg pg n j) (x, y) vals := by rw [ha, childIdx_eq]; rfl
    have htoff : c.mem (c.reg gTOFF + j') = toffAt pg n k j' := by
      rw [hR.toff.getD (by rw [length_tabOffs]; omega), getD_tabOffs (by omega)]
    have htab : c.mem (c.reg gTAB + (toffAt pg n k j' + childIdx pg n k (sg pg n j) (x, y) vals)) =
        table pg n k (x, y) (childIdx pg n k (sg pg n j) (x, y) vals) := by
      have h := getD_tabDone (pg := pg) (n := n) (k := k) hjS hj'j hlt2
      rw [hSj'] at h
      rw [hR.tb.getD (by rw [length_tabDone]; exact hidx), h]
    have := hR.btoff
    have := hR.btb
    rw [length_tabDone] at this
    rw [length_tabOffs] at *
    refine ⟨by addr_ok [ccPost, hwi, htoff, ha'], ?_⟩
    refine ⟨hG c _ hag hg, ?_⟩
    simp +decide only [ccPost, run_seq', run_ld, run_add, setReg_reg, ↓reduceIte, setReg_mem, hwi,
      htoff, ha', htab, ht]
  have hb := length_bnd_le' (k := k) hP hws
  have hle : (bnd pg n k (x, y)).length * (tEnc k + 4) ≤ Rb k * (tEnc k + 4) :=
    Nat.mul_le_mul_right _ hb
  exact (h₁.seq (h₂.seq h₃)).weaken (by unfold tCC; omega)

end STACS2027.RAM.P3

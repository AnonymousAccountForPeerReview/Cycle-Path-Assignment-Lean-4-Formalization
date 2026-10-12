module

public import Outerplanar.RAM.Poly3Alpha
import Mathlib.Tactic

/-!
# Phase P3 of the polygon solver: one segment and the loop over the segments

* `segRd_spec`: the data of the segment `j` (`SegD`) from the interface arrays: its ends, its
  face offset and size, the offset and number of its boundary cycles, the first index and the
  number of its top cycles (`topIdx_eq`), its table offset;
* `segPow_spec`: `k ^ nb`, `k ^ nc`;
* `segRel_spec`: the relevant cycles `rel s = bnd s ++ topIdx s` written to a fresh array
  (`relBody_spec`), and fresh zero digits;
* `segBody_spec`: the segment `j`: from `MSt j` (the tables of the first `j` segments) to
  `MSt (j + 1)`;
* `segLoop_spec`: all segments.

All triples are bounded (`HTB S`): before the segment `j` the free pointer is at most
`A + toffAt NS + 4 Rb k j` (`FrP`), so `S ≥ A + toffAt NS + 4 Rb k NS` suffices for the loop.
-/

@[expose] public section

namespace STACS2027.RAM.P3

open STACS2027.Poly STACS2027.RAM.P1

variable {pg : Graph} {n k : ℕ}

/-! ### The state of the main loop -/

/-- The state before the segment `j`: the registers, the tables of the first `j` segments at
`T` and `A`, the memory below `T` as `mR`. -/
def MSt (pg : Graph) (n k : ℕ) (mR : ℕ → ℕ) (T A j : ℕ) (c : Config) : Prop :=
  (Glob pg n k mR T c ∧ c.reg gARG = A ∧ A + toffAt pg n k (segOrder pg n).length ≤ c.reg rFREE) ∧
    SameOn (· < T) mR c.mem ∧ Arr c.mem T (tabDone pg n k j) ∧ Arr c.mem A (argDone pg n k j) ∧
    ZeroFrom c.mem (c.reg rFREE)

/-- The data of the segment `j` read by `segRd`. -/
@[mk_iff] structure SegD (pg : Graph) (n k j : ℕ) (c : Config) : Prop where
  jj : c.reg rJ = j
  sa : c.reg rSA = (sg pg n j).1
  sb : c.reg rSB = (sg pg n j).2
  fo : c.reg rFO = fOff pg n j
  fl : c.reg rFL = (faceVerts pg n (sg pg n j)).length - 1
  nb : c.reg rNB = (bnd pg n k (sg pg n j)).length
  nc : c.reg rNC = (topIdx pg n k (sg pg n j)).length
  nr : c.reg rNR = (rel pg n k (sg pg n j)).length
  tO : c.reg rTO = toffAt pg n k j
  sbo : c.reg rSBO = (((segOrder pg n).take j).map fun t => (bnd pg n k t).length).sum
  ts : c.reg rTS = (((segOrder pg n).take j).map fun t => (rpF pg n k n t.1 t.2 k).length).sum

theorem sum_take_succ_seg (g : ℕ × ℕ → ℕ) {j : ℕ} (hj : j < (segOrder pg n).length) :
    (((segOrder pg n).take (j + 1)).map g).sum = (((segOrder pg n).take j).map g).sum + g (segOrder pg n)[j] := by
  rw [take_succ_segOrder hj, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]

/-- The top cycles of the segment `j`. -/
theorem topIdx_sg {j : ℕ} (hj : j < (segOrder pg n).length) :
    topIdx pg n k (sg pg n j) = List.range'
      (((segOrder pg n).take j).map fun t => (rpF pg n k n t.1 t.2 k).length).sum
      (rpF pg n k n (segOrder pg n)[j].1 (segOrder pg n)[j].2 k).length := by
  rw [sg_eq hj]; exact topIdx_eq (List.getElem?_eq_getElem hj)

theorem length_topIdx_sg {j : ℕ} (hj : j < (segOrder pg n).length) :
    (topIdx pg n k (sg pg n j)).length = (rpF pg n k n (segOrder pg n)[j].1 (segOrder pg n)[j].2 k).length := by
  rw [topIdx_sg hj, List.length_range']

theorem segRd_spec {S : ℕ} {mR : ℕ → ℕ} {T A j : ℕ} (hj : j < (segOrder pg n).length)
    (hT : T ≤ S) :
    HTB S segRd (fun c => MSt pg n k mR T A j c ∧ c.reg rJ = j ∧
      c.reg gNS = (segOrder pg n).length)
      (fun c => MSt pg n k mR T A j c ∧ SegD pg n k j c) 26 := by
  refine HTB.run_le (by decide) (by decide) fun c ⟨hM, hJ, _⟩ => ?_
  have hg := hM.1.1
  have := hg.bsa; have := hg.bsb; have := hg.bfoff; have := hg.btst; have := hg.bboff
  have := hg.btoff
  refine ⟨by addr_ok [segRd, hJ], ?_⟩
  have hag : Agree (wregs segRd) c (RAM.run segRd c) := agree_run (by decide) rfl rfl (by decide) c
  refine ⟨(show Indep (wregs segRd) (MSt pg n k mR T A j) by unfold MSt; indep [glob_iff]) c _ hag hM, ?_⟩
  obtain ⟨hsa, hsb, -, hfoff, -, -, htst, hboff, -, htoff⟩ := hM.1.1.rd hM.2.1
  have hSj := sg_eq (pg := pg) (n := n) hj
  have e1 : c.mem (c.reg gSA + j) = (sg pg n j).1 := by
    rw [hsa.getD (by simpa using hj), hSj]; simp [List.getD_eq_getElem?_getD, hj]
  have e2 : c.mem (c.reg gSB + j) = (sg pg n j).2 := by
    rw [hsb.getD (by simpa using hj), hSj]; simp [List.getD_eq_getElem?_getD, hj]
  have e3 : c.mem (c.reg gFOFF + j) = fOff pg n j := by
    rw [arr_prefixSums_seg_read _ hfoff hj.le, fOff_eq]
  have e4 : c.mem (c.reg gFOFF + (j + 1)) = fOff pg n j + (faceVerts pg n (sg pg n j)).length := by
    rw [arr_prefixSums_seg_read _ hfoff hj, sum_take_succ_seg _ hj, fOff_eq, hSj]
  have e5 : c.mem (c.reg gBOFF + j) = (((segOrder pg n).take j).map fun t => (bnd pg n k t).length).sum :=
    arr_prefixSums_seg_read _ hboff hj.le
  have e6 : c.mem (c.reg gBOFF + (j + 1)) =
      (((segOrder pg n).take j).map fun t => (bnd pg n k t).length).sum + (bnd pg n k (sg pg n j)).length := by
    rw [arr_prefixSums_seg_read _ hboff hj, sum_take_succ_seg _ hj, hSj]
  have e7 : c.mem (c.reg gTST + j) =
      (((segOrder pg n).take j).map fun t => (rpF pg n k n t.1 t.2 k).length).sum :=
    arr_prefixSums_seg_read _ htst hj.le
  have e8 : c.mem (c.reg gTST + (j + 1)) =
      (((segOrder pg n).take j).map fun t => (rpF pg n k n t.1 t.2 k).length).sum +
        (topIdx pg n k (sg pg n j)).length := by
    rw [arr_prefixSums_seg_read _ htst hj, sum_take_succ_seg _ hj, length_topIdx_sg hj]
  have e9 : c.mem (c.reg gTOFF + j) = toffAt pg n k j := by
    rw [htoff.getD (by rw [length_tabOffs]; omega), getD_tabOffs hj.le]
  have hrel : (rel pg n k (sg pg n j)).length =
      (bnd pg n k (sg pg n j)).length + (topIdx pg n k (sg pg n j)).length := by
    rw [rel, List.length_append]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp +decide only [segRd, run_seq', run_ld, run_addc, run_sub, run_dec, run_add,
    setReg_reg, ↓reduceIte, setReg_mem, hJ, e1, e2, e3, e4, e5, e6, e7, e8, e9,
    Nat.add_sub_cancel_left, hrel]

/-! ### The powers -/

theorem segPow_spec {S : ℕ} {mR : ℕ → ℕ} {T A j : ℕ} :
    HTB S segPow (fun c => MSt pg n k mR T A j c ∧ SegD pg n k j c)
      (fun c => ((MSt pg n k mR T A j c ∧ SegD pg n k j c) ∧
        c.reg rPB = k ^ (bnd pg n k (sg pg n j)).length) ∧
        c.reg rPC = k ^ (topIdx pg n k (sg pg n j)).length)
      ((bnd pg n k (sg pg n j)).length * (5 * k + 10) + 8 +
        ((topIdx pg n k (sg pg n j)).length * (5 * k + 10) + 8)) := by
  have h₁ := powTo_spec (k := k) (e := (bnd pg n k (sg pg n j)).length) (dst := rPB) (src := rNB)
    (fun c => MSt pg n k mR T A j c ∧ SegD pg n k j c)
    (by unfold MSt; indep [glob_iff, segD_iff]) (fun c hc => ⟨hc.1.1.1.kk, hc.2.nb⟩)
    (by decide) (by decide) (by decide)
  have h₂ := powTo_spec (k := k) (e := (topIdx pg n k (sg pg n j)).length) (dst := rPC) (src := rNC)
    (fun c => (MSt pg n k mR T A j c ∧ SegD pg n k j c) ∧
      c.reg rPB = k ^ (bnd pg n k (sg pg n j)).length)
    (by unfold MSt; indep [glob_iff, segD_iff]) (fun c hc => ⟨hc.1.1.1.1.kk, hc.1.2.nc⟩)
    (by decide) (by decide) (by decide)
  exact HTB.of_HT rfl (h₁.seq h₂)

/-! ### The relevant cycles -/

theorem getD_rel_sg {j : ℕ} (hj : j < (segOrder pg n).length) {r : ℕ}
    (hr : r < (rel pg n k (sg pg n j)).length) :
    (rel pg n k (sg pg n j)).getD r 0 = if r < (bnd pg n k (sg pg n j)).length then
      (bnd pg n k (sg pg n j)).getD r 0 else
      (((segOrder pg n).take j).map fun t => (rpF pg n k n t.1 t.2 k).length).sum +
        (r - (bnd pg n k (sg pg n j)).length) := by
  have hl : (rel pg n k (sg pg n j)).length =
      (bnd pg n k (sg pg n j)).length + (topIdx pg n k (sg pg n j)).length := by
    rw [rel, List.length_append]
  split
  · exact getD_append_left' 0 (by omega)
  · rw [rel, getD_append_right' 0 (by omega)]
    have h2 : r - (bnd pg n k (sg pg n j)).length < (topIdx pg n k (sg pg n j)).length := by omega
    rw [getD_of_lt h2]
    simp only [topIdx_sg hj, List.getElem_range']
    omega

theorem run_relBody (c : Config) :
    (RAM.run relBody c).mem = upd c.mem (c.reg rREL + c.reg rR)
      (if c.reg rR < c.reg rNB then c.mem (c.reg gBIDX + (c.reg rSBO + c.reg rR))
        else c.reg rTS + c.reg rR - c.reg rNB) := by
  simp only [relBody]
  rw [run_ifLt]
  split_ifs <;> simp +decide [run_st]

/-- The state of the fill of the relevant cycles. -/
def RInv (pg : Graph) (n k : ℕ) (mR : ℕ → ℕ) (T A R j r : ℕ) (c : Config) : Prop :=
  (Glob pg n k mR T c ∧ SegD pg n k j c ∧ c.reg rPB = k ^ (bnd pg n k (sg pg n j)).length ∧
    c.reg rPC = k ^ (topIdx pg n k (sg pg n j)).length ∧ c.reg gARG = A ∧ c.reg rREL = R ∧
    c.reg rFREE = R + (rel pg n k (sg pg n j)).length) ∧
  (SameOn (· < T) mR c.mem ∧ Arr c.mem T (tabDone pg n k j) ∧ Arr c.mem A (argDone pg n k j) ∧
    Arr c.mem R ((rel pg n k (sg pg n j)).take r) ∧ ZeroFrom c.mem (R + (rel pg n k (sg pg n j)).length))

theorem relBody_spec {S : ℕ} {mR : ℕ → ℕ} {T A R j : ℕ} (hj : j < (segOrder pg n).length)
    (hTA : T + toffAt pg n k (segOrder pg n).length = A)
    (hAR : A + toffAt pg n k (segOrder pg n).length ≤ R)
    (hSz : R + (rel pg n k (sg pg n j)).length ≤ S) (r : ℕ)
    (hr : r < (rel pg n k (sg pg n j)).length) :
    HTB S relBody (fun c => RInv pg n k mR T A R j r c ∧ c.reg rR = r ∧
        c.reg rNR = (rel pg n k (sg pg n j)).length)
      (fun c => RInv pg n k mR T A R j (r + 1) c ∧ c.reg rR = r ∧
        c.reg rNR = (rel pg n k (sg pg n j)).length) 11 := by
  refine HTB.run_le (by decide) (by decide) fun c ⟨⟨hreg, hsame, htb, hag, hrl, hz⟩, hR, hNR⟩ => ?_
  have hreg' : ∀ x, x ∉ wregs relBody → (RAM.run relBody c).reg x = c.reg x :=
    fun x hx => run_reg_of_not_mem (by decide) hx c
  have hbl : r < (bnd pg n k (sg pg n j)).length → c.reg gBIDX + (c.reg rSBO + r) < S := by
    intro hrb
    have h1 := lt_length_flatMap_seg (pg := pg) (n := n) (bnd pg n k) hj (i := r)
      (by rw [← sg_eq hj]; exact hrb)
    have h2 := hreg.1.bbidx
    rw [hreg.2.1.sbo]
    rw [bndCat] at h2
    omega
  have hrr0 := hreg.2.2.2.2.2.1
  have hnb0 := hreg.2.1.nb
  refine ⟨by addr_ok [relBody, hR, hnb0, hrr0], ?_⟩
  have hreg2 := (show RegIndep (wregs relBody) (fun c => Glob pg n k mR T c ∧ SegD pg n k j c ∧
      c.reg rPB = k ^ (bnd pg n k (sg pg n j)).length ∧
      c.reg rPC = k ^ (topIdx pg n k (sg pg n j)).length ∧ c.reg gARG = A ∧ c.reg rREL = R ∧
      c.reg rFREE = R + (rel pg n k (sg pg n j)).length) by indep [glob_iff, segD_iff]) c _ hreg' hreg
  obtain ⟨hg, hd, -, -, -, hrr, -⟩ := hreg
  have hval : (if c.reg rR < c.reg rNB then c.mem (c.reg gBIDX + (c.reg rSBO + c.reg rR))
      else c.reg rTS + c.reg rR - c.reg rNB) = (rel pg n k (sg pg n j)).getD r 0 := by
    rw [getD_rel_sg hj hr, hR, hd.nb, hd.sbo, hd.ts]
    split
    · next h =>
      obtain ⟨-, -, -, -, -, -, -, -, hbidx, -⟩ := hg.rd hsame
      rw [arr_flatMap_seg_read _ hbidx hj (by rw [← sg_eq hj]; exact h), sg_eq hj]
    · omega
  have hlen : ((rel pg n k (sg pg n j)).take r).length = r := by rw [List.length_take]; omega
  have hTlen := length_tabDone (pg := pg) (n := n) (k := k) j
  have hAlen := length_argDone (pg := pg) (n := n) (k := k) j
  have hmono := toffAt_mono (pg := pg) (n := n) (k := k) (show j ≤ (segOrder pg n).length by omega)
  refine ⟨⟨hreg2, ?_, ?_, ?_, ?_, ?_⟩, by rw [hreg' _ (by decide)]; exact hR,
    by rw [hreg' _ (by decide)]; exact hNR⟩
  all_goals rw [run_relBody, hval, hrr, hR]
  · exact hsame.upd_of_ge (by omega) _
  · exact htb.upd_of_disjoint (by omega)
  · exact hag.upd_of_disjoint (by omega)
  · rw [List.take_succ_eq_append_getElem hr, ← getD_of_lt hr]
    exact hrl.upd_snoc (by rw [hlen])
  · exact hz.upd (by omega)

theorem cfg_zero_eq (k L : ℕ) : cfg k L 0 = List.replicate L 0 := by
  simp [cfg, List.map_const']

theorem segRel_spec {S : ℕ} {mR : ℕ → ℕ} {T A j : ℕ} (hj : j < (segOrder pg n).length)
    (hTA : T + toffAt pg n k (segOrder pg n).length = A) (R : ℕ)
    (hAR : A + toffAt pg n k (segOrder pg n).length ≤ R)
    (hSz : R + (rel pg n k (sg pg n j)).length ≤ S) :
    HTB S segRel (fun c => (((MSt pg n k mR T A j c ∧ SegD pg n k j c) ∧
        c.reg rPB = k ^ (bnd pg n k (sg pg n j)).length) ∧
        c.reg rPC = k ^ (topIdx pg n k (sg pg n j)).length) ∧ c.reg rFREE = R)
      (fun c => Lay pg n k T A R (R + (rel pg n k (sg pg n j)).length) j ∧
        AInv pg n k mR T A R (R + (rel pg n k (sg pg n j)).length) j 0 c ∧
        c.reg rPB = k ^ (bnd pg n k (sg pg n j)).length)
      ((rel pg n k (sg pg n j)).length * 15 + 13) := by
  set nr := (rel pg n k (sg pg n j)).length
  have h₁ : HTB S (alloc rREL rNR) (fun c => (((MSt pg n k mR T A j c ∧ SegD pg n k j c) ∧
        c.reg rPB = k ^ (bnd pg n k (sg pg n j)).length) ∧
        c.reg rPC = k ^ (topIdx pg n k (sg pg n j)).length) ∧ c.reg rFREE = R)
      (fun c => RInv pg n k mR T A R j 0 c ∧ c.reg rNR = nr) 3 := by
    refine HTB.of_HT rfl <| HT.run_le (by decide) (by decide)
      fun c ⟨⟨⟨⟨⟨⟨hg, harg, _⟩, hsame, htb, hag, hz⟩, hd⟩, hpb⟩, hpc⟩,
      hF⟩ => ?_
    have hreg' : ∀ x, x ∉ wregs (alloc rREL rNR) → (RAM.run (alloc rREL rNR) c).reg x = c.reg x :=
      fun x hx => run_reg_of_not_mem (by decide) hx c
    have hR := (show RegIndep (wregs (alloc rREL rNR)) (fun c => Glob pg n k mR T c ∧ SegD pg n k j c ∧
      c.reg rPB = k ^ (bnd pg n k (sg pg n j)).length ∧
      c.reg rPC = k ^ (topIdx pg n k (sg pg n j)).length ∧ c.reg gARG = A) by
        indep [glob_iff, segD_iff]) c _ hreg' ⟨hg, hd, hpb, hpc, harg⟩
    obtain ⟨hg', hd', hpb', hpc', harg'⟩ := hR
    have hmem : (RAM.run (alloc rREL rNR) c).mem = c.mem := run_mem_of_stores (by decide) rfl c
    refine ⟨⟨⟨hg', hd', hpb', hpc', harg', ?_, ?_⟩, ?_⟩, ?_⟩
    · rw [run_alloc (by decide) (by decide)]; simp +decide [hF]
    · rw [run_alloc (by decide) (by decide)]; simp +decide [hF, hd.nr]
    · rw [hmem]
      exact ⟨hsame, htb, hag, by simp, hz.mono (by rw [hF]; omega)⟩
    · rw [hreg' _ (by decide)]; exact hd.nr
  have h₂ := HTB.forUpC (S := S) (i := rR) (n := rNR) (N := nr) (body := relBody)
    (RInv pg n k mR T A R j) 11
    (by decide) (by decide) (by decide) (fun r => by unfold RInv; indep [glob_iff, segD_iff])
    (fun r hr => relBody_spec hj hTA hAR hSz r hr)
  have h₃ : HTB S valAlloc (fun c => RInv pg n k mR T A R j nr c ∧ c.reg rR = nr ∧ c.reg rNR = nr)
      (fun c => Lay pg n k T A R (R + nr) j ∧ AInv pg n k mR T A R (R + nr) j 0 c ∧
        c.reg rPB = k ^ (bnd pg n k (sg pg n j)).length) 4 := by
    refine HTB.of_HT rfl <| HT.run_le (by decide) (by decide)
      fun c ⟨⟨⟨hg, hd, hpb, hpc, harg, hrr, hF⟩,
      hsame, htb, hag, hrl, hz⟩, _, hNR⟩ => ?_
    have hreg' : ∀ x, x ∉ wregs valAlloc → (RAM.run valAlloc c).reg x = c.reg x :=
      fun x hx => run_reg_of_not_mem (by decide) hx c
    have hR := (show RegIndep (wregs valAlloc) (fun c => Glob pg n k mR T c ∧ SegD pg n k j c ∧
      c.reg rPB = k ^ (bnd pg n k (sg pg n j)).length ∧
      c.reg rPC = k ^ (topIdx pg n k (sg pg n j)).length ∧ c.reg gARG = A ∧ c.reg rREL = R) by
        indep [glob_iff, segD_iff]) c _ hreg' ⟨hg, hd, hpb, hpc, harg, hrr⟩
    obtain ⟨hg', hd', hpb', hpc', harg', hrr'⟩ := hR
    have hmem : (RAM.run valAlloc c).mem = c.mem := run_mem_of_stores (by decide) rfl c
    have hrun : (RAM.run valAlloc c).reg rVAL = R + nr ∧
        (RAM.run valAlloc c).reg rFREE = R + nr + nr ∧
        (RAM.run valAlloc c).reg rVB = R + nr + (bnd pg n k (sg pg n j)).length := by
      simp only [valAlloc, run_seq']
      rw [run_alloc (by decide) (by decide)]
      simp +decide [hF, hNR, hd.nb]
      rfl
    have hnr : nr = (bnd pg n k (sg pg n j)).length + (topIdx pg n k (sg pg n j)).length := by
      simp only [nr]; rw [rel, List.length_append]
    refine ⟨⟨hTA, hAR, rfl⟩, ⟨⟨hg', ⟨hd'.jj, hd'.sa, hd'.sb, hd'.fo, hd'.fl, hd'.nb, hd'.nc, hd'.nr,
      hpb', hpc', hd'.tO⟩, harg', hrr', hrun.1, hrun.2.2, hrun.2.1⟩, ?_⟩, hpb'⟩
    rw [hmem]
    refine ⟨hsame, by simpa [tabPre] using htb, by simpa [argPre] using hag,
      by rw [← List.take_length (l := rel pg n k (sg pg n j))]; exact hrl, ?_, hz.mono (by omega)⟩
    have : valsAB pg n k j 0 0 = List.replicate nr 0 := by
      rw [valsAB, cfg_zero_eq, cfg_zero_eq, List.replicate_append_replicate, hnr]
    rw [this]
    exact hz.arr le_rfl nr
  refine (h₁.seq (h₂.seq h₃)).weaken ?_
  omega

/-! ### One segment -/

/-- The bound of one segment. -/
def tSeg (k fl : ℕ) : ℕ := k ^ Rb k * (tAlpha k fl + 4) + Rb k * (10 * k + 50) + 60

/-- The bound of the free pointer before the segment `j`: the relevant cycles and the digits
of the earlier segments (`2 |rel s| ≤ 4 Rb k` cells each) above the tables. -/
def FrP (pg : Graph) (n k A j : ℕ) (c : Config) : Prop :=
  c.reg rFREE ≤ A + toffAt pg n k (segOrder pg n).length + 4 * Rb k * j

/-- **One segment**: the tables of the segment `j`. -/
theorem segBody_spec {S : ℕ} {mR : ℕ → ℕ} {T A j : ℕ} (hP : IsPolygon pg n) (hk : 3 ≤ k)
    (hj : j < (segOrder pg n).length) (hTA : T + toffAt pg n k (segOrder pg n).length = A)
    (hSz : A + toffAt pg n k (segOrder pg n).length + 4 * Rb k * (j + 1) ≤ S) :
    HTB S segBody (fun c => (MSt pg n k mR T A j c ∧ FrP pg n k A j c) ∧ c.reg rJ = j ∧
        c.reg gNS = (segOrder pg n).length)
      (fun c => (MSt pg n k mR T A (j + 1) c ∧ FrP pg n k A (j + 1) c) ∧ c.reg rJ = j ∧
        c.reg gNS = (segOrder pg n).length)
      (tSeg k (faceVerts pg n (sg pg n j)).length) := by
  refine HTB.of_forall fun c₀ hc₀ => ?_
  have hAR : A + toffAt pg n k (segOrder pg n).length ≤ c₀.reg rFREE := hc₀.1.1.1.2.2
  have hFP := hc₀.1.2
  unfold FrP at hFP
  have hrel := length_rel_le (k := k) hP (sg_mem hj)
  have e4 : 4 * Rb k * (j + 1) = 4 * Rb k * j + 4 * Rb k := by ring
  have hR2 :
      c₀.reg rFREE + (rel pg n k (sg pg n j)).length + (rel pg n k (sg pg n j)).length ≤ S := by
    omega
  have h₁ := (segRd_spec (S := S) (pg := pg) (n := n) (k := k) (mR := mR) (T := T) (A := A) hj
    (by omega)).frameIndep rfl rfl (F := fun c => c.reg rFREE = c₀.reg rFREE) (by indep)
  have h₂ := (segPow_spec (S := S) (pg := pg) (n := n) (k := k) (mR := mR) (T := T) (A := A)
    (j := j)).frameIndep rfl rfl (F := fun c => c.reg rFREE = c₀.reg rFREE) (by indep)
  have h₃ := segRel_spec (S := S) (pg := pg) (n := n) (k := k) (mR := mR) hj hTA (c₀.reg rFREE) hAR
    (by omega)
  have hlay : Lay pg n k T A (c₀.reg rFREE) (c₀.reg rFREE + (rel pg n k (sg pg n j)).length) j :=
    ⟨hTA, hAR, rfl⟩
  have h₄ := (alphaLoop_spec (mR := mR) hP hk hj hlay hR2).pre
    (P' := fun c => Lay pg n k T A (c₀.reg rFREE) (c₀.reg rFREE + (rel pg n k (sg pg n j)).length) j ∧
      AInv pg n k mR T A (c₀.reg rFREE) (c₀.reg rFREE + (rel pg n k (sg pg n j)).length) j 0 c ∧
      c.reg rPB = k ^ (bnd pg n k (sg pg n j)).length) (fun c h => h.2)
  refine (h₁.seq (h₂.seq (h₃.seq h₄))).mono
    (fun c hc => ⟨by rw [hc]; exact ⟨hc₀.1.1, hc₀.2⟩, by rw [hc]⟩) ?_ ?_
  · rintro c ⟨hS, hM⟩
    have hjS : j + 1 ≤ (segOrder pg n).length := hj
    have hrel := length_rel_le (k := k) hP (sg_mem hj)
    refine ⟨⟨⟨⟨hS.glob, hS.arg, by rw [hS.free]; omega⟩, hM.same, ?_, ?_, by rw [hS.free]; exact hM.free⟩,
      ?_⟩, hS.seg.jj, hS.glob.ns⟩
    · have := hM.tb
      rwa [tabPre, sg_eq hj, ← blk, ← tabDone_succ hj] at this
    · have := hM.ag
      rwa [argPre, sg_eq hj, ← ablk, ← argDone_succ hj] at this
    · unfold FrP; rw [hS.free]
      omega
  · have h1 := length_bnd_le' (k := k) hP (sg_mem hj)
    have h2 := length_topIdx_le' (k := k) hP (sg pg n j)
    have h3 := length_rel_le (k := k) hP (sg_mem hj)
    have e1 : (bnd pg n k (sg pg n j)).length * (5 * k + 10) ≤ Rb k * (5 * k + 10) :=
      Nat.mul_le_mul_right _ h1
    have e2 : (topIdx pg n k (sg pg n j)).length * (5 * k + 10) ≤ Rb k * (5 * k + 10) :=
      Nat.mul_le_mul_right _ h2
    have e3 : Rb k * (10 * k + 50) = Rb k * (5 * k + 10) + Rb k * (5 * k + 10) + Rb k * 30 := by ring
    unfold tSeg; omega

/-! ### All segments -/

/-- **All segments**: the tables of all segments. -/
theorem segLoop_spec {S : ℕ} {mR : ℕ → ℕ} {T A : ℕ} (hP : IsPolygon pg n) (hk : 3 ≤ k)
    (hTA : T + toffAt pg n k (segOrder pg n).length = A)
    (hSz : A + toffAt pg n k (segOrder pg n).length + 4 * Rb k * (segOrder pg n).length ≤ S) :
    HTB S (forUp rJ gNS segBody)
      (fun c => (MSt pg n k mR T A 0 c ∧ FrP pg n k A 0 c) ∧ c.reg gNS = (segOrder pg n).length)
      (fun c => MSt pg n k mR T A (segOrder pg n).length c ∧
        FrP pg n k A (segOrder pg n).length c)
      (∑ j ∈ Finset.range (segOrder pg n).length, (tSeg k (faceVerts pg n (sg pg n j)).length + 4) + 3) :=
  (HTB.forUp (i := rJ) (n := gNS) (N := (segOrder pg n).length) (body := segBody)
    (fun j c => MSt pg n k mR T A j c ∧ FrP pg n k A j c)
    (fun j => tSeg k (faceVerts pg n (sg pg n j)).length)
    (by decide) (by decide) (by decide) (fun j => by unfold MSt FrP; indep [glob_iff])
    (fun j hj => segBody_spec hP hk hj hTA (by
      have := Nat.mul_le_mul_left (4 * Rb k) (show j + 1 ≤ (segOrder pg n).length by omega)
      omega))).post fun _ h => h.1

end STACS2027.RAM.P3

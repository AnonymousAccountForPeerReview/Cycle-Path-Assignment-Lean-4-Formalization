module

public import Outerplanar.RAM.Poly2Seg
import Mathlib.Tactic

/-!
# Phase P2 of the polygon solver, stage R: the region paths of all segments

Stage R (`stageR`) runs over the segments `t = 0, 1, …` of `segOrder` (children before
parents). For the segment `t`, starting from the partial path `([s.1], 0)`, it folds over the
slots of its face (`slotLoop`), and records the address and the number of the final partial
paths `fin s` in the tables at `L.fb` and `L.fc` (`sgFin`), so that the parents find them
(`FinOK`). The cost is linear in the total size of the faces (`stageR_spec`), and so is the
memory: every current list of partial paths has at most `encB k` cells (`FrB`, `FrS`), so that
stage R runs within the bound `S ≥ L.fr + encB k * |faceCat|` (`HTB S`).
-/

@[expose] public section

namespace STACS2027.RAM.P2

open STACS2027.Poly P1

/-! ### Programs -/

/-- Read the segment `t`: its first end, its face offset, its number of slots. -/
def sgRd : Stmt :=
  .seq (ld rSA gSA rSt) (.seq (ld rOFF gFOFF rSt) (.seq (addc rW rSt 1)
    (.seq (ld rNSL gFOFF rW) (.seq (.sub rNSL rNSL rOFF) (subc rNSL rNSL 1)))))
/-- The partial path `([s.1], 0)`. -/
def sgInit : Stmt :=
  .seq (mov rP rFREE) (.seq (.const rW 0) (.seq (push rW) (.seq (push rSA) (.const rPN 1))))
/-- Record the final partial paths. -/
def sgFin : Stmt := .seq (st rFB rSt rP) (st rFC rSt rPN)
/-- **One segment.** -/
def segBody : Stmt := .seq sgRd (.seq sgInit (.seq slotLoop sgFin))
/-- **Stage R**: all segments. -/
def stageR : Stmt := forUp rSt gNS segBody

/-- The invariant of stage R before the segment `t`. -/
def SegInv (pg : Graph) (n k : ℕ) (L : Lay) (m₁ : ℕ → ℕ) (t : ℕ) (c : Config) : Prop :=
  RSt pg n k L m₁ t c ∧ Zf c

/-- The bound of the free pointer before the segment `t`: at most `encB k` cells per face
vertex of the earlier segments above `L.fr`. -/
def FrS (pg : Graph) (n k : ℕ) (L : Lay) (t : ℕ) (c : Config) : Prop :=
  c.reg rFREE ≤ L.fr + encB k * fOff pg n t

variable {pg : Graph} {n k : ℕ}

theorem SegInv.indep (L : Lay) (m₁ : ℕ → ℕ) (t : ℕ) :
    Indep [rT, rSt, rSA, rOFF, rW, rNSL, rP, rPN] (SegInv pg n k L m₁ t) := by
  indep [SegInv, RSt, rCtx_iff, FinOK, Bel, Zf]

/-- Steps for the segment `s`. -/
def TSg (k : ℕ) (pg : Graph) (n : ℕ) (s : ℕ × ℕ) : ℕ := (slots pg n s).length * (TSl k + 4) + 28

/-- The constant data survive a change of the memory at or above `L.fb` and of `rT`. -/
theorem RCtx.of_below {L : Lay} (hL : LayOK pg n L) {c c' : Config} (h : RCtx pg n k L c)
    (hreg : ∀ r, r ≠ rT → c'.reg r = c.reg r) (hm : SameOn (· < L.fb) c.mem c'.mem) :
    RCtx pg n k L c' := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try (rw [hreg _ (by decide)])
  · exact h.rk
  · exact h.pn
  · exact h.ns
  · exact h.rsb
  · exact h.rfsid
  · exact h.rfv
  · exact h.rfoff
  · exact h.rsa
  · exact h.rfb
  · exact h.rfc
  · exact h.sb.of_below hm (by simpa using hL.sb)
  · exact h.fsid.of_below hm (by rw [length_fsidCat]; exact hL.fsid)
  · exact h.fv.of_below hm hL.fv
  · exact h.foff.of_below hm (by simpa [faceOffs, prefixSums] using hL.foff)
  · exact h.sa.of_below hm (by simpa using hL.sa)
  · exact h.fr

/-! ### One segment -/

theorem segBody_spec {S : ℕ} (hP : IsPolygon pg n) {L : Lay} (hL : LayOK pg n L) (m₁ : ℕ → ℕ)
    {t : ℕ} (ht : t < (segOrder pg n).length) (hSz : L.fr + encB k * (faceCat pg n).length ≤ S) :
    HTB S segBody
      (fun c => (SegInv pg n k L m₁ t c ∧ FrS pg n k L t c) ∧ c.reg rSt = t ∧
        c.reg gNS = (segOrder pg n).length)
      (fun c => (SegInv pg n k L m₁ (t + 1) c ∧ FrS pg n k L (t + 1) c) ∧ c.reg rSt = t ∧
        c.reg gNS = (segOrder pg n).length)
      (TSg k pg n ((segOrder pg n).getD t (0, 0))) := by
  rw [getD_of_lt ht]
  have hfs := fOff_succ (pg := pg) (n := n) ht
  have hsl : (slots pg n (segOrder pg n)[t]).length = (faceVerts pg n (segOrder pg n)[t]).length - 1 :=
    length_pairs _
  have h3 := hP.three_le_length_faceVerts (mem_segOrder.mp (List.getElem_mem ht))
  have hfl := fOff_le_length (pg := pg) (n := n) (t + 1)
  have := hL.sa; have := hL.foff; have := hL.fc; have := hL.fr
  -- reading the segment
  have hA : HTB S sgRd
      (fun c => SegInv pg n k L m₁ t c ∧ c.reg rSt = t ∧ c.reg gNS = (segOrder pg n).length)
      (fun c => (SegInv pg n k L m₁ t c ∧ c.reg rSt = t) ∧ c.reg rSA = (segOrder pg n)[t].1 ∧
        c.reg rOFF = fOff pg n t ∧ c.reg rNSL = (slots pg n (segOrder pg n)[t]).length) 11 := by
    refine HTB.run_le (by decide) (by decide) fun c ⟨hI, hst, _⟩ => ?_
    have hAg : Agree [rSA, rOFF, rT, rW, rNSL] c (RAM.run sgRd c) :=
      agree_run (by decide) rfl rfl (by decide) c
    have hR := hI.1.1
    refine ⟨by addr_ok [sgRd, hst, hR.rsa, hR.rfoff], ?_⟩
    have hsa : c.mem (L.sa + t) = (segOrder pg n)[t].1 := by
      rw [hR.sa.get (by simpa using ht)]; simp
    have hf0 : c.mem (L.foff + t) = fOff pg n t := by
      rw [hR.foff.get (by simp [faceOffs, prefixSums]; omega), faceOffs_getElem (by omega)]
    have hf1 : c.mem (L.foff + (t + 1)) = fOff pg n (t + 1) := by
      rw [hR.foff.get (by simp [faceOffs, prefixSums]; omega), faceOffs_getElem (by omega)]
    refine ⟨⟨(SegInv.indep L m₁ t).mono (by decide) c _ hAg hI, by rw [hAg.reg _ (by decide), hst]⟩,
      ?_, ?_, ?_⟩
    · simp +decide [sgRd, run_addc, run_subc, hst, hR.rsa, hsa]
    · simp +decide [sgRd, run_addc, run_subc, hst, hR.rfoff, hf0]
    · simp +decide [sgRd, run_addc, run_subc, hst, hR.rfoff, hf0, hf1, hfs]
      omega
  have hA' := hA.frame (F := FrS pg n k L t) fun c c' hfr h => by
    unfold FrS at *; rw [hfr.reg rFREE (by decide)]; exact h
  -- the partial path `([s.1], 0)`
  have hB : HTB S sgInit
      (fun c => ((SegInv pg n k L m₁ t c ∧ c.reg rSt = t) ∧ c.reg rSA = (segOrder pg n)[t].1 ∧
        c.reg rOFF = fOff pg n t ∧ c.reg rNSL = (slots pg n (segOrder pg n)[t]).length) ∧
        FrS pg n k L t c)
      (fun c => (SlInv pg n k L m₁ t 0 c ∧ FrB pg n k L t 0 c) ∧
        c.reg rNSL = (slots pg n (segOrder pg n)[t]).length) 10 := by
    refine HTB.run_le (by decide) (by decide) fun c ⟨⟨⟨⟨hR, hZ⟩, hst⟩, hsa, hoff, hnsl⟩, hFr⟩ => ?_
    have h2 := two_le_encB (k := k)
    have hm1 := Nat.mul_le_mul_left (encB k) (show fOff pg n t + 1 ≤ (faceCat pg n).length by omega)
    have e1 : encB k * (fOff pg n t + 1) = encB k * fOff pg n t + encB k := by ring
    unfold FrS at hFr
    refine ⟨by addr_ok [sgInit, push], ?_⟩
    have hA2 : Agree [rT, rP, rW] c (RAM.run (.seq (mov rP rFREE) (.const rW 0)) c) :=
      agree_run (by decide) rfl rfl (by decide) c
    have hS2 : Strm (c.reg rFREE) [] (RAM.run (.seq (mov rP rFREE) (.const rW 0)) c) :=
      strm_agree hA2 (by decide) ⟨by simp, by simp, hZ⟩
    have hw : (RAM.run (.seq (mov rP rFREE) (.const rW 0)) c).reg rW = 0 := by simp
    have hp : (RAM.run (.seq (mov rP rFREE) (.const rW 0)) c).reg rP = c.reg rFREE := by
      simp +decide [run_mov]
    have hS3 := push_strm hS2 rW
    rw [hw] at hS3
    have hS4 := push_strm hS3 rSA
    rw [push_reg _ _ (by decide) (by decide), hA2.reg _ (by decide), hsa] at hS4
    have hA5 : Agree [rPN] (RAM.run (push rSA) (RAM.run (push rW)
        (RAM.run (.seq (mov rP rFREE) (.const rW 0)) c)))
        (RAM.run (.const rPN 1) (RAM.run (push rSA) (RAM.run (push rW)
          (RAM.run (.seq (mov rP rFREE) (.const rW 0)) c)))) :=
      agree_run (by decide) rfl rfl (by decide) _
    have hrun : RAM.run sgInit c = RAM.run (.const rPN 1) (RAM.run (push rSA) (RAM.run (push rW)
        (RAM.run (.seq (mov rP rFREE) (.const rW 0)) c))) := rfl
    have hG : Grow [rT, rP, rW, rFREE, rPN] c (RAM.run sgInit c) := by
      rw [hrun]
      exact (grow_of_agree hA2 (by decide) (by decide)).trans (((push_grow rW _).mono (by decide)).trans
        (((push_grow rSA _).mono (by decide)).trans (grow_of_agree hA5 (by decide) (by decide))))
    rw [hrun] at hG ⊢
    have hS5 := strm_agree hA5 (by decide) hS4
    refine ⟨⟨(slInv_iff ht).mpr ⟨RSt.stable hL (by decide) m₁ t c _ hR hG, ?_, ?_, ?_, ?_, ?_,
      hS5.2.2⟩, ?_⟩, ?_⟩
    · rw [hG.reg _ (by decide), hoff]
    · rw [hG.reg _ (by decide), hst]
    · rw [hA5.reg _ (by decide), push_reg _ _ (by decide) (by decide),
        push_reg _ _ (by decide) (by decide), hp]
      exact hR.1.fr
    · rw [hA5.reg _ (by decide), push_reg _ _ (by decide) (by decide),
        push_reg _ _ (by decide) (by decide), hp, finPre_zero, enc_singleton]
      simpa using hS5.bel
    · simp [finPre_zero]
    · unfold FrB
      have hl := hS5.2.1
      simp only [List.length_append, List.length_nil, List.length_singleton] at hl
      have e : encB k * (fOff pg n t + 0 + 1) = encB k * fOff pg n t + encB k := by ring
      omega
    · rw [hG.reg _ (by decide), hnsl]
  -- the slots
  have hC := (slotLoop_spec (k := k) hP hL m₁ ht hSz).toHTB
  -- recording the final partial paths
  have hD : HTB S sgFin
      (fun c => (SlInv pg n k L m₁ t (slots pg n (segOrder pg n)[t]).length c ∧
        FrB pg n k L t (slots pg n (segOrder pg n)[t]).length c) ∧
        c.reg rSj = (slots pg n (segOrder pg n)[t]).length ∧
        c.reg rNSL = (slots pg n (segOrder pg n)[t]).length)
      (fun c => (SegInv pg n k L m₁ (t + 1) c ∧ FrS pg n k L (t + 1) c) ∧ c.reg rSt = t ∧
        c.reg gNS = (segOrder pg n).length) 4 := by
    refine HTB.run_le (by decide) (by decide) fun c ⟨⟨hI, hFB⟩, _, _⟩ => ?_
    obtain ⟨⟨hR, hF, hm₁⟩, -, hst, hfrP, hB, hpn, hZ⟩ := (slInv_iff ht).mp hI
    refine ⟨by addr_ok [sgFin, hR.rfb, hR.rfc, hst], ?_⟩
    rw [finPre_full] at hB hpn
    have hreg : ∀ r, r ≠ rT → (RAM.run sgFin c).reg r = c.reg r := fun r hr =>
      run_reg_of_not_mem (by decide) (by simp [sgFin, hr]) c
    have hmem : (RAM.run sgFin c).mem =
        upd (upd c.mem (L.fb + t) (c.reg rP)) (L.fc + t) (c.reg rPN) := by
      simp +decide [sgFin, run_st, hR.rfb, hR.rfc, hst]
    have hfc := hL.fc
    have hfr := hL.fr
    have hFR := hR.fr
    have hne : L.fb + t ≠ L.fc + t := by omega
    have hSm : SameOn (· < L.fb) c.mem (RAM.run sgFin c).mem := by
      rw [hmem]
      exact ((SameOn.refl _ _).upd_of_ge (by omega) _).upd_of_ge (by omega) _
    have hBel : ∀ {b : ℕ} {l : List ℕ}, L.fr ≤ b → Bel b l c → Bel b l (RAM.run sgFin c) := by
      intro b l hb h
      refine ⟨?_, by rw [hreg _ (by decide)]; exact h.2⟩
      rw [hmem]
      exact (h.1.upd_of_disjoint (by omega)).upd_of_disjoint (by omega)
    refine ⟨⟨⟨⟨RCtx.of_below hL hR hreg hSm, ⟨by rw [hreg _ (by decide)]; exact hFR, ?_⟩,
      hm₁.trans (hSm.mono fun a ha => ha)⟩, ?_⟩, ?_⟩, by rw [hreg _ (by decide), hst],
      by rw [hreg _ (by decide), hR.ns]⟩
    · intro t' ht' hts
      rcases Nat.lt_succ_iff_lt_or_eq.mp ht' with ht' | rfl
      · obtain ⟨h1, h2, h3⟩ := hF.2 t' ht' hts
        have e1 : (RAM.run sgFin c).mem (L.fb + t') = c.mem (L.fb + t') := by
          rw [hmem, upd_ne _ _ (by omega), upd_ne _ _ (by omega)]
        have e2 : (RAM.run sgFin c).mem (L.fc + t') = c.mem (L.fc + t') := by
          rw [hmem, upd_ne _ _ (by omega), upd_ne _ _ (by omega)]
        rw [e1, e2]
        exact ⟨h1, hBel h1 h2, h3⟩
      · have e1 : (RAM.run sgFin c).mem (L.fb + t') = c.reg rP := by
          rw [hmem, upd_ne _ _ hne, upd_same]
        have e2 : (RAM.run sgFin c).mem (L.fc + t') = c.reg rPN := by
          rw [hmem, upd_same]
        rw [e1, e2]
        exact ⟨hfrP, hBel hfrP hB, hpn⟩
    · unfold Zf
      rw [hreg _ (by decide), hmem]
      exact (hZ.upd (by omega)).upd (by omega)
    · unfold FrS; unfold FrB at hFB
      rw [hreg _ (by decide), hfs]
      rw [hsl] at hFB
      have e : fOff pg n t + ((faceVerts pg n (segOrder pg n)[t]).length - 1) + 1 =
          fOff pg n t + (faceVerts pg n (segOrder pg n)[t]).length := by omega
      rw [e] at hFB
      exact hFB
  refine ((hA'.pre fun c ⟨⟨hI, hFr⟩, hst, hns⟩ => ⟨⟨hI, hst, hns⟩, hFr⟩).seq
    (hB.seq ((hC.pre fun c h => h).seq hD))).weaken (by unfold TSg; omega)

/-! ### All segments -/

theorem sum_slots_le (A B : ℕ) : ∀ l : List (ℕ × ℕ),
    (l.map fun s => (slots pg n s).length * A + B).sum ≤
      (l.flatMap (faceVerts pg n)).length * A + B * l.length
  | [] => by simp
  | s :: l => by
    have ih := sum_slots_le A B l
    have h1 : (slots pg n s).length ≤ (faceVerts pg n s).length := by
      rw [slots, length_pairs]; omega
    have h2 := Nat.mul_le_mul_right A h1
    simp only [List.map_cons, List.sum_cons, List.flatMap_cons, List.length_append,
      List.length_cons, Nat.add_mul, Nat.mul_succ]
    omega

/-- **Stage R**: the final partial paths of all segments, within
`|faceCat| * (TSl k + 4) + 32 * |segOrder| + 3` steps. -/
theorem stageR_spec {S : ℕ} (hP : IsPolygon pg n) {L : Lay} (hL : LayOK pg n L) (m₁ : ℕ → ℕ)
    (hSz : L.fr + encB k * (faceCat pg n).length ≤ S) :
    HTB S stageR (fun c => (SegInv pg n k L m₁ 0 c ∧ FrS pg n k L 0 c) ∧
        c.reg gNS = (segOrder pg n).length)
      (fun c => (SegInv pg n k L m₁ (segOrder pg n).length c ∧
        FrS pg n k L (segOrder pg n).length c) ∧
        c.reg rSt = (segOrder pg n).length ∧ c.reg gNS = (segOrder pg n).length)
      ((faceCat pg n).length * (TSl k + 4) + 32 * (segOrder pg n).length + 3) := by
  have h := HTB.forUp (S := S) (i := rSt) (n := gNS) (N := (segOrder pg n).length) (body := segBody)
    (fun t c => SegInv pg n k L m₁ t c ∧ FrS pg n k L t c)
    (fun t => TSg k pg n ((segOrder pg n).getD t (0, 0)))
    (by decide) (by decide) (by decide)
    (fun t => ((SegInv.indep L m₁ t).mono (by decide)).and (by unfold FrS; indep))
    (fun t ht => segBody_spec hP hL m₁ ht hSz)
  refine h.weaken ?_
  have hsum := sum_range_getD (fun s => TSg k pg n s + 4) (0, 0) (segOrder pg n)
  have hle := sum_slots_le (pg := pg) (n := n) (TSl k + 4) 32 (segOrder pg n)
  have he : ((segOrder pg n).map fun s => TSg k pg n s + 4) =
      (segOrder pg n).map fun s => (slots pg n s).length * (TSl k + 4) + 32 := by
    apply List.map_congr_left; intro s _; unfold TSg; omega
  rw [hsum, he]
  rw [faceCat]
  omega

end STACS2027.RAM.P2
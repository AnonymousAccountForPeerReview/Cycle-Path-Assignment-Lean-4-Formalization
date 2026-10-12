module

public import Outerplanar.RAM.Poly3Seg
import Mathlib.Tactic

/-!
# Phase P3 of the polygon solver: the minimization over `β` and the loop over `α`

For the segment `j` (`s = sg j`, `nb = |bnd s|`, `nc = |topIdx s|`):

* `betaBody_spec`: one `β`: the total `totAB s α β` (`total_spec`), the update of the best
  pair by `stepB` (`keepB`), and the odometer on the digits of `β`;
* `betaLoop_spec`: all `β < k ^ nc`: the best pair is `best s α`, and the digits of `β` are
  zero again (`cfg_pow`);
* `alphaBody_spec`: one `α`: the minimization, the store of `table s α = (best s α).2` and
  `argTab s α = (best s α).1` (`AMem.store`), the odometer on the digits of `α`;
* `alphaLoop_spec`: all `α < k ^ nb`.

All triples are bounded (`HTB S`) for `S` at or above the end `V + |rel s|` of the digits.
-/

@[expose] public section

namespace STACS2027.RAM.P3

open STACS2027.Poly STACS2027.RAM.P1

variable {pg : Graph} {n k : ℕ}

/-- The digits of `(α, β)` for the segment `j`. -/
def valsAB (pg : Graph) (n k j a b : ℕ) : List ℕ :=
  cfg k (bnd pg n k (sg pg n j)).length a ++ cfg k (topIdx pg n k (sg pg n j)).length b

/-- The best pair after the first `b` configurations `β`. -/
def foldB (pg : Graph) (n k j a b : ℕ) : ℕ × ℕ :=
  (List.range b).foldl (stepB (totAB pg n k (sg pg n j) a)) (0, 0)

theorem length_valsAB (j a b : ℕ) : (valsAB pg n k j a b).length = (rel pg n k (sg pg n j)).length := by
  simp [valsAB, rel]

theorem valsAB_lt (hk : 0 < k) (j a b : ℕ) : ∀ x ∈ valsAB pg n k j a b, x < k := by
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · exact cfg_lt hk _ _ x h
  · exact cfg_lt hk _ _ x h

/-! ### One `β` -/

theorem run_keepB (c : Config) :
    (RAM.run keepB c).reg rBEST = (if c.reg rB = 0 ∨ c.reg rTOT < c.reg rBEST then c.reg rTOT
      else c.reg rBEST) ∧
    (RAM.run keepB c).reg rARGB = (if c.reg rB = 0 ∨ c.reg rTOT < c.reg rBEST then c.reg rB
      else c.reg rARGB) := by
  simp only [keepB, keep, run_ifz']
  rw [run_ifLt]
  by_cases h0 : c.reg rB = 0
  · simp +decide [h0, run_mov]
  · by_cases h1 : c.reg rTOT < c.reg rBEST
    · simp +decide [h0, h1, run_mov]
    · simp +decide [h0, h1]

/-- The state of the `β` loop. -/
def BInv (pg : Graph) (n k : ℕ) (mR : ℕ → ℕ) (T A R V j a b : ℕ) (c : Config) : Prop :=
  (SSt pg n k mR T A R V j c ∧ c.reg rA = a ∧ c.reg rARGB = (foldB pg n k j a b).1 ∧
    c.reg rBEST = (foldB pg n k j a b).2) ∧ AMem pg n k mR T A R V j a (valsAB pg n k j a b) c.mem

/-- The bound of one `β`. -/
def tBeta (k fl : ℕ) : ℕ := tTot k * (fl + 1) + Rb k * 19 + 30

theorem betaBody_spec {S : ℕ} {mR : ℕ → ℕ} {T A R V j a : ℕ} (hP : IsPolygon pg n)
    (hk : 3 ≤ k) (hj : j < (segOrder pg n).length) (hlay : Lay pg n k T A R V j)
    (hSz : V + (rel pg n k (sg pg n j)).length ≤ S)
    (ha : a < k ^ (bnd pg n k (sg pg n j)).length) (b : ℕ) :
    HTB S betaBody
      (fun c => BInv pg n k mR T A R V j a b c ∧ c.reg rB = b ∧
        c.reg rPC = k ^ (topIdx pg n k (sg pg n j)).length)
      (fun c => BInv pg n k mR T A R V j a (b + 1) c ∧ c.reg rB = b ∧
        c.reg rPC = k ^ (topIdx pg n k (sg pg n j)).length)
      (tBeta k (faceVerts pg n (sg pg n j)).length) := by
  have hk0 : 0 < k := by omega
  set nc := (topIdx pg n k (sg pg n j)).length
  set nb := (bnd pg n k (sg pg n j)).length
  -- the total
  have h₁ := total_spec (pg := pg) (n := n) (k := k) (j := j) (vals := valsAB pg n k j a b)
    (fun c => BInv pg n k mR T A R V j a b c ∧ c.reg rB = b ∧ c.reg rPC = k ^ nc)
    (by unfold BInv; indep [sSt_iff, glob_iff, segR_iff])
    (fun c hc => rd_of hc.1.1.1 hc.1.2 hlay hj.le (length_valsAB j a b) hSz) hP hj hk0
    (valsAB_lt hk0 j a b) (length_valsAB j a b)
  -- the update of the best pair
  have h₂ : HTB S keepB
      (fun c => (BInv pg n k mR T A R V j a b c ∧ c.reg rB = b ∧ c.reg rPC = k ^ nc) ∧
        c.reg rTOT = totV pg n k (sg pg n j) (valsAB pg n k j a b))
      (fun c => ((SSt pg n k mR T A R V j c ∧ c.reg rA = a ∧ c.reg rARGB = (foldB pg n k j a (b + 1)).1 ∧
        c.reg rBEST = (foldB pg n k j a (b + 1)).2) ∧ c.reg rB = b ∧ c.reg rPC = k ^ nc) ∧
        AMem pg n k mR T A R V j a (valsAB pg n k j a b) c.mem) 12 := by
    refine HTB.of_HT rfl <| HT.run_le (by decide) (by decide)
      fun c ⟨⟨⟨⟨hS, hA, hARG, hBEST⟩, hM⟩, hB, hPC⟩, hT⟩ => ?_
    have hag : Agree (wregs keepB) c (RAM.run keepB c) := agree_run (by decide) rfl rfl (by decide) c
    have hS' : SSt pg n k mR T A R V j (RAM.run keepB c) :=
      (show RegIndep (wregs keepB) (SSt pg n k mR T A R V j) by indep [sSt_iff, glob_iff, segR_iff])
        c _ hag.reg hS
    obtain ⟨hb1, hb2⟩ := run_keepB c
    have hstep : foldB pg n k j a (b + 1) = stepB (totAB pg n k (sg pg n j) a) (foldB pg n k j a b) b :=
      foldl_stepB_succ _ b
    refine ⟨⟨⟨hS', ?_, ?_, ?_⟩, ?_, ?_⟩, by rw [hag.mem]; exact hM⟩
    · rw [hag.reg _ (by decide)]; exact hA
    · rw [hb2, hstep, stepB, hB, hT, hARG, hBEST]
      unfold totAB valsAB
      split_ifs <;> rfl
    · rw [hb1, hstep, stepB, hB, hT, hBEST]
      unfold totAB valsAB
      split_ifs <;> rfl
    · rw [hag.reg _ (by decide)]; exact hB
    · rw [hag.reg _ (by decide)]; exact hPC
  -- the odometer on the digits of `β`
  let Gr : Config → Prop := fun c => ((SSt pg n k mR T A R V j c ∧ c.reg rA = a ∧
    c.reg rARGB = (foldB pg n k j a (b + 1)).1 ∧ c.reg rBEST = (foldB pg n k j a (b + 1)).2) ∧
    c.reg rB = b ∧ c.reg rPC = k ^ nc) ∧ c.reg rOB = V + nb ∧ c.reg rOL = nc
  let Fr : List ℕ → (ℕ → ℕ) → Prop := fun ds m =>
    ds.length = nc ∧ AMem pg n k mR T A R V j a (cfg k nb a ++ ds) m
  have h₃ : HTB S bOdoArgs
      (fun c => ((SSt pg n k mR T A R V j c ∧ c.reg rA = a ∧ c.reg rARGB = (foldB pg n k j a (b + 1)).1 ∧
        c.reg rBEST = (foldB pg n k j a (b + 1)).2) ∧ c.reg rB = b ∧ c.reg rPC = k ^ nc) ∧
        AMem pg n k mR T A R V j a (valsAB pg n k j a b) c.mem)
      (fun c => Gr c ∧ Fr (cfg k nc b) c.mem) 4 := by
    refine HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c ⟨hc, hM⟩ => ?_
    have hag : Agree (wregs bOdoArgs) c (RAM.run bOdoArgs c) :=
      agree_run (by decide) rfl rfl (by decide) c
    have hc' := (show Indep (wregs bOdoArgs) (fun c => (SSt pg n k mR T A R V j c ∧ c.reg rA = a ∧
        c.reg rARGB = (foldB pg n k j a (b + 1)).1 ∧ c.reg rBEST = (foldB pg n k j a (b + 1)).2) ∧
        c.reg rB = b ∧ c.reg rPC = k ^ nc) by indep [sSt_iff, glob_iff, segR_iff]) c _ hag hc
    refine ⟨⟨hc', ?_, ?_⟩, by simp [nc], by rw [hag.mem]; exact hM⟩
    all_goals (simp +decide only [bOdoArgs, run_seq', run_mov, setReg_reg, ↓reduceIte,
      hc.1.1.vb, hc.1.1.seg.nc]; try rfl)
  have hrl : (rel pg n k (sg pg n j)).length = nb + nc := by rw [rel, List.length_append]
  have h₄ := odo_spec (S := S) (k := k) (ob := V + nb) (ds := cfg k nc b) Gr
    (by simp only [Gr]; indep [sSt_iff, glob_iff, segR_iff])
    (fun c hc => ⟨hc.2.1, by rw [hc.2.2, length_cfg], hc.1.1.1.glob.kk⟩) Fr
    (fun l m h => by
      have := (arr_append.mp h.2.vl).2
      rwa [length_cfg] at this)
    (fun l m t v h ht => by
      refine ⟨by rw [List.length_set]; exact h.1, ?_⟩
      have := h.2.updV hlay hj ha.le (by rw [List.length_append, length_cfg, h.1, rel,
        List.length_append]) (t := nb + t) (by simp; omega) v
      rw [List.set_append_right _ _ (by simp), length_cfg, Nat.add_sub_cancel_left,
        ← Nat.add_assoc] at this
      exact this) (by rw [length_cfg]; omega)
  refine (h₁.seq (h₂.seq (h₃.seq h₄))).mono (fun _ h => h) ?_ ?_
  · intro c ⟨⟨⟨⟨hS, hA, hARG, hBEST⟩, hB, hPC⟩, _, _⟩, _, hM⟩
    refine ⟨⟨⟨hS, hA, hARG, hBEST⟩, ?_⟩, hB, hPC⟩
    rw [odoL_cfg hk0] at hM
    exact hM
  · have : nc ≤ Rb k := length_topIdx_le' hP _
    have : nc * 19 ≤ Rb k * 19 := Nat.mul_le_mul_right _ this
    rw [length_cfg]; unfold tBeta; omega

/-! ### The `β` loop -/

/-- **The minimization over `β`.** -/
theorem betaLoop_spec {S : ℕ} {mR : ℕ → ℕ} {T A R V j a : ℕ} (hP : IsPolygon pg n)
    (hk : 3 ≤ k) (hj : j < (segOrder pg n).length) (hlay : Lay pg n k T A R V j)
    (hSz : V + (rel pg n k (sg pg n j)).length ≤ S)
    (ha : a < k ^ (bnd pg n k (sg pg n j)).length) :
    HTB S (forUp rB rPC betaBody)
      (fun c => BInv pg n k mR T A R V j a 0 c ∧ c.reg rPC = k ^ (topIdx pg n k (sg pg n j)).length)
      (fun c => BInv pg n k mR T A R V j a (k ^ (topIdx pg n k (sg pg n j)).length) c ∧
        c.reg rB = k ^ (topIdx pg n k (sg pg n j)).length ∧
        c.reg rPC = k ^ (topIdx pg n k (sg pg n j)).length)
      (k ^ (topIdx pg n k (sg pg n j)).length * (tBeta k (faceVerts pg n (sg pg n j)).length + 4) + 3) :=
  HTB.forUpC (i := rB) (n := rPC) (body := betaBody) (BInv pg n k mR T A R V j a)
    (tBeta k (faceVerts pg n (sg pg n j)).length) (by decide) (by decide) (by decide)
    (fun b => by unfold BInv; indep [sSt_iff, glob_iff, segR_iff])
    (fun b _ => betaBody_spec hP hk hj hlay hSz ha b)

/-! ### One `α` -/

/-- The state of the `α` loop. -/
def AInv (pg : Graph) (n k : ℕ) (mR : ℕ → ℕ) (T A R V j a : ℕ) (c : Config) : Prop :=
  SSt pg n k mR T A R V j c ∧ AMem pg n k mR T A R V j a (valsAB pg n k j a 0) c.mem

/-- The bound of one `α`. -/
def tAlpha (k fl : ℕ) : ℕ := k ^ Rb k * (tBeta k fl + 4) + Rb k * 19 + 20

theorem alphaBody_spec {S : ℕ} {mR : ℕ → ℕ} {T A R V j : ℕ} (hP : IsPolygon pg n)
    (hk : 3 ≤ k) (hj : j < (segOrder pg n).length) (hlay : Lay pg n k T A R V j)
    (hSz : V + (rel pg n k (sg pg n j)).length ≤ S) (a : ℕ)
    (ha : a < k ^ (bnd pg n k (sg pg n j)).length) :
    HTB S alphaBody
      (fun c => AInv pg n k mR T A R V j a c ∧ c.reg rA = a ∧
        c.reg rPB = k ^ (bnd pg n k (sg pg n j)).length)
      (fun c => AInv pg n k mR T A R V j (a + 1) c ∧ c.reg rA = a ∧
        c.reg rPB = k ^ (bnd pg n k (sg pg n j)).length)
      (tAlpha k (faceVerts pg n (sg pg n j)).length) := by
  have hk0 : 0 < k := by omega
  set nc := (topIdx pg n k (sg pg n j)).length
  set nb := (bnd pg n k (sg pg n j)).length
  have h₁ : HTB S aInit
      (fun c => AInv pg n k mR T A R V j a c ∧ c.reg rA = a ∧ c.reg rPB = k ^ nb)
      (fun c => BInv pg n k mR T A R V j a 0 c ∧ c.reg rPC = k ^ nc) 2 := by
    refine HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c ⟨⟨hS, hM⟩, hA, _⟩ => ?_
    have hag : Agree (wregs aInit) c (RAM.run aInit c) := agree_run (by decide) rfl rfl (by decide) c
    have hS' : SSt pg n k mR T A R V j (RAM.run aInit c) :=
      (show Indep (wregs aInit) (SSt pg n k mR T A R V j) by indep [sSt_iff, glob_iff, segR_iff])
        c _ hag hS
    refine ⟨⟨⟨hS', ?_, ?_, ?_⟩, by rw [hag.mem]; exact hM⟩, ?_⟩
    all_goals simp +decide only [aInit, run_seq', run_const, setReg_reg, ↓reduceIte, hA,
      hS.seg.pc, foldB, List.range_zero, List.foldl_nil]
    rfl
  have h₂ := betaLoop_spec (mR := mR) hP hk hj hlay hSz ha
  have hbest : foldB pg n k j a (k ^ nc) = best pg n k (sg pg n j) a := rfl
  have hval : valsAB pg n k j a (k ^ nc) = valsAB pg n k j a 0 := by
    rw [valsAB, valsAB, cfg_pow hk0]
  have h₃ : HTB S store
      (fun c => BInv pg n k mR T A R V j a (k ^ nc) c ∧ c.reg rB = k ^ nc ∧ c.reg rPC = k ^ nc)
      (fun c => (SSt pg n k mR T A R V j c ∧ c.reg rA = a) ∧
        AMem pg n k mR T A R V j (a + 1) (valsAB pg n k j a 0) c.mem) 5 := by
    refine HTB.run_le (by decide) (by decide) fun c ⟨⟨⟨hS, hA, hARG, hBEST⟩, hM⟩, _, _⟩ => ?_
    have hl := toffAt_le_full (pg := pg) (n := n) (k := k) hj (show a + 1 ≤ k ^ nb by omega)
    have h1 := hlay.ta
    have h2 := hlay.ar
    have h3 := hlay.rv
    refine ⟨by addr_ok [store, hS.seg.tO, hA, hS.glob.tab, hS.arg], ?_⟩
    have hreg : ∀ r, r ∉ wregs store → (RAM.run store c).reg r = c.reg r :=
      fun r hr => run_reg_of_not_mem (by decide) hr c
    have hS' : SSt pg n k mR T A R V j (RAM.run store c) :=
      (show RegIndep (wregs store) (SSt pg n k mR T A R V j) by indep [sSt_iff, glob_iff, segR_iff])
        c _ hreg hS
    refine ⟨⟨hS', by rw [hreg _ (by decide)]; exact hA⟩, ?_⟩
    have hmem : (RAM.run store c).mem = upd (upd c.mem (T + (toffAt pg n k j + a))
        (table pg n k (sg pg n j) a)) (A + (toffAt pg n k j + a)) (argTab pg n k (sg pg n j) a) := by
      simp +decide only [store, run_seq', run_add, run_st (show rBEST ≠ rT by decide),
        run_st (show rARGB ≠ rT by decide), setReg_reg, ↓reduceIte, setMem_reg, setReg_mem,
        setMem_mem_upd, hS.seg.tO, hA, hS.glob.tab, hS.arg, hARG, hBEST, hbest,
        table_eq hP hk0 (sg_mem hj), argTab_eq hP hk0 (sg_mem hj)]
    rw [hmem, ← hval]
    exact hM.store hlay hj ha
  let Gr : Config → Prop := fun c => (SSt pg n k mR T A R V j c ∧ c.reg rA = a) ∧
    c.reg rOB = V ∧ c.reg rOL = nb
  let Fr : List ℕ → (ℕ → ℕ) → Prop := fun ds m =>
    ds.length = nb ∧ AMem pg n k mR T A R V j (a + 1) (ds ++ cfg k nc 0) m
  have h₄ : HTB S aOdoArgs
      (fun c => (SSt pg n k mR T A R V j c ∧ c.reg rA = a) ∧
        AMem pg n k mR T A R V j (a + 1) (valsAB pg n k j a 0) c.mem)
      (fun c => Gr c ∧ Fr (cfg k nb a) c.mem) 4 := by
    refine HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c ⟨hc, hM⟩ => ?_
    have hag : Agree (wregs aOdoArgs) c (RAM.run aOdoArgs c) :=
      agree_run (by decide) rfl rfl (by decide) c
    have hc' := (show Indep (wregs aOdoArgs) (fun c => SSt pg n k mR T A R V j c ∧ c.reg rA = a)
      by indep [sSt_iff, glob_iff, segR_iff]) c _ hag hc
    refine ⟨⟨hc', ?_, ?_⟩, length_cfg _ _ _, by rw [hag.mem]; exact hM⟩
    all_goals (simp +decide only [aOdoArgs, run_seq', run_mov, setReg_reg, ↓reduceIte,
      hc.1.vv, hc.1.seg.nb]; try rfl)
  have hrl : (rel pg n k (sg pg n j)).length = nb + nc := by rw [rel, List.length_append]
  have h₅ := odo_spec (S := S) (k := k) (ob := V) (ds := cfg k nb a) Gr
    (by simp only [Gr]; indep [sSt_iff, glob_iff, segR_iff])
    (fun c hc => ⟨hc.2.1, by rw [hc.2.2, length_cfg], hc.1.1.glob.kk⟩) Fr
    (fun l m h => (arr_append.mp h.2.vl).1)
    (fun l m t v h ht => by
      refine ⟨by rw [List.length_set]; exact h.1, ?_⟩
      have := h.2.updV hlay hj ha (by rw [List.length_append, length_cfg, h.1, rel,
        List.length_append]) (t := t) (by simp; omega) v
      rw [List.set_append_left _ _ ht] at this
      exact this) (by rw [length_cfg]; omega)
  refine (h₁.seq (h₂.seq (h₃.seq (h₄.seq h₅)))).mono (fun _ h => h) ?_ ?_
  · intro c ⟨⟨⟨hS, hA⟩, _, _⟩, _, hM⟩
    rw [odoL_cfg hk0] at hM
    exact ⟨⟨hS, hM⟩, hA, hS.seg.pb⟩
  · have h1 : nc ≤ Rb k := length_topIdx_le' hP _
    have h2 : nb ≤ Rb k := length_bnd_le' hP (sg_mem hj)
    have h3 : k ^ (topIdx pg n k (sg pg n j)).length ≤ k ^ Rb k := Nat.pow_le_pow_right hk0 h1
    have h4 : k ^ (topIdx pg n k (sg pg n j)).length *
        (tBeta k (faceVerts pg n (sg pg n j)).length + 4) ≤
        k ^ Rb k * (tBeta k (faceVerts pg n (sg pg n j)).length + 4) := Nat.mul_le_mul_right _ h3
    have h5 : nb * 19 ≤ Rb k * 19 := Nat.mul_le_mul_right _ h2
    rw [length_cfg]; unfold tAlpha; omega

/-! ### The `α` loop -/

/-- **The loop over `α`**: all entries of the segment `j`. -/
theorem alphaLoop_spec {S : ℕ} {mR : ℕ → ℕ} {T A R V j : ℕ} (hP : IsPolygon pg n)
    (hk : 3 ≤ k) (hj : j < (segOrder pg n).length) (hlay : Lay pg n k T A R V j)
    (hSz : V + (rel pg n k (sg pg n j)).length ≤ S) :
    HTB S (forUp rA rPB alphaBody)
      (fun c => AInv pg n k mR T A R V j 0 c ∧ c.reg rPB = k ^ (bnd pg n k (sg pg n j)).length)
      (fun c => AInv pg n k mR T A R V j (k ^ (bnd pg n k (sg pg n j)).length) c)
      (k ^ Rb k * (tAlpha k (faceVerts pg n (sg pg n j)).length + 4) + 3) := by
  have hk0 : 0 < k := by omega
  have hl := HTB.forUpC (S := S) (i := rA) (n := rPB) (body := alphaBody)
    (AInv pg n k mR T A R V j)
    (tAlpha k (faceVerts pg n (sg pg n j)).length) (by decide) (by decide) (by decide)
    (fun a => by unfold AInv; indep [sSt_iff, glob_iff, segR_iff])
    (fun a ha => alphaBody_spec hP hk hj hlay hSz a ha)
  have h3 : k ^ (bnd pg n k (sg pg n j)).length ≤ k ^ Rb k :=
    Nat.pow_le_pow_right hk0 (length_bnd_le' hP (sg_mem hj))
  exact hl.mono (fun _ h => h) (fun _ h => h.1) (by
    have := Nat.mul_le_mul_right (tAlpha k (faceVerts pg n (sg pg n j)).length + 4) h3
    omega)

end STACS2027.RAM.P3

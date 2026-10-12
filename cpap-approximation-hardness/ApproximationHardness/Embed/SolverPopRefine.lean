module

public import ApproximationHardness.Embed.SolverPopRAM
public import ApproximationHardness.Embed.SolverPopBounds
public import ApproximationHardness.Embed.SolverStepRefine
import Mathlib.Tactic.IntervalCases
import Lean.Elab.Tactic.Omega

/-! Finite-layout refinement of the upper-stack pop instruction. -/

@[expose] public section

set_option maxHeartbeats 1500000

namespace STACS2027.Embed.RAMSolver

open RAM

/-- Scratch-register work with no memory changes preserves the finite state representation. -/
theorem Rep.frame {L : Layout} {c d : Config} {s : SMS} (hr : Rep L c s)
    (hs : ∀ i, i < 20 → d.reg i = c.reg i)
    (hb : ∀ i, 50 ≤ i → d.reg i = c.reg i) (hm : d.mem = c.mem) : Rep L d s := by
  constructor
  · refine ⟨(hs 0 (by decide)).trans hr.bases.1,
      (hs 1 (by decide)).trans hr.bases.2.1,
      (hs 2 (by decide)).trans hr.bases.2.2.1,
      (hs 3 (by decide)).trans hr.bases.2.2.2.1, ?_⟩
    intro j hj
    exact (hb _ (by omega)).trans (hr.bases.2.2.2.2 j hj)
  · intro j hj i hi
    rw [hm]
    exact hr.arrays j hj i hi
  · exact (hs 6 (by decide)).trans hr.index
  · exact (hs 7 (by decide)).trans hr.mode
  · exact (hs 8 (by decide)).trans hr.node
  · exact (hs 9 (by decide)).trans hr.group
  · exact (hs 10 (by decide)).trans hr.upperLow
  · exact (hs 11 (by decide)).trans hr.resultLow
  · exact (hs 12 (by decide)).trans hr.upperHead
  · exact (hs 13 (by decide)).trans hr.lowerHead
  · exact (hs 14 (by decide)).trans hr.positiveHead
  · exact (hs 15 (by decide)).trans hr.positiveTail
  · exact (hs 16 (by decide)).trans hr.negativeHead
  · exact (hs 17 (by decide)).trans hr.negativeTail
  · exact (hs 18 (by decide)).trans hr.lowerClassHead
  · exact (hs 19 (by decide)).trans hr.lowerClassTail

/-- Updating the mode register refines the corresponding scalar machine update. -/
theorem Rep.setMode {L : Layout} {c : Config} {s : SMS} (hr : Rep L c s) (mode : Nat) :
    Rep L (c.setReg 7 mode) {s with mode := mode} := by
  constructor
  · refine ⟨by simpa using hr.bases.1,
      by simpa using hr.bases.2.1,
      by simpa using hr.bases.2.2.1,
      by simpa using hr.bases.2.2.2.1, ?_⟩
    intro j hj
    have hn : 50 + j ≠ 7 := by omega
    simpa [hn] using hr.bases.2.2.2.2 j hj
  · exact hr.arrays
  · simpa using hr.index
  · rfl
  · simpa using hr.node
  · simpa using hr.group
  · simpa using hr.upperLow
  · simpa using hr.resultLow
  · simpa using hr.upperHead
  · simpa using hr.lowerHead
  · simpa using hr.positiveHead
  · simpa using hr.positiveTail
  · simpa using hr.negativeHead
  · simpa using hr.negativeTail
  · simpa using hr.lowerClassHead
  · simpa using hr.lowerClassTail

/-- The empty-head convention and indexed key loads agree with the solver tables. -/
theorem rawHeadKey_eq {L : Layout} {c : Config} {s : SMS} {S : Sol} {post : List Nat}
    {vertexBound dartBound h : Nat} (hr : Rep L c s)
    (ht : Tables L c S post vertexBound dartBound) (hh : h ≤ dartBound) :
    rawHeadKey c h = S.khM h := by
  by_cases hz : h = 0
  · simp [rawHeadKey, Sol.khM, hz]
  · have hi : h - 1 < dartBound := by omega
    have hbase := hr.bases.2.2.2.2 12 (by decide)
    have hk : c.mem (c.reg 62 + (h - 1)) = S.key (h - 1) := by
      simpa [hbase, Layout.cell] using ht.keys (h - 1) hi
    simp [rawHeadKey, Sol.khM, hz, hk]

/-- The probe reads the represented group and keys without mutating memory or live scalars. -/
theorem popProbe_rep {L : Layout} {c : Config} {s : SMS} {S : Sol} {post : List Nat}
    {vertexBound dartBound : Nat} (hr : Rep L c s) (hb : StepBounds L s dartBound)
    (ht : Tables L c S post vertexBound dartBound) (hx : s.rxp ≠ 0) :
    let p := run popProbe c
    (∀ i, i < 20 ∨ 50 ≤ i → p.reg i = c.reg i) ∧
    p.reg 20 = s.rxp - 1 ∧ p.reg 21 = s.m.ph (s.rxp - 1) ∧
    p.reg 22 = s.m.pt (s.rxp - 1) ∧ p.reg 23 = s.m.mh (s.rxp - 1) ∧
    p.reg 24 = s.m.mt (s.rxp - 1) ∧ p.reg 28 = s.m.gn (s.rxp - 1) ∧
    p.reg 25 = S.khM (s.m.ph (s.rxp - 1)) - s.lh ∧
    p.reg 26 = S.khM (s.m.mh (s.rxp - 1)) - s.lh ∧
    p.mem = c.mem ∧ p.out = c.out := by
  have hg : s.rxp - 1 < L.width := by have := hb.upper; omega
  have hbase := hr.bases.2.2.2.2
  have hread : ∀ j, j < 12 → c.mem (c.reg (50 + j) + (c.reg 12 - 1)) =
      memField s.m j (s.rxp - 1) := by
    intro j hj
    simpa [hbase j (by omega), hr.upperHead, Layout.cell] using hr.arrays j hj (s.rxp - 1) hg
  obtain ⟨hf, hg', hp, hpt, hm, hmt, hgn, hkp, hkm, hmem, hout⟩ :=
    popProbe_raw c hr.bases.1 hr.bases.2.1
  simp only [hread 1 (by decide), hread 2 (by decide), hread 3 (by decide),
    hread 4 (by decide), hread 5 (by decide), memField] at hp hpt hm hmt hgn hkp hkm
  rw [rawHeadKey_eq hr ht (hb.positiveHeads _ hg), hr.upperLow] at hkp
  rw [rawHeadKey_eq hr ht (hb.negativeHeads _ hg), hr.upperLow] at hkm
  exact ⟨hf, (hg'.trans (congrArg (fun n => n - 1) hr.upperHead)), hp, hpt, hm, hmt, hgn, hkp, hkm, hmem, hout⟩

/-- Splitting the probe from the executable branch is an exact operational identity. -/
theorem popStepProgram_run_probe (c : Config) (hx : c.reg 12 ≠ 0) :
    let p := run popProbe c
    run popStepProgram c =
      if p.reg 25 = 0 then
        if p.reg 26 = 0 then p.setReg 7 2
        else run (consumeRecord 12) (run (popClasses false) p)
      else run (consumeRecord 12) (run (popClasses true) p) := by
  simp [popStepProgram, popProbe, seqs, run, hx]

/-- The active pop branch refines the linked state and preserves every plan table. -/
theorem popStepProgram_active {L : Layout} {c : Config} {s : SMS} {S : Sol} {post : List Nat}
    {vertexBound dartBound : Nat} (hr : Rep L c s) (hb : StepBounds L s dartBound)
    (ht : Tables L c S post vertexBound dartBound)
    (hpop : s.rxp ≠ 0 ∧ s.lh < S.gtopM s.m (s.rxp - 1)) :
    Rep L (run popStepProgram c) (S.popStep s) ∧
      Tables L (run popStepProgram c) S post vertexBound dartBound := by
  have hg : s.rxp - 1 < L.width := by have := hb.upper; omega
  have hbase := hr.bases.2.2.2.2
  let p := run popProbe c
  obtain ⟨hf, hgroup, hph, hpt, hmh, hmt, hgn, hpk, hmk, hpMem, hpOut⟩ := popProbe_rep hr hb ht hpop.1
  change (∀ i, i < 20 ∨ 50 ≤ i → p.reg i = c.reg i) at hf
  change p.reg 20 = s.rxp - 1 at hgroup
  change p.reg 21 = s.m.ph (s.rxp - 1) at hph
  change p.reg 22 = s.m.pt (s.rxp - 1) at hpt
  change p.reg 23 = s.m.mh (s.rxp - 1) at hmh
  change p.reg 24 = s.m.mt (s.rxp - 1) at hmt
  change p.reg 28 = s.m.gn (s.rxp - 1) at hgn
  change p.mem = c.mem at hpMem
  change p.out = c.out at hpOut
  have hp0 : p.reg 0 = 0 := (hf 0 (Or.inl (by decide))).trans hr.bases.1
  have hp1 : p.reg 1 = 1 := (hf 1 (Or.inl (by decide))).trans hr.bases.2.1
  let up := decide (s.lh < S.khM (s.m.ph (s.rxp - 1)))
  have hrun : run popStepProgram c = run (consumeRecord 12) (run (popClasses up) p) := by
    rw [popStepProgram_run_probe c (by simpa [hr.upperHead] using hpop.1)]
    change (if p.reg 25 = 0 then
      if p.reg 26 = 0 then p.setReg 7 2
      else run (consumeRecord 12) (run (popClasses false) p)
      else run (consumeRecord 12) (run (popClasses true) p)) = _
    rw [hpk, hmk]
    by_cases hu : s.lh < S.khM (s.m.ph (s.rxp - 1))
    · have hn : S.khM (s.m.ph (s.rxp - 1)) - s.lh ≠ 0 := by omega
      simp [up, hu, hn]
    · have hz : S.khM (s.m.ph (s.rxp - 1)) - s.lh = 0 := by omega
      have hm : s.lh < S.khM (s.m.mh (s.rxp - 1)) := by
        have hh := hpop.2
        dsimp [Sol.gtopM] at hh
        omega
      have hn : S.khM (s.m.mh (s.rxp - 1)) - s.lh ≠ 0 := by omega
      simp [up, hu, hz, hn]
  obtain ⟨hs, hm, hreg, hout⟩ := popExecute_raw p up hp0 hp1
  have hsmall : ∀ i, i < 20 → p.reg i = c.reg i := fun i hi => hf i (Or.inl hi)
  have hlarge : ∀ i, 50 ≤ i → p.reg i = c.reg i := fun i hi => hf i (Or.inr hi)
  simp only [hpMem, hph, hpt, hmh, hmt, hgroup,
    hsmall 14 (by decide), hsmall 15 (by decide), hsmall 16 (by decide),
    hsmall 17 (by decide), hsmall 9 (by decide), hlarge 50 (by decide),
    hlarge 58 (by decide), hlarge 59 (by decide), hr.positiveHead, hr.positiveTail,
    hr.negativeHead, hr.negativeTail, hr.group, hbase 0 (by decide),
    hbase 8 (by decide), hbase 9 (by decide), appL_head, appL_tail] at hm
  let uh := if up then s.m.ph (s.rxp - 1) else s.m.mh (s.rxp - 1)
  let ut := if up then s.m.pt (s.rxp - 1) else s.m.mt (s.rxp - 1)
  let wh := if up then s.m.mh (s.rxp - 1) else s.m.ph (s.rxp - 1)
  let wt := if up then s.m.mt (s.rxp - 1) else s.m.pt (s.rxp - 1)
  let a := appL s.m.nx s.ah s.at' uh ut
  let b := appL a.2.2 s.bh s.bt wh wt
  let m₁ := appendMem c.mem (L.block 0) s.ah s.at' uh
  let m₂ := appendMem m₁ (L.block 0) s.bh s.bt wh
  have hx₁ : ∀ i, i < L.width → m₁ (L.cell 0 i) = a.2.2 i := by
    intro i hi
    exact appendMem_rep L c.mem s.m.nx s.ah s.at' uh ut i hb.positive hb.width hi
      (fun i hi => hr.arrays 0 (by decide) i hi)
  have hx₂ : ∀ i, i < L.width → m₂ (L.cell 0 i) = b.2.2 i := by
    intro i hi
    exact appendMem_rep L m₁ a.2.2 s.bh s.bt wh wt i hb.negative hb.width hi hx₁
  have hforeign : ∀ j i, j ≠ 0 → i < L.width → m₂ (L.cell j i) = c.mem (L.cell j i) := by
    intro j i hj hi
    rw [show m₂ (L.cell j i) = m₁ (L.cell j i) from
      appendMem_foreign L m₁ s.bh s.bt wh j i hb.negative hb.width hi hj]
    exact appendMem_foreign L c.mem s.ah s.at' uh j i hb.positive hb.width hi hj
  have hm' : (run popStepProgram c).mem =
      upd (upd m₂ (L.cell 8 (s.rxp - 1)) (s.G + 1))
        (L.cell 9 (s.rxp - 1)) (if up then 0 else 1) := by
    rw [hrun]
    simpa only [m₂, m₁, uh, wh, Layout.cell] using hm
  have hscalar : ∀ i, i < 20 → (run popStepProgram c).reg i =
      if i = 12 then s.m.gn (s.rxp - 1) else if i = 14 then a.1
      else if i = 15 then a.2.1 else if i = 16 then b.1
      else if i = 17 then b.2.1 else c.reg i := by
    intro i hi
    rw [hrun, hs i hi]
    simp only [hgn, hph, hpt, hmh, hmt, hpMem, hsmall i hi,
      hsmall 14 (by decide), hsmall 15 (by decide), hsmall 16 (by decide),
      hsmall 17 (by decide), hr.positiveHead, hr.positiveTail, hr.negativeHead,
      hr.negativeTail, a, b, uh, ut, wh, wt, appL_head, appL_tail]
  have hprotected : ∀ i, 50 ≤ i → (run popStepProgram c).reg i = c.reg i := by
    intro i hi
    rw [hrun]
    exact (hreg i hi).trans (hlarge i hi)
  have hstep : S.popStep s = { s with
      m := { s.m with
        nx := b.2.2
        gp := upd s.m.gp (s.rxp - 1) (s.G + 1)
        gf := upd s.m.gf (s.rxp - 1) (if up then 0 else 1) }
      rxp := s.m.gn (s.rxp - 1)
      ah := a.1
      at' := a.2.1
      bh := b.1
      bt := b.2.1
      cons := s.cons ++ [s.rxp - 1] } := by
    unfold Sol.popStep
    rw [if_pos hpop]
    all_goals rfl
  refine ⟨?_, ?_⟩
  · rw [hstep]
    constructor
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simpa [hr.bases.1] using hscalar 0 (by decide)
      · simpa [hr.bases.2.1] using hscalar 1 (by decide)
      · simpa [hr.bases.2.2.1] using hscalar 2 (by decide)
      · simpa [hr.bases.2.2.2.1] using hscalar 3 (by decide)
      · intro j hj
        rw [hprotected _ (by omega)]
        exact hbase j hj
    · intro j hj i hi
      rw [hm']
      simp only [update_cell L _ j 9 i (s.rxp - 1) _ hi hg,
        update_cell L _ j 8 i (s.rxp - 1) _ hi hg]
      interval_cases j
      · simpa [memField, b, a] using hx₂ i hi
      · simp [memField, upd, hforeign 1 i (by decide) hi, hr.arrays 1 (by decide) i hi]
      · simp [memField, upd, hforeign 2 i (by decide) hi, hr.arrays 2 (by decide) i hi]
      · simp [memField, upd, hforeign 3 i (by decide) hi, hr.arrays 3 (by decide) i hi]
      · simp [memField, upd, hforeign 4 i (by decide) hi, hr.arrays 4 (by decide) i hi]
      · simp [memField, upd, hforeign 5 i (by decide) hi, hr.arrays 5 (by decide) i hi]
      · simp [memField, upd, hforeign 6 i (by decide) hi, hr.arrays 6 (by decide) i hi]
      · simp [memField, upd, hforeign 7 i (by decide) hi, hr.arrays 7 (by decide) i hi]
      · simp [memField, upd, hforeign 8 i (by decide) hi, hr.arrays 8 (by decide) i hi]
      · simp [memField, upd, hforeign 9 i (by decide) hi, hr.arrays 9 (by decide) i hi]
      · simp [memField, upd, hforeign 10 i (by decide) hi, hr.arrays 10 (by decide) i hi]
      · simp [memField, upd, hforeign 11 i (by decide) hi, hr.arrays 11 (by decide) i hi]
    · simpa [a, b, hr.index] using hscalar 6 (by decide)
    · simpa [a, b, hr.mode] using hscalar 7 (by decide)
    · simpa [a, b, hr.node] using hscalar 8 (by decide)
    · simpa [a, b, hr.group] using hscalar 9 (by decide)
    · simpa [a, b, hr.upperLow] using hscalar 10 (by decide)
    · simpa [a, b, hr.resultLow] using hscalar 11 (by decide)
    · simpa [a, b, hr.upperHead] using hscalar 12 (by decide)
    · simpa [a, b, hr.lowerHead] using hscalar 13 (by decide)
    · simpa [a, b, hr.positiveHead] using hscalar 14 (by decide)
    · simpa [a, b, hr.positiveTail] using hscalar 15 (by decide)
    · simpa [a, b, hr.negativeHead] using hscalar 16 (by decide)
    · simpa [a, b, hr.negativeTail] using hscalar 17 (by decide)
    · simpa [a, b, hr.lowerClassHead] using hscalar 18 (by decide)
    · simpa [a, b, hr.lowerClassTail] using hscalar 19 (by decide)
  · have h₁ : TableMemEq L m₁ c.mem := TableMemEq.append L c.mem _ _ _ hb.positive hb.width
    have h₂ : TableMemEq L m₂ c.mem :=
      (TableMemEq.append L m₁ _ _ _ hb.negative hb.width).trans h₁
    have h₃ := (TableMemEq.update L m₂ 8 (s.rxp - 1) (s.G + 1) (by decide) hg).trans h₂
    have h₄ := (TableMemEq.update L _ 9 (s.rxp - 1) (if up then 0 else 1) (by decide) hg).trans h₃
    apply ht.frame (by simpa using hscalar 4 (by decide)) (by simpa using hscalar 5 (by decide))
    rw [hm']
    exact h₄

/-- The inactive pop branch changes only the mode to the consume phase. -/
theorem popStepProgram_inactive {L : Layout} {c : Config} {s : SMS} {S : Sol} {post : List Nat}
    {vertexBound dartBound : Nat} (hr : Rep L c s) (hb : StepBounds L s dartBound)
    (ht : Tables L c S post vertexBound dartBound)
    (hpop : ¬(s.rxp ≠ 0 ∧ s.lh < S.gtopM s.m (s.rxp - 1))) :
    Rep L (run popStepProgram c) (S.popStep s) ∧
      Tables L (run popStepProgram c) S post vertexBound dartBound := by
  have hstep : S.popStep s = { s with mode := 2 } := by simp [Sol.popStep, hpop]
  rw [hstep]
  by_cases hx : s.rxp = 0
  · have hrun : run popStepProgram c = c.setReg 7 2 := by
      simp [popStepProgram, run, hr.upperHead, hx]
    rw [hrun]
    exact ⟨hr.setMode 2, ht.frame (by simp) (by simp) (TableMemEq.refl L c.mem)⟩
  · let p := run popProbe c
    obtain ⟨hf, _, _, _, _, _, _, hpk, hmk, hmem, _⟩ := popProbe_rep hr hb ht hx
    have hle : S.gtopM s.m (s.rxp - 1) ≤ s.lh := by omega
    have hp : S.khM (s.m.ph (s.rxp - 1)) - s.lh = 0 := by
      dsimp [Sol.gtopM] at hle
      omega
    have hm : S.khM (s.m.mh (s.rxp - 1)) - s.lh = 0 := by
      dsimp [Sol.gtopM] at hle
      omega
    have hrun : run popStepProgram c = p.setReg 7 2 := by
      rw [popStepProgram_run_probe c (by simpa [hr.upperHead] using hx)]
      simp only [hpk, hmk, hp, hm, ↓reduceIte]
      all_goals rfl
    have hrp : Rep L p s := hr.frame (fun i hi => hf i (Or.inl hi))
      (fun i hi => hf i (Or.inr hi)) hmem
    have htp : Tables L p S post vertexBound dartBound := ht.frame
      (hf 4 (Or.inl (by decide))) (hf 5 (Or.inl (by decide))) (by rw [hmem]; exact TableMemEq.refl L c.mem)
    rw [hrun]
    exact ⟨hrp.setMode 2, htp.frame (by simp) (by simp) (TableMemEq.refl L p.mem)⟩

/-- Both executable pop branches refine the linked machine and preserve its tables. -/
theorem popStepProgram_rep_tables {L : Layout} {c : Config} {s : SMS} {S : Sol} {post : List Nat}
    {vertexBound dartBound : Nat} (hr : Rep L c s) (hb : StepBounds L s dartBound)
    (ht : Tables L c S post vertexBound dartBound) :
    Rep L (run popStepProgram c) (S.popStep s) ∧
      Tables L (run popStepProgram c) S post vertexBound dartBound := by
  by_cases hpop : s.rxp ≠ 0 ∧ s.lh < S.gtopM s.m (s.rxp - 1)
  · exact popStepProgram_active hr hb ht hpop
  · exact popStepProgram_inactive hr hb ht hpop

/-- Actual bounded execution of a pop step, its state refinement, and preserved tables. -/
theorem popStepProgram_simulation {L : Layout} {c : Config} {s : SMS} {S : Sol} {post : List Nat}
    {vertexBound dartBound : Nat} (hr : Rep L c s) (hb : StepBounds L s dartBound)
    (ht : Tables L c S post vertexBound dartBound) :
    ∃ t, ExecB L.limit popStepProgram c t (run popStepProgram c) ∧ t ≤ 200 ∧
      Rep L (run popStepProgram c) (S.popStep s) ∧
      Tables L (run popStepProgram c) S post vertexBound dartBound := by
  obtain ⟨t, he, ht'⟩ := popStepProgram_exec_ofRep hr hb ht
  obtain ⟨hr', htab⟩ := popStepProgram_rep_tables hr hb ht
  exact ⟨t, he, ht', hr', htab⟩

end STACS2027.Embed.RAMSolver

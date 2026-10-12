module

public import ApproximationHardness.Embed.SolverStepRAM
public import ApproximationHardness.Embed.SolverStepBounds
public import ApproximationHardness.Embed.SolverFrameRAM
import Mathlib.Tactic.IntervalCases
import Lean.Elab.Tactic.Omega

/-! Finite-layout refinement of the linked solver's consume steps. -/

@[expose] public section

set_option maxHeartbeats 1500000

namespace STACS2027.Embed.RAMSolver

open RAM

/-- The consume program refines the actual linked machine for a nonempty lower stack. -/
theorem consumeGroupProgram_rep {L : Layout} {c : Config} {s : SMS} {dartBound : Nat}
    (hr : Rep L c s) (hb : StepBounds L s dartBound) (hy : s.ryp ≠ 0) :
    Rep L (run consumeGroupProgram c) (Sol.consStep s) := by
  have hg : s.ryp - 1 < L.width := by have := hb.lower; omega
  have hbase := hr.bases.2.2.2.2
  have hph : c.mem (c.reg 51 + (c.reg 13 - 1)) = s.m.ph (s.ryp - 1) := by
    simpa [hbase 1 (by decide), hr.lowerHead, memField, Layout.cell] using
      hr.arrays 1 (by decide) (s.ryp - 1) hg
  have hpt : c.mem (c.reg 52 + (c.reg 13 - 1)) = s.m.pt (s.ryp - 1) := by
    simpa [hbase 2 (by decide), hr.lowerHead, memField, Layout.cell] using
      hr.arrays 2 (by decide) (s.ryp - 1) hg
  have hmh : c.mem (c.reg 53 + (c.reg 13 - 1)) = s.m.mh (s.ryp - 1) := by
    simpa [hbase 3 (by decide), hr.lowerHead, memField, Layout.cell] using
      hr.arrays 3 (by decide) (s.ryp - 1) hg
  have hmt : c.mem (c.reg 54 + (c.reg 13 - 1)) = s.m.mt (s.ryp - 1) := by
    simpa [hbase 4 (by decide), hr.lowerHead, memField, Layout.cell] using
      hr.arrays 4 (by decide) (s.ryp - 1) hg
  have hgn : c.mem (c.reg 55 + (c.reg 13 - 1)) = s.m.gn (s.ryp - 1) := by
    simpa [hbase 5 (by decide), hr.lowerHead, memField, Layout.cell] using
      hr.arrays 5 (by decide) (s.ryp - 1) hg
  simp only [hr.lowerHead] at hph hpt hmh hmt hgn
  obtain ⟨hs, hm, hf, hout⟩ := consumeGroupProgram_raw c hr.bases.1 hr.bases.2.1
  simp only [hph, hpt, hmh, hmt, hgn, hr.lowerClassHead, hr.lowerClassTail,
    hr.lowerHead, hr.group, hbase 0 (by decide), hbase 8 (by decide),
    hbase 9 (by decide), appL_head, appL_tail] at hs hm
  let a := appL s.m.nx s.ch s.ct (s.m.ph (s.ryp - 1)) (s.m.pt (s.ryp - 1))
  let b := appL a.2.2 a.1 a.2.1 (s.m.mh (s.ryp - 1)) (s.m.mt (s.ryp - 1))
  let m₁ := appendMem c.mem (L.block 0) s.ch s.ct (s.m.ph (s.ryp - 1))
  let m₂ := appendMem m₁ (L.block 0) a.1 a.2.1 (s.m.mh (s.ryp - 1))
  have ha : a.2.1 ≤ L.width := by
    dsimp [a]
    rw [appL_tail]
    split
    · exact hb.positiveTails _ hg
    · split
      · exact hb.lowerClass
      · exact hb.positiveTails _ hg
  have hx₁ : ∀ i, i < L.width → m₁ (L.cell 0 i) = a.2.2 i := by
    intro i hi
    exact appendMem_rep L c.mem s.m.nx s.ch s.ct _ _ i hb.lowerClass hb.width hi
      (fun i hi => hr.arrays 0 (by decide) i hi)
  have hx₂ : ∀ i, i < L.width → m₂ (L.cell 0 i) = b.2.2 i := by
    intro i hi
    exact appendMem_rep L m₁ a.2.2 a.1 a.2.1 _ _ i ha hb.width hi hx₁
  have hforeign : ∀ j i, j ≠ 0 → i < L.width → m₂ (L.cell j i) = c.mem (L.cell j i) := by
    intro j i hj hi
    rw [show m₂ (L.cell j i) = m₁ (L.cell j i) from
      appendMem_foreign L m₁ a.1 a.2.1 _ j i ha hb.width hi hj]
    exact appendMem_foreign L c.mem s.ch s.ct _ j i hb.lowerClass hb.width hi hj
  have hm' : (run consumeGroupProgram c).mem =
      upd (upd m₂ (L.cell 8 (s.ryp - 1)) (s.G + 1))
        (L.cell 9 (s.ryp - 1)) (if s.m.ph (s.ryp - 1) = 0 then 0 else 1) := by
    simpa only [m₂, m₁, a, appL_head, appL_tail, Layout.cell] using hm
  have hstep : Sol.consStep s = { s with
      m := { s.m with
        nx := b.2.2
        gp := upd s.m.gp (s.ryp - 1) (s.G + 1)
        gf := upd s.m.gf (s.ryp - 1) (if s.m.ph (s.ryp - 1) ≠ 0 then 1 else 0) }
      ryp := s.m.gn (s.ryp - 1)
      ch := b.1
      ct := b.2.1
      cons := s.cons ++ [s.ryp - 1] } := by
    unfold Sol.consStep
    rw [if_pos hy]
    all_goals rfl
  rw [hstep]
  constructor
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [hr.bases.1] using hs 0 (by decide)
    · simpa [hr.bases.2.1] using hs 1 (by decide)
    · simpa [hr.bases.2.2.1] using hs 2 (by decide)
    · simpa [hr.bases.2.2.2.1] using hs 3 (by decide)
    · intro j hj
      rw [hf _ (by omega)]
      exact hbase j hj
  · intro j hj i hi
    rw [hm']
    simp only [update_cell L _ j 9 i (s.ryp - 1) _ hi hg,
      update_cell L _ j 8 i (s.ryp - 1) _ hi hg]
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
  · simpa [a, b, hr.index] using hs 6 (by decide)
  · simpa [a, b, hr.mode] using hs 7 (by decide)
  · simpa [a, b, hr.node] using hs 8 (by decide)
  · simpa [a, b, hr.group] using hs 9 (by decide)
  · simpa [a, b, hr.upperLow] using hs 10 (by decide)
  · simpa [a, b, hr.resultLow] using hs 11 (by decide)
  · simpa [a, b, hr.upperHead] using hs 12 (by decide)
  · simpa [a, b, hr.lowerHead] using hs 13 (by decide)
  · simpa [a, b, hr.positiveHead] using hs 14 (by decide)
  · simpa [a, b, hr.positiveTail] using hs 15 (by decide)
  · simpa [a, b, hr.negativeHead] using hs 16 (by decide)
  · simpa [a, b, hr.negativeTail] using hs 17 (by decide)
  · simpa [a, b, hr.lowerClassHead] using hs 18 (by decide)
  · simpa [a, b, hr.lowerClassTail] using hs 19 (by decide)

/-- The final consume branch stores the merged stack without changing the accumulators. -/
theorem finishMergeProgram_rep {L : Layout} {c : Config} {s : SMS} {dartBound : Nat}
    (hr : Rep L c s) (hb : StepBounds L s dartBound) (hy : s.ryp = 0) :
    Rep L (run finishMergeProgram c) (Sol.consStep s) := by
  have hbase := hr.bases.2.2.2.2
  obtain ⟨hs, hm, hf, hout⟩ := finishMergeProgram_raw c hr.bases.1 hr.bases.2.1
  simp only [hr.lowerClassHead, hr.lowerClassTail, hr.negativeHead, hr.negativeTail,
    hr.group, hr.node, hr.positiveHead, hr.positiveTail, hr.upperHead, hr.resultLow,
    hbase 0 (by decide), hbase 1 (by decide), hbase 2 (by decide),
    hbase 3 (by decide), hbase 4 (by decide), hbase 5 (by decide),
    hbase 6 (by decide), hbase 7 (by decide), appL_head, appL_tail] at hm
  let y := appL s.m.nx s.ch s.ct s.bh s.bt
  let m₀ := appendMem c.mem (L.block 0) s.ch s.ct s.bh
  have hx : ∀ i, i < L.width → m₀ (L.cell 0 i) = y.2.2 i := by
    intro i hi
    exact appendMem_rep L c.mem s.m.nx s.ch s.ct s.bh s.bt i hb.lowerClass hb.width hi
      (fun i hi => hr.arrays 0 (by decide) i hi)
  have hforeign : ∀ j i, j ≠ 0 → i < L.width → m₀ (L.cell j i) = c.mem (L.cell j i) := by
    intro j i hj hi
    exact appendMem_foreign L c.mem s.ch s.ct s.bh j i hb.lowerClass hb.width hi hj
  have hm' : (run finishMergeProgram c).mem =
    upd (upd (upd (upd (upd (upd (upd m₀ (L.cell 1 s.G) s.ah)
      (L.cell 2 s.G) s.at') (L.cell 3 s.G) y.1) (L.cell 4 s.G) y.2.1)
      (L.cell 5 s.G) s.rxp) (L.cell 6 s.v) (s.G + 1)) (L.cell 7 s.v) s.lx := by
    simpa only [m₀, y, appL_head, appL_tail, Layout.cell] using hm
  have hstep : Sol.consStep s = { s with
      m := { SMem.store { s.m with nx := y.2.2 } s.v (s.G + 1) s.lx with
        ph := upd s.m.ph s.G s.ah
        pt := upd s.m.pt s.G s.at'
        mh := upd s.m.mh s.G y.1
        mt := upd s.m.mt s.G y.2.1
        gn := upd s.m.gn s.G s.rxp }
      mode := 0 } := by
    unfold Sol.consStep
    rw [if_neg (by simp [hy])]
    all_goals rfl
  rw [hstep]
  constructor
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [hr.bases.1] using hs 0 (by decide)
    · simpa [hr.bases.2.1] using hs 1 (by decide)
    · simpa [hr.bases.2.2.1] using hs 2 (by decide)
    · simpa [hr.bases.2.2.2.1] using hs 3 (by decide)
    · intro j hj
      rw [hf _ (by omega)]
      exact hbase j hj
  · intro j hj i hi
    rw [hm']
    simp only [update_cell L _ j 7 i s.v _ hi hb.node,
      update_cell L _ j 6 i s.v _ hi hb.node,
      update_cell L _ j 5 i s.G _ hi hb.group,
      update_cell L _ j 4 i s.G _ hi hb.group,
      update_cell L _ j 3 i s.G _ hi hb.group,
      update_cell L _ j 2 i s.G _ hi hb.group,
      update_cell L _ j 1 i s.G _ hi hb.group]
    interval_cases j
    · simpa [SMem.store, memField, y] using hx i hi
    · simp [SMem.store, memField, upd, y, hforeign 1 i (by decide) hi, hr.arrays 1 (by decide) i hi]
    · simp [SMem.store, memField, upd, y, hforeign 2 i (by decide) hi, hr.arrays 2 (by decide) i hi]
    · simp [SMem.store, memField, upd, y, hforeign 3 i (by decide) hi, hr.arrays 3 (by decide) i hi]
    · simp [SMem.store, memField, upd, y, hforeign 4 i (by decide) hi, hr.arrays 4 (by decide) i hi]
    · simp [SMem.store, memField, upd, y, hforeign 5 i (by decide) hi, hr.arrays 5 (by decide) i hi]
    · simp [SMem.store, memField, upd, y, hforeign 6 i (by decide) hi, hr.arrays 6 (by decide) i hi]
    · simp [SMem.store, memField, upd, y, hforeign 7 i (by decide) hi, hr.arrays 7 (by decide) i hi]
    · simp [SMem.store, memField, upd, y, hforeign 8 i (by decide) hi, hr.arrays 8 (by decide) i hi]
    · simp [SMem.store, memField, upd, y, hforeign 9 i (by decide) hi, hr.arrays 9 (by decide) i hi]
    · simp [SMem.store, memField, upd, y, hforeign 10 i (by decide) hi, hr.arrays 10 (by decide) i hi]
    · simp [SMem.store, memField, upd, y, hforeign 11 i (by decide) hi, hr.arrays 11 (by decide) i hi]
  · simpa [y, hr.index] using hs 6 (by decide)
  · simpa [y, hr.mode] using hs 7 (by decide)
  · simpa [y, hr.node] using hs 8 (by decide)
  · simpa [y, hr.group] using hs 9 (by decide)
  · simpa [y, hr.upperLow] using hs 10 (by decide)
  · simpa [y, hr.resultLow] using hs 11 (by decide)
  · simpa [y, hr.upperHead] using hs 12 (by decide)
  · simpa [y, hr.lowerHead] using hs 13 (by decide)
  · simpa [y, hr.positiveHead] using hs 14 (by decide)
  · simpa [y, hr.positiveTail] using hs 15 (by decide)
  · simpa [y, hr.negativeHead] using hs 16 (by decide)
  · simpa [y, hr.negativeTail] using hs 17 (by decide)
  · simpa [y, hr.lowerClassHead] using hs 18 (by decide)
  · simpa [y, hr.lowerClassTail] using hs 19 (by decide)

/-- Both branches of the consume dispatcher refine the linked machine. -/
theorem consStepProgram_rep {L : Layout} {c : Config} {s : SMS} {dartBound : Nat}
    (hr : Rep L c s) (hb : StepBounds L s dartBound) :
    Rep L (run consStepProgram c) (Sol.consStep s) := by
  by_cases hy : s.ryp = 0
  · simpa [consStepProgram, run, hr.lowerHead, hy] using finishMergeProgram_rep hr hb hy
  · simpa [consStepProgram, run, hr.lowerHead, hy] using consumeGroupProgram_rep hr hb hy

/-- Consumption preserves the preprocessing and DFS tables. -/
theorem consumeGroupProgram_tables {L : Layout} {c : Config} {s : SMS} {S : Sol} {post : List Nat}
    {vertexBound dartBound : Nat} (hr : Rep L c s) (hb : StepBounds L s dartBound)
    (ht : Tables L c S post vertexBound dartBound) (hy : s.ryp ≠ 0) :
    Tables L (run consumeGroupProgram c) S post vertexBound dartBound := by
  have hg : s.ryp - 1 < L.width := by have := hb.lower; omega
  have hbase := hr.bases.2.2.2.2
  obtain ⟨hs, hm, hf, hout⟩ := consumeGroupProgram_raw c hr.bases.1 hr.bases.2.1
  let g := c.reg 13 - 1
  let ph := c.mem (c.reg 51 + g)
  let pt := c.mem (c.reg 52 + g)
  let mh := c.mem (c.reg 53 + g)
  let a := appL (fun i => c.mem (c.reg 50 + i)) (c.reg 18) (c.reg 19) ph pt
  let m₁ := appendMem c.mem (L.block 0) (c.reg 18) (c.reg 19) ph
  let m₂ := appendMem m₁ (L.block 0) a.1 a.2.1 mh
  have hct : c.reg 19 ≤ L.width := by rw [hr.lowerClassTail]; exact hb.lowerClass
  have hpt : pt ≤ L.width := by
    have hm := hr.arrays 2 (by decide) (s.ryp - 1) hg
    simp only [memField] at hm
    have he : pt = s.m.pt (s.ryp - 1) := by
      simpa [pt, g, Layout.cell, hbase 2 (by decide), hr.lowerHead] using hm
    rw [he]; exact hb.positiveTails _ hg
  have ha : a.2.1 ≤ L.width := by
    dsimp [a]; rw [appL_tail]
    split
    · exact hpt
    · split
      · exact hct
      · exact hpt
  have hm' : (run consumeGroupProgram c).mem =
      upd (upd m₂ (L.cell 8 (s.ryp - 1)) (s.G + 1))
        (L.cell 9 (s.ryp - 1)) (if ph = 0 then 0 else 1) := by
    simpa only [m₂, m₁, a, ph, pt, mh, g, Layout.cell, hr.lowerHead, hr.group,
      hbase 0 (by decide), hbase 8 (by decide), hbase 9 (by decide)] using hm
  have h₁ : TableMemEq L m₁ c.mem := TableMemEq.append L c.mem _ _ _ hct hb.width
  have h₂ : TableMemEq L m₂ c.mem :=
    (TableMemEq.append L m₁ _ _ _ ha hb.width).trans h₁
  have h₃ := (TableMemEq.update L m₂ 8 (s.ryp - 1) (s.G + 1) (by decide) hg).trans h₂
  have h₄ := (TableMemEq.update L _ 9 (s.ryp - 1) (if ph = 0 then 0 else 1) (by decide) hg).trans h₃
  apply ht.frame (by simpa using hs 4 (by decide)) (by simpa using hs 5 (by decide))
  rw [hm']
  exact h₄

/-- Finishing a merge preserves all read-only tables. -/
theorem finishMergeProgram_tables {L : Layout} {c : Config} {s : SMS} {S : Sol} {post : List Nat}
    {vertexBound dartBound : Nat} (hr : Rep L c s) (hb : StepBounds L s dartBound)
    (ht : Tables L c S post vertexBound dartBound) :
    Tables L (run finishMergeProgram c) S post vertexBound dartBound := by
  have hbase := hr.bases.2.2.2.2
  obtain ⟨hs, hm, hf, hout⟩ := finishMergeProgram_raw c hr.bases.1 hr.bases.2.1
  let y := appL (fun i => c.mem (c.reg 50 + i)) (c.reg 18) (c.reg 19) (c.reg 16) (c.reg 17)
  let m₀ := appendMem c.mem (L.block 0) (c.reg 18) (c.reg 19) (c.reg 16)
  have hct : c.reg 19 ≤ L.width := by rw [hr.lowerClassTail]; exact hb.lowerClass
  have h₀ : TableMemEq L m₀ c.mem := TableMemEq.append L c.mem _ _ _ hct hb.width
  have h₁ := (TableMemEq.update L m₀ 1 s.G (c.reg 14) (by decide) hb.group).trans h₀
  have h₂ := (TableMemEq.update L _ 2 s.G (c.reg 15) (by decide) hb.group).trans h₁
  have h₃ := (TableMemEq.update L _ 3 s.G y.1 (by decide) hb.group).trans h₂
  have h₄ := (TableMemEq.update L _ 4 s.G y.2.1 (by decide) hb.group).trans h₃
  have h₅ := (TableMemEq.update L _ 5 s.G (c.reg 12) (by decide) hb.group).trans h₄
  have h₆ := (TableMemEq.update L _ 6 s.v (c.reg 9 + 1) (by decide) hb.node).trans h₅
  have h₇ := (TableMemEq.update L _ 7 s.v (c.reg 11) (by decide) hb.node).trans h₆
  apply ht.frame (by simpa using hs 4 (by decide)) (by simpa using hs 5 (by decide))
  rw [hm]
  simpa only [m₀, y, Layout.cell, hr.group, hr.node, hbase 0 (by decide),
    hbase 1 (by decide), hbase 2 (by decide), hbase 3 (by decide),
    hbase 4 (by decide), hbase 5 (by decide), hbase 6 (by decide), hbase 7 (by decide)] using h₇

/-- The consume dispatcher preserves all read-only tables. -/
theorem consStepProgram_tables {L : Layout} {c : Config} {s : SMS} {S : Sol} {post : List Nat}
    {vertexBound dartBound : Nat} (hr : Rep L c s) (hb : StepBounds L s dartBound)
    (ht : Tables L c S post vertexBound dartBound) :
    Tables L (run consStepProgram c) S post vertexBound dartBound := by
  by_cases hy : s.ryp = 0
  · simpa [consStepProgram, run, hr.lowerHead, hy] using finishMergeProgram_tables hr hb ht
  · simpa [consStepProgram, run, hr.lowerHead, hy] using consumeGroupProgram_tables hr hb ht hy

/-- A concrete bounded run, finite representation, and preserved tables for every consume step. -/
theorem consStepProgram_simulation {L : Layout} {c : Config} {s : SMS} {S : Sol} {post : List Nat}
    {vertexBound dartBound : Nat} (hr : Rep L c s) (hb : StepBounds L s dartBound)
    (ht : Tables L c S post vertexBound dartBound) :
    ∃ t, ExecB L.limit consStepProgram c t (run consStepProgram c) ∧ t ≤ 200 ∧
      Rep L (run consStepProgram c) (Sol.consStep s) ∧
      Tables L (run consStepProgram c) S post vertexBound dartBound := by
  obtain ⟨t, he, ht'⟩ := consStepProgram_exec_ofRep hr hb
  exact ⟨t, he, ht', consStepProgram_rep hr hb, consStepProgram_tables hr hb ht⟩

end STACS2027.Embed.RAMSolver

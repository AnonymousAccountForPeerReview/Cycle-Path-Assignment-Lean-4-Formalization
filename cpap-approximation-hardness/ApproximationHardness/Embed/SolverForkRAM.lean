module

public import ApproximationHardness.Embed.SolverItemRAM
public import ApproximationHardness.Embed.SolverItemBounds
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases
import Lean.Elab.Tactic.Omega

/-! Node-result stores and the constant-time start of a linked fork. -/

@[expose] public section

set_option maxHeartbeats 1500000

namespace STACS2027.Embed.RAMSolver

open RAM

/-- Store a finished node result while preserving all read-only formula tables. -/
theorem storeNodeResult_rep {L : Layout} {c : Config} {s : SMS} {S : Sol} {post : List Nat}
    {vertexBound dartBound head low v : Nat} (hr : Rep L c s)
    (ht : Tables L c S post vertexBound dartBound) (hv : v < L.width) (hnode : c.reg 20 = v)
    (hh : head < 30 ∧ head ≠ 40) (hl : low < 30 ∧ low ≠ 40) :
    Rep L (run (storeNodeResult head low) c)
      {s with m := {SMem.store s.m v (c.reg head) (c.reg low) with inf := upd s.m.inf v 0}, k := s.k + 1} ∧
    Tables L (run (storeNodeResult head low) c) S post vertexBound dartBound := by
  obtain ⟨hs, hm, hf, hout⟩ := storeNodeResult_raw c head low hh hl hr.bases.1 hr.bases.2.1
  have hbase := hr.bases.2.2.2.2
  let m₁ := upd c.mem (L.cell 6 v) (c.reg head)
  let m₂ := upd m₁ (L.cell 7 v) (c.reg low)
  let m₃ := upd m₂ (L.cell 10 v) 0
  have hm' : (run (storeNodeResult head low) c).mem = m₃ := by
    simpa only [m₃, m₂, m₁, Layout.cell, hnode, hbase 6 (by decide),
      hbase 7 (by decide), hbase 10 (by decide)] using hm
  refine ⟨?_, ?_⟩
  · constructor
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simpa [hr.bases.1] using hs 0 (by decide)
      · simpa [hr.bases.2.1] using hs 1 (by decide)
      · simpa [hr.bases.2.2.1] using hs 2 (by decide)
      · simpa [hr.bases.2.2.2.1] using hs 3 (by decide)
      · intro j hj; exact (hf _ (by omega)).trans (hbase j hj)
    · intro j hj i hi
      rw [hm']
      dsimp only [m₃, m₂, m₁]
      simp only [update_cell L _ j 10 i v _ hi hv, update_cell L _ j 7 i v _ hi hv,
        update_cell L _ j 6 i v _ hi hv]
      interval_cases j
      · simp [SMem.store, memField, upd, hr.arrays 0 (by decide) i hi]
      · simp [SMem.store, memField, upd, hr.arrays 1 (by decide) i hi]
      · simp [SMem.store, memField, upd, hr.arrays 2 (by decide) i hi]
      · simp [SMem.store, memField, upd, hr.arrays 3 (by decide) i hi]
      · simp [SMem.store, memField, upd, hr.arrays 4 (by decide) i hi]
      · simp [SMem.store, memField, upd, hr.arrays 5 (by decide) i hi]
      · simp [SMem.store, memField, upd, hr.arrays 6 (by decide) i hi]
      · simp [SMem.store, memField, upd, hr.arrays 7 (by decide) i hi]
      · simp [SMem.store, memField, upd, hr.arrays 8 (by decide) i hi]
      · simp [SMem.store, memField, upd, hr.arrays 9 (by decide) i hi]
      · simp [SMem.store, memField, upd, hr.arrays 10 (by decide) i hi]
      · simp [SMem.store, memField, upd, hr.arrays 11 (by decide) i hi]
    · simpa [hr.index] using hs 6 (by decide)
    · simpa [hr.mode] using hs 7 (by decide)
    · simpa [hr.node] using hs 8 (by decide)
    · simpa [hr.group] using hs 9 (by decide)
    · simpa [hr.upperLow] using hs 10 (by decide)
    · simpa [hr.resultLow] using hs 11 (by decide)
    · simpa [hr.upperHead] using hs 12 (by decide)
    · simpa [hr.lowerHead] using hs 13 (by decide)
    · simpa [hr.positiveHead] using hs 14 (by decide)
    · simpa [hr.positiveTail] using hs 15 (by decide)
    · simpa [hr.negativeHead] using hs 16 (by decide)
    · simpa [hr.negativeTail] using hs 17 (by decide)
    · simpa [hr.lowerClassHead] using hs 18 (by decide)
    · simpa [hr.lowerClassTail] using hs 19 (by decide)
  · have h₁ := TableMemEq.update L c.mem 6 v (c.reg head) (by decide) hv
    have h₂ := (TableMemEq.update L m₁ 7 v (c.reg low) (by decide) hv).trans h₁
    have h₃ := (TableMemEq.update L m₂ 10 v 0 (by decide) hv).trans h₂
    apply ht.frame (by simpa using hs 4 (by decide)) (by simpa using hs 5 (by decide))
    rw [hm']
    exact h₃

/-- Storing one result has a fixed instruction count. -/
theorem storeNodeResult_size (head low : Nat) : size (storeNodeResult head low) ≤ 20 := by
  norm_num [storeNodeResult, storeCell, size, seqs]

/-- Actual bounded execution of a finished result store. -/
theorem storeNodeResult_exec {L : Layout} {c : Config} {s : SMS} {head low v : Nat}
    (hr : Rep L c s) (hv : v < L.width) (hnode : c.reg 20 = v)
    (hh : head < 30 ∧ head ≠ 40) (hl : low < 30 ∧ low ≠ 40) :
    ∃ t, ExecB L.limit (storeNodeResult head low) c t (run (storeNodeResult head low) c) ∧ t ≤ 20 := by
  have hbase := hr.bases.2.2.2.2
  have h₆ : c.reg 56 + c.reg 20 < L.limit := by rw [hbase 6 (by decide), hnode]; exact L.cell_lt (by decide) hv
  have h₇ : c.reg 57 + c.reg 20 < L.limit := by rw [hbase 7 (by decide), hnode]; exact L.cell_lt (by decide) hv
  have h₁₀ : c.reg 60 + c.reg 20 < L.limit := by rw [hbase 10 (by decide), hnode]; exact L.cell_lt (by decide) hv
  have ha : AddrOK L.limit (storeNodeResult head low) c := by
    simp [storeNodeResult, storeCell, AddrOK, run, seqs, h₆, h₇, h₁₀]
  have hlp : LoopFree (storeNodeResult head low) := by simp [storeNodeResult, storeCell, LoopFree, seqs]
  exact ⟨_, execB_run _ hlp c ha, Nat.le_trans (cost_le_size _ _) (storeNodeResult_size _ _)⟩

theorem beginForkProgram_rep {L : Layout} {c : Config} {s : SMS} {S : Sol} {post : List Nat}
    {vertexBound dartBound v code : Nat} (hr : Rep L c s)
    (ht : Tables L c S post vertexBound dartBound) (hv : v < vertexBound)
    (hnode : c.reg 20 = v) (hcode : c.reg 31 = code) (hy : c.reg 28 ≠ 0) :
    Rep L (run beginForkProgram c)
      (S.forkStart s s.m v (c.reg 24) (c.reg 25) (c.reg 28) (c.reg 29) code) ∧
    Tables L (run beginForkProgram c) S post vertexBound dartBound := by
  have hvw := hv.trans_le ht.vertices
  obtain ⟨hs, hm, hf, hout⟩ := beginForkProgram_raw c hr.bases.1 hr.bases.2.1
  have hbase := hr.bases.2.2.2.2
  have hm' : (run beginForkProgram c).mem = upd c.mem (L.cell 10 v) code := by
    simpa [hbase 10 (by decide), Layout.cell, hnode, hcode] using hm
  have hgroup : (upd c.mem (c.reg 60 + c.reg 20) (c.reg 31)) (c.reg 65 + c.reg 20) = S.gid v := by
    rw [hbase 10 (by decide), hbase 15 (by decide), hnode]
    change upd c.mem (L.cell 10 v) (c.reg 31) (L.cell 15 v) = _
    rw [update_cell L c.mem 15 10 v v _ hvw hvw]
    simpa using ht.groupIds v hv
  have hgroup' : (upd c.mem (c.reg 60 + v) (c.reg 31)) (c.reg 65 + v) = S.gid v := by
    simpa [hnode] using hgroup
  simp only [hnode] at hs
  refine ⟨?_, ?_⟩
  · simp only [Sol.forkStart, hy, ↓reduceIte]
    constructor
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simpa [hr.bases.1] using hs 0 (by decide)
      · simpa [hr.bases.2.1] using hs 1 (by decide)
      · simpa [hr.bases.2.2.1] using hs 2 (by decide)
      · simpa [hr.bases.2.2.2.1] using hs 3 (by decide)
      · intro j hj; exact (hf _ (by omega)).trans (hbase j hj)
    · intro j hj i hi
      rw [hm', update_cell L c.mem j 10 i v code hi hvw]
      interval_cases j <;> simp [memField, upd, hr.arrays, *]
    · simpa [hr.index] using hs 6 (by decide)
    · simpa using hs 7 (by decide)
    · simpa using hs 8 (by decide)
    · simpa [hgroup'] using hs 9 (by decide)
    · simpa using hs 10 (by decide)
    · simpa using hs 11 (by decide)
    · simpa using hs 12 (by decide)
    · simpa using hs 13 (by decide)
    · simpa using hs 14 (by decide)
    · simpa using hs 15 (by decide)
    · simpa using hs 16 (by decide)
    · simpa using hs 17 (by decide)
    · simpa using hs 18 (by decide)
    · simpa using hs 19 (by decide)
  · apply ht.frame (by simpa using hs 4 (by decide)) (by simpa using hs 5 (by decide))
    rw [hm']
    exact TableMemEq.update L c.mem 10 v code (by decide) hvw

theorem beginForkProgram_exec {L : Layout} {c : Config} {s : SMS} {v : Nat}
    (hr : Rep L c s) (hv : v < L.width) (hnode : c.reg 20 = v) :
    ∃ t, ExecB L.limit beginForkProgram c t (run beginForkProgram c) ∧ t ≤ 100 := by
  have hbase := hr.bases.2.2.2.2
  have hstore : c.reg 60 + c.reg 20 < L.limit := by
    rw [hbase 10 (by decide), hnode]; exact L.cell_lt (by decide) hv
  have hload : c.reg 65 + c.reg 20 < L.limit := by
    rw [hbase 15 (by decide), hnode]; exact L.cell_lt (by decide) hv
  have ha : AddrOK L.limit beginForkProgram c := by
    simp [beginForkProgram, loadCell, storeCell, AddrOK, run, seqs, hstore, hload]
  have hl : LoopFree beginForkProgram := by simp [beginForkProgram, loadCell, storeCell, LoopFree, seqs]
  have hsize : size beginForkProgram ≤ 100 := by norm_num [beginForkProgram, loadCell, storeCell, size, seqs]
  exact ⟨_, execB_run _ hl c ha, (cost_le_size _ _).trans hsize⟩

theorem forkResultProgram_rep {L : Layout} {c : Config} {s : SMS} {S : Sol} {post : List Nat}
    {vertexBound dartBound v code : Nat} (hr : Rep L c s)
    (ht : Tables L c S post vertexBound dartBound) (hv : v < vertexBound)
    (hnode : c.reg 20 = v) (hcode : c.reg 31 = code) :
    Rep L (run forkResultProgram c)
      (S.forkStart s s.m v (c.reg 24) (c.reg 25) (c.reg 28) (c.reg 29) code) ∧
    Tables L (run forkResultProgram c) S post vertexBound dartBound := by
  by_cases hy : c.reg 28 = 0
  · simpa [forkResultProgram, run, hy, Sol.forkStart] using
      storeNodeResult_rep (head := 24) (low := 25) hr ht (hv.trans_le ht.vertices)
        hnode (by decide) (by decide)
  · simpa [forkResultProgram, run, hy] using beginForkProgram_rep hr ht hv hnode hcode hy

theorem forkResultProgram_exec {L : Layout} {c : Config} {s : SMS} {v : Nat}
    (hr : Rep L c s) (hv : v < L.width) (hnode : c.reg 20 = v) :
    ∃ t, ExecB L.limit forkResultProgram c t (run forkResultProgram c) ∧ t ≤ 101 := by
  by_cases hy : c.reg 28 = 0
  · obtain ⟨t, Ht, Hb⟩ := storeNodeResult_exec (head := 24) (low := 25) hr hv hnode (by decide) (by decide)
    exact ⟨t + 1, by simpa [forkResultProgram, run, hy] using ExecB.ifzTrue hy Ht, by omega⟩
  · obtain ⟨t, Ht, Hb⟩ := beginForkProgram_exec hr hv hnode
    exact ⟨t + 1, by simpa [forkResultProgram, run, hy] using ExecB.ifzFalse hy Ht, by omega⟩

end STACS2027.Embed.RAMSolver

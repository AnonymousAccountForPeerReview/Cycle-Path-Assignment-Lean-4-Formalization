module

public import ApproximationHardness.Embed.SolverNodeRefine
public import ApproximationHardness.Embed.SolverNodeBounds
import Lean.Elab.Tactic.Omega

/-! The actual bounded RAM solver dispatcher refines every mathematical transition. -/

@[expose] public section

namespace STACS2027.Embed.RAMSolver

open RAM

/-- Full operational simulation of one actual solver transition in its finite layout. -/
theorem mstepProgram_simulation {L : Layout} {c : Config} {s : SMS} {S : Sol} {post : List Nat}
    {vertices darts : Nat} (hr : Rep L c s) (ht : Tables L c S post vertices darts)
    (hb : StateBounds L s darts) (hk : s.k ≤ post.length) :
    ∃ t, ExecB L.limit mstepProgram c t (run mstepProgram c) ∧ t ≤ 2000 ∧
      Rep L (run mstepProgram c) (S.mstep post s) ∧
      Tables L (run mstepProgram c) S post vertices darts := by
  have hs : Rep L (run mstepProgram c) (S.mstep post s) ∧
      Tables L (run mstepProgram c) S post vertices darts ∧ AddrOK L.limit mstepProgram c := by
    by_cases hm : s.mode = 0
    · let c₁ := c.setReg 21 (c.reg 4 - c.reg 6)
      have hr₁ := hr.temp 21 (c.reg 4 - c.reg 6) (by decide) (by decide)
      have ht₁ := ht.temp 21 (c.reg 4 - c.reg 6) (by decide)
      by_cases heq : s.k = post.length
      · have hget : post[s.k]? = none := by simp [heq]
        have hrun : run mstepProgram c = c₁ := by
          simp [mstepProgram, run, seqs, hr.mode, hm, ht.length, hr.index, heq, c₁]
        have hstep : S.mstep post s = s := by simp [Sol.mstep, hm, hget]
        refine ⟨?_, ?_, ?_⟩
        · rw [hrun, hstep]; exact hr₁
        · rw [hrun]; exact ht₁
        · simp [mstepProgram, AddrOK, run, seqs, hr.mode, hm, ht.length, hr.index, heq]
      · have hlt : s.k < post.length := by omega
        let v := post[s.k]'hlt
        have hget : post[s.k]? = some v := List.getElem?_eq_getElem hlt
        have hv : v < vertices := ht.nodeBound v (List.mem_of_getElem? hget)
        let c₂ := run (loadCell 20 21 6) c₁
        have hr₂ := hr₁.loadTemp 20 21 6 (by decide) (by decide)
        have ht₂ := ht₁.loadTemp 20 21 6 (by decide)
        have hn₂ : c₂.reg 20 = v := by
          have hx : c₂.reg 20 = c₁.mem (c₁.reg 71 + c₁.reg 6) := by simp [c₂, loadCell, run, seqs]
          rw [hr₁.bases.2.2.2.2 21 (by decide), hr₁.index] at hx
          exact hx.trans (ht₁.order s.k hlt)
        obtain ⟨t, he, _, hr', ht'⟩ := nodeStepProgram_simulation hr₂ ht₂ hb.memory hv hn₂
        have ha' := (boundedRun_addr he nodeStepProgram_loopFree).2
        have hdiff : c.reg 4 - c.reg 6 ≠ 0 := by rw [ht.length, hr.index]; omega
        have hrun : run mstepProgram c = run nodeStepProgram c₂ := by
          simp [mstepProgram, run, seqs, hr.mode, hm, hdiff, c₂, c₁]
        have hstep : S.mstep post s = S.nodeStep s v := by simp [Sol.mstep, hm, hget]
        have haLoad : AddrOK L.limit (loadCell 20 21 6) c₁ := by
          have hx : c₁.reg 71 + c₁.reg 6 < L.limit := by
            rw [hr₁.bases.2.2.2.2 21 (by decide), hr₁.index]
            exact L.cell_lt (by decide) (hlt.trans_le ht.orderBound)
          simpa [loadCell, AddrOK, run, seqs] using hx
        refine ⟨?_, ?_, ?_⟩
        · rw [hrun, hstep]; exact hr'
        · rw [hrun]; exact ht'
        · simpa [mstepProgram, AddrOK, run, seqs, hr.mode, hm, hdiff, c₂, c₁] using And.intro haLoad ha'
    · let c₁ := c.setReg 21 (c.reg 7 - c.reg 1)
      have hr₁ := hr.temp 21 (c.reg 7 - c.reg 1) (by decide) (by decide)
      have ht₁ := ht.temp 21 (c.reg 7 - c.reg 1) (by decide)
      by_cases hp : s.mode = 1
      · obtain ⟨t, he, _, hr', ht'⟩ := popStepProgram_simulation hr₁ hb.stepBounds ht₁
        have ha' := (boundedRun_addr he popStepProgram_loopFree).2
        have hrun : run mstepProgram c = run popStepProgram c₁ := by
          simp [mstepProgram, run, seqs, hr.mode, hm, hp, hr.bases.2.1, c₁]
        have hstep : S.mstep post s = S.popStep s := by simp [Sol.mstep, hm, hp]
        refine ⟨?_, ?_, ?_⟩
        · rw [hrun, hstep]; exact hr'
        · rw [hrun]; exact ht'
        · simpa [mstepProgram, AddrOK, run, seqs, hr.mode, hm, hp, hr.bases.2.1, c₁] using ha'
      · obtain ⟨t, he, _, hr', ht'⟩ := consStepProgram_simulation hr₁ hb.stepBounds ht₁
        have ha' := (boundedRun_addr he consStepProgram_loopFree).2
        have hdiff : s.mode - 1 ≠ 0 := by omega
        have hrun : run mstepProgram c = run consStepProgram c₁ := by
          simp [mstepProgram, run, seqs, hr.mode, hm, hr.bases.2.1, hdiff, c₁]
        have hstep : S.mstep post s = Sol.consStep s := by simp [Sol.mstep, hm, hp]
        refine ⟨?_, ?_, ?_⟩
        · rw [hrun, hstep]; exact hr'
        · rw [hrun]; exact ht'
        · simpa [mstepProgram, AddrOK, run, seqs, hr.mode, hm, hr.bases.2.1, hdiff, c₁] using ha'
  obtain ⟨hr', ht', ha⟩ := hs
  exact ⟨_, execB_run _ mstepProgram_loopFree c ha,
    (cost_le_size _ _).trans mstepProgram_size, hr', ht'⟩

end STACS2027.Embed.RAMSolver

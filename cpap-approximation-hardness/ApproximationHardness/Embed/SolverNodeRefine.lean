module

public import ApproximationHardness.Embed.SolverNodeSimple
public import ApproximationHardness.Embed.SolverTwoRAM
import Lean.Elab.Tactic.Omega

/-! Full refinement and bounded execution of the actual node dispatcher. -/

@[expose] public section

namespace STACS2027.Embed.RAMSolver

open RAM

/-- Dispatching on the at-most-two parts table refines the semantic node step. -/
theorem nodeStepProgram_rep_addr {L : Layout} {c : Config} {s : SMS} {S : Sol} {post : List Nat}
    {vertices darts v : Nat} (hr : Rep L c s) (ht : Tables L c S post vertices darts)
    (hb : MemoryBounds s.m L.width darts) (hv : v < vertices) (hnode : c.reg 20 = v) :
    Rep L (run nodeStepProgram c) (S.nodeStep s v) ∧
    Tables L (run nodeStepProgram c) S post vertices darts ∧ AddrOK L.limit nodeStepProgram c := by
  let c₁ := run (loadCell 21 16 20) c
  have hr₁ := hr.loadTemp 21 16 20 (by decide) (by decide)
  have ht₁ := ht.loadTemp 21 16 20 (by decide)
  have hn₁ : c₁.reg 20 = v := (loadCell_frame c 21 16 20 20 (by decide)).trans hnode
  have hcount : c₁.reg 21 = (S.P.parts v).length := by
    have hx := ht.counts v hv
    simpa [c₁, loadCell, run, seqs, hnode, hr.bases.2.2.2.2 16 (by decide), Layout.cell] using hx
  have haLoad : AddrOK L.limit (loadCell 21 16 20) c := by
    have hx : c.reg 66 + c.reg 20 < L.limit := by
      rw [hr.bases.2.2.2.2 16 (by decide), hnode]
      exact L.cell_lt (by decide) (hv.trans_le ht.vertices)
    simpa [loadCell, AddrOK, run, seqs] using hx
  cases hparts : S.P.parts v with
  | nil =>
    obtain ⟨hsr, hst⟩ := leafNodeProgram_rep hr₁ ht₁ hv hn₁
    obtain ⟨t, he, _⟩ := leafNodeProgram_exec hr₁ ht₁ hv hn₁
    have hlp : LoopFree leafNodeProgram := by
      simp [leafNodeProgram, storeNodeResult, storeCell, LoopFree, seqs]
    have hsa := (boundedRun_addr he hlp).2
    have hnrun : run nodeStepProgram c = run leafNodeProgram c₁ := by
      simp [nodeStepProgram, run, seqs, c₁, hcount, hparts]
    refine ⟨?_, ?_, ?_⟩
    · rw [hnrun]; simpa only [Sol.nodeStep, hparts] using hsr
    · rw [hnrun]; exact hst
    · simpa [nodeStepProgram, AddrOK, run, seqs, c₁, hcount, hparts] using And.intro haLoad hsa
  | cons p ps =>
    let c₂ := c₁.setReg 21 (c₁.reg 21 - c₁.reg 1)
    have hr₂ := hr₁.temp 21 (c₁.reg 21 - c₁.reg 1) (by decide) (by decide)
    have ht₂ := ht₁.temp 21 (c₁.reg 21 - c₁.reg 1) (by decide)
    have hn₂ : c₂.reg 20 = v := by simpa [c₂] using hn₁
    cases ps with
    | nil =>
      obtain ⟨hsr, hst⟩ := singleNodeProgram_rep hr₂ ht₂ hv hn₂ p hparts
      obtain ⟨t, he, _⟩ := singleNodeProgram_exec hr₂ ht₂ hv hn₂ p hparts
      have hlp : LoopFree singleNodeProgram := by
        simp [singleNodeProgram, itemResultInto_loopFree, storeNodeResult, storeCell, loadCell, LoopFree, seqs]
      have hsa := (boundedRun_addr he hlp).2
      have hnrun : run nodeStepProgram c = run singleNodeProgram c₂ := by
        simp [nodeStepProgram, run, seqs, c₂, c₁, hcount, hparts, hr₁.bases.2.1]
      refine ⟨?_, ?_, ?_⟩
      · rw [hnrun]; simpa only [Sol.nodeStep, hparts] using hsr
      · rw [hnrun]; exact hst
      · simpa [nodeStepProgram, AddrOK, run, seqs, c₂, c₁, hcount, hparts, hr₁.bases.2.1] using And.intro haLoad hsa
    | cons q qs =>
      have hlen := ht.partsBound v hv
      rw [hparts] at hlen
      have hnil : qs = [] := by
        apply List.length_eq_zero_iff.mp
        simp only [List.length_cons] at hlen
        omega
      subst qs
      obtain ⟨hsr, hst, hsa⟩ := twoNodeProgram_rep_addr hr₂ ht₂ hb hv hn₂ p q hparts
      have hnrun : run nodeStepProgram c = run twoNodeProgram c₂ := by
        simp [nodeStepProgram, run, seqs, c₂, c₁, hcount, hparts, hr₁.bases.2.1]
      refine ⟨?_, ?_, ?_⟩
      · rw [hnrun]; simpa only [Sol.nodeStep, hparts] using hsr
      · rw [hnrun]; exact hst
      · simpa [nodeStepProgram, AddrOK, run, seqs, c₂, c₁, hcount, hparts, hr₁.bases.2.1] using And.intro haLoad hsa

/-- Each actual node step has a bounded run of at most one fixed instruction constant. -/
theorem nodeStepProgram_simulation {L : Layout} {c : Config} {s : SMS} {S : Sol} {post : List Nat}
    {vertices darts v : Nat} (hr : Rep L c s) (ht : Tables L c S post vertices darts)
    (hb : MemoryBounds s.m L.width darts) (hv : v < vertices) (hnode : c.reg 20 = v) :
    ∃ t, ExecB L.limit nodeStepProgram c t (run nodeStepProgram c) ∧ t ≤ 1000 ∧
      Rep L (run nodeStepProgram c) (S.nodeStep s v) ∧
      Tables L (run nodeStepProgram c) S post vertices darts := by
  obtain ⟨hr', ht', ha⟩ := nodeStepProgram_rep_addr hr ht hb hv hnode
  exact ⟨_, execB_run _ nodeStepProgram_loopFree c ha,
    (cost_le_size _ _).trans nodeStepProgram_size, hr', ht'⟩

end STACS2027.Embed.RAMSolver

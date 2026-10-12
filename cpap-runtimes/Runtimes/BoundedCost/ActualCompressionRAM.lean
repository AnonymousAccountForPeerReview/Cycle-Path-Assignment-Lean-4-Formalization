module

public import Runtimes.BoundedCost.CompressionStart
public import Runtimes.BoundedCost.CompilerCostBridge
import Mathlib.Tactic

/-! The concrete compression program partitions the prefix, executes both
exhaustive ternary scans, and returns the exact semantic compression answer. -/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 STACS2027.RAM Complexity.SAT

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

def compressionCompilerCost (F : Stmt) (constant clauses budget : ℕ) : ℕ :=
  84 * clauses + 7 + compilerOuterTime constant (wregs (Flow.hornSeparator F)).length
    clauses budget (min budget clauses + 1)

theorem compressionFinish_spec {F : Stmt} {S budget depth processed : ℕ}
    {layout : CompilerLayout} {original special : CNF} {τ : Assignment}
    {rows : List (Bool × Clause)} {oldOutput digits : List ℕ} (answer : Option Assignment) :
    HTB S (.ifz (callerRegister nodeSuccess) (.const (callerRegister Compiler.alive) 0) .skip)
      (OuterRep F layout (2 * original.length + 1) original τ rows special budget depth
        processed oldOutput answer digits)
      (Compiler.PrefixRep F layout original budget depth oldOutput processed answer) 2 := by
  intro c ⟨hb, ha⟩
  obtain ⟨hg, hc, hr, hz, ho, hbase, hspecial, hob, hol, hk, hd, hlen, hcount, hp, halive⟩ := hb
  cases answer with
  | none =>
    refine ⟨c.setReg (callerRegister Compiler.alive) 0, 2, .ifzTrue ha (.const _ _ _), ?_, le_rfl⟩
    refine ⟨⟨?_, hc, ?_, ho⟩, by simp [Compiler.PrefixAnswerRep]⟩
    · exact (Compiler.globals_reg_indep layout (2 * original.length + 1) original.length budget depth
        [callerRegister Compiler.alive] (by
          intro r hr
          simp only [List.mem_singleton]
          intro he
          have he' := callerRegister_injective he
          subst r
          simp [Compiler.globalRegisters, Compiler.alive] at hr)).setReg (by simp) 0 hg
    · exact (Compiler.stageZero_reg_indep (Flow.hornSeparator F) [callerRegister Compiler.alive]
        (by intro r hr; have he := List.mem_singleton.mp hr; subst r; decide)).setReg (by simp) 0 hz
  | some σ =>
    exact ⟨c, 2, .ifzFalse (by rw [ha.1]; decide) (.skip c),
      ⟨⟨hg, hc, hz, ho⟩, halive, hp, ha.2⟩, le_rfl⟩

theorem actualCompressionRAM_spec {F : Stmt} {T : ℕ → ℕ}
    (hF : Flow.MinCostFlowSolver F T) (hAL : Flow.AlmostLinear T) :
    ∃ C : ℕ, ∀ {S budget index : ℕ} {f : CNF} {τ : Assignment} {oldOutput : List ℕ},
      SolverDomain f → (compilerLayout C f.length budget).space ≤ S →
      budget < f.length → index < f.length →
      unsatisfiedCount τ (f.take index) ≤ budget →
      budget < unsatisfiedCount τ (f.take (index + 1)) →
      HTB S (Compiler.compression F)
        (Compiler.CompressionReady F (compilerLayout C f.length budget) f budget
          (min budget f.length + 1) oldOutput index τ)
        (Compiler.PrefixRep F (compilerLayout C f.length budget) f budget
          (min budget f.length + 1) oldOutput (index + 1)
          (encodedCompressionSearch (citedFlowLeastCutOperation hF hAL τ) τ
            (min budget f.length + 1) (compressionBase τ (f.take index))
            (compressionSpecial τ (f.take index) (f.getD index [])) budget))
        (compressionCompilerCost F C f.length budget) := by
  obtain ⟨C, houter⟩ := completeOuterRAM_spec hF hAL
  refine ⟨C, ?_⟩
  intro S budget index f τ oldOutput hf hspace hbudget hi hold hnew
  let layout := compilerLayout C f.length budget
  let depth := min budget f.length + 1
  let rows := setupOccurrenceMask τ f (index + 1)
  let special := compressionSpecial τ (f.take index) (f.getD index [])
  have hprefix : f.take (index + 1) = f.take index ++ [f.getD index []] :=
    Compiler.take_next f index hi
  have htrigger : budget < unsatisfiedCount τ (f.take index ++ [f.getD index []]) := by
    rwa [hprefix] at hnew
  have hsp := setupSpecialPrefix_compression τ f (f.take index) (f.getD index [])
    (index + 1) budget (solverDomain_clauses2 hf) (by omega) hprefix hold htrigger
  have hspecialBound : special.length ≤ depth := by
    rw [hsp.1, List.length_map] at hsp
    dsimp [special, depth]
    rw [Nat.min_eq_left (by omega)]
    exact hsp.2
  have hgeo := outerGeometry_compilerLayout C f.length budget S special.length hspace hspecialBound
  have hlen : rows.length = f.length := setupOccurrenceMask_length _ _ _
  have hmap : rows.map Prod.snd = f := setupOccurrenceMask_clauses _ _ _
  have hrows : ∀ row ∈ rows, row.2.length = 2 ∧ ∀ l ∈ row.2, l.var < 2 * f.length + 1 := by
    intro row hr
    apply hf
    rw [← hmap]
    exact List.mem_map.mpr ⟨row, hr, rfl⟩
  have hs : TwoSat.IsTwoCNF (2 * f.length + 1) special :=
    compressionSpecial_twoCNF (by
      rw [← hprefix]
      exact twoCNF_sublist hf (List.take_sublist _ _)) τ
  have hbase : activeOccurrences rows = compressionBase τ (f.take index) :=
    setupOccurrenceMask_compressionBase τ f (f.take index) (f.getD index [])
      (index + 1) budget (by omega) hprefix hold htrigger
  have href : evalCNF τ (activeOccurrences rows) = true := by
    rw [hbase]
    exact compressionBase_satisfied τ _
  have hstart := compressionStart_spec (F := F) (oldOutput := oldOutput) hf hspace hi hold hnew
  have hscan := houter (budget := budget) (processed := index + 1) (oldOutput := oldOutput)
    (by omega : 3 ≤ 2 * f.length + 1) (by omega) rfl hgeo hlen hmap
    hrows hs href
  have hfinish := compressionFinish_spec (F := F) (S := S) (layout := layout)
    (budget := budget) (depth := depth) (processed := index + 1) (original := f)
    (special := special) (τ := τ) (rows := rows) (oldOutput := oldOutput)
    (digits := Poly.cfg 3 special.length 0)
    (encodedCompressionSearch (citedFlowLeastCutOperation hF hAL τ) τ depth
      (activeOccurrences rows) special budget)
  have hscan' := hscan.mono (fun _ h => h) (fun _ h => h.1) le_rfl
  have hfull := (hstart.seq (hscan'.seq hfinish).assoc).assoc
  refine hfull.mono (fun _ h => h) ?_ ?_
  · intro c hc
    simpa only [hbase] using hc
  · have hcost := (outerCompleteCost_le F C f.length budget special.length).trans
      (compilerOuterTime_mono_special C (wregs (Flow.hornSeparator F)).length f.length budget hspecialBound)
    unfold compressionCompilerCost
    dsimp only [depth] at hcost
    omega

end STACS2027.Runtimes.BoundedCost

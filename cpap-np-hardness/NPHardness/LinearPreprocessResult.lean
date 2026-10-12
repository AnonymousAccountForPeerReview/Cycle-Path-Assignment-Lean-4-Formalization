module

public import NPHardness.LinearPreprocessInit

/-! The semantic result of the now initialized bounded-adjacency queue kernel.
The separate pipeline module accounts for normalization, initialization,
extraction and padding as well as the kernel itself. -/

@[expose] public section
namespace STACS2027.LinearPreprocessResult
open Complexity.SAT
open LinearPreprocessUnits LinearPreprocessInit

def ResultSpec (f : CNF) : LinearPreprocessUnits.State → Prop
  | .running _ _ => False
  | .rejected => ¬ Satisfiable f
  | .done mem =>
      let g := contents (normalizeClauses f).length mem
      (Satisfiable g ↔ Satisfiable f) ∧ BoundedOccurrence g ∧
      ClauseVariablesDistinct g ∧ FormulaDeletion g f ∧
      g.length ≤ f.length ∧ variableBound g ≤ variableBound f

theorem result_correct {f : CNF} (hf : BoundedOccurrence f)
    {result : LinearPreprocessUnits.State}
    (h : TerminalSpec (normalizeClauses f).length (normalizeClauses f) result) :
    ResultSpec f result := by
  have hsat : Satisfiable (normalizeClauses f) ↔ Satisfiable f := by
    simp only [Satisfiable,normalizeClauses_eval]
  cases result with
  | running mem queue => exact h
  | rejected => exact fun hf => h (hsat.mpr hf)
  | done mem =>
    have hd := h.2.1.trans (normalizeClauses_deletion f)
    have hthree := hd.threeCNF hf.isThreeCNF
    refine ⟨h.1.trans hsat,⟨?_,?_,?_⟩,
      h.2.1.distinct (normalizeClauses_distinct f),hd,hd.2.1,hd.variableBound_le⟩
    · intro c hc
      have hlo := h.2.2 c hc
      have hhi := hthree c hc
      omega
    · intro v
      exact Nat.le_trans (hd.occurrences_le v true) (hf.2.1 v)
    · intro v
      exact Nat.le_trans (hd.occurrences_le v false) (hf.2.2 v)

/-- Actual queue execution on the concrete initialized tables, with no
assumed incidence certificate.  The tables are produced by
`LinearPreprocessInit.executes_initialize`. -/
theorem normalized_kernel_correct {f : CNF} (hf : BoundedOccurrence f) :
    ∃ t result, t ≤ 5*(normalizeClauses f).length+1 ∧
      LinearPreprocessUnits.Executes (initialAdj (normalizeClauses f)) t
        (.running (initialMemory (normalizeClauses f)) (List.range (normalizeClauses f).length)) result ∧
      ResultSpec f result := by
  obtain ⟨hv,ha⟩ := normalized_initial_valid hf
  obtain ⟨t,result,ht,hr,hs⟩ := kernel_linear (normalizeClauses f).length
    (initialAdj (normalizeClauses f)) ha (initialMemory (normalizeClauses f)) hv
  rw [contents_initialMemory] at hs
  exact ⟨t,result,ht,hr,result_correct hf hs⟩

end STACS2027.LinearPreprocessResult

module

public import NPHardness.SourceWordMachine

/-! Actual terminating construction of occurrence-ring graphs with internally
computed endpoint choices. The supplied input header is its clause count;
neither a variable-bound traversal nor a sign-table traversal is uncharged. -/

@[expose] public section
namespace STACS2027.SourceWord
open Complexity.SAT WordPipeline PlanarSource

def linearCoefficient (k : Nat) : Nat := WordConstructor.linearCoefficient k+13

/-- A fully charged run on the ring family. The assumptions describe the
input formula; no orientation function or certificate is a machine input. -/
theorem linear_construction {k : Nat} (hk : 5≤k) (f : CNF) (next : Nat→Nat)
    (hn : ∀i,i<f.flatten.length→next i<f.flatten.length)
    (hf : BoundedOccurrence (Formula.ringFormula f next (Formula.sourceSigns f)))
    (hd : ClauseVariablesDistinct (Formula.ringFormula f next (Formula.sourceSigns f))) :
    let input := Formula.ringFormula f next (Formula.sourceSigns f)
    ∃t, Runs (step k input.length input) t (initial input)
        (.graph f.flatten.length (Formula.sourceSigns f)
          ⟨.done,historyMemory input.flatten,
            (orientedFormulaGraph (sourceEndpointChoices (Formula.sourceSigns f)) k input).reverse⟩) ∧
      t≤(f.flatten.length+1)*linearCoefficient k ∧
      (Satisfiable input ↔ HasAssignment
        (orientedFormulaGraph (sourceEndpointChoices (Formula.sourceSigns f)) k input).reverse k input.length) := by
  dsimp only
  let input := Formula.ringFormula f next (Formula.sourceSigns f)
  let n := f.flatten.length
  have hv : variableBound input=n := Formula.ringFormula_variableBound_of_bounded f next _ hn
  obtain ⟨t,ht,hr⟩ := extracts_sourceSigns k f next hn
  change t≤input.flatten.length+2*input.length+f.length+n+3 at ht
  have hc : ∀c∈input,c.length≤3 := by
    intro c hc
    rcases hf.1 c hc with h | h <;> omega
  have hg := graph_runs (budget := input.length)
    (WordConstructor.executes_graph (sourceEndpointChoices (Formula.sourceSigns f)) k input hc)
  rw [hv] at hg
  have hcTime := WordConstructor.transitionCount_linear hk hf n
    (fun c hc l hl => by rw [←hv]; exact literal_lt_variableBound hc hl)
  change WordConstructor.transitionCount k n input≤(n+1)*WordConstructor.linearCoefficient k at hcTime
  have hm : input.length≤3*n := by
    have hh := hf.clause_count_variableBound
    rw [hv] at hh
    change 2*input.length≤3*n at hh
    omega
  have hlf : f.length≤input.length := by
    dsimp only [input]
    rw [Formula.ringFormula_length]
    omega
  have hl : input.flatten.length=3*n := Formula.ringFormula_flatten_length f next _
  have ht' : t≤(n+1)*13 := by rw [hl] at ht; omega
  refine ⟨t+WordConstructor.transitionCount k n input,hr.trans hg,?_,?_⟩
  · change t+WordConstructor.transitionCount k n input≤(n+1)*(WordConstructor.linearCoefficient k+13)
    rw [Nat.mul_add]
    omega
  · exact WordConstructor.graph_correct (sourceEndpointChoices (Formula.sourceSigns f)) hk hf hd

end STACS2027.SourceWord

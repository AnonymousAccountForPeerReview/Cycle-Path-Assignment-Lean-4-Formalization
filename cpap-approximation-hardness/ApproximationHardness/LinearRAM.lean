module

public import ApproximationHardness.RAM.Correct
public import ApproximationHardness.LReduction
public import NPHardness.GlobalCompleteness
import Lean.Elab.Tactic.Omega

/-!
# Theorem 8 in `O(n)` time and space on a unit-cost RAM

The manuscript's Theorem 8: for every fixed `k ≥ 5`, an `n`-variable Definition 7
formula `φ` with `m` clauses is transformed in `O(n)` time into an instance
`(G, k)` of CPAP such that `φ` is satisfiable iff `G` has an assignment of cost at
most `m`. Here the transformation is a program of the unit-cost RAM of
`ApproximationHardness/RAM/Model.lean` (ANONYMIZED–ANONYMIZED: constants, `+`, truncated `-`,
indirect load and store, output; one step per instruction and per test), and
the time and space bounds are proved: at most `C_k · (n + 1)` steps, and only the memory
addresses below `C_k · (n + 1)` read or written (`RAM.ComputesIn`, input included), on every
Definition 7 formula, `n = variableBound f`.
-/

@[expose] public section

namespace STACS2027

open Complexity.SAT

/-- **Theorem 8, with its `O(n)` running time and space on a unit-cost RAM.** For every `k ≥ 5`
there are a RAM program and a constant `C` such that, on the input `ramInput f` (the clause count,
then per clause its length and `var, sign` per literal) of every Definition 7 formula `f`, the
program halts within `C · (n + 1)` steps, `n = variableBound f`, accessing only the memory addresses
below `C · (n + 1)`, and outputs the budget `|f|` followed by the endpoints of a list of pairs `es`
whose normalized edges are the Theorem 8 graph `formulaGraph k f`; and `f` is satisfiable iff that
graph has an assignment of cost at most `|f|`. -/
theorem gadget_reduction_linear_ram {k : Nat} (hk : 5 ≤ k) :
    ∃ (prog : RAM.Stmt) (C : Nat), ∀ f, LeOneLeTwoCNF f →
      ∃ (es : List (Nat × Nat)) (t : Nat),
        RAM.ComputesIn prog (RAM.ramInput f) (f.length :: RAM.edgeWord es) t (C * (variableBound f + 1)) ∧
        t ≤ C * (variableBound f + 1) ∧ formulaGraph k f = es.map (fun e => edge e.1 e.2) ∧
        (Satisfiable f ↔ HasAssignment (formulaGraph k f) k f.length) := by
  refine ⟨RAM.program k, RAM.ramLinConst k, ?_⟩
  intro f hf
  obtain ⟨t, hc, ht⟩ := RAM.ram_linear_time k f hf.1
  exact ⟨RAM.formulaPairs k f, t, hc, ht, RAM.formulaGraph_eq_pairs k f,
    formulaGraph_sat_iff_assignment hk hf.1 hf.2⟩

end STACS2027

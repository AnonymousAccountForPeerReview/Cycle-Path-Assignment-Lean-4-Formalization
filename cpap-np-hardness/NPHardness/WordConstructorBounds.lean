module

public import NPHardness.WordConstructor
public import NPHardness.AssignmentRelabel

/-!
Linear transition bound for the explicit word constructor, with SAT correctness
on the clause-distinct domain of the existing raw-graph correctness theorem.
The transition bound itself does not need distinctness. In particular, this
does not assert a runtime bound for `cleanFormula` or `globalReductionGraph`.
-/

@[expose] public section
namespace STACS2027.WordConstructor
open Complexity.SAT

theorem clauseTime_bound {k : Nat} (hk : 5 ≤ k) (m : CounterMemory) (f : CNF) :
    clauseTime k m f ≤ f.flatten.length + f.length*(10*k+3)+1 := by
  induction f generalizing m with
  | nil => simp [clauseTime]
  | cons c f ih =>
    have he := clauseGraph_edge_bound hk (allocateLiterals m c).1
    have ht := ih (allocateLiterals m c).2
    simp only [clauseTime, List.flatten_cons, List.length_append, List.length_cons,
      Nat.add_mul, Nat.one_mul]
    omega

def linearCoefficient (k : Nat) : Nat := (2*k+1)+3+3*(10*k+3)+2

theorem linearCoefficient_eq (k : Nat) : linearCoefficient k = 32*k+15 := by
  unfold linearCoefficient
  omega

theorem transitionCount_linear {k : Nat} (hk : 5 ≤ k) {f : CNF}
    (hf : BoundedOccurrence f) (n : Nat) (hb : ∀ c ∈ f, ∀ l ∈ c, l.var < n) :
    transitionCount k n f ≤ (n+1)*linearCoefficient k := by
  have hl := hf.literal_count n hb
  have hc := hf.clause_count n hb
  have hm : f.length ≤ 3*n := by omega
  have ht := clauseTime_bound hk (historyMemory []) f
  have hm' := Nat.mul_le_mul_right (10*k+3) hm
  have hv := variableGraph_edge_count k hk
  have hv' : (variableGraph k).length+2 = 2*k+1 := by omega
  unfold transitionCount
  rw [hv']
  have hbase : n*(2*k+1)+1+clauseTime k (historyMemory []) f ≤
      n*(2*k+1) + 3*n + (3*n)*(10*k+3) + 2 := by omega
  apply Nat.le_trans hbase
  simp only [linearCoefficient, Nat.mul_add, Nat.add_mul, Nat.one_mul, Nat.mul_assoc,
    Nat.mul_comm, Nat.mul_left_comm]
  omega

theorem graph_correct (flips : EndpointChoices) {k : Nat} (hk : 5 ≤ k) {f : CNF}
    (hf : BoundedOccurrence f) (hd : ClauseVariablesDistinct f) :
    Satisfiable f ↔ HasAssignment (orientedFormulaGraph flips k f).reverse k f.length :=
  (orientedFormulaGraph_sat_iff_assignment flips hk hf hd).trans
    (hasAssignment_graph_perm (List.reverse_perm _) k f.length).symm

end STACS2027.WordConstructor

module

public import ApproximationHardness.Registered.Semantics
import Lean.Elab.Tactic.Omega

/-!
# The records of the Theorem 8 graph

`formulaRecords k f` lists one record `[x u, x v]` per edge of `formulaGraph k f`,
with the endpoints in the order of the gadget's edge list (before normalization);
`formulaRecords_output` shows that these records, and their reversal, write the
graph `formulaGraph k f` (resp. its reversal) with budget `0`.
-/

@[expose] public section

namespace STACS2027.Registered

open Complexity
open Complexity.SAT

/-- The record of the pair `(u, v)`: two positive literals. -/
def pairRecord (u v : Nat) : Clause := [⟨u, true⟩, ⟨v, true⟩]

/-- The records of the edges of `g` relabelled by `t`. -/
def rawRecords (t : Nat → Nat) (g : Graph) : CNF := g.map fun e => pairRecord (t e.1) (t e.2)

theorem pairRecord_output (u v : Nat) : GraphOutput [pairRecord u v] [edge u v] 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro c hc
    simp only [List.mem_singleton] at hc
    subst hc
    right
    simp [pairRecord]
  · simp [instructionGraph, recordEdge, pairRecord]
  · simp [instructionBudget, pairRecord]

theorem rawRecords_output (t : Nat → Nat) (g : Graph) : GraphOutput (rawRecords t g) (mapGraph t g) 0 := by
  induction g with
  | nil => exact GraphOutput.nil
  | cons e g ih =>
    have h := (pairRecord_output (t e.1) (t e.2)).append ih
    simpa [rawRecords, mapGraph, mapEdge] using h

theorem GraphOutput.reverse {f : CNF} {g : Graph} {b : Nat} (h : GraphOutput f g b) :
    GraphOutput f.reverse g.reverse b := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun c hc => h1 c (List.mem_reverse.mp hc), ?_, ?_⟩
  · simp only [instructionGraph, List.filterMap_reverse] at h2 ⊢
    rw [h2]
  · simp only [instructionBudget, List.countP_reverse] at h3 ⊢
    exact h3

theorem GraphOutput.mapIdx_flatten {α : Type} (L : List α) (F : Nat → α → CNF) (G : Nat → α → Graph)
    (h : ∀ i a, GraphOutput (F i a) (G i a) 0) :
    GraphOutput (L.mapIdx F).flatten (L.mapIdx G).flatten 0 := by
  induction L generalizing F G with
  | nil => exact GraphOutput.nil
  | cons a L ih =>
    simp only [List.mapIdx_cons, List.flatten_cons]
    exact (h 0 a).append (ih (fun i => F (i + 1)) (fun i => G (i + 1)) (fun i a => h (i + 1) a))

/-- The records of the variable gadgets `v₀, …, v₀ + t - 1`. -/
def varRecords (k v₀ t : Nat) : CNF :=
  (List.range' v₀ t).flatMap fun v => rawRecords (blockVertex (gadgetWidth k) v) (variableGraph k)

/-- The records of the gadget of the clause `c` at index `j`, after the literals `past`. -/
def clauseRecords (k n j : Nat) (past : List Literal) (c : Clause) : CNF :=
  rawRecords (clauseVertex (gadgetWidth k) n j (placeLiterals past c)) (clauseGraph k (placeLiterals past c))

/-- The records of the clauses of `f`, the first at index `j`, after the literals `past`. -/
def clauseRecordsFrom (k n : Nat) : Nat → List Literal → CNF → CNF
  | _, _, [] => []
  | j, past, c :: f => clauseRecords k n j past c ++ clauseRecordsFrom k n (j + 1) (past ++ c) f

theorem clauseRecordsFrom_eq (k n : Nat) (f : CNF) : ∀ (j : Nat) (past : List Literal),
    clauseRecordsFrom k n j past f =
      ((placeFormula past f).mapIdx fun i c => rawRecords (clauseVertex (gadgetWidth k) n (j + i) c)
        (clauseGraph k c)).flatten := by
  induction f with
  | nil => intro j past; rfl
  | cons c f ih =>
    intro j past
    simp only [clauseRecordsFrom, placeFormula, List.mapIdx_cons, List.flatten_cons, Nat.add_zero,
      clauseRecords]
    rw [ih (j + 1) (past ++ c)]
    have hfun : (fun i c' => rawRecords (clauseVertex (gadgetWidth k) n (j + 1 + i) c') (clauseGraph k c')) =
        (fun i c' => rawRecords (clauseVertex (gadgetWidth k) n (j + (i + 1)) c') (clauseGraph k c')) := by
      funext i c'
      rw [Nat.add_assoc, Nat.add_comm 1 i]
    rw [hfun]

/-- The records of the Theorem 8 graph, in the order of its edge list. -/
def formulaRecords (k : Nat) (f : CNF) : CNF :=
  varRecords k 0 (variableBound f) ++ clauseRecordsFrom k (variableBound f) 0 [] f

theorem formulaRecords_output (k : Nat) (f : CNF) : GraphOutput (formulaRecords k f) (formulaGraph k f) 0 := by
  unfold formulaRecords formulaGraph
  rw [clauseRecordsFrom_eq, varRecords, ← List.range_eq_range']
  have h1 := GraphOutput.flatMap (List.range (variableBound f))
    (fun v => rawRecords (blockVertex (gadgetWidth k) v) (variableGraph k)) (placedVariableGraph k)
    (fun _ => 0) (fun v _ => rawRecords_output _ _)
  have h2 := GraphOutput.mapIdx_flatten (placeFormula [] f)
    (fun i c => rawRecords (clauseVertex (gadgetWidth k) (variableBound f) (0 + i) c) (clauseGraph k c))
    (fun j c => placedClauseGraph k (variableBound f) j c)
    (fun i c => by simpa [placedClauseGraph] using rawRecords_output (clauseVertex (gadgetWidth k)
      (variableBound f) i c) (clauseGraph k c))
  have h := h1.append h2
  simpa using h

end STACS2027.Registered

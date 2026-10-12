module

public import NPHardness.GridWheelProgram
public import NPHardness.RegisteredFoundation

/-! A copy template for the grid emitter, and invariance of the occurrence bounds
and of satisfiability under permutation of the clauses. -/

@[expose] public section
namespace STACS2027
open Complexity Complexity.SAT Complexity.StackTableauEmitter

def gridCopyTemplate {m n : Nat} (root : ClauseProgram m) (ls : List (LiteralExpr n))
    (C slot : NumExpr n) : ClauseProgram n :=
  .clause (ls.zipIdx.map fun p =>
    ⟨.add (.mul p.1.index (.mul (.const 6) (emitterSlotsExpr root C)))
      (.add (.mul slot (.const 6)) (.const (2*p.2 + if p.1.positive then 0 else 1))),false⟩)

theorem gridCopyTemplate_emit {m n : Nat} (root : ClauseProgram m) (ls : List (LiteralExpr n))
    (C slot : NumExpr n) (input : SAT.Word) (env : Env n) :
    (gridCopyTemplate root ls C slot).emit input env =
      [sourceCopies (gridCopyClause (emitterSlots root (C.eval env)) (slot.eval env)
        (ls.map (fun l => l.eval env)))] := by
  simp only [gridCopyTemplate,ClauseProgram.emit,gridCopyClause,sourceCopies,List.zipIdx_map,
    List.map_map,LiteralExpr.eval,NumExpr.eval,emitterSlotsExpr_eval,gridCopyIndex,Function.comp_def,
    Prod.map, id_eq]

theorem boundedOccurrence_perm {f g : CNF} (hp : f.Perm g) :
    BoundedOccurrence f ↔ BoundedOccurrence g := by
  have ho (v : Nat) (b : Bool) : occurrences f v b = occurrences g v b := by
    rw [occurrences_eq_count,occurrences_eq_count]
    exact hp.flatten.count_eq _
  have hc : (∀ c ∈ f, c.length = 2 ∨ c.length = 3) ↔ (∀ c ∈ g, c.length = 2 ∨ c.length = 3) := by
    constructor <;> intro h c hc
    · exact h c (hp.mem_iff.mpr hc)
    · exact h c (hp.mem_iff.mp hc)
  simp only [BoundedOccurrence,hc,ho]

theorem satisfiable_perm {f g : CNF} (hp : f.Perm g) : Satisfiable f ↔ Satisfiable g := by
  have he (a : Assignment) : evalCNF a f = evalCNF a g := hp.all_eq
  simp only [Satisfiable,he]

end STACS2027

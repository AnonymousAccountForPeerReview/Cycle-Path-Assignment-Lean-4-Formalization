module
public import NPHardness.PlanarSourceGraphProgram
public import NPHardness.PlanarSourcePackedReduction

/-! The complete target graph constructor is closed emitter syntax, including
its endpoint choices and local successor tests. Its polynomial-time theorem
uses the registered two-stage single-tape compiler, with no rotation oracle. -/

@[expose] public section
namespace STACS2027.PlanarSource.Packed
open Complexity Complexity.SAT Complexity.StackTableauEmitter Complexity.Planar.Emit

def graphBody (k : Nat) (P : ClauseProgram 1) : ClauseProgram 3 :=
  gridGraphProgram k (at1 (Ax P)) (.var 0) (at1 (Rx P)) (at1 (Wx P))

def graphSourceProgram (k : Nat) (P : ClauseProgram 1) : ClauseProgram 1 :=
  stage2 P (graphBody k P)

/-- The actual finite graph-and-budget encoding emitted on an arbitrary word. -/
def graphOutput (k : Nat) (P : ClauseProgram 1) (w : SAT.Word) : CNF :=
  (graphSourceProgram k P).emit (word1 P w) (fun _ => (word1 P w).length)

/-- Polynomial time on the registered single-tape model, for each fixed k. -/
theorem graphOutput_polyTime (k : Nat) (P : ClauseProgram 1) :
    PolyTime (fun w => SAT.encode (graphOutput k P w)) :=
  polyTime_two_stages (stage1 P) (graphSourceProgram k P)

/-- The counted dimension-recovery stage executes exactly once at the true
source dimensions, including the empty-formula case. -/
theorem graphOutput_eq (k : Nat) (P : ClauseProgram 1) (w : SAT.Word) :
    graphOutput k P w =
      (Layout.graphProgram ⟨(at1 (Ax P)).lift,(NumExpr.var (0 : Fin 3)).lift,
        (at1 (Rx P)).lift,(at1 (Wx P)).lift,.var 0⟩ k).emit
      (word1 P w)
      (extend (((P.emit w (fun _ => w.length)).length+1)/2)
        (extend (P.emit w (fun _ => w.length)).length
          (extend w.length (fun _ => (word1 P w).length)))) := by
  unfold graphOutput graphSourceProgram
  rw [stage2_emit P _ _ (emit_length_le P w) (word1_length P w),graphBody,gridGraphProgram_emit]
  rfl

end STACS2027.PlanarSource.Packed

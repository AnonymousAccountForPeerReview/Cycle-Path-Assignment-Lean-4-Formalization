module

public import NPHardness.PlanarSourcePackedProgram

/-!
The packed source constructor on actual binary inputs.  It reuses the
registered occurrence-table first stage and its dimension-recovery program.
The resulting total reduction function is polynomial on the registered
single-tape machine model.  Its SAT/planarity identification is established
separately from this computational fact.
-/

@[expose] public section
namespace STACS2027.PlanarSource.Packed
open Complexity Complexity.SAT Complexity.StackTableauEmitter Complexity.Planar.Emit

def gridBody (P : ClauseProgram 1) : ClauseProgram 3 :=
  gridProgram (at1 (Ax P)) (.var 0) (at1 (Rx P)) (at1 (Wx P))

def sourceProgram (P : ClauseProgram 1) : ClauseProgram 1 := stage2 P (gridBody P)

def output (P : ClauseProgram 1) (w : SAT.Word) : CNF :=
  (sourceProgram P).emit (word1 P w) (fun _ => (word1 P w).length)

theorem output_polyTime (P : ClauseProgram 1) :
    PolyTime (fun w => SAT.encode (output P w)) :=
  polyTime_two_stages (stage1 P) (sourceProgram P)

/-- Exact input, loop environment, and half-count passed to the packed body. -/
theorem output_eq (P : ClauseProgram 1) (w : SAT.Word) :
    output P w =
      (Layout.program ⟨(at1 (Ax P)).lift,(NumExpr.var (0 : Fin 3)).lift,
        (at1 (Rx P)).lift,(at1 (Wx P)).lift,.var 0⟩).emit
      (word1 P w)
      (extend (((P.emit w (fun _ => w.length)).length+1)/2)
        (extend (P.emit w (fun _ => w.length)).length
          (extend w.length (fun _ => (word1 P w).length)))) := by
  unfold output sourceProgram
  rw [stage2_emit P _ _ (emit_length_le P w) (word1_length P w), gridBody, gridProgram_emit]
  rfl

end STACS2027.PlanarSource.Packed

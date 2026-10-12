module

public import NPHardness.PlanarSourcePackedOutput
public import NPHardness.PlanarSourceCombRotation
public import NPHardness.PlanarSourceEmptyGrid

/-!
The polynomial emitter and the planar occurrence-ring construction produce
the same concrete CNF.  The comparison uses the exact cyclic successor after
deleting the registered comb spine, including all literal multiplicities.
-/

@[expose] public section
namespace STACS2027.PlanarSource
open Complexity Complexity.SAT Complexity.Planar Comb Grid

theorem Formula.ringFormula_next_congr (f : CNF) (next next' : Nat → Nat)
    (signs : Nat → Bool) (h : ∀ i, i<f.flatten.length → next i=next' i) :
    Formula.ringFormula f next signs = Formula.ringFormula f next' signs := by
  unfold Formula.ringFormula Formula.ringClauses
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [h i (List.mem_range.mp hi)]

/-- The arithmetic successor selected by the compiled program is exactly the
variable rotation of the executable incidence-only planar embedding. -/
theorem Packed.incidenceNext_grid (W m : Nat) (bits : Nat → Nat → Bool×Bool)
    (hm : 1≤m) (i : Fin (gridCNF W m bits).flatten.length) :
    incidenceNext (gridCNF W m bits) i.val =
      Formula.nextIndex (ComputableFormula.formulaData (gridCNF W m bits)
        (ComputableComb.gridIncidenceEmbedding W m bits hm)).rotation i.val := by
  rw [Formula.nextIndex_at,ComputableComb.gridIncidenceEmbedding_formulaData_next]
  rw [ComputableComb.variableAt_eq_vr]
  · rfl
  · simpa only [RotationTable.nM_eq_flatten] using i.isLt

/-- For a nonempty grid, the actual compiled ring formula is the proven planar
ring expansion, rather than merely an equisatisfiable alternative formula. -/
theorem Packed.ringFormula_eq_gridRingOutput (W m : Nat)
    (bits : Nat → Nat → Bool×Bool) (hm : 1≤m) :
    Formula.ringFormula (gridCNF W m bits) (incidenceNext (gridCNF W m bits))
      (Formula.sourceSigns (gridCNF W m bits)) =
        ComputableComb.gridRingOutput W m bits hm := by
  apply Formula.ringFormula_next_congr
  intro i hi
  exact incidenceNext_grid W m bits hm ⟨i,hi⟩

theorem Packed.ringGrid_correct (W m : Nat) (bits : Nat → Nat → Bool×Bool) :
    let f := gridCNF W m bits
    let g := Formula.ringFormula f (incidenceNext f) (Formula.sourceSigns f)
    BoundedOccurrence g ∧ PlanarGraph (incidenceGraph g) ∧
      (Satisfiable g ↔ Satisfiable f) := by
  dsimp only
  cases m with
  | zero =>
    rw [gridCNF_zero,ringFormula_nil]
    exact ⟨empty_source_properties.1,empty_source_properties.2.1,Iff.rfl⟩
  | succ m =>
    rw [ringFormula_eq_gridRingOutput W (m+1) bits (by omega)]
    exact ComputableComb.gridRingOutput_correct W (m+1) bits (by omega)

/-- End-to-end correctness on every binary input. The output is an actual
Definition 7 instance with planar incidence multigraph, and its satisfiability
is precisely that of the input emitter's formula. -/
theorem Packed.output_correct (P : Complexity.StackTableauEmitter.ClauseProgram 1)
    (w : SAT.Word) :
    BoundedOccurrence (Packed.output P w) ∧
      PlanarGraph (incidenceGraph (Packed.output P w)) ∧
      (Satisfiable (Packed.output P w) ↔ Satisfiable (P.emit w (fun _ => w.length))) := by
  have h : BoundedOccurrence (Packed.output P w) ∧
      PlanarGraph (incidenceGraph (Packed.output P w)) ∧
      (Satisfiable (Packed.output P w) ↔ Satisfiable (Emit.gridOut P w)) := by
    rw [Packed.output_ringFormula,Emit.gridOut_eq]
    exact Packed.ringGrid_correct _ _ _
  exact ⟨h.1,h.2.1,h.2.2.trans (Emit.gridOut_sat P w)⟩

end STACS2027.PlanarSource

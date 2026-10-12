module

public import OAI.Computability.UniqueGames.Machines.GraphIterationBoundsLemmas
public import OAI.Computability.UniqueGames.PCP.LoopInitializationLemmas
public import OAI.Computability.UniqueGames.PCP.RawInitialTablesLemmas
public import OAI.Computability.UniqueGames.PCP.TableIteration

/-!
# The gap-amplification map: statement used by the rest of the project

Adapted from the ANONYMIZED mathematics repository (https://github.com/openai/math,
commit adc7f1241b42e322a6451854ab7e4b4c146bf78a, file
`lean/OAI/Computability/UniqueGames/PCP/TableGapReductionLemmas.lean`), Apache-2.0.
Changes: only the part about the 3-CNF gap map is kept (the later stage of the source file is
dropped), the clause gap is stated as an inequality between natural numbers, and the file is
converted to the Lean module system.

For a base expander table `H` with a spectral certificate, `TableIteration.gapMap H` maps
3-CNF formulas to 3-CNF formulas, satisfiable formulas to satisfiable formulas
(`gapMap_completeness`), and unsatisfiable formulas to formulas of which every assignment fails
at least one clause in `walkLength * 40960` (`gapMap_clauseCount`). It is computed in polynomial
time by a multi-stack machine with finite alphabets (`gapMachine`, `gapMachine_finite`).
-/

@[expose] public section

namespace OAI

namespace UniqueGamesTheorem.Foundations.PCP.TableGapReduction

open RoundTables TableIteration SpectralReturn Target

variable (H : BaseTable)
  (certificate : SpectralCertificate (ExpanderTables.graph H) (1 / 100 : ℝ))

include certificate

theorem run_gap (n : Nat) (input : Input) :
    min (2 ^ n * gap input) FinalConstants.cap ≤ gap (TableIteration.run H n input) :=
  AmplificationIteration.run_gap (step H) gap FinalConstants.cap FinalConstants.cap_positive.le
    (RoundTableGap.step_gap H certificate) n input

theorem output_gap (F : Formula) (unsat : ¬ F.Satisfiable) :
    FinalConstants.cap ≤ gap (TableIteration.output H F) := by
  have hu : ¬ Satisfiable (initial F) := fun sat => unsat ((initial_satisfiable_iff F).mp sat)
  exact AmplificationIteration.run_reaches_cap (step H) gap FinalConstants.cap
    FinalConstants.cap_positive.le FinalConstants.cap_le_one (RoundTableGap.step_gap H certificate)
    (size (initial F)) (initial F) (gap_nonnegative (initial F))
    (one_le_size_mul_gap (initial F) hu)

theorem output_count_gap (F : Formula) (unsat : ¬ F.Satisfiable)
    (labeling : Fin (outputTable H F).vertices → GraphTables.Label) :
    (outputTable H F).darts ≤ FinalConstants.walkLength *
      (GraphTables.semantics (outputTable H F)).rejectionCount labeling := by
  have hp := output_darts_positive H F
  let : Nonempty (Fin (outputTable H F).darts) := ⟨⟨0, hp⟩⟩
  have bound := output_gap H certificate F unsat
  change FinalConstants.cap ≤ (GraphTables.semantics (TableIteration.output H F).val).gap at bound
  rw [output_val] at bound
  have count := ((GraphTables.semantics (outputTable H F)).le_gap_iff FinalConstants.cap).mp bound labeling
  simp only [Fintype.card_fin] at count
  have ht : (0 : ℝ) < FinalConstants.walkLength := Nat.cast_pos.mpr FinalConstants.walkLength_positive
  have divided : ((outputTable H F).darts : ℝ) / FinalConstants.walkLength ≤
      ((GraphTables.semantics (outputTable H F)).rejectionCount labeling : ℝ) := by
    simpa only [FinalConstants.cap, one_div_mul_eq_div] using count
  have multiplied := (div_le_iff₀ ht).mp divided
  exact_mod_cast (show ((outputTable H F).darts : ℝ) ≤ (FinalConstants.walkLength : ℝ) *
      ((GraphTables.semantics (outputTable H F)).rejectionCount labeling : ℝ) by
    simpa only [mul_comm] using multiplied)

/-- Soundness of the gap map, as an inequality between natural numbers: if `F` is
unsatisfiable, every assignment of `gapMap H F` fails at least one clause in every
`walkLength * 40960`. -/
theorem gapMap_clauseCount (F : Formula) (unsat : ¬ F.Satisfiable)
    (assignment : Fin (gapMap H F).variables → Bool) :
    (gapMap H F).clauses.length ≤
      (FinalConstants.walkLength * 40960) *
        NameCompaction.failedCount (gapMap H F) assignment :=
  FinalTableFormula.clauseCount (outputTable H F) (output_count_gap H certificate F unsat)
    assignment

end UniqueGamesTheorem.Foundations.PCP.TableGapReduction

namespace UniqueGamesTheorem.Foundations.PCP.GapTheorem

open UniqueGamesTheorem.Foundations Target Complexity PCP
open MachineFiniteAlphabet

noncomputable def roundMachine (H : RoundTables.BaseTable) :=
  RoundComputation.tablePolynomialTime H (PreprocessingRuntime.tablePolynomialTime H)

theorem roundMachine_finite (H : RoundTables.BaseTable) :
    FiniteAlphabet (roundMachine H).tm :=
  RoundComputation.tablePolynomialTime_finite_alphabet H
    (PreprocessingRuntime.tablePolynomialTime H) (PreprocessingRuntime.finiteAlphabet H)

/-- The gap map is computed in polynomial time by a multi-stack machine, on the unary
serialisation `formulaBits` of formulas. -/
noncomputable def gapMachine (H : RoundTables.BaseTable) :
    Turing.TM2ComputableInPolyTime formulaBits formulaBits (TableIteration.gapMap H) :=
  MachineTableIteration.gapMapCertificate H (roundMachine H)

theorem gapMachine_finite (H : RoundTables.BaseTable) :
    FiniteAlphabet (gapMachine H).tm :=
  TableIterationFiniteAlphabet.gapMap H (roundMachine H) (roundMachine_finite H)

/-- Everything the rest of the project needs about the gap map, for one fixed base table. -/
theorem exists_gapMap :
    ∃ (gap : Formula → Formula)
      (machine : Turing.TM2ComputableInPolyTime formulaBits formulaBits gap),
      FiniteAlphabet machine.tm ∧
      (∀ F, F.Satisfiable → (gap F).Satisfiable) ∧
      (∀ F, 0 < (gap F).clauses.length) ∧
      (∀ F, ¬ F.Satisfiable → ∀ assignment : Fin (gap F).variables → Bool,
        (gap F).clauses.length ≤
          (FinalConstants.walkLength * 40960) * NameCompaction.failedCount (gap F) assignment) := by
  obtain ⟨H, certificate⟩ := ExpanderTables.exists_base_table
  refine ⟨TableIteration.gapMap H, gapMachine H, gapMachine_finite H,
    TableIteration.gapMap_completeness H, ?_,
    TableGapReduction.gapMap_clauseCount H certificate⟩
  intro F
  exact List.length_pos_iff.mpr (TableIteration.gapMap_nonempty H F)

end UniqueGamesTheorem.Foundations.PCP.GapTheorem

end OAI

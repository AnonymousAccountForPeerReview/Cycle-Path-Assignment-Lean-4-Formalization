module

public import Hardness.Decode.GapDecode
public import OAI.Computability.UniqueGames.PCP.GapTheorem

/-!
# The gap map with its decoder

`exists_gapMap_decoder` extends `GapTheorem.exists_gapMap`: soundness is stated in
constructive, pointwise form, with the explicit decoder `Decode.gapDecode`.
-/

@[expose] public section

namespace OAI.UniqueGamesTheorem.Foundations.PCP.GapTheorem

open UniqueGamesTheorem.Foundations Target Complexity PCP
open MachineFiniteAlphabet

/-- `exists_gapMap` with soundness in constructive, pointwise form: for one fixed base table
`H`, the gap map `gapMap H` is computed in polynomial time by a machine with finite alphabets,
preserves satisfiability, has nonempty output, and every assignment of `gapMap H F` failing
fewer than one clause in `walkLength * 40960` is turned by the explicit decoder
`Decode.gapDecode H F` into a satisfying assignment of `F`. -/
theorem exists_gapMap_decoder :
    ∃ (H : RoundTables.BaseTable)
      (machine : Turing.TM2ComputableInPolyTime formulaBits formulaBits (TableIteration.gapMap H)),
      FiniteAlphabet machine.tm ∧
      (∀ F, F.Satisfiable → (TableIteration.gapMap H F).Satisfiable) ∧
      (∀ F, 0 < (TableIteration.gapMap H F).clauses.length) ∧
      (∀ (F : Formula) (τ : Fin (TableIteration.gapMap H F).variables → Bool),
        (FinalConstants.walkLength * 40960) *
            NameCompaction.failedCount (TableIteration.gapMap H F) τ <
          (TableIteration.gapMap H F).clauses.length →
        ∀ cl ∈ F.clauses, cl.eval (Decode.gapDecode H F τ) = true) := by
  obtain ⟨H, certificate⟩ := ExpanderTables.exists_base_table
  refine ⟨H, gapMachine H, gapMachine_finite H,
    TableIteration.gapMap_completeness H, ?_,
    Decode.gapDecode_satisfies H certificate⟩
  intro F
  exact List.length_pos_iff.mpr (TableIteration.gapMap_nonempty H F)

end OAI.UniqueGamesTheorem.Foundations.PCP.GapTheorem

module

public import OAI.Computability.UniqueGames.Machines.FinalCNFPattern
public import OAI.Computability.UniqueGames.PCP.InputLemmas
public import OAI.Computability.UniqueGames.PCP.FinalBooleanVerifier
public import OAI.Computability.UniqueGames.PCP.FinalConstantsLemmas
public import OAI.Computability.UniqueGames.PCP.NameCompaction

/-!
Adapted from the ANONYMIZED mathematics repository (https://github.com/openai/math,
commit adc7f1241b42e322a6451854ab7e4b4c146bf78a, file `lean/OAI/Computability/UniqueGames/PCP/FinalTableFormula.lean`), Apache-2.0.
Changes: converted to the Lean module system (`module` header, `public import`,
`@[expose] public section`); the clause-gap theorem is restated in count form
(`clauseCount`) so that this file no longer imports the unrelated later stage.
-/

@[expose] public section

namespace OAI

section

/-! The exact table-to-formula converter used by the final CNF machine.
Its semantic count premise is explicit; amplification supplies that premise
elsewhere. The converter chooses no vertex or dart numbering. -/

namespace UniqueGamesTheorem.Foundations.PCP.FinalTableFormula

open Target Complexity

def output (table : GraphTables.Table) : Formula :=
  FinalBooleanVerifier.cnf (FinalCNFPattern.tableGraph table) (Equiv.refl _) (Equiv.refl _)

theorem satisfiable_iff (table : GraphTables.Table) :
    (output table).Satisfiable ↔ (GraphTables.semantics table).Satisfiable :=
  (FinalBooleanVerifier.cnf_satisfiable_iff (FinalCNFPattern.tableGraph table)
    (Equiv.refl _) (Equiv.refl _)).trans
      ((GraphTables.semantics table).satisfiable_reindex (Equiv.refl _) (Equiv.refl _)
        FinalCNFPattern.labelEquiv.symm)

@[simp] theorem variable_count (table : GraphTables.Table) :
    (output table).variables = table.vertices * 6 + table.darts * 36864 :=
  FinalBooleanVerifier.cnf_variable_count _ (Equiv.refl _) (Equiv.refl _)

@[simp] theorem clause_count (table : GraphTables.Table) :
    (output table).clauses.length = table.darts * 40960 :=
  FinalBooleanVerifier.cnf_clause_count _ (Equiv.refl _) (Equiv.refl _)

theorem nonempty (table : GraphTables.Table) (hd : 0 < table.darts) :
    (output table).clauses ≠ [] :=
  FinalBooleanVerifier.cnf_nonempty _ (Equiv.refl _) (Equiv.refl _) hd

/-- Boolean labels and numeric labels have exactly the same rejected darts. -/
theorem tableGraph_rejectionCount (table : GraphTables.Table)
    (labeling : Fin table.vertices → FinalBooleanVerifier.Label) :
    (FinalCNFPattern.tableGraph table).rejectionCount labeling =
      (GraphTables.semantics table).rejectionCount
        (fun v => FinalCNFPattern.labelEquiv (labeling v)) := by
  have h := (GraphTables.semantics table).reindex_rejectionCount
    (Equiv.refl _) (Equiv.refl _) FinalCNFPattern.labelEquiv.symm
    (fun v => FinalCNFPattern.labelEquiv (labeling v))
  simpa [FinalCNFPattern.tableGraph, ConstraintGraph.labelingEquiv] using h

/-- A uniform numeric-label count bound transfers to the machine's Boolean-label graph. -/
theorem tableGraph_count_lower (table : GraphTables.Table) (walkLength : Nat)
    (hgap : ∀ labeling : Fin table.vertices → GraphTables.Label,
      table.darts ≤ walkLength * (GraphTables.semantics table).rejectionCount labeling)
    (labeling : Fin table.vertices → FinalBooleanVerifier.Label) :
    Fintype.card (Fin table.darts) ≤
      walkLength * (FinalCNFPattern.tableGraph table).rejectionCount labeling := by
  rw [Fintype.card_fin, tableGraph_rejectionCount]
  exact hgap _

/-- Count form of the final clause gap: if every labeling of the table rejects at least a
`1 / walkLength` fraction of the darts, every assignment of the output formula fails at least a
`1 / (40960 * walkLength)` fraction of the clauses. -/
theorem clauseCount (table : GraphTables.Table)
    (hgap : ∀ labeling : Fin table.vertices → GraphTables.Label,
      table.darts ≤ FinalConstants.walkLength *
        (GraphTables.semantics table).rejectionCount labeling)
    (assignment : Fin (output table).variables → Bool) :
    (output table).clauses.length ≤
      (FinalConstants.walkLength * 40960) * NameCompaction.failedCount (output table) assignment := by
  have h := FinalBooleanVerifier.cnf_gap (FinalCNFPattern.tableGraph table)
    (Equiv.refl _) (Equiv.refl _) 1 FinalConstants.walkLength
    (fun labeling => by
      simpa only [one_mul] using tableGraph_count_lower table _ hgap labeling) assignment
  rw [one_mul] at h
  exact h

theorem total_size_le (table : GraphTables.Table) :
    (output table).variables + (output table).clauses.length ≤
      77824 * (table.vertices + table.darts) := by
  have hv := variable_count table
  have hc := clause_count table
  omega

/-- A fixed quadratic in the full serialized input length. -/
noncomputable def sizePolynomial : Polynomial Nat :=
  Polynomial.C 77824 * Polynomial.X + Polynomial.C 2 +
    (Polynomial.C 40960 * Polynomial.X) *
      (Polynomial.C 3 * (Polynomial.C 36864 * Polynomial.X + Polynomial.C 2))

theorem sizePolynomial_eval (N : Nat) :
    sizePolynomial.eval N = 77824 * N + 2 + (40960 * N) * (3 * (36864 * N + 2)) := by
  simp [sizePolynomial]

theorem formulaBits_length_le_polynomial (table : GraphTables.Table) :
    (formulaBits (output table)).length ≤
      sizePolynomial.eval (GraphTables.tableBits table).length := by
  have hinput := GraphTableComplexity.size_add_two_le_bits table
  have hv : (output table).variables ≤ 36864 * (GraphTables.tableBits table).length := by
    rw [variable_count]
    omega
  have hc : (output table).clauses.length ≤ 40960 * (GraphTables.tableBits table).length := by
    rw [clause_count]
    omega
  have hsum : (output table).variables + (output table).clauses.length + 2 ≤
      77824 * (GraphTables.tableBits table).length + 2 := by omega
  have hproduct := Nat.mul_le_mul hc (Nat.mul_le_mul_left 3 (Nat.add_le_add_right hv 2))
  rw [sizePolynomial_eval]
  exact (formulaBits_length_le (output table)).trans (Nat.add_le_add hsum hproduct)

end UniqueGamesTheorem.Foundations.PCP.FinalTableFormula

end

end OAI

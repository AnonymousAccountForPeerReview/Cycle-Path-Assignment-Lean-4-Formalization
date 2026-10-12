module

public import OAI.Computability.UniqueGames.PCP.RawInitialTablesLemmas
public import OAI.Computability.UniqueGames.PCP.FinalTableFormula

/-!
# Decoding the two end stages of the gap map

* `finalDecode table τ` reads a labeling of `table` off an assignment `τ` of the final formula
  `FinalTableFormula.output table`: the label of the vertex `v` is the number whose binary
  digits (least significant first) are the values of the variables `6 * v + j`, `j < 6`.
  `finalDecode_bound`: it rejects at most as many darts as `τ` fails clauses.
* `initialDecode F L` reads an assignment of `F` off a labeling `L` of the initial table
  `RawInitialTables.table F`: the value of the variable `x` is the least significant binary
  digit of the label of the vertex number `x`.
  `initialDecode_satisfies`: if `L` rejects no dart, the assignment satisfies `F`.
-/

@[expose] public section

namespace OAI.UniqueGamesTheorem.Foundations.PCP.Decode

open Target

/-! ### Final stage -/

/-- Stage decoder for the final formula: the six label bits of the vertex `v` are the variables
`6 * v + j`. -/
def finalDecode (table : GraphTables.Table)
    (τ : Fin (FinalTableFormula.output table).variables → Bool) :
    Fin table.vertices → GraphTables.Label :=
  fun v => Complexity.FinalCNFPattern.labelEquiv
    (FinalBooleanVerifier.extractLabeling (Complexity.FinalCNFPattern.tableGraph table)
      (Equiv.refl _) (Equiv.refl _) τ v)

/-- Index-level form of `finalDecode`: the label of `v` has the binary digits
`τ (6 * v + j)`, `j < 6`, least significant first. -/
theorem finalDecode_val (table : GraphTables.Table)
    (τ : Fin (FinalTableFormula.output table).variables → Bool) (v : Fin table.vertices) :
    (finalDecode table τ v).val =
      ∑ j : Fin 6, AlphabetTable.Enumeration.bitValue (τ ⟨j.val + 6 * v.val, by
        have := v.isLt
        have := j.isLt
        rw [FinalTableFormula.variable_count]
        omega⟩) * 2 ^ j.val := by
  unfold finalDecode
  rw [Complexity.FinalCNFPattern.labelEquiv_val]
  rfl

/-- Pointwise soundness of the final stage. -/
theorem finalDecode_bound (table : GraphTables.Table)
    (τ : Fin (FinalTableFormula.output table).variables → Bool) :
    (GraphTables.semantics table).rejectionCount (finalDecode table τ) ≤
      NameCompaction.failedCount (FinalTableFormula.output table) τ := by
  unfold finalDecode
  rw [← FinalTableFormula.tableGraph_rejectionCount]
  exact FinalBooleanVerifier.cnf_count_bridge (Complexity.FinalCNFPattern.tableGraph table)
    (Equiv.refl _) (Equiv.refl _) τ

/-! ### Initial stage -/

open InitialGraph in
/-- Pointwise form of `InitialGraph.raw_reflects`. -/
theorem raw_reflects_pointwise (F : Formula) (labeling : InitialGraph.Vertex F → InitialGraph.Label)
    (hlabeling : ∀ e, (raw F).edgeSatisfied labeling e = true) :
    ∀ c ∈ F.clauses, c.eval (fun v => (labeling (variableVertex F v)).1) = true := by
  let A : Fin F.variables → Bool := fun v => (labeling (variableVertex F v)).1
  have slot_correct (i : Fin F.clauses.length) (s : Slot) :
      localSatisfies (clauseAt F i) (toClauseAnswer (labeling (clauseVertex F i))) = true ∧
        answerAt (toClauseAnswer (labeling (clauseVertex F i))) s =
          A (nameAt (clauseAt F i) s) := by
    exact incidenceAccept_true F (i, s) _ _ (hlabeling (.inl ((i, s), false)))
  have clause_correct (i : Fin F.clauses.length) : (clauseAt F i).eval A = true := by
    have equal : toClauseAnswer (labeling (clauseVertex F i)) = honestAnswer (clauseAt F i) A :=
      clauseAnswer_eq_of_slots _ _ (fun s => by
        simpa only [honest_answerAt] using (slot_correct i s).2)
    have satisfied := (slot_correct i .first).1
    rw [equal, honest_satisfies] at satisfied
    exact satisfied
  intro c hc
  obtain ⟨i, hi, heq⟩ := List.getElem_of_mem hc
  simpa only [clauseAt, heq] using clause_correct ⟨i, hi⟩

/-- Stage decoder for the initial table: the value of the variable `x` is the least
significant bit of the label of the vertex number `x`. -/
def initialDecode (F : Formula)
    (L : Fin (RawInitialTables.table F).vertices → GraphTables.Label) :
    Fin F.variables → Bool :=
  fun x => (L ⟨x.val, by
    have := x.isLt
    rw [RawInitialTables.table_vertices]
    omega⟩).val.testBit 0

/-- Pointwise soundness of the initial stage. -/
theorem initialDecode_satisfies (F : Formula)
    (L : Fin (RawInitialTables.table F).vertices → GraphTables.Label)
    (zero : (GraphTables.semantics (RawInitialTables.table F)).rejectionCount L = 0) :
    ∀ c ∈ F.clauses, c.eval (initialDecode F L) = true := by
  let lifted : InitialGraph.Vertex F → AlphabetRetraction.Label64 :=
    fun v => RawInitialTables.labelOrder.symm (L (RawInitialTables.vertexOrder F v))
  have restored : (fun v => RawInitialTables.labelOrder
      (lifted ((RawInitialTables.vertexOrder F).symm v))) = L := by
    funext v
    simp only [lifted, Equiv.apply_symm_apply]
  have count := GraphTables.enumeratedGraph_rejectionCount (RawInitialTables.raw64 F)
    (RawInitialTables.vertexOrder F) (RawInitialTables.dartOrder F)
    RawInitialTables.labelOrder lifted
  rw [restored] at count
  have zero' : (GraphTables.enumeratedGraph (RawInitialTables.raw64 F)
      (RawInitialTables.vertexOrder F) (RawInitialTables.dartOrder F)
      RawInitialTables.labelOrder).rejectionCount L = 0 :=
    (GraphTables.semantics_ofGraph_rejectionCount _ L).symm.trans zero
  have zero'' : (RawInitialTables.raw64 F).rejectionCount lifted = 0 := count.symm.trans zero'
  have satisfied : ∀ e, (InitialGraph.raw F).edgeSatisfied
      (AlphabetRetraction.decode64 ∘ lifted) e = true :=
    ((RawInitialTables.raw64 F).rejectionCount_eq_zero_iff lifted).mp zero''
  exact raw_reflects_pointwise F (AlphabetRetraction.decode64 ∘ lifted) satisfied

end OAI.UniqueGamesTheorem.Foundations.PCP.Decode

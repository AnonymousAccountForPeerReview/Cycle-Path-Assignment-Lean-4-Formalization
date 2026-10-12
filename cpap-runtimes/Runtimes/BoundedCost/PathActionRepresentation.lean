module

public import Runtimes.BoundedCost.PathRepresentation
public import Runtimes.BoundedCost.NodeActionTables
import Mathlib.Tactic

/-! Concrete mask and forced-bit updates represent the semantic node action. -/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 STACS2027.RAM Complexity.SAT

theorem activeOccurrences_disable_sublist {α : Type*} (rows : List (Bool × α)) (i : ℕ) :
    (activeOccurrences (disableOccurrence rows i)).Sublist (activeOccurrences rows) := by
  induction rows generalizing i with
  | nil => simp [disableOccurrence, activeOccurrences]
  | cons row rows ih =>
    rcases row with ⟨active, clause⟩
    cases i with
    | zero => cases active <;> simp [disableOccurrence, activeOccurrences]
    | succ i =>
      cases active with
      | false => simpa [disableOccurrence, activeOccurrences] using ih i
      | true => simpa [disableOccurrence, activeOccurrences] using (ih i).cons_cons clause

theorem nodeAction_force_bound {summary : SearchSummary} {budget choice code bound : ℕ}
    (hf : summary.firstLiteral < bound) (hs : summary.secondLiteral < bound)
    (ha : nodeAction summary budget choice = .force code) : code < bound := by
  unfold nodeAction at ha
  split_ifs at ha <;> simp_all

theorem pathStateRep_of_nodeUpdated {layout : CompilerLayout} {nodes : ℕ} {original : CNF}
    {τ δ : Assignment} {rows : List (Bool × Clause)} {forced : ℕ → Bool}
    {required : List Literal} {budget choice : ℕ} {memory : ℕ → ℕ} {c : Config}
    (hlen : rows.length = original.length) (horiginal : rows.map Prod.snd = original)
    (hrows : ∀ row ∈ rows, row.2.length = 2 ∧ ∀ l ∈ row.2, l.var < nodes)
    (href : evalCNF τ (activeOccurrences rows) = true)
    (hmask : MaskTable memory layout.active rows)
    (hforced : ForcedTable memory layout.forced nodes forced)
    (hrequired : ∀ σ, Requires σ (denseRequirements nodes forced) ↔ Requires σ required)
    (hsep : layout.active + original.length ≤ layout.forced)
    (hcodes : (summarizePrefix (searchRowsOf τ δ rows) rows.length).firstLiteral < 2 * nodes ∧
      (summarizePrefix (searchRowsOf τ δ rows) rows.length).secondLiteral < 2 * nodes)
    (htruth : TruthTable c.mem layout.candidate nodes δ)
    (hupdated : NodeUpdated layout.active layout.forced budget choice 0
      (summarizePrefix (searchRowsOf τ δ rows) rows.length) memory (registerView callerRegister c)) :
    PathStateRep layout nodes original τ
      (nodeActionState (nodeAction (summarizePrefix (searchRowsOf τ δ rows) rows.length) budget choice)
        δ rows required budget) c := by
  let summary := summarizePrefix (searchRowsOf τ δ rows) rows.length
  have hbudget := hupdated.2.2.1
  have hsuccess := hupdated.2.2.2.2.1
  have hlive := hupdated.2.2.2.2.2.1
  have hmemory := hupdated.2.2.2.2.2.2.2
  change c.reg (callerRegister nodeBudget) = nodeActionBudget (nodeAction summary budget choice) budget at hbudget
  change c.reg (callerRegister nodeSuccess) = nodeActionSuccess (nodeAction summary budget choice) 0 at hsuccess
  change c.reg (callerRegister nodeLive) = nodeActionLive (nodeAction summary budget choice) at hlive
  change c.mem = nodeActionMemory (nodeAction summary budget choice) layout.active layout.forced memory at hmemory
  change PathStateRep layout nodes original τ (nodeActionState (nodeAction summary budget choice) δ rows required budget) c
  have hbounded : NodeActionBounded nodes rows.length (nodeAction summary budget choice) :=
    nodeAction_bounded (summarizePrefix_conflict_le _ _) hcodes.1 hcodes.2
  cases ha : nodeAction summary budget choice with
  | accept =>
    simp only [ha, nodeActionLive, nodeActionSuccess] at hlive hsuccess
    exact ⟨hlive, hsuccess, htruth⟩
  | prune =>
    simp only [ha, nodeActionLive, nodeActionSuccess] at hlive hsuccess
    exact ⟨hlive, hsuccess⟩
  | delete i =>
    have hi : i < rows.length := by simpa only [ha, NodeActionBounded] using hbounded
    simp only [ha, nodeActionLive, nodeActionSuccess, nodeActionBudget, nodeActionMemory] at hlive hsuccess hbudget hmemory
    refine ⟨disableOccurrence rows i, forced, ?_, ?_, ?_, rfl, ?_, ?_, hrequired, ?_,
      hbudget, hlive, hsuccess⟩
    · simpa [disableOccurrence_length] using hlen
    · rw [disableOccurrence_clauses, horiginal]
    · exact disableOccurrence_domain hrows i
    · rw [hmemory]
      exact hmask.disable i
    · rw [hmemory]
      exact hforced.upd_outside (by omega)
    · apply (evalCNF_iff τ _).mpr
      intro clause hc
      exact (evalCNF_iff τ _).mp href clause ((activeOccurrences_disable_sublist rows i).subset hc)
  | force code =>
    have hcode : code < 2 * nodes := nodeAction_force_bound hcodes.1 hcodes.2 ha
    simp only [ha, nodeActionLive, nodeActionSuccess, nodeActionBudget, nodeActionMemory] at hlive hsuccess hbudget hmemory
    refine ⟨rows, Function.update forced code true, hlen, horiginal, hrows, rfl, ?_, ?_, ?_,
      href, hbudget, hlive, hsuccess⟩
    · rw [hmemory]
      exact hmask.upd_outside (by omega)
    · rw [hmemory]
      exact hforced.force code
    · intro σ
      have hvar : (literalOfCode code).var < nodes := by change code / 2 < nodes; omega
      have h := requires_dense_force_congr hrequired (literalOfCode code) hvar σ
      simpa only [code_literalOfCode] using h

end STACS2027.Runtimes.BoundedCost

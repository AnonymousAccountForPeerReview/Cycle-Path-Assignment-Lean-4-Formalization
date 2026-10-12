module

public import Runtimes.BoundedCost.NodeFrames
import Mathlib.Tactic

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 STACS2027.RAM Complexity.SAT

def NodeActionBounded (n m : ℕ) : NodeAction → Prop
  | .delete i => i < m
  | .force code => code < 2 * n
  | _ => True

def nodeActionRows (action : NodeAction) (rows : List (Bool × Clause)) : List (Bool × Clause) :=
  match action with
  | .delete i => disableOccurrence rows i
  | _ => rows

def nodeActionForced (action : NodeAction) (forced : ℕ → Bool) : ℕ → Bool :=
  match action with
  | .force code => Function.update forced code true
  | _ => forced

@[simp] theorem nodeActionRows_length (action : NodeAction) (rows : List (Bool × Clause)) :
    (nodeActionRows action rows).length = rows.length := by
  cases action <;> simp [nodeActionRows, disableOccurrence_length]

@[simp] theorem nodeActionRows_clauses (action : NodeAction) (rows : List (Bool × Clause)) :
    (nodeActionRows action rows).map Prod.snd = rows.map Prod.snd := by
  cases action <;> simp [nodeActionRows, disableOccurrence_clauses]

theorem nodeAction_bounded {n m : ℕ} {summary : SearchSummary} {budget choice : ℕ}
    (hc : summary.conflict ≤ m) (hf : summary.firstLiteral < 2 * n)
    (hs : summary.secondLiteral < 2 * n) : NodeActionBounded n m (nodeAction summary budget choice) := by
  unfold nodeAction
  split_ifs <;> simp only [NodeActionBounded] <;> omega

/-- Each bounded concrete action updates the exact occurrence and requirement
tables while preserving the original formula and both truth tables. -/
theorem nodeAction_tables {S span formula active candidate reference forcedBase labels output n : ℕ}
    {rows : List (Bool × Clause)} {memory : ℕ → ℕ} {τ δ : Assignment} {forced : ℕ → Bool}
    (geometry : LeastCutGeometry S span formula active candidate reference forcedBase labels output n rows.length)
    (hrows : ∀ row ∈ rows, row.2.length = 2 ∧ ∀ l ∈ row.2, l.var < n)
    (action : NodeAction) (ha : NodeActionBounded n rows.length action)
    (hcodes : Arr memory formula (TwoSat.codes (rows.map Prod.snd)))
    (hmask : MaskTable memory active rows) (hforced : ForcedTable memory forcedBase n forced)
    (hreference : TruthTable memory reference n τ) (hcandidate : TruthTable memory candidate n δ) :
    let next := nodeActionMemory action active forcedBase memory
    Arr next formula (TwoSat.codes ((nodeActionRows action rows).map Prod.snd)) ∧
      MaskTable next active (nodeActionRows action rows) ∧
      ForcedTable next forcedBase n (nodeActionForced action forced) ∧
      TruthTable next reference n τ ∧ TruthTable next candidate n δ := by
  obtain ⟨hh, hfa, hac, hcr, hrf, hfl, hlo, hos⟩ := geometry
  have hf : TwoSat.IsTwoCNF n (rows.map Prod.snd) := by
    intro c hc
    obtain ⟨row, hr, rfl⟩ := List.mem_map.mp hc
    exact hrows row hr
  have hlength : (TwoSat.codes (rows.map Prod.snd)).length = 2 * rows.length := by
    simpa using TwoSat.length_codes hf
  cases action with
  | accept => exact ⟨hcodes, hmask, hforced, hreference, hcandidate⟩
  | prune => exact ⟨hcodes, hmask, hforced, hreference, hcandidate⟩
  | delete i =>
    change i < rows.length at ha
    refine ⟨?_, hmask.disable i, ?_, ?_, ?_⟩
    · simpa only [nodeActionMemory, nodeActionRows, disableOccurrence_clauses] using
        hcodes.upd_of_disjoint (a := active + i) (v := 0) (by rw [hlength]; omega)
    · exact hforced.upd_outside (by omega)
    · exact hreference.upd_outside (by omega)
    · exact hcandidate.upd_outside (by omega)
  | force code =>
    change code < 2 * n at ha
    refine ⟨?_, ?_, hforced.force code, ?_, ?_⟩
    · exact hcodes.upd_of_disjoint (by rw [hlength]; omega)
    · exact hmask.upd_outside (by omega)
    · exact hreference.upd_outside (by omega)
    · exact hcandidate.upd_outside (by omega)

end STACS2027.Runtimes.BoundedCost

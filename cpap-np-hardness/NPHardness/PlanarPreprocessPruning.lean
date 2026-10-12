module

public import NPHardness.LinearPreprocessResult
public import Complexity.Planar.Incidence

/-!
The actual preprocessors delete clauses and literals in their original rows.
This is stronger than `FormulaDeletion`, whose per-clause existential witness
does not specify an injective correspondence of clause vertices.  The present
relation supplies that missing indexed structure for an incidence-graph
planarity proof; it does not assume an unproved minor-closure theorem.
-/

@[expose] public section
namespace STACS2027.PlanarPreprocess
open Complexity.SAT

inductive Prunes : CNF → CNF → Prop where
  | nil : Prunes [] []
  | drop {g f : CNF} (c : Clause) : Prunes g f → Prunes g (c::f)
  | keep {g f : CNF} {c d : Clause} : c.Sublist d → Prunes g f → Prunes (c::g) (d::f)

theorem Prunes.trans {g f h : CNF} (hgf : Prunes g f) (hfh : Prunes f h) : Prunes g h := by
  induction hfh generalizing g with
  | nil => cases hgf; exact .nil
  | drop c hfh ih => exact .drop c (ih hgf)
  | keep hcd hfh ih =>
    cases hgf with
    | drop _ hgf => exact .drop _ (ih hgf)
    | keep hgc hgf => exact .keep (hgc.trans hcd) (ih hgf)

theorem normalize_prunes (f : CNF) : Prunes (normalizeClauses f) f := by
  induction f with
  | nil => exact .nil
  | cons c f ih =>
    rw [LinearPreprocessNormalize.normalizeClauses_cons]
    split
    · exact .drop c ih
    · exact .keep (distinctLiterals_sublist c) ih

open LinearPreprocessUnits

def CellsPrune (original mem : Memory) : Prop :=
  ∀ i c, mem i = some c → ∃ d, original i = some d ∧ c.Sublist d

theorem CellsPrune.refl (mem : Memory) : CellsPrune mem mem :=
  fun _ c hc => ⟨c,hc,List.Sublist.refl _⟩

theorem updateAt_prunes (original mem : Memory) (queue : List Nat) (l : Literal) (j : Nat)
    (h : CellsPrune original mem) : CellsPrune original (updateAt l j mem queue).1 := by
  intro i c hc
  change write mem j (simplifyCell l (mem j)) i = some c at hc
  by_cases he : i = j
  · subst i
    rw [write_same] at hc
    obtain ⟨d,hd,hcd⟩ := simplifyCell_deletion hc
    obtain ⟨e,he,hde⟩ := h j d hd
    exact ⟨e,he,hcd.trans hde⟩
  · rw [write_other mem i j _ he] at hc
    exact h i c hc

theorem updateIds_prunes (original mem : Memory) (queue : List Nat) (l : Literal) (ids : List Nat)
    (h : CellsPrune original mem) : CellsPrune original (updateIds l ids mem queue).1 := by
  induction ids generalizing mem queue with
  | nil => exact h
  | cons j js ih => exact ih _ _ (updateAt_prunes original mem queue l j h)

theorem CellsPrune.contents {original mem : Memory} (h : CellsPrune original mem) (size : Nat) :
    Prunes (contents size mem) (contents size original) := by
  unfold LinearPreprocessUnits.contents
  generalize List.range size = ids
  induction ids with
  | nil => exact .nil
  | cons j js ih =>
    cases hm : mem j with
    | none =>
      cases ho : original j with
      | none => simpa [hm,ho] using ih
      | some d => simpa [hm,ho] using Prunes.drop d ih
    | some c =>
      obtain ⟨d,hd,hcd⟩ := h j c hm
      simpa [hm,hd] using Prunes.keep hcd ih

def StatePrunes (original : Memory) : LinearPreprocessUnits.State → Prop
  | .running mem _ => CellsPrune original mem
  | .done mem => CellsPrune original mem
  | .rejected => True

theorem step_prunes (original : Memory) (adj : Incidences) (s : LinearPreprocessUnits.State)
    (h : StatePrunes original s) : StatePrunes original (step adj s) := by
  cases s with
  | done mem => exact h
  | rejected => trivial
  | running mem queue =>
    cases queue with
    | nil => exact h
    | cons j queue =>
      cases hj : mem j with
      | none => simpa only [step,hj,StatePrunes] using h
      | some c => cases c with
        | nil => simp [step,hj,StatePrunes]
        | cons l c => cases c with
          | nil => simpa only [step,hj,StatePrunes] using updateIds_prunes original mem queue l (adj l.var) h
          | cons r c => simpa only [step,hj,StatePrunes] using h

theorem executes_prunes {original : Memory} {adj : Incidences} {t : Nat}
    {s u : LinearPreprocessUnits.State} (h : Executes adj t s u) (hp : StatePrunes original s) :
    StatePrunes original u := by
  induction h with
  | refl => exact hp
  | next h ih => exact ih (step_prunes original adj _ hp)

theorem normalized_output_prunes {f : CNF} {t : Nat} {mem : Memory}
    (h : Executes (LinearPreprocessInit.initialAdj (normalizeClauses f)) t
      (.running (LinearPreprocessInit.initialMemory (normalizeClauses f))
        (List.range (normalizeClauses f).length)) (.done mem)) :
    Prunes (contents (normalizeClauses f).length mem) f := by
  have hp := executes_prunes h (CellsPrune.refl (LinearPreprocessInit.initialMemory (normalizeClauses f)))
  have he := CellsPrune.contents hp (normalizeClauses f).length
  rw [LinearPreprocessInit.contents_initialMemory] at he
  exact he.trans (normalize_prunes f)

end STACS2027.PlanarPreprocess

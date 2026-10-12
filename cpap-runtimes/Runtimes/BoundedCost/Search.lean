module

public import Runtimes.BoundedCost.CutGraph
import Mathlib.Tactic

/-!
# Executable annotated Almost 2-SAT search

The search calls the least-minimum-cut operation on the variable cut graph.
It branches only on a reference-true conflict, with a depth bounded by the
deletion budget above the minimum-cut lower bound.  The cut operation is an
explicit interface here, to be realized by the external flow solver.
-/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 Complexity.SAT

theorem unsatisfiedCount_perm {f g : CNF} (h : f.Perm g) (σ : Assignment) :
    unsatisfiedCount σ f = unsatisfiedCount σ g := h.countP_eq _

theorem cutCost_perm {f g : CNF} (h : f.Perm g) (τ σ : Assignment) :
    cutCost τ σ f = cutCost τ σ g := (h.map _).sum_eq

theorem annotated_perm {f g : CNF} (h : f.Perm g) (L : List Literal) (k : ℕ) :
    AnnotatedAlmostSatisfiable f L k ↔ AnnotatedAlmostSatisfiable g L k := by
  unfold AnnotatedAlmostSatisfiable
  simp only [unsatisfiedCount_perm h]

theorem annotated_member_branches {f : CNF} {a b : Literal} (hc : [a, b] ∈ f)
    (L : List Literal) (k : ℕ) :
    AnnotatedAlmostSatisfiable f L k ↔
      (0 < k ∧ AnnotatedAlmostSatisfiable (f.erase [a, b]) L (k - 1)) ∨
      AnnotatedAlmostSatisfiable f (a :: L) k ∨
      AnnotatedAlmostSatisfiable f (b :: L) k := by
  have hp := List.perm_cons_erase hc
  rw [annotated_perm hp L k, annotated_cons_branches]
  rw [← annotated_perm hp (a :: L) k, ← annotated_perm hp (b :: L) k]

theorem cutCost_erase_conflict {f : CNF} {c : Clause} (hc : c ∈ f)
    {τ : Assignment} (hτc : c.all (evalLiteral τ) = true) (σ : Assignment) :
    cutCost τ σ (f.erase c) = cutCost τ σ f := by
  rw [cutCost_perm (List.perm_cons_erase hc) τ σ, cutCost_cons_conflict hτc]

theorem leastCut_erase_conflict {τ δ : Assignment} {f : CNF} {c : Clause}
    {L : List Literal} (hδ : IsLeastCut τ f L δ) (hc : c ∈ f)
    (hτc : c.all (evalLiteral τ) = true) : IsLeastCut τ (f.erase c) L δ := by
  refine ⟨hδ.required, ?_, ?_⟩
  · intro σ hσ
    simpa only [cutCost_erase_conflict hc hτc] using hδ.optimal σ hσ
  · intro σ hσ he x hx
    apply hδ.least σ hσ ?_ x hx
    simpa only [cutCost_erase_conflict hc hτc] using he

/-- An operation returning a least minimum cut, or detecting incompatible
literal requirements. -/
abbrev LeastCutOperation := CNF → List Literal → Option Assignment

/-- The semantic contract that the concrete flow-to-cut wrapper must prove. -/
def LeastCutOperationCorrect (τ : Assignment) (cut : LeastCutOperation) : Prop :=
  ∀ f L, Clauses2 f → evalCNF τ f = true →
    (cut f L = none ↔ ¬ ∃ σ, Requires σ L) ∧
      ∀ δ, cut f L = some δ → IsLeastCut τ f L δ

/-- Find one conflict clause falsified by the least-cut assignment. -/
def findCutConflict (τ δ : Assignment) (f : CNF) : Option Clause :=
  f.find? fun c => !(evalClause δ c) && c.all (evalLiteral τ)

theorem findCutConflict_some {τ δ : Assignment} {f : CNF} {c : Clause}
    (h : findCutConflict τ δ f = some c) :
    c ∈ f ∧ evalClause δ c = false ∧ c.all (evalLiteral τ) = true := by
  exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

theorem conflictCost_zero_of_findCutConflict_none {τ δ : Assignment} {f : CNF}
    (h : findCutConflict τ δ f = none) : conflictCost τ δ f = 0 := by
  have hn := List.find?_eq_none.mp h
  unfold conflictCost
  apply List.sum_eq_zero_iff.mpr
  intro n hn'
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hn'
  have := hn c hc
  simp_all [conflictClause]

/-- Search with explicit bounded depth.  Deleted occurrences are reconstructed
from the final assignment, so equal clauses need no auxiliary identifiers here. -/
def annotatedSearch (cut : LeastCutOperation) (τ : Assignment) :
    ℕ → CNF → List Literal → ℕ → Option Assignment
  | 0, _, _, _ => none
  | fuel + 1, f, L, k =>
      match cut f L with
      | none => none
      | some δ =>
          if unsatisfiedCount δ f ≤ k then some δ
          else if k < cutCost τ δ f then none
          else match findCutConflict τ δ f with
            | none => none
            | some [a, b] =>
                (if k = 0 then none else annotatedSearch cut τ fuel (f.erase [a, b]) L (k - 1)).orElse
                  (fun _ => (annotatedSearch cut τ fuel f (a :: L) k).orElse
                    (fun _ => annotatedSearch cut τ fuel f (b :: L) k))
            | some _ => none

/-- Every assignment returned by the search is a valid annotated solution. -/
theorem annotatedSearch_sound (cut : LeastCutOperation) (τ : Assignment)
    (hcut : LeastCutOperationCorrect τ cut) :
    ∀ fuel f L k, Clauses2 f → evalCNF τ f = true →
      ∀ σ, annotatedSearch cut τ fuel f L k = some σ →
        unsatisfiedCount σ f ≤ k ∧ Requires σ L := by
  intro fuel
  induction fuel with
  | zero => intro f L k hf hτ σ h; simp [annotatedSearch] at h
  | succ fuel ih =>
    intro f L k hf hτ σ h
    cases hδ : cut f L with
    | none => simp [annotatedSearch, hδ] at h
    | some δ =>
      have hd := (hcut f L hf hτ).2 δ hδ
      by_cases hs : unsatisfiedCount δ f ≤ k
      · simp [annotatedSearch, hδ, hs] at h
        subst σ
        exact ⟨hs, hd.required⟩
      · by_cases hb : k < cutCost τ δ f
        · simp [annotatedSearch, hδ, hs, hb] at h
        · cases hc : findCutConflict τ δ f with
          | none => simp [annotatedSearch, hδ, hs, hb, hc] at h
          | some c =>
            have hm := (findCutConflict_some hc).1
            obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp (hf c hm)
            have herase : Clauses2 (f.erase [a, b]) :=
              fun c hc => hf c (List.mem_of_mem_erase hc)
            have ht : evalCNF τ (f.erase [a, b]) = true :=
              (evalCNF_iff τ _).mpr fun c hc =>
                (evalCNF_iff τ f).mp hτ c (List.mem_of_mem_erase hc)
            simp only [annotatedSearch, hδ, hs, hb, hc, ↓reduceIte] at h
            by_cases hk : k = 0
            · simp only [hk, ↓reduceIte, Option.orElse_none] at h
              cases ha : annotatedSearch cut τ fuel f (a :: L) 0 with
              | some ρ =>
                simp only [ha, Option.orElse_some, Option.some.injEq] at h
                subst σ
                obtain ⟨hρ, hL⟩ := ih f (a :: L) 0 hf hτ ρ ha
                exact ⟨by simpa [hk] using hρ, fun x hx => hL x (by simp [hx])⟩
              | none =>
                simp only [ha, Option.orElse_none] at h
                obtain ⟨hρ, hL⟩ := ih f (b :: L) 0 hf hτ σ h
                exact ⟨by simpa [hk] using hρ, fun x hx => hL x (by simp [hx])⟩
            · simp only [hk, ↓reduceIte] at h
              cases hd : annotatedSearch cut τ fuel (f.erase [a, b]) L (k - 1) with
              | some ρ =>
                simp only [hd, Option.orElse_some, Option.some.injEq] at h
                subst σ
                obtain ⟨hρ, hL⟩ := ih _ L (k - 1) herase ht ρ hd
                refine ⟨?_, hL⟩
                rw [unsatisfiedCount_perm (List.perm_cons_erase hm) ρ, unsatisfiedCount_cons]
                split <;> omega
              | none =>
                simp only [hd, Option.orElse_none] at h
                cases ha : annotatedSearch cut τ fuel f (a :: L) k with
                | some ρ =>
                  simp only [ha, Option.orElse_some, Option.some.injEq] at h
                  subst σ
                  obtain ⟨hρ, hL⟩ := ih f (a :: L) k hf hτ ρ ha
                  exact ⟨hρ, fun x hx => hL x (by simp [hx])⟩
                | none =>
                  simp only [ha, Option.orElse_none] at h
                  obtain ⟨hρ, hL⟩ := ih f (b :: L) k hf hτ σ h
                  exact ⟨hρ, fun x hx => hL x (by simp [hx])⟩

theorem orElse_exists_some_left {α : Type} (a b : Option α) (h : ∃ x, a = some x) :
    ∃ x, a.orElse (fun _ => b) = some x := by
  obtain ⟨x, rfl⟩ := h
  exact ⟨x, rfl⟩

theorem orElse_exists_some_right {α : Type} (a b : Option α) (h : ∃ x, b = some x) :
    ∃ x, a.orElse (fun _ => b) = some x := by
  cases a with
  | none => simpa using h
  | some x => exact ⟨x, rfl⟩

/-- A depth strictly exceeding the budget above the cut lower bound suffices
to find every annotated solution. -/
theorem annotatedSearch_complete (cut : LeastCutOperation) (τ : Assignment)
    (hcut : LeastCutOperationCorrect τ cut) :
    ∀ fuel f L k, Clauses2 f → evalCNF τ f = true →
      (∀ δ, cut f L = some δ → k < cutCost τ δ f + fuel) →
      AnnotatedAlmostSatisfiable f L k → ∃ σ, annotatedSearch cut τ fuel f L k = some σ := by
  intro fuel
  induction fuel with
  | zero =>
    intro f L k hf hτ hbound hsol
    cases hd : cut f L with
    | none =>
      obtain ⟨σ, _, hL⟩ := hsol
      exact ((hcut f L hf hτ).1.mp hd ⟨σ, hL⟩).elim
    | some δ =>
      have hl := leastCut_lower_bound ((hcut f L hf hτ).2 δ hd) hsol
      have hb := hbound δ hd
      omega
  | succ fuel ih =>
    intro f L k hf hτ hbound hsol
    cases hd : cut f L with
    | none =>
      obtain ⟨σ, _, hL⟩ := hsol
      exact ((hcut f L hf hτ).1.mp hd ⟨σ, hL⟩).elim
    | some δ =>
      have hδ := (hcut f L hf hτ).2 δ hd
      have hbd := hbound δ hd
      by_cases hs : unsatisfiedCount δ f ≤ k
      · exact ⟨δ, by simp [annotatedSearch, hd, hs]⟩
      · have hb : ¬k < cutCost τ δ f := not_lt.mpr (leastCut_lower_bound hδ hsol)
        cases hc : findCutConflict τ δ f with
        | none =>
          have hz := conflictCost_zero_of_findCutConflict_none hc
          have hu := unsatisfiedCount_eq_cut_add_conflict τ δ f
          omega
        | some c =>
          obtain ⟨hm, hdc, htc⟩ := findCutConflict_some hc
          obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp (hf c hm)
          have hta : evalLiteral τ a = true := by simpa using (by simpa using htc :
            evalLiteral τ a = true ∧ evalLiteral τ b = true).1
          have htb : evalLiteral τ b = true := by simpa using (by simpa using htc :
            evalLiteral τ a = true ∧ evalLiteral τ b = true).2
          have hda : evalLiteral δ a = false := (by simpa [evalClause] using hdc :
            evalLiteral δ a = false ∧ evalLiteral δ b = false).1
          have hdb : evalLiteral δ b = false := (by simpa [evalClause] using hdc :
            evalLiteral δ a = false ∧ evalLiteral δ b = false).2
          have herase : Clauses2 (f.erase [a, b]) :=
            fun c hc => hf c (List.mem_of_mem_erase hc)
          have hτerase : evalCNF τ (f.erase [a, b]) = true :=
            (evalCNF_iff τ _).mpr fun c hc =>
              (evalCNF_iff τ f).mp hτ c (List.mem_of_mem_erase hc)
          have hforce (x : Literal) (htx : evalLiteral τ x = true)
              (hdx : evalLiteral δ x = false) :
              ∀ δ', cut f (x :: L) = some δ' → k < cutCost τ δ' f + fuel := by
            intro δ' hd'
            have hδ' := (hcut f (x :: L) hf hτ).2 δ' hd'
            have hi := leastCut_requirement_increases hδ htx hdx hδ'.required
            omega
          rw [annotated_member_branches hm] at hsol
          simp only [annotatedSearch, hd, hs, hb, hc, ↓reduceIte]
          rcases hsol with ⟨hk, hsol⟩ | hsol | hsol
          · have hke : k ≠ 0 := by omega
            have hδerase := leastCut_erase_conflict hδ hm htc
            have hbe : ∀ δ', cut (f.erase [a, b]) L = some δ' →
                k - 1 < cutCost τ δ' (f.erase [a, b]) + fuel := by
              intro δ' hd'
              have hδ' := (hcut (f.erase [a, b]) L herase hτerase).2 δ' hd'
              have hlo := hδerase.optimal δ' hδ'.required
              have hhi := hδ'.optimal δ hδerase.required
              have he := cutCost_erase_conflict hm htc δ
              omega
            have he := ih _ L (k - 1) herase hτerase hbe hsol
            apply orElse_exists_some_left
            simpa only [hke, ↓reduceIte] using he
          · apply orElse_exists_some_right
            apply orElse_exists_some_left
            exact ih f (a :: L) k hf hτ (hforce a hta hda) hsol
          · apply orElse_exists_some_right
            apply orElse_exists_some_right
            exact ih f (b :: L) k hf hτ (hforce b htb hdb) hsol

/-- The executable bounded-depth search is exact at depth `k + 1`. -/
theorem annotatedSearch_correct (cut : LeastCutOperation) (τ : Assignment)
    (hcut : LeastCutOperationCorrect τ cut) {f : CNF} (hf : Clauses2 f)
    (hτ : evalCNF τ f = true) (L : List Literal) (k : ℕ) :
    (∃ σ, annotatedSearch cut τ (k + 1) f L k = some σ) ↔
      AnnotatedAlmostSatisfiable f L k := by
  constructor
  · rintro ⟨σ, hσ⟩
    obtain ⟨hc, hL⟩ := annotatedSearch_sound cut τ hcut _ f L k hf hτ σ hσ
    exact ⟨σ, hc, hL⟩
  · exact annotatedSearch_complete cut τ hcut _ f L k hf hτ (fun δ _ => by omega)

end STACS2027.Runtimes.BoundedCost

module

public import NPHardness.UnitSimplify

/-! Total unit propagation: at most one iteration per original clause. -/

@[expose] public section
namespace STACS2027
open Complexity.SAT

def firstUnit : CNF → Option Literal
  | [] => none
  | [l] :: _ => some l
  | _ :: f => firstUnit f

theorem firstUnit_some {f : CNF} {l : Literal} (h : firstUnit f = some l) : [l] ∈ f := by
  induction f with
  | nil => simp [firstUnit] at h
  | cons c f ih =>
    cases c with
    | nil => exact List.mem_cons_of_mem _ (ih h)
    | cons r rs => cases rs with
      | nil => have he : r = l := by simpa [firstUnit] using h
               simp [he]
      | cons s ss => exact List.mem_cons_of_mem _ (ih h)

theorem firstUnit_none {f : CNF} (h : firstUnit f = none) : ∀ l, [l] ∉ f := by
  induction f with
  | nil => simp
  | cons c f ih =>
    cases c with
    | nil => intro l; simpa using ih h l
    | cons r rs => cases rs with
      | nil => simp [firstUnit] at h
      | cons s ss => intro l; simpa using ih h l

def unitReduce : Nat → CNF → Option CNF
  | 0,f => some f
  | fuel+1,f => if [] ∈ f then none else
      match firstUnit f with
      | none => some f
      | some l => unitReduce fuel (setLiteral l f)

theorem unitReduce_sat (fuel : Nat) (f : CNF) :
    match unitReduce fuel f with
    | none => ¬ Satisfiable f
    | some g => Satisfiable g ↔ Satisfiable f := by
  induction fuel generalizing f with
  | zero => exact Iff.rfl
  | succ fuel ih =>
    by_cases hempty : [] ∈ f
    · rw [unitReduce,ite_eq_left hempty]
      exact empty_clause_unsatisfiable hempty
    · rw [unitReduce,ite_eq_right hempty]
      cases hu : firstUnit f with
      | none => exact Iff.rfl
      | some l =>
        have hs := setLiteral_satisfiable (firstUnit_some hu)
        have h := ih (setLiteral l f)
        change (match unitReduce fuel (setLiteral l f) with
          | none => ¬ Satisfiable f
          | some g => Satisfiable g ↔ Satisfiable f)
        cases hr : unitReduce fuel (setLiteral l f) with
        | none =>
          rw [hr] at h
          exact fun hf => h (hs.mpr hf)
        | some g =>
          rw [hr] at h
          exact h.trans hs

theorem unitReduce_deletion {fuel : Nat} {f g : CNF} (h : unitReduce fuel f = some g) :
    FormulaDeletion g f := by
  induction fuel generalizing f g with
  | zero => have he : f = g := Option.some.inj h
            subst g; exact FormulaDeletion.refl _
  | succ fuel ih =>
    unfold unitReduce at h
    split at h
    · cases h
    · cases hu : firstUnit f with
      | none =>
        simp only [hu] at h
        have he := Option.some.inj h
        subst g
        exact FormulaDeletion.refl _
      | some l =>
        simp only [hu] at h
        exact (ih h).trans (setLiteral_deletion l f)

theorem unitReduce_clause_lower {fuel : Nat} {f g : CNF} (hfuel : f.length ≤ fuel)
    (h : unitReduce fuel f = some g) : ∀ c ∈ g, 2 ≤ c.length := by
  induction fuel generalizing f g with
  | zero =>
    have hf : f = [] := List.length_eq_zero_iff.mp (by omega)
    have hg : g = [] := by simpa [unitReduce,hf] using h.symm
    simp [hg]
  | succ fuel ih =>
    unfold unitReduce at h
    split at h
    · cases h
    · next hempty =>
        cases hu : firstUnit f with
        | none =>
          simp only [hu] at h
          have he := Option.some.inj h
          subst g
          intro c hc
          cases c with
          | nil => exact False.elim (hempty hc)
          | cons l ls => cases ls with
            | nil => exact False.elim (firstUnit_none hu l hc)
            | cons r rs => simp
        | some l =>
          simp only [hu] at h
          have hlen := setLiteral_length_lt (firstUnit_some hu)
          exact ih (by omega) h

def cleanFormula (f : CNF) : Option CNF :=
  unitReduce (normalizeClauses f).length (normalizeClauses f)

theorem cleanFormula_sat (f : CNF) :
    match cleanFormula f with
    | none => ¬ Satisfiable f
    | some g => Satisfiable g ↔ Satisfiable f := by
  have he : Satisfiable (normalizeClauses f) ↔ Satisfiable f := by
    simp only [Satisfiable,normalizeClauses_eval]
  have h := unitReduce_sat (normalizeClauses f).length (normalizeClauses f)
  cases hr : cleanFormula f with
  | none =>
    change unitReduce (normalizeClauses f).length (normalizeClauses f) = none at hr
    rw [hr] at h
    exact fun hf => h (he.mpr hf)
  | some g =>
    change unitReduce (normalizeClauses f).length (normalizeClauses f) = some g at hr
    rw [hr] at h
    exact h.trans he

theorem cleanFormula_bounded {f g : CNF} (hf : BoundedOccurrence f) (hg : cleanFormula f = some g) :
    BoundedOccurrence g ∧ ClauseVariablesDistinct g ∧ g.length ≤ f.length := by
  have hunit := unitReduce_deletion hg
  have hnorm := normalizeClauses_deletion f
  have hdel := hunit.trans hnorm
  have hthree := hdel.threeCNF hf.isThreeCNF
  have hlower := unitReduce_clause_lower (Nat.le_refl (normalizeClauses f).length) hg
  refine ⟨⟨?_,?_,?_⟩,hunit.distinct (normalizeClauses_distinct f),hdel.2.1⟩
  · intro c hc
    have h3 := hthree c hc
    have h2 := hlower c hc
    omega
  · intro v
    exact Nat.le_trans (hdel.occurrences_le v true) (hf.2.1 v)
  · intro v
    exact Nat.le_trans (hdel.occurrences_le v false) (hf.2.2 v)

end STACS2027

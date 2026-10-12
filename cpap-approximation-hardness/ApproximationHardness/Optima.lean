module

public import ApproximationHardness.Optimization

/-!
# Existence of the optima

`S* = max_A s(A)` exists because `s` is bounded by the number of clauses; `C*` exists
because the budgets admitting an assignment form a nonempty set of naturals.
-/

@[expose] public section
namespace STACS2027
open Complexity.SAT

theorem exists_greatest (P : Nat → Prop) (B : Nat) (h : ∃ n, n ≤ B ∧ P n) :
    ∃ S, S ≤ B ∧ P S ∧ ∀ n, n ≤ B → P n → n ≤ S := by
  classical
  induction B with
  | zero =>
    obtain ⟨n, hn, hP⟩ := h
    have : n = 0 := by omega
    subst this
    exact ⟨0, Nat.le_refl 0, hP, fun n hn _ => hn⟩
  | succ B ih =>
    by_cases hB : P (B + 1)
    · exact ⟨B + 1, Nat.le_refl _, hB, fun n hn _ => hn⟩
    · obtain ⟨n, hn, hP⟩ := h
      have hn' : n ≤ B := by
        rcases Nat.lt_or_eq_of_le hn with h | h
        · omega
        · subst h; exact absurd hP hB
      obtain ⟨S, hS, hPS, hmax⟩ := ih ⟨n, hn', hP⟩
      refine ⟨S, Nat.le_succ_of_le hS, hPS, ?_⟩
      intro m hm hPm
      rcases Nat.lt_or_eq_of_le hm with h | h
      · exact hmax m (by omega) hPm
      · subst h; exact absurd hPm hB

theorem exists_least (P : Nat → Prop) (h : ∃ n, P n) : ∃ C, P C ∧ ∀ B, P B → C ≤ B := by
  classical
  obtain ⟨n, hn⟩ := h
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases hbelow : ∃ m, m < n ∧ P m
    · obtain ⟨m, hm, hPm⟩ := hbelow
      exact ih m hm hPm
    · refine ⟨n, hn, ?_⟩
      intro B hB
      apply Classical.byContradiction
      intro hlt
      exact hbelow ⟨B, by omega, hB⟩

theorem satisfiedCount_le (a : Assignment) (f : CNF) : satisfiedCount a f ≤ f.length :=
  List.countP_le_length

/-- `S*` exists. -/
theorem maxSat_exists (f : CNF) : ∃ S, IsMaxSat f S := by
  obtain ⟨S, _, ⟨a, ha⟩, hmax⟩ := exists_greatest (fun n => ∃ a : Assignment, satisfiedCount a f = n) f.length
    ⟨satisfiedCount (fun _ => false) f, satisfiedCount_le _ f, ⟨_, rfl⟩⟩
  exact ⟨S, ⟨a, ha⟩, fun b => hmax _ (satisfiedCount_le b f) ⟨b, rfl⟩⟩

/-- `C*` exists as soon as some assignment does. -/
theorem minCost_exists {g : Graph} {k : Nat} (h : ∃ B, HasAssignment g k B) : ∃ C, IsMinCost g k C :=
  exists_least (HasAssignment g k) h

theorem IsMaxSat.unique {f : CNF} {S S' : Nat} (h : IsMaxSat f S) (h' : IsMaxSat f S') : S = S' := by
  obtain ⟨⟨a, ha⟩, hmax⟩ := h
  obtain ⟨⟨a', ha'⟩, hmax'⟩ := h'
  have h1 := hmax a'
  have h2 := hmax' a
  omega

theorem IsMinCost.unique {g : Graph} {k C C' : Nat} (h : IsMinCost g k C) (h' : IsMinCost g k C') : C = C' := by
  have h1 := h.2 C' h'.1
  have h2 := h'.2 C h.1
  omega

end STACS2027

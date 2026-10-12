module

public import BoundedCost.Equivalence

/-!
# Algorithm 3: the case `Ψ = 0`, and computing `OPT` by increasing `Ψ`

"The same algorithm computes `OPT` by testing `Ψ = 0, 1, 2, …` until an assignment is
returned" (Appendix B). For `k ≥ 4`, Algorithm 3 returns an assignment for the budget `Ψ`
exactly when Almost 2-SAT accepts `(Γ', Ψ)` (Theorem 4, `almostSatisfiable_iff_hasAssignment`),
and for `Ψ = 0` exactly when the 2-SAT instance `Γ_∅` is satisfiable
(`permittedFormula_nil_satisfiable_iff`). Here:

* the test is monotone in `Ψ` (`almostSatisfiable_mono`) and succeeds for some `Ψ`
  (`exists_almostSatisfiable`), so the search terminates;
* the first `Ψ` it accepts is the optimum `OPT` (`isOptimalCost_iff_least_accepted`), with
  `IsOptimalCost g k C` the predicate "`C = OPT`" (Section 6's `IsMinCost`);
* the search itself, `searchOptimum`, run with any correct decision procedure for the test,
  stops by the cost of an explicit assignment and returns `OPT` (`searchOptimum_correct`).

The running time of the cited Almost 2-SAT algorithm is not formalized.
-/

@[expose] public section
namespace STACS2027
open Complexity.SAT

/-- `C` is the optimum `OPT` of `CPAP(g, k)`: some assignment has cost at most `C`, and every
budget admitting an assignment is at least `C` (the predicate `IsMinCost` of Section 6). -/
def IsOptimalCost (g : Graph) (k C : Nat) : Prop :=
  HasAssignment g k C ∧ ∀ B, HasAssignment g k B → C ≤ B

/-- The cost of the assignment that omits the first vertex of every cycle: an upper bound on
`OPT`, at which the search can stop. -/
def firstOptionCost (g : Graph) (k : Nat) : Nat :=
  cost ((cycles g k).map fun c => selected c 0)

/-- Computing `OPT` by testing `Ψ = 0, 1, 2, …`, with a decision procedure `test` telling
whether Algorithm 3 returns an assignment for the budget `Ψ`: the first accepted budget,
searched up to `firstOptionCost g k`. -/
def searchOptimum (g : Graph) (k : Nat) (test : Nat → Bool) : Option Nat :=
  (List.range (firstOptionCost g k + 1)).find? test

/-! ## The case `Ψ = 0` -/

theorem almostFormula_zero (g : Graph) (k : Nat) : almostFormula g k 0 = permittedFormula g k [] := by
  have : (candidateOverlaps g k).filter (fun u => !([] : List (Nat × Nat × Edge)).contains u) =
      candidateOverlaps g k := List.filter_eq_self.mpr fun _ _ => rfl
  unfold almostFormula permittedFormula
  rw [this]
  simp

theorem almostSatisfiable_zero_iff (f : CNF) : AlmostSatisfiable f 0 ↔ Satisfiable f := by
  constructor
  · rintro ⟨sub, hsub, hlen, hsat⟩
    rw [hsub.eq_of_length_le (by omega)] at hsat
    exact hsat
  · intro h
    exact ⟨f, List.Sublist.refl f, by omega, h⟩

/-- **Algorithm 3, the case `Ψ = 0`**: "for `Ψ = 0`, ordinary 2-SAT suffices" — `Γ_∅` is
satisfiable iff an assignment of cost `0` exists (for `k ≥ 4`); a satisfying truth assignment
gives one by `recoverAssignment_correct`. -/
theorem permittedFormula_nil_satisfiable_iff {k : Nat} (hk : 4 ≤ k) (g : Graph) :
    Satisfiable (permittedFormula g k []) ↔ HasAssignment g k 0 := by
  rw [← almostFormula_zero, ← almostSatisfiable_zero_iff]
  exact almostSatisfiable_iff_hasAssignment hk g 0

/-! ## The optimum -/

theorem hasAssignment_mono {g : Graph} {k B B' : Nat} (h : B ≤ B') :
    HasAssignment g k B → HasAssignment g k B' := by
  rintro ⟨ps, hv, hc⟩
  exact ⟨ps, hv, Nat.le_trans hc h⟩

theorem validChoices_first (cs : List Cycle) (h : ∀ c ∈ cs, 0 < c.length) :
    ValidChoices (cs.map selectedOptions) (cs.map fun c => selected c 0) := by
  induction cs with
  | nil => trivial
  | cons c cs ih =>
    exact ⟨List.mem_map.mpr ⟨0, List.mem_range.mpr (h c List.mem_cons_self), rfl⟩,
      ih fun d hd => h d (List.mem_cons_of_mem c hd)⟩

theorem hasAssignment_firstOptionCost (g : Graph) (k : Nat) :
    HasAssignment g k (firstOptionCost g k) := by
  refine ⟨_, validChoices_first (cycles g k) ?_, Nat.le_refl _⟩
  intro c hc
  have h := enumerated_isCycle hc
  have := h.1
  have := h.2.1
  omega

theorem exists_least_of_exists {P : Nat → Prop} (h : ∃ n, P n) :
    ∃ n, P n ∧ ∀ m, m < n → ¬ P m := by
  obtain ⟨n, hn⟩ := h
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hm : ∃ m, m < n ∧ P m
    · obtain ⟨m, hmn, hPm⟩ := hm
      exact ih m hmn hPm
    · exact ⟨n, hn, fun m hmn hPm => hm ⟨m, hmn, hPm⟩⟩

/-- `OPT` exists (for every `k`). -/
theorem exists_isOptimalCost (g : Graph) (k : Nat) : ∃ C, IsOptimalCost g k C := by
  obtain ⟨C, hC, hmin⟩ := exists_least_of_exists ⟨_, hasAssignment_firstOptionCost g k⟩
  exact ⟨C, hC, fun B hB => Nat.le_of_not_lt fun hlt => hmin B hlt hB⟩

theorem isOptimalCost_unique {g : Graph} {k C C' : Nat} (h : IsOptimalCost g k C)
    (h' : IsOptimalCost g k C') : C = C' :=
  Nat.le_antisymm (h.2 C' h'.1) (h'.2 C h.1)

/-! ## Increasing `Ψ` -/

/-- The test of Algorithm 3 is monotone in `Ψ` (for `k ≥ 4`): if Almost 2-SAT accepts
`(Γ', Ψ)`, it accepts the formula and budget of every larger `Ψ'`. -/
theorem almostSatisfiable_mono {k : Nat} (hk : 4 ≤ k) (g : Graph) {Ψ Ψ' : Nat} (h : Ψ ≤ Ψ') :
    AlmostSatisfiable (almostFormula g k Ψ) Ψ → AlmostSatisfiable (almostFormula g k Ψ') Ψ' := by
  rw [almostSatisfiable_iff_hasAssignment hk, almostSatisfiable_iff_hasAssignment hk]
  exact hasAssignment_mono h

/-- The search by increasing `Ψ` terminates: Almost 2-SAT accepts `(Γ', Ψ)` for some `Ψ` (for
`k ≥ 4`). -/
theorem exists_almostSatisfiable {k : Nat} (hk : 4 ≤ k) (g : Graph) :
    ∃ Ψ, AlmostSatisfiable (almostFormula g k Ψ) Ψ :=
  ⟨_, (almostSatisfiable_iff_hasAssignment hk g _).mpr (hasAssignment_firstOptionCost g k)⟩

/-- **Computing `OPT` by increasing `Ψ`**: the first `Ψ` for which Almost 2-SAT accepts
`(Γ', Ψ)` is `OPT` (for `k ≥ 4`). -/
theorem isOptimalCost_iff_least_accepted {k : Nat} (hk : 4 ≤ k) (g : Graph) (Ψ : Nat) :
    IsOptimalCost g k Ψ ↔
      AlmostSatisfiable (almostFormula g k Ψ) Ψ ∧
        ∀ Ψ', Ψ' < Ψ → ¬ AlmostSatisfiable (almostFormula g k Ψ') Ψ' := by
  simp only [almostSatisfiable_iff_hasAssignment hk]
  constructor
  · rintro ⟨hΨ, hmin⟩
    exact ⟨hΨ, fun Ψ' hlt hΨ' => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hlt (hmin Ψ' hΨ'))⟩
  · rintro ⟨hΨ, hmin⟩
    exact ⟨hΨ, fun B hB => Nat.le_of_not_lt fun hlt => hmin B hlt hB⟩

theorem find?_range_eq_some_iff (p : Nat → Bool) (n a : Nat) :
    (List.range n).find? p = some a ↔ a < n ∧ p a = true ∧ ∀ b, b < a → p b = false := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.find?_append, List.find?_singleton]
    cases h : (List.range n).find? p with
    | some a' =>
      have := (ih a').mp h
      simp only [Option.some_or, Option.some.injEq]
      constructor
      · rintro rfl
        exact ⟨by omega, this.2⟩
      · rintro ⟨_, hpa, hlt⟩
        apply Classical.byContradiction
        intro hne
        rcases Nat.lt_or_gt_of_ne hne with hl | hl
        · rw [hlt a' hl] at this; exact Bool.noConfusion this.2.1
        · rw [this.2.2 a hl] at hpa; exact Bool.noConfusion hpa
    | none =>
      have hnone := List.find?_eq_none.mp h
      simp only [Option.none_or]
      constructor
      · intro hs
        split at hs
        · cases hs
          refine ⟨by omega, by assumption, fun b hb => ?_⟩
          cases hpb : p b
          · rfl
          · exact absurd hpb (hnone b (List.mem_range.mpr hb))
        · cases hs
      · rintro ⟨han, hpa, _⟩
        have : a = n := by
          apply Classical.byContradiction
          intro hne
          exact hnone a (List.mem_range.mpr (by omega)) hpa
        subst this
        simp [hpa]

/-- **Computing `OPT` by increasing `Ψ`**: with any decision procedure `test` for the test of
Algorithm 3 (whether Almost 2-SAT accepts `(Γ', Ψ)`), the search over `Ψ = 0, 1, 2, …` stops
and returns `OPT` (for `k ≥ 4`). -/
theorem searchOptimum_correct {k : Nat} (hk : 4 ≤ k) (g : Graph) (test : Nat → Bool)
    (htest : ∀ Ψ, test Ψ = true ↔ AlmostSatisfiable (almostFormula g k Ψ) Ψ) :
    (searchOptimum g k test).isSome = true ∧
      ∀ C, searchOptimum g k test = some C ↔ IsOptimalCost g k C := by
  have ht : ∀ Ψ, test Ψ = true ↔ HasAssignment g k Ψ := fun Ψ =>
    (htest Ψ).trans (almostSatisfiable_iff_hasAssignment hk g Ψ)
  have hiff : ∀ C, searchOptimum g k test = some C ↔ IsOptimalCost g k C := by
    intro C
    unfold searchOptimum
    rw [find?_range_eq_some_iff]
    constructor
    · rintro ⟨_, hC, hmin⟩
      refine ⟨(ht C).mp hC, fun B hB => Nat.le_of_not_lt fun hlt => ?_⟩
      have := hmin B hlt
      rw [(ht B).mpr hB] at this
      cases this
    · rintro ⟨hC, hmin⟩
      refine ⟨Nat.lt_succ_of_le (hmin _ (hasAssignment_firstOptionCost g k)), (ht C).mpr hC, ?_⟩
      intro b hb
      cases htb : test b
      · rfl
      · exact absurd (hmin b ((ht b).mp htb)) (Nat.not_le_of_lt hb)
  refine ⟨?_, hiff⟩
  obtain ⟨C, hC⟩ := exists_isOptimalCost g k
  rw [(hiff C).mpr hC]
  rfl

end STACS2027

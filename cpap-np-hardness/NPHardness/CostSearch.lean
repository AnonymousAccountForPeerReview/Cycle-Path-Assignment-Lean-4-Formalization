module

public import NPHardness.FiniteCycles

/-!
Verified finite search for local CPAP certificates. Search is only a proof
method here; no polynomial-time claim is made for the search algorithm.
`cost` uses the manuscript's pairwise-overlap form of the objective.
-/

@[expose] public section
namespace STACS2027

/-- The paths of `k - 2` edges in the `k`-cycle `c`, one for each deleted vertex. -/
def selectedOptions (c : Cycle) : List (List Edge) :=
  (List.range c.length).map (selected c)

def searchBudget (options : List (List (List Edge)))
    (chosen : List (List Edge)) (budget : Nat) : Bool :=
  match options with
  | [] => decide (cost chosen ≤ budget)
  | opts :: rest => opts.any fun p =>
      decide (cost (p :: chosen) ≤ budget) && searchBudget rest (p :: chosen) budget

theorem cost_tail_le (p : List Edge) (ps : List (List Edge)) :
    cost ps ≤ cost (p :: ps) := Nat.le_add_left ..

/-- `chosen` takes one entry from each list in `options`, in order. -/
def ValidChoices (options : List (List (List Edge))) (chosen : List (List Edge)) : Prop :=
  List.rec (motive := fun _ => List (List Edge) → Prop)
    (fun ps => List.casesOn ps True (fun _ _ => False))
    (fun opts _ previous ps => List.casesOn ps False
      (fun p tail => p ∈ opts ∧ previous tail)) options chosen

def validChoicesDecidable : (opts : List (List (List Edge))) →
    (ps : List (List Edge)) → Decidable (ValidChoices opts ps)
  | [], [] => isTrue trivial
  | [], _ :: _ => isFalse id
  | _ :: _, [] => isFalse id
  | _o :: os, _p :: ps => @instDecidableAnd _ _ (inferInstance) (validChoicesDecidable os ps)

instance (opts : List (List (List Edge))) (ps : List (List Edge)) :
    Decidable (ValidChoices opts ps) := validChoicesDecidable opts ps

theorem searchBudget_complete (options : List (List (List Edge)))
    (chosen ps : List (List Edge)) (budget : Nat)
    (hv : ValidChoices options ps) (hc : cost (ps.reverse ++ chosen) ≤ budget) :
    searchBudget options chosen budget = true := by
  induction options generalizing chosen ps with
  | nil =>
    cases ps with
    | nil => simpa [searchBudget] using hc
    | cons p ps => exact False.elim hv
  | cons opts rest ih =>
    cases ps with
    | nil => exact False.elim hv
    | cons p qs =>
     obtain ⟨hp, hv⟩ := hv
     simp only [List.reverse_cons, List.append_assoc, List.singleton_append] at hc
     apply List.any_eq_true.mpr
     refine ⟨p, hp, ?_⟩
     rw [Bool.and_eq_true]
     refine ⟨?_, ih (p :: chosen) qs hv hc⟩
     apply decide_eq_true
     have aux : ∀ xs : List (List Edge), cost (p :: chosen) ≤ cost (xs ++ p :: chosen) := by
       intro xs
       induction xs with
       | nil => exact Nat.le_refl _
       | cons x xs h => exact Nat.le_trans h (cost_tail_le x _)
     exact Nat.le_trans (aux qs.reverse) hc

theorem searchBudget_excludes (options : List (List (List Edge)))
    (chosen ps : List (List Edge)) (budget : Nat)
    (hn : searchBudget options chosen budget = false) (hv : ValidChoices options ps) :
    budget < cost (ps.reverse ++ chosen) := by
  by_cases hc : cost (ps.reverse ++ chosen) ≤ budget
  · have := searchBudget_complete options chosen ps budget hv hc
    simp [hn] at this
  · omega

theorem searchBudget_excludes_cost (options : List (List (List Edge)))
    (ps : List (List Edge)) (budget : Nat)
    (hn : searchBudget options [] budget = false) (hv : ValidChoices options ps) :
    budget < cost ps := by
  have h := searchBudget_excludes options [] ps budget hn hv
  simpa [cost_reverse] using h

end STACS2027

module

public import ApproximationHardness.Polarize
public import ApproximationHardness.Optima

/-!
# Lemma 10: the L-reduction inequalities

"These choices can be extended from any assignment of `ψ`, and `OPT(φ) = r + OPT(ψ)`.
[...] Thus `OPT(φ') = OPT(φ)`. Given any assignment of `φ'`, undo the complementations and
restore the eliminated variables. The recovered assignment satisfies all `r` deleted
clauses and at least as many clauses overall as the target assignment. Both L-reduction
conditions follow with `α = β = 1`."
-/

@[expose] public section
namespace STACS2027
open Complexity.SAT

/-! ## Splitting the objective -/

theorem satisfiedCount_append (a : Assignment) (g h : CNF) :
    satisfiedCount a (g ++ h) = satisfiedCount a g + satisfiedCount a h := by
  simp [satisfiedCount, List.countP_append]

/-- The clauses Lemma 10 deletes. -/
def deletedClauses (f : CNF) : CNF := f.filter (deleted f)

theorem countP_split {α : Type} (l : List α) (p q : α → Bool) :
    l.countP p = (l.filter q).countP p + (l.filter fun x => !q x).countP p := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.countP_cons, List.filter_cons]
    cases hq : q x <;> cases hp : p x <;> simp [hp, ih] <;> omega

theorem satisfiedCount_split (a : Assignment) (f : CNF) :
    satisfiedCount a f = satisfiedCount a (deletedClauses f) + satisfiedCount a (kept f) :=
  countP_split f (evalClause a) (deleted f)

theorem satisfiedCount_deleted_le (a : Assignment) (f : CNF) :
    satisfiedCount a (deletedClauses f) ≤ deletedCount f := by
  unfold satisfiedCount deletedClauses deletedCount
  rw [List.countP_eq_length_filter (p := deleted f)]
  exact List.countP_le_length

theorem evalClause_congr {a b : Assignment} {c : Clause} (h : ∀ l ∈ c, a l.var = b l.var) :
    evalClause a c = evalClause b c := by
  induction c with
  | nil => rfl
  | cons l c ih =>
    simp only [evalClause, List.any_cons] at ih ⊢
    rw [ih fun l' hl' => h l' (List.mem_cons_of_mem l hl')]
    have := h l List.mem_cons_self
    simp [evalLiteral, this]

/-! ## Restoring the eliminated variables -/

/-- The assignment `b` with every eliminated variable set to its pure value. -/
def extendPure (f : CNF) (b : Assignment) : Assignment :=
  fun v => if pureThree f v then pureValue f v else b v

theorem occurrences_pos_of_mem {f : CNF} {c : Clause} {l : Literal} (hc : c ∈ f) (hl : l ∈ c) :
    1 ≤ occurrences f l.var l.positive := by
  rw [occurrences_eq_count]
  exact List.count_pos_iff.mpr (List.mem_flatten.mpr ⟨c, hc, hl⟩)

/-- Every occurrence of an eliminated variable has its pure polarity. -/
theorem pureValue_of_mem {f : CNF} {c : Clause} {l : Literal} (hc : c ∈ f) (hl : l ∈ c)
    (hp : pureThree f l.var = true) : l.positive = pureValue f l.var := by
  have h1 := occurrences_pos_of_mem hc hl
  simp only [pureThree, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hp
  simp only [pureValue]
  rcases hp with ⟨h3, h0⟩ | ⟨h3, h0⟩
  · cases hpos : l.positive
    · rw [hpos] at h1; omega
    · simp [h3]
  · cases hpos : l.positive
    · simp [h0]
    · rw [hpos] at h1; omega

theorem evalClause_extendPure_kept (f : CNF) (b : Assignment) {c : Clause} (hc : c ∈ kept f) :
    evalClause (extendPure f b) c = evalClause b c := by
  apply evalClause_congr
  intro l hl
  have hkept := (List.mem_filter.mp hc).2
  simp only [Bool.not_eq_true', deleted, Bool.or_eq_false_iff, List.any_eq_false] at hkept
  have := hkept.2 l hl
  simp [extendPure, this]

theorem evalClause_extendPure_deleted (f : CNF) (b : Assignment) {c : Clause} (hc : c ∈ f)
    (hd : deleted f c = true) : evalClause (extendPure f b) c = true := by
  simp only [deleted, Bool.or_eq_true, List.any_eq_true] at hd
  rcases hd with hd | ⟨l, hl, hp⟩
  · exact tautological_eval hd _
  · simp only [evalClause, List.any_eq_true]
    refine ⟨l, hl, ?_⟩
    have hv := pureValue_of_mem hc hl hp
    simp only [evalLiteral, extendPure, hp, ↓reduceIte]
    cases hpos : l.positive <;> simp_all

theorem satisfiedCount_extendPure_deleted (f : CNF) (b : Assignment) :
    satisfiedCount (extendPure f b) (deletedClauses f) = deletedCount f := by
  unfold satisfiedCount deletedClauses deletedCount
  rw [List.countP_eq_length_filter (p := deleted f)]
  apply List.countP_eq_length.mpr
  intro c hc
  exact evalClause_extendPure_deleted f b (List.mem_filter.mp hc).1 (List.mem_filter.mp hc).2

theorem satisfiedCount_extendPure_kept (f : CNF) (b : Assignment) :
    satisfiedCount (extendPure f b) (kept f) = satisfiedCount b (kept f) := by
  unfold satisfiedCount
  apply List.countP_congr
  intro c hc
  rw [evalClause_extendPure_kept f b hc]

/-! ## Undoing the complementations -/

/-- The assignment `b` with the values of the variables selected by `F` complemented. -/
def flipAssign (F : Nat → Bool) (b : Assignment) : Assignment :=
  fun v => if F v then !(b v) else b v

theorem evalLiteral_flip (F : Nat → Bool) (b : Assignment) (l : Literal) :
    evalLiteral b (flipLiteral F l) = evalLiteral (flipAssign F b) l := by
  cases l with
  | mk x q =>
    simp only [evalLiteral, flipLiteral, flipAssign]
    cases hF : F x <;> cases q <;> simp

theorem evalClause_flip (F : Nat → Bool) (b : Assignment) (c : Clause) :
    evalClause b (c.map (flipLiteral F)) = evalClause (flipAssign F b) c := by
  simp [evalClause, List.any_map, Function.comp_def, evalLiteral_flip]

theorem satisfiedCount_flipFormula (F : Nat → Bool) (b : Assignment) (g : CNF) :
    satisfiedCount b (flipFormula F g) = satisfiedCount (flipAssign F b) g := by
  unfold satisfiedCount flipFormula
  rw [List.countP_map]
  apply List.countP_congr
  intro c _
  simp [evalClause_flip]

theorem flipAssign_flipAssign (F : Nat → Bool) (b : Assignment) : flipAssign F (flipAssign F b) = b := by
  funext v
  simp only [flipAssign]
  cases F v <;> simp

/-! ## The padding -/

theorem satisfiedCount_padding_le (b : Assignment) (base r : Nat) :
    satisfiedCount b (padding base r) ≤ r := by
  unfold satisfiedCount
  refine Nat.le_trans List.countP_le_length ?_
  simp [padding]

/-- The assignment `b` with every variable from `base` on set to true. -/
def padTrue (base : Nat) (b : Assignment) : Assignment := fun v => if base ≤ v then true else b v

theorem satisfiedCount_padTrue_padding (base r : Nat) (b : Assignment) :
    satisfiedCount (padTrue base b) (padding base r) = r := by
  unfold satisfiedCount
  have hlen : (padding base r).length = r := by simp [padding]
  calc (padding base r).countP (evalClause (padTrue base b)) = (padding base r).length := ?_
    _ = r := hlen
  apply List.countP_eq_length.mpr
  intro c hc
  simp only [padding, List.mem_map, List.mem_range] at hc
  obtain ⟨j, _, rfl⟩ := hc
  simp [evalClause, evalLiteral, padTrue]

theorem evalClause_padTrue {base : Nat} {c : Clause} (h : ∀ l ∈ c, l.var < base) (b : Assignment) :
    evalClause (padTrue base b) c = evalClause b c := by
  apply evalClause_congr
  intro l hl
  have := h l hl
  simp [padTrue, Nat.not_le.mpr this]

theorem satisfiedCount_padTrue_kept (f : CNF) (b : Assignment) :
    satisfiedCount (padTrue (variableBound f) b) (flipFormula (complemented f) (kept f)) =
      satisfiedCount b (flipFormula (complemented f) (kept f)) := by
  unfold satisfiedCount
  apply List.countP_congr
  intro c hc
  rw [evalClause_padTrue (fun l hl => variable_lt_of_mem_flipFormula_kept hc hl)]

/-! ## The L-reduction -/

/-- Recovering an assignment of `φ` from one of `φ'`: "undo the complementations and
restore the eliminated variables." -/
def recover (f : CNF) (b : Assignment) : Assignment := extendPure f (flipAssign (complemented f) b)

/-- "The recovered assignment satisfies all `r` deleted clauses and at least as many clauses
overall as the target assignment." -/
theorem satisfiedCount_recover (f : CNF) (b : Assignment) :
    satisfiedCount b (polarize f) ≤ satisfiedCount (recover f b) f := by
  rw [polarize, satisfiedCount_append, satisfiedCount_flipFormula, satisfiedCount_split (recover f b) f,
    recover, satisfiedCount_extendPure_deleted, satisfiedCount_extendPure_kept]
  have := satisfiedCount_padding_le b (variableBound f) (deletedCount f)
  omega

/-- Every assignment of `φ` yields one of `φ'` satisfying at least as many clauses. -/
theorem satisfiedCount_polarize_ge (f : CNF) (a : Assignment) :
    satisfiedCount a f ≤ satisfiedCount (padTrue (variableBound f) (flipAssign (complemented f) a)) (polarize f) := by
  rw [polarize, satisfiedCount_append, satisfiedCount_padTrue_kept, satisfiedCount_flipFormula,
    flipAssign_flipAssign, satisfiedCount_padTrue_padding, satisfiedCount_split a f]
  have := satisfiedCount_deleted_le a f
  omega

/-- `OPT(φ') = OPT(φ)`. -/
theorem polarize_maxSat_eq {f : CNF} {S S' : Nat} (hS : IsMaxSat f S) (hS' : IsMaxSat (polarize f) S') :
    S = S' := by
  obtain ⟨⟨a, ha⟩, hmax⟩ := hS
  obtain ⟨⟨b, hb⟩, hmax'⟩ := hS'
  have h1 := satisfiedCount_polarize_ge f a
  have h2 := hmax' (padTrue (variableBound f) (flipAssign (complemented f) a))
  have h3 := satisfiedCount_recover f b
  have h4 := hmax (recover f b)
  omega

/-- **Lemma 10**: the transformation is an L-reduction with `α = β = 1`. -/
theorem polarize_lreduction : LReductionSat ThreeOccurrence polarize 1 1 1 1 := by
  intro f _ S S' hS hS'
  have heq := polarize_maxSat_eq hS hS'
  refine ⟨by omega, ?_⟩
  intro b
  refine ⟨recover f b, ?_⟩
  have := satisfiedCount_recover f b
  omega

end STACS2027

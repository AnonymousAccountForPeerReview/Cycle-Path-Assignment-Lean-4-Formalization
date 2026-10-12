module

public import Runtimes.BoundedCost.AnnotatedNode
import Mathlib.Tactic

/-! Dense occurrence masks and literal-requirement tables used by the RAM search.
Equal clauses keep separate occurrence positions. -/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 Complexity.SAT

def activeOccurrences {α : Type*} : List (Bool × α) → List α
  | [] => []
  | (active, clause) :: rows =>
      if active then clause :: activeOccurrences rows else activeOccurrences rows

def disableOccurrence {α : Type*} : List (Bool × α) → ℕ → List (Bool × α)
  | [], _ => []
  | (_, clause) :: rows, 0 => (false, clause) :: rows
  | row :: rows, i + 1 => row :: disableOccurrence rows i

theorem disableOccurrence_length {α : Type*} (rows : List (Bool × α)) (i : ℕ) :
    (disableOccurrence rows i).length = rows.length := by
  induction rows generalizing i with
  | nil => rfl
  | cons row rows ih => cases i <;> simp [disableOccurrence, ih]

theorem activeOccurrences_disable_first {α : Type*} [DecidableEq α]
    (rows : List (Bool × α)) (i : ℕ) (clause : α)
    (hi : i < rows.length) (hrow : rows[i] = (true, clause))
    (hfirst : ∀ j, (hj : j < i) → rows[j]'(by omega) ≠ (true, clause)) :
    activeOccurrences (disableOccurrence rows i) = (activeOccurrences rows).erase clause := by
  induction rows generalizing i with
  | nil => simp at hi
  | cons row rows ih =>
    rcases row with ⟨active, head⟩
    cases i with
    | zero =>
      simp only [List.getElem_cons_zero, Prod.mk.injEq] at hrow
      rcases hrow with ⟨rfl, rfl⟩
      simp [disableOccurrence, activeOccurrences]
    | succ i =>
      have hi' : i < rows.length := by simpa using hi
      have hrow' : rows[i] = (true, clause) := by simpa using hrow
      have hf' : ∀ j, (hj : j < i) → rows[j]'(by omega) ≠ (true, clause) := by
        intro j hj
        simpa using hfirst (j + 1) (by omega)
      have hh : (active, head) ≠ (true, clause) := by
        simpa using hfirst 0 (by omega)
      have he := ih i hi' hrow' hf'
      cases active
      · simpa [disableOccurrence, activeOccurrences] using he
      · have hn : head ≠ clause := by simpa using hh
        simpa [disableOccurrence, activeOccurrences, hn] using congrArg (List.cons head) he

def literalOfCode (u : ℕ) : Literal := ⟨u / 2, u % 2 = 0⟩

theorem code_literalOfCode (u : ℕ) : TwoSat.code (literalOfCode u) = u := by
  by_cases h : u % 2 = 0 <;> simp [literalOfCode, TwoSat.code, h] <;> omega

theorem literalOfCode_code (l : Literal) : literalOfCode (TwoSat.code l) = l := by
  rcases l with ⟨x, sign⟩
  cases sign <;> simp [literalOfCode, TwoSat.code, show (2 * x + 1) % 2 = 1 by omega,
    show (2 * x + 1) / 2 = x by omega]

theorem evalLiteral_literalOfCode (σ : Assignment) (u : ℕ) :
    evalLiteral σ (literalOfCode u) = TwoSat.nodeVal σ u := by
  rw [← TwoSat.nodeVal_code, code_literalOfCode]

def denseRequirements (n : ℕ) (forced : ℕ → Bool) : List Literal :=
  ((List.range (2 * n)).filter forced).map literalOfCode

theorem denseRequirements_bounded (n : ℕ) (forced : ℕ → Bool) :
    ∀ l ∈ denseRequirements n forced, l.var < n := by
  intro l hl
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hl
  have hlt := List.mem_range.mp (List.mem_filter.mp hu).1
  change u / 2 < n
  omega

theorem requires_denseRequirements (σ : Assignment) (n : ℕ) (forced : ℕ → Bool) :
    Requires σ (denseRequirements n forced) ↔
      ∀ u < 2 * n, forced u = true → TwoSat.nodeVal σ u = true := by
  simp only [Requires, denseRequirements, List.mem_map, List.mem_filter, List.mem_range]
  constructor
  · intro h u hu hf
    simpa [evalLiteral_literalOfCode] using h (literalOfCode u) ⟨u, ⟨hu, hf⟩, rfl⟩
  · rintro h l ⟨u, ⟨hu, hf⟩, rfl⟩
    simpa [evalLiteral_literalOfCode] using h u hu hf

theorem requires_denseRequirements_force (σ : Assignment) (n : ℕ)
    (forced : ℕ → Bool) (u : ℕ) (hu : u < 2 * n) :
    Requires σ (denseRequirements n (Function.update forced u true)) ↔
      TwoSat.nodeVal σ u = true ∧ Requires σ (denseRequirements n forced) := by
  rw [requires_denseRequirements, requires_denseRequirements]
  constructor
  · intro h
    refine ⟨h u hu (by simp), ?_⟩
    intro v hv hf
    by_cases he : v = u
    · simpa [he] using h u hu (by simp)
    · exact h v hv (by simpa [Function.update_of_ne he] using hf)
  · rintro ⟨hu', h⟩ v hv hf
    by_cases he : v = u
    · simpa [he] using hu'
    · exact h v hv (by simpa [Function.update_of_ne he] using hf)

theorem requires_denseRequirements_force_literal (σ : Assignment) (n : ℕ)
    (forced : ℕ → Bool) (l : Literal) (hl : l.var < n) :
    Requires σ (denseRequirements n (Function.update forced (TwoSat.code l) true)) ↔
      Requires σ (l :: denseRequirements n forced) := by
  rw [requires_denseRequirements_force σ n forced _ (TwoSat.code_lt hl)]
  simp [Requires, TwoSat.nodeVal_code]

end STACS2027.Runtimes.BoundedCost

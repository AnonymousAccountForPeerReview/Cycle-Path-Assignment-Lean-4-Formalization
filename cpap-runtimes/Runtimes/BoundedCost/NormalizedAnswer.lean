module

public import Runtimes.BoundedCost.Iterative
import Mathlib.Tactic

/-!
# Normalized Almost 2-SAT answers

Scan clause positions and variable identifiers in increasing order.  The
result deletes exactly the false clause occurrences and lists exactly the
occurring variables set to true by the computed assignment.
-/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 Complexity.SAT

def occursInBool (f : CNF) (x : ℕ) : Bool :=
  f.any (fun c => c.any (fun l => l.var == x))

@[simp] theorem occursInBool_eq_true (f : CNF) (x : ℕ) :
    occursInBool f x = true ↔ OccursIn f x := by
  simp [occursInBool, OccursIn, List.any_eq_true]

def falseIndices (σ : Assignment) (f : CNF) : List ℕ :=
  (f.zipIdx.filter (fun e => !(evalClause σ e.1))).map Prod.snd

theorem falseIndices_pairwise (σ : Assignment) (f : CNF) :
    (falseIndices σ f).Pairwise (· < ·) := by
  apply List.Pairwise.sublist (List.filter_sublist.map Prod.snd)
  simpa only [List.zipIdx_map_snd, ← List.range_eq_range'] using
    (List.pairwise_lt_range (n := f.length))

theorem mem_falseIndices (σ : Assignment) (f : CNF) (i : ℕ) :
    i ∈ falseIndices σ f ↔ ∃ hi : i < f.length, evalClause σ f[i] = false := by
  constructor
  · intro hi
    obtain ⟨⟨c, j⟩, hmem, hji⟩ := List.mem_map.mp hi
    obtain ⟨hz, hc⟩ := List.mem_filter.mp hmem
    dsimp at hji
    subst j
    obtain ⟨hb, he⟩ := List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp hz)
    refine ⟨hb, ?_⟩
    rw [he]
    cases h : evalClause σ c <;> simp_all
  · rintro ⟨hi, hc⟩
    apply List.mem_map.mpr
    refine ⟨(f[i], i), List.mem_filter.mpr ⟨?_, ?_⟩, rfl⟩
    · exact List.mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem hi)
    · simpa only [hc] using (show (!false) = true from rfl)

theorem falseIndices_bounded (σ : Assignment) (f : CNF) :
    ∀ i ∈ falseIndices σ f, i < f.length :=
  fun i hi => (mem_falseIndices σ f i).mp hi |>.choose

@[simp] theorem falseIndices_length (σ : Assignment) (f : CNF) :
    (falseIndices σ f).length = unsatisfiedCount σ f := by
  unfold falseIndices unsatisfiedCount
  rw [List.length_map, ← List.countP_eq_length_filter]
  calc
    _ = List.countP (fun c => !(evalClause σ c)) (f.zipIdx.map Prod.fst) := by
      rw [List.countP_map]; rfl
    _ = _ := by rw [List.zipIdx_map_fst]

theorem falseIndices_as_filterRange (σ : Assignment) (f : CNF) :
    falseIndices σ f = (List.range f.length).filter
      (fun i => !(evalClause σ (f.getD i []))) := by
  apply (falseIndices_pairwise σ f).eq_of_mem_iff (List.pairwise_lt_range.filter _)
  intro i
  rw [mem_falseIndices]
  simp only [List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨hi, hfalse⟩
    refine ⟨hi, ?_⟩
    rw [← List.getElem_eq_getD (h := hi) [], hfalse]
    rfl
  · rintro ⟨hi, hfalse⟩
    refine ⟨hi, ?_⟩
    rw [← List.getElem_eq_getD (h := hi) []] at hfalse
    cases he : evalClause σ f[i] <;> simp_all

/-- The increasing deletion prefix used by the certificate scan. -/
def falseIndicesPrefix (σ : Assignment) (f : CNF) (n : ℕ) : List ℕ :=
  (List.range n).filter (fun i => !(evalClause σ (f.getD i [])))

@[simp] theorem falseIndicesPrefix_zero (σ : Assignment) (f : CNF) :
    falseIndicesPrefix σ f 0 = [] := rfl

theorem falseIndicesPrefix_succ (σ : Assignment) (f : CNF) (n : ℕ) :
    falseIndicesPrefix σ f (n + 1) = falseIndicesPrefix σ f n ++
      if evalClause σ (f.getD n []) then [] else [n] := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : evalClause σ (f[n]?.getD []) <;>
    simp [falseIndicesPrefix, List.range_succ, List.filter_append, h]

theorem occursInBool_iff_codes (f : CNF) (x : ℕ) :
    occursInBool f x = true ↔ 2 * x ∈ TwoSat.codes f ∨ 2 * x + 1 ∈ TwoSat.codes f := by
  rw [occursInBool_eq_true]
  constructor
  · rintro ⟨c, hc, l, hl, he⟩
    cases hp : l.positive
    · apply Or.inr
      apply List.mem_flatMap.mpr
      refine ⟨c, hc, List.mem_map.mpr ⟨l, hl, ?_⟩⟩
      simp [TwoSat.code, hp, he]
    · apply Or.inl
      apply List.mem_flatMap.mpr
      refine ⟨c, hc, List.mem_map.mpr ⟨l, hl, ?_⟩⟩
      simp [TwoSat.code, hp, he]
  · intro h
    rcases h with h | h
    · obtain ⟨c, hc, hcode⟩ := List.mem_flatMap.mp h
      obtain ⟨l, hl, he⟩ := List.mem_map.mp hcode
      refine ⟨c, hc, l, hl, ?_⟩
      change TwoSat.code l = 2 * x at he
      cases hp : l.positive <;> simp [TwoSat.code, hp] at he <;> omega
    · obtain ⟨c, hc, hcode⟩ := List.mem_flatMap.mp h
      obtain ⟨l, hl, he⟩ := List.mem_map.mp hcode
      refine ⟨c, hc, l, hl, ?_⟩
      change TwoSat.code l = 2 * x + 1 at he
      cases hp : l.positive <;> simp [TwoSat.code, hp] at he <;> omega

def trueVariables (n : ℕ) (f : CNF) (σ : Assignment) : List ℕ :=
  (List.range n).filter (fun x => σ x && occursInBool f x)

theorem trueVariables_pairwise (n : ℕ) (f : CNF) (σ : Assignment) :
    (trueVariables n f σ).Pairwise (· < ·) :=
  List.pairwise_lt_range.filter _

@[simp] theorem mem_trueVariables (n : ℕ) (f : CNF) (σ : Assignment) (x : ℕ) :
    x ∈ trueVariables n f σ ↔ x < n ∧ σ x = true ∧ OccursIn f x := by
  simp [trueVariables]

theorem trueVariables_occurring (n : ℕ) (f : CNF) (σ : Assignment) :
    ∀ x ∈ trueVariables n f σ, OccursIn f x :=
  fun x hx => ((mem_trueVariables n f σ x).mp hx).2.2

theorem trueVariables_agree {n : ℕ} {f : CNF} (hf : TwoSat.IsTwoCNF n f)
    (σ : Assignment) {x : ℕ} (hx : OccursIn f x) :
    decide (x ∈ trueVariables n f σ) = σ x := by
  obtain ⟨c, hc, l, hl, he⟩ := hx
  have hb : x < n := he ▸ (hf c hc).2 l hl
  have ho : OccursIn f x := ⟨c, hc, l, hl, he⟩
  cases hs : σ x <;> simp [mem_trueVariables, hs, hb, ho]

theorem evalClause_trueVariables {n : ℕ} {f : CNF} (hf : TwoSat.IsTwoCNF n f)
    (σ : Assignment) {c : Clause} (hc : c ∈ f) :
    evalClause (fun x => decide (x ∈ trueVariables n f σ)) c = evalClause σ c := by
  unfold evalClause
  have hm : c.map (evalLiteral (fun x => decide (x ∈ trueVariables n f σ))) =
      c.map (evalLiteral σ) := by
    apply List.map_congr_left
    intro l hl
    have ha := trueVariables_agree hf σ (show OccursIn f l.var from ⟨c, hc, l, hl, rfl⟩)
    simp only [evalLiteral, ha]
  have he := congrArg (fun bs : List Bool => bs.any id) hm
  simpa using he

def assignmentAnswer (f : CNF) (σ : Assignment) : List ℕ :=
  let D := falseIndices σ f
  let T := trueVariables (2 * f.length + 1) f σ
  1 :: D.length :: (D ++ T)

theorem assignmentAnswer_correct {f : CNF} (hf : SolverDomain f)
    {k : ℕ} {σ : Assignment} (hσ : unsatisfiedCount σ f ≤ k) :
    A2Answer f k (assignmentAnswer f σ) := by
  apply Or.inr
  refine ⟨falseIndices σ f, trueVariables (2 * f.length + 1) f σ, rfl,
    falseIndices_pairwise σ f, falseIndices_bounded σ f,
    by simpa using hσ, trueVariables_pairwise _ f σ, trueVariables_occurring _ f σ, ?_⟩
  intro i hi hkeep
  rw [evalClause_trueVariables hf σ (List.getElem_mem hi)]
  have hfalse : evalClause σ f[i] ≠ false := by
    intro h
    exact hkeep ((mem_falseIndices σ f i).mpr ⟨hi, h⟩)
  cases h : evalClause σ f[i] <;> simp_all

def searchAnswer (factory : LeastCutFactory) (f : CNF) (k : ℕ) : List ℕ :=
  match almostTwoSatSearch factory f k with
  | none => [0]
  | some σ => assignmentAnswer f σ

theorem searchAnswer_correct (factory : LeastCutFactory)
    (hfactory : LeastCutFactoryCorrect factory) {f : CNF} (hf : SolverDomain f) (k : ℕ) :
    A2Answer f k (searchAnswer factory f k) := by
  have hc := solverDomain_clauses2 hf
  cases hs : almostTwoSatSearch factory f k with
  | none =>
    simp only [searchAnswer, hs]
    apply Or.inl
    refine ⟨?_, rfl⟩
    intro h
    obtain ⟨σ, hσ⟩ := (almostTwoSatSearch_correct factory hfactory hc k).mpr h
    rw [hs] at hσ
    cases hσ
  | some σ =>
    simp only [searchAnswer, hs]
    apply assignmentAnswer_correct hf
    exact iterativeSearch_sound factory hfactory k f [] (fun _ => false)
      (by simpa using hc) (by simp) σ hs

end STACS2027.Runtimes.BoundedCost

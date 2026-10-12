module

public import Runtimes.ZeroCost
public import Outerplanar.RAM.BoundedAll
import Mathlib.Tactic

/-!
# Almost 2-SAT input, output, and verified solver interface

Theorem 4 applies the cited Almost 2-SAT result of ANONYMIZED and ANONYMIZED [RO09]
(JCSS 2009). `Almost2SatSolver` records its RAM input/output contract and
`FPTBound` the manuscript's fixed-parameter bound.

`Runtimes/BoundedCost/ActualCompilerRAM.lean` now instantiates this interface
with one fixed executed RAM program. It verifies iterative compression,
compression-vector and annotated-path enumeration, every least-cut call,
normalized certificate output, and the complete uniform resource bound. The
only algorithmic hypothesis is the external cited almost-linear flow contract
(`MinCostFlowSolver` and `AlmostLinear`). The theorem
`almostTwoSatFptSolverExists_of_citedFlow` proves the retained named construction
claim; `boundedCost_ram_fpt_from_citedFlow` closes the solver dependency of the
cycle-path assignment reduction. The manuscript's citations remain citations.

The input `a2In f Ψ` is `Ψ :: |f| :: codes f`. `SolverDomain` requires two
literals per clause and variable identifiers below `2|f|+1`. The output is `[0]`
when no deletion of at most `Ψ` clauses suffices, or
`1 :: |D| :: (D ++ T)` with sorted deleted clause positions and sorted occurring
true variables. `NormalizedAnswer` and `CertificateRAM` prove and execute this
normalization. In the cycle-path assignment pipeline variables are shifted by
one, so the returned true-variable list can be read up to its first zero cell.

The remaining facts below verify shifting and recovery: `codes_shiftF`,
`almostSatisfiable_shiftF`, `evalClause_shiftL`, and the kept-clause operations.
-/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 STACS2027.RAM Complexity.SAT

/-! ### Input and solver interface -/

/-- Every clause of `f` has exactly two literals. -/
def Clauses2 (f : CNF) : Prop := ∀ c ∈ f, c.length = 2

/-- The word-bounded input domain: two-literal clauses and variable identifiers
at most the number of literal occurrences.  The extra endpoint allows the
pipeline's one-based shifted variable numbering. -/
def SolverDomain (f : CNF) : Prop := TwoSat.IsTwoCNF (2 * f.length + 1) f

theorem solverDomain_clauses2 {f : CNF} (hf : SolverDomain f) : Clauses2 f :=
  fun c hc => (hf c hc).1

/-- The variable `x` occurs in `f`. -/
def OccursIn (f : CNF) (x : ℕ) : Prop := ∃ c ∈ f, ∃ l ∈ c, l.var = x

/-- **The input of the Almost 2-SAT solver**: `Ψ`, `m = |f|`, then the literal codes of the
clauses (`2v` for `x_v`, `2v + 1` for `¬x_v`), two per clause. -/
def a2In (f : CNF) (Ψ : ℕ) : List ℕ := Ψ :: f.length :: TwoSat.codes f

/-- **The answer of an Almost 2-SAT solver**: `[0]` if deleting at most `Ψ` clauses never makes
`f` satisfiable; otherwise `1`, `|D|`, the deleted clause positions `D` (increasing, below
`|f|`, at most `Ψ`) and the increasing list `T` of the variables (occurring in `f`) set to true,
such that setting exactly the variables of `T` to true satisfies every clause outside `D`. -/
def A2Answer (f : CNF) (Ψ : ℕ) (out : List ℕ) : Prop :=
  (¬ AlmostSatisfiable f Ψ ∧ out = [0]) ∨
    ∃ D T : List ℕ, out = 1 :: D.length :: (D ++ T) ∧
      D.Pairwise (· < ·) ∧ (∀ i ∈ D, i < f.length) ∧ D.length ≤ Ψ ∧
      T.Pairwise (· < ·) ∧ (∀ x ∈ T, OccursIn f x) ∧
      ∀ i (hi : i < f.length), i ∉ D → evalClause (fun x => decide (x ∈ T)) f[i] = true

/-- **The Almost 2-SAT RAM solver interface** ([RO09]): on `a2In f Ψ`, for any
formula `f` in `SolverDomain` and any `Ψ`, `F` halts within `T Ψ N` steps and the addresses
below `T Ψ N` (`N` the length of the input) with a correct answer (`A2Answer`). -/
def Almost2SatSolver (F : RAM.Stmt) (T : ℕ → ℕ → ℕ) : Prop :=
  ∀ (f : CNF) (Ψ : ℕ), SolverDomain f →
    ∃ (out : List ℕ) (steps : ℕ),
      RAM.ComputesIn F (a2In f Ψ) out steps (T Ψ (a2In f Ψ).length) ∧
      steps ≤ T Ψ (a2In f Ψ).length ∧ A2Answer f Ψ out

/-- **The manuscript's bound** `O(15^Ψ Ψ m³)` (for `Ψ ≥ 1`) in terms of the input length `N`:
`T Ψ N ≤ C 15^Ψ (Ψ + 1) (N + 1)³`. -/
def FPTBound (T : ℕ → ℕ → ℕ) : Prop :=
  ∃ C : ℕ, ∀ Ψ N : ℕ, T Ψ N ≤ C * 15 ^ Ψ * (Ψ + 1) * (N + 1) ^ 3

/-! ### Shifting the variables by one -/

/-- The literal on the next variable. -/
def shiftL (l : Literal) : Literal := ⟨l.var + 1, l.positive⟩

/-- The formula with every variable `v` renamed `v + 1`. -/
def shiftF (f : CNF) : CNF := f.map (List.map shiftL)

@[simp] theorem length_shiftF (f : CNF) : (shiftF f).length = f.length := by simp [shiftF]

theorem code_shiftL (l : Literal) : TwoSat.code (shiftL l) = TwoSat.code l + 2 := by
  rcases l with ⟨v, p⟩
  cases p <;> simp [TwoSat.code, shiftL] <;> omega

/-- The codes of the shifted formula are the codes plus `2`. -/
theorem codes_shiftF (f : CNF) : TwoSat.codes (shiftF f) = (TwoSat.codes f).map (· + 2) := by
  induction f with
  | nil => rfl
  | cons c f ih =>
    simp only [shiftF, TwoSat.codes, List.map_cons, List.flatMap_cons, List.map_append,
      List.map_map] at ih ⊢
    rw [← ih]
    congr 1
    apply List.map_congr_left
    intro l _
    simp [code_shiftL]

theorem evalClause_shiftL (σ : Assignment) (c : Clause) :
    evalClause σ (c.map shiftL) = evalClause (fun x => σ (x + 1)) c := by
  simp only [evalClause, evalLiteral, shiftL, List.any_map, Function.comp_def]
  rfl

theorem evalCNF_shiftF (σ : Assignment) (f : CNF) :
    evalCNF σ (shiftF f) = evalCNF (fun x => σ (x + 1)) f := by
  simp [evalCNF, shiftF, List.all_map, Function.comp_def, evalClause_shiftL]

theorem clauses2_shiftF {f : CNF} (h : Clauses2 f) : Clauses2 (shiftF f) := by
  intro c hc
  simp only [shiftF, List.mem_map] at hc
  obtain ⟨c', hc', rfl⟩ := hc
  simpa using h c' hc'

/-- A variable occurring in the shifted formula of a 2-CNF over `n` variables is in `[1, n]`. -/
theorem occursIn_shiftF {n : ℕ} {f : CNF} (hf : TwoSat.IsTwoCNF n f) {x : ℕ}
    (h : OccursIn (shiftF f) x) : 1 ≤ x ∧ x ≤ n := by
  obtain ⟨c, hc, l, hl, rfl⟩ := h
  simp only [shiftF, List.mem_map] at hc
  obtain ⟨c', hc', rfl⟩ := hc
  simp only [List.mem_map] at hl
  obtain ⟨l', hl', rfl⟩ := hl
  have := (hf c' hc').2 l' hl'
  simp only [shiftL]
  omega

/-- Almost satisfiability survives the renaming. -/
theorem almostSatisfiable_shiftF {f : CNF} {Ψ : ℕ} (h : AlmostSatisfiable f Ψ) :
    AlmostSatisfiable (shiftF f) Ψ := by
  obtain ⟨sub, hsub, hlen, σ, hσ⟩ := h
  refine ⟨shiftF sub, hsub.map _, by simpa using hlen, fun x => σ (x - 1), ?_⟩
  rw [evalCNF_shiftF]
  simpa using hσ

/-! ### The kept clauses -/

/-- The formula without the clauses at the positions `D`. -/
def keptOf (f : CNF) (D : List ℕ) : CNF :=
  (f.zipIdx.filter (fun e => decide (e.2 ∉ D))).map Prod.fst

theorem length_filter_range (g : ℕ → Bool) : ∀ m : ℕ,
    ((List.range m).filter g).length = ∑ i ∈ Finset.range m, if g i = true then 1 else 0
  | 0 => by simp
  | m + 1 => by
    rw [List.range_succ, List.filter_append, List.length_append, length_filter_range g m,
      Finset.sum_range_succ]
    by_cases h : g m = true <;> simp [h]

theorem card_filter_mem_range {D : List ℕ} (hD : D.Pairwise (· < ·)) {m : ℕ}
    (hDm : ∀ i ∈ D, i < m) : ((Finset.range m).filter (· ∈ D)).card = D.length := by
  rw [← List.toFinset_card_of_nodup hD.nodup]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range, List.mem_toFinset]
  exact ⟨fun h => h.2, fun h => ⟨hDm i h, h⟩⟩

theorem count_not_mem_range {D : List ℕ} (hD : D.Pairwise (· < ·)) {m : ℕ}
    (hDm : ∀ i ∈ D, i < m) :
    ((List.range m).filter (fun i => decide (i ∉ D))).length + D.length = m := by
  rw [length_filter_range, ← card_filter_mem_range hD hDm, Finset.card_filter,
    ← Finset.sum_add_distrib]
  have : ∀ i ∈ Finset.range m, ((if decide (i ∉ D) = true then 1 else 0) +
      (if i ∈ D then 1 else 0)) = 1 := by
    intro i _
    by_cases h : i ∈ D <;> simp [h]
  rw [Finset.sum_congr rfl this]
  simp

theorem keptOf_sublist (f : CNF) (D : List ℕ) : (keptOf f D).Sublist f := by
  have := ((List.filter_sublist (p := fun e : Clause × ℕ => decide (e.2 ∉ D))
    (l := f.zipIdx)).map Prod.fst)
  rwa [List.zipIdx_map_fst] at this

theorem keptOf_length {f : CNF} {D : List ℕ} (hD : D.Pairwise (· < ·))
    (hDm : ∀ i ∈ D, i < f.length) : (keptOf f D).length + D.length = f.length := by
  unfold keptOf
  rw [List.length_map, ← List.countP_eq_length_filter, ← count_not_mem_range hD hDm,
    ← List.countP_eq_length_filter, List.range_eq_range', ← List.length_zipIdx (i := 0),
    ← List.zipIdx_map_snd, List.countP_map, List.length_zipIdx]
  rfl

theorem mem_keptOf {f : CNF} {D : List ℕ} {c : Clause} (hc : c ∈ keptOf f D) :
    ∃ i, ∃ hi : i < f.length, i ∉ D ∧ c = f[i] := by
  unfold keptOf at hc
  obtain ⟨⟨c', i⟩, he, rfl⟩ := List.mem_map.1 hc
  obtain ⟨he, hi⟩ := List.mem_filter.1 he
  have := List.mem_zipIdx_iff_getElem?.1 he
  obtain ⟨hil, hget⟩ := List.getElem?_eq_some_iff.1 this
  exact ⟨i, hil, by simpa using hi, hget.symm⟩

theorem evalCNF_keptOf {f : CNF} {D : List ℕ} {σ : Assignment}
    (h : ∀ i (hi : i < f.length), i ∉ D → evalClause σ f[i] = true) :
    evalCNF σ (keptOf f D) = true := by
  unfold evalCNF
  rw [List.all_eq_true]
  intro c hc
  obtain ⟨i, hi, hiD, rfl⟩ := mem_keptOf hc
  exact h i hi hiD

/-! ### Reading an answer for `Γ'` -/

/-- A strictly increasing list of numbers in `[1, n]` has at most `n` entries. -/
theorem length_le_of_pairwise {T : List ℕ} {n : ℕ} (hT : T.Pairwise (· < ·))
    (hb : ∀ x ∈ T, 1 ≤ x ∧ x ≤ n) : T.length ≤ n := by
  have h1 : T.toFinset ⊆ Finset.Icc 1 n := fun x hx => by
    rw [List.mem_toFinset] at hx
    exact Finset.mem_Icc.mpr (hb x hx)
  have := Finset.card_le_card h1
  rw [List.toFinset_card_of_nodup hT.nodup, Nat.card_Icc] at this
  omega

/-- **A negative answer for the shifted `Γ'`**: no assignment of cost at most `Ψ`. -/
theorem noAssignment_of_shift {g : Graph} {k Ψ : ℕ} (hk : 4 ≤ k)
    (h : ¬ AlmostSatisfiable (shiftF (almostFormula g k Ψ)) Ψ) : ¬ HasAssignment g k Ψ :=
  fun hA => h (almostSatisfiable_shiftF ((almostSatisfiable_iff_hasAssignment hk g Ψ).mpr hA))

/-- **A positive answer for the shifted `Γ'`**: the assignment `x ↦ (x + 1 ∈ T)` satisfies
`Γ_𝓘` for the deleted overlaps `𝓘` (at most `Ψ` of them). -/
theorem permitted_of_shift {g : Graph} {k Ψ : ℕ} {D T : List ℕ}
    (hD : D.Pairwise (· < ·)) (hDm : ∀ i ∈ D, i < (shiftF (almostFormula g k Ψ)).length)
    (hDl : D.length ≤ Ψ)
    (hs : ∀ i (hi : i < (shiftF (almostFormula g k Ψ)).length), i ∉ D →
      evalClause (fun x => decide (x ∈ T)) (shiftF (almostFormula g k Ψ))[i] = true) :
    ∃ I : List (ℕ × ℕ × Edge), I.length ≤ Ψ ∧
      evalCNF (fun x => decide (x + 1 ∈ T)) (permittedFormula g k I) = true := by
  set f := almostFormula g k Ψ
  have hDm' : ∀ i ∈ D, i < f.length := fun i hi => by simpa using hDm i hi
  have hk : ∀ i (hi : i < f.length), i ∉ D → evalClause (fun x => decide (x + 1 ∈ T)) f[i] = true :=
    fun i hi hiD => by
      have := hs i (by simpa using hi) hiD
      simp only [shiftF, List.getElem_map] at this
      rwa [evalClause_shiftL] at this
  have hlen := keptOf_length hD hDm'
  have hfl : f.length = (almostFormula g k Ψ).length := rfl
  obtain ⟨hI, hσ⟩ := deletedOverlaps_spec g k Ψ (keptOf f D) (keptOf_sublist f D) (by omega)
  exact ⟨_, hI, hσ _ (evalCNF_keptOf hk)⟩

end STACS2027.Runtimes.BoundedCost

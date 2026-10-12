module

public import BoundedCost.Algorithm3Recovery

/-!
# Theorem 4: the encodings are correct

`Γ_𝓘` is satisfiable exactly when some assignment has all its overlaps in `𝓘`
(`permittedFormula_satisfiable_iff`), and Almost 2-SAT accepts `(Γ', Ψ)` exactly
when an assignment of cost at most `Ψ` exists (`almostSatisfiable_iff_hasAssignment`),
for every `k ≥ 4`. The directions from formulas to assignments are the explicit steps of
Algorithm 3 (`BoundedCost.Algorithm3Recovery`): the deleted overlaps and the recovered paths.
-/

@[expose] public section
namespace STACS2027
open Complexity.SAT

/-! ## Decoding and encoding assignments -/

/-- The omitted-vertex indices of paths `f` (`0` beyond the cycles). -/
noncomputable def omittedIndex {g : Graph} {k : Nat} {f : Nat → List Edge} (hf : PathsOf g k f) (i : Nat) : Nat :=
  if h : i < (cycles g k).length then Classical.choose (hf i h) else 0

theorem omittedIndex_spec {g : Graph} {k : Nat} {f : Nat → List Edge} (hf : PathsOf g k f) {i : Nat}
    (hi : i < (cycles g k).length) :
    omittedIndex hf i < k ∧ f i = selected (kCycle g k i) (omittedIndex hf i) := by
  unfold omittedIndex
  simp only [hi, ↓reduceDIte]
  exact Classical.choose_spec (hf i hi)

/-- The overlap constraint of a candidate overlap, under the omission variables of paths `f`:
true iff some path omits the edge. -/
theorem evalClause_overlapClause {g : Graph} {k : Nat} {f : Nat → List Edge} (_hf : PathsOf g k f)
    {u : Nat × Nat × Edge} (hu : u ∈ candidateOverlaps g k) :
    evalClause (assignmentOf g k f) (overlapClause g k u) = true ↔ violatedBy f u = false := by
  obtain ⟨i, i', e, hlt, hi', he, he', rfl⟩ := (mem_candidateOverlaps g k u).mp hu
  have hi : i < (cycles g k).length := by omega
  unfold overlapClause
  rw [evalClause_two_pos]
  simp only [edgeVariable]
  rw [assignmentOf_pathVariable_iff g f i (edgePosition_lt hi he),
    assignmentOf_pathVariable_iff g f i' (edgePosition_lt hi' he'),
    cycleEdgeAt_edgePosition hi he, cycleEdgeAt_edgePosition hi' he']
  simp only [violatedBy, Bool.and_eq_false_iff, contains_eq_false_iff]

/-! ## `Γ_𝓘` -/

/-- `Γ_𝓘` is satisfiable iff some assignment has all its overlaps in `𝓘`. -/
theorem permittedFormula_satisfiable_iff {g : Graph} {k : Nat} (hk : 4 ≤ k)
    (permitted : List (Nat × Nat × Edge)) :
    Satisfiable (permittedFormula g k permitted) ↔
      ∃ f : Nat → List Edge, PathsOf g k f ∧
        ∀ u ∈ candidateOverlaps g k, violatedBy f u = true → u ∈ permitted := by
  constructor
  · rintro ⟨σ, hσ⟩
    rw [evalCNF_iff] at hσ
    exact ⟨recoveredPath g k σ, recoveredPath_pathsOf g (by omega) σ,
      recoveredPath_permitted hk g permitted σ hσ⟩
  · rintro ⟨f, hf, hperm⟩
    refine ⟨assignmentOf g k f, ?_⟩
    rw [evalCNF_iff]
    intro cl hcl
    simp only [permittedFormula, List.mem_append, List.mem_map, List.mem_filter] at hcl
    rcases hcl with hcl | ⟨u, ⟨hu, hnot⟩, rfl⟩
    · exact pathConstraints_satisfied g f (omittedIndex hf) (fun i hi => omittedIndex_spec hf hi) cl hcl
    · rw [evalClause_overlapClause hf hu]
      cases hv : violatedBy f u
      · rfl
      · exfalso
        have := hperm u hu hv
        simp [this] at hnot

/-! ## Almost 2-SAT -/

theorem almostFormula_length (g : Graph) (k Ψ : Nat) :
    (almostFormula g k Ψ).length =
      (Ψ + 1) * (pathConstraints g k).length + (candidateOverlaps g k).length := by
  simp [almostFormula]

theorem mem_almostFormula (g : Graph) (k Ψ : Nat) (cl : Clause) :
    cl ∈ almostFormula g k Ψ ↔
      cl ∈ pathConstraints g k ∨ ∃ u ∈ candidateOverlaps g k, cl = overlapClause g k u := by
  simp only [almostFormula, List.mem_append, mem_flatten_replicate, List.mem_map]
  constructor
  · rintro (⟨_, h⟩ | ⟨u, hu, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨u, hu, rfl⟩
  · rintro (h | ⟨u, hu, rfl⟩)
    · exact Or.inl ⟨by omega, h⟩
    · exact Or.inr ⟨u, hu, rfl⟩

/-- **Theorem 4**, the encoding: Almost 2-SAT accepts `(Γ', Ψ)` iff an assignment of cost at
most `Ψ` exists. -/
theorem almostSatisfiable_iff_hasAssignment {k : Nat} (hk : 4 ≤ k) (g : Graph) (Ψ : Nat) :
    AlmostSatisfiable (almostFormula g k Ψ) Ψ ↔ HasAssignment g k Ψ := by
  constructor
  · -- the steps of Algorithm 3: the deleted overlaps, then the recovered paths
    rintro ⟨sub, hsub, hlen, σ, hσ⟩
    obtain ⟨hI, hσI⟩ := deletedOverlaps_spec g k Ψ sub hsub hlen
    obtain ⟨hv, hc⟩ := recoverAssignment_correct hk g _ σ (hσI σ hσ)
    exact ⟨_, hv, Nat.le_trans hc hI⟩
  · rintro ⟨ps, hv, hc⟩
    obtain ⟨hf, hps⟩ := pathsOf_of_validChoices hv
    rw [hps, cost_eq_countP_violated g k hf] at hc
    refine ⟨(List.replicate (Ψ + 1) (pathConstraints g k)).flatten ++
      ((candidateOverlaps g k).filter fun u => !violatedBy (fun i => ps.getD i []) u).map (overlapClause g k),
      ?_, ?_, ?_⟩
    · exact (List.Sublist.refl _).append (List.filter_sublist.map _)
    · rw [almostFormula_length, List.length_append, length_flatten_replicate, List.length_map]
      have := List.length_eq_countP_add_countP (violatedBy fun i => ps.getD i [])
        (l := candidateOverlaps g k)
      have hc' : (candidateOverlaps g k).countP (fun a => ¬ violatedBy (fun i => ps.getD i []) a = true) =
          ((candidateOverlaps g k).filter fun u => !violatedBy (fun i => ps.getD i []) u).length := by
        rw [List.countP_eq_length_filter]
        apply congrArg List.length
        apply List.filter_congr
        intro x _; simp
      omega
    · refine ⟨assignmentOf g k (fun i => ps.getD i []), ?_⟩
      rw [evalCNF_iff]
      intro cl hcl
      simp only [List.mem_append, mem_flatten_replicate, List.mem_map, List.mem_filter] at hcl
      rcases hcl with ⟨_, hcl⟩ | ⟨u, ⟨hu, hnot⟩, rfl⟩
      · exact pathConstraints_satisfied g _ (omittedIndex hf) (fun i hi => omittedIndex_spec hf hi) cl hcl
      · rw [evalClause_overlapClause hf hu]
        simpa using hnot

end STACS2027

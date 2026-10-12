module

public import BoundedCost.Tools

/-!
# Algorithm 3: the deleted overlaps and the recovery of the paths

After the Almost 2-SAT call on `(Γ', Ψ)` returns a deletion set `𝒟`, Algorithm 3 takes the
permitted overlaps `𝓘 = {u ∈ 𝒰 : λ_u is deleted by 𝒟}`, solves `Γ_𝓘` by 2-SAT (for `Ψ = 0`
it solves `Γ_∅` directly), and recovers an assignment from the truth assignment `σ` by its
last loop: for each cycle `C`, the marked edges `W_C = {e ∈ E(C) : σ(b_{C,e})}`, a vertex
`ρ(C) ∈ V(C)` with `W_C ⊆ E(C, ρ(C))`, and the path `τ(C) = E(C) \ E(C, ρ(C))`.

The steps are the computable functions `deletedOverlaps`, `markedEdges`, `omittedPosition`
(`ρ(C)` is the first vertex of `C` that works), `omittedVertex`, `recoveredPath` and
`recoverAssignment`. For `k ≥ 4`:

* `deletedOverlaps_spec`: if Almost 2-SAT keeps the clauses `kept` of `Γ'`, deleting at most
  `Ψ` of them, then `|𝓘| ≤ Ψ` and every truth assignment satisfying `kept` satisfies `Γ_𝓘`;
* `recoveredPath_spec`: if `σ` satisfies `Γ₁`, then `ρ(C)` is a vertex of `C`, it is incident
  to every marked edge, and `τ(C)` consists of the edges of `C` not incident to it;
* `recoverAssignment_correct`: if `σ` satisfies `Γ_𝓘`, the recovered paths are a cycle-path
  assignment (one of the options of each cycle, in the format of Section 5) of cost at most
  `|𝓘|`; its overlaps all lie in `𝓘` (`recoveredPath_permitted`).

These are the arguments of Appendix B's proof of Theorem 4; `BoundedCost.Equivalence` derives the
encoding theorems from them.
-/

@[expose] public section
namespace STACS2027
open Complexity.SAT

/-- `W_C` for `C = C_i`: the edges of `C_i` marked for omission by the truth assignment `σ`,
the `e` with `b_{C_i,e}` true. -/
def markedEdges (g : Graph) (k : Nat) (σ : Assignment) (i : Nat) : List Edge :=
  (cycleEdges (kCycle g k i)).filter fun e => σ (edgeVariable g k i e)

/-- `e ∈ E(C, v)`: the edge `e` is incident to the vertex `v`. -/
def incident (v : Nat) (e : Edge) : Bool :=
  e.1 == v || e.2 == v

/-- The position of `ρ(C_i)` on `C_i`: the first `i₀ < k` whose vertex `c_{i₀}` is incident to
every marked edge, `W_{C_i} ⊆ E(C_i, c_{i₀})` (`0` if there is none). -/
def omittedPosition (g : Graph) (k : Nat) (σ : Assignment) (i : Nat) : Nat :=
  ((List.range k).find? fun i₀ =>
    (markedEdges g k σ i).all (incident ((kCycle g k i).getD i₀ 0))).getD 0

/-- `ρ(C_i)`: the vertex of `C_i` at the position `omittedPosition g k σ i`. -/
def omittedVertex (g : Graph) (k : Nat) (σ : Assignment) (i : Nat) : Nat :=
  (kCycle g k i).getD (omittedPosition g k σ i) 0

/-- `τ(C_i) = E(C_i) \ E(C_i, ρ(C_i))`: the path of `k − 2` edges of `C_i` that omits the
vertex `ρ(C_i)`, as the option `selected (C_i) i₀` of Section 5. -/
def recoveredPath (g : Graph) (k : Nat) (σ : Assignment) (i : Nat) : List Edge :=
  selected (kCycle g k i) (omittedPosition g k σ i)

/-- Algorithm 3's last loop: the recovered paths `τ(C)` of all cycles `C ∈ 𝒞_k`, in the order
of `cycles g k`. -/
def recoverAssignment (g : Graph) (k : Nat) (σ : Assignment) : List (List Edge) :=
  (List.range (cycles g k).length).map (recoveredPath g k σ)

/-- `𝓘 = {u ∈ 𝒰 : λ_u is deleted by 𝒟}`: the candidate overlaps whose overlap constraint is
not among the clauses `kept` of `Γ'` that a solution `𝒟` of Almost 2-SAT keeps. -/
def deletedOverlaps (g : Graph) (k : Nat) (kept : CNF) : List (Nat × Nat × Edge) :=
  (candidateOverlaps g k).filter fun u => !kept.contains (overlapClause g k u)

/-! ## The omitted vertex -/

theorem omittedPosition_lt (g : Graph) {k : Nat} (hk : 0 < k) (σ : Assignment) (i : Nat) :
    omittedPosition g k σ i < k := by
  unfold omittedPosition
  cases h : (List.range k).find? fun i₀ =>
      (markedEdges g k σ i).all (incident ((kCycle g k i).getD i₀ 0)) with
  | none => exact hk
  | some i₀ => exact List.mem_range.mp (List.mem_of_find?_eq_some h)

/-- The recovered paths are paths of the cycles: `τ(C_i)` is the option omitting `ρ(C_i)`. -/
theorem recoveredPath_pathsOf (g : Graph) {k : Nat} (hk : 0 < k) (σ : Assignment) :
    PathsOf g k (recoveredPath g k σ) :=
  fun i _ => ⟨omittedPosition g k σ i, omittedPosition_lt g hk σ i, rfl⟩

theorem incident_eq_false_iff (v : Nat) (e : Edge) : incident v e = false ↔ e.1 ≠ v ∧ e.2 ≠ v := by
  simp [incident]

/-- The path omitting the vertex at position `i₀` consists of the edges of the cycle not
incident to that vertex. -/
theorem mem_selected_iff_incident {g : Graph} {k : Nat} {c : Cycle} (hc : IsCycle g k c)
    {i₀ : Nat} (hi₀ : i₀ < c.length) (e : Edge) :
    e ∈ selected c i₀ ↔ e ∈ cycleEdges c ∧ incident (c.getD i₀ 0) e = false := by
  rw [(selected_perm_selectedAt hc hi₀).mem_iff, selectedAt_mem, incident_eq_false_iff]
  have : c[i₀] = c.getD i₀ 0 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi₀]; rfl
  rw [this]

theorem mem_markedEdges (g : Graph) (k : Nat) (σ : Assignment) (i : Nat) (e : Edge) :
    e ∈ markedEdges g k σ i ↔ e ∈ cycleEdges (kCycle g k i) ∧ σ (edgeVariable g k i e) = true := by
  simp [markedEdges]

/-- If `σ` satisfies `Γ₁` (and `k ≥ 4`), the omitted vertex is incident to every marked edge:
`W_C ⊆ E(C, ρ(C))`. -/
theorem omittedVertex_incident {k : Nat} (hk : 4 ≤ k) (g : Graph) (σ : Assignment)
    (hσ : ∀ cl ∈ pathConstraints g k, evalClause σ cl = true) {i : Nat}
    (hi : i < (cycles g k).length) :
    ∀ e ∈ markedEdges g k σ i, incident (omittedVertex g k σ i) e = true := by
  have hc := kCycle_isCycle g hi
  let P : Nat → Bool := fun i₀ => (markedEdges g k σ i).all (incident ((kCycle g k i).getD i₀ 0))
  -- the vertex given by `decode_of_satisfied` works
  obtain ⟨i₀, hi₀, hdec⟩ := decode_of_satisfied g hk σ hσ hi
  have hP : P i₀ = true := by
    simp only [P, List.all_eq_true]
    intro e he
    obtain ⟨hec, hσe⟩ := (mem_markedEdges g k σ i e).mp he
    have hpos := edgePosition_lt hi hec
    have hnot := hdec _ hpos hσe
    rw [cycleEdgeAt_edgePosition hi hec, mem_selected_iff_incident hc (by rw [hc.2.1]; exact hi₀)] at hnot
    cases h : incident ((kCycle g k i).getD i₀ 0) e
    · exact absurd ⟨hec, h⟩ hnot
    · rfl
  -- so the search finds a vertex, and that vertex works
  have hsome : ((List.range k).find? P).isSome = true :=
    List.find?_isSome.mpr ⟨i₀, List.mem_range.mpr hi₀, hP⟩
  obtain ⟨i₁, h₁⟩ := Option.isSome_iff_exists.mp hsome
  have hP₁ : P i₁ = true := List.find?_some h₁
  have hpos : omittedPosition g k σ i = i₁ := by
    show ((List.range k).find? P).getD 0 = i₁
    rw [h₁]; rfl
  intro e he
  unfold omittedVertex
  rw [hpos]
  exact List.all_eq_true.mp hP₁ e he

/-- If `σ` satisfies `Γ₁` (and `k ≥ 4`), the recovered path of `C_i` omits every edge marked
for omission. -/
theorem recoveredPath_omits {k : Nat} (hk : 4 ≤ k) (g : Graph) (σ : Assignment)
    (hσ : ∀ cl ∈ pathConstraints g k, evalClause σ cl = true) :
    ∀ i, i < (cycles g k).length → ∀ e ∈ cycleEdges (kCycle g k i),
      σ (edgeVariable g k i e) = true → e ∉ recoveredPath g k σ i := by
  intro i hi e he hσe hmem
  have hc := kCycle_isCycle g hi
  have hlt : omittedPosition g k σ i < (kCycle g k i).length := by
    rw [hc.2.1]; exact omittedPosition_lt g (by omega) σ i
  have hinc := omittedVertex_incident hk g σ hσ hi e ((mem_markedEdges g k σ i e).mpr ⟨he, hσe⟩)
  have := ((mem_selected_iff_incident hc hlt e).mp hmem).2
  unfold omittedVertex at hinc
  rw [hinc] at this
  cases this

/-- **Algorithm 3, the recovery loop**: if `σ` satisfies the path constraints `Γ₁` (and
`k ≥ 4`), then for every cycle `C = C_i` the chosen `ρ(C)` is a vertex of `C` with
`W_C ⊆ E(C, ρ(C))`, and the recovered path is `τ(C) = E(C) \ E(C, ρ(C))`. -/
theorem recoveredPath_spec {k : Nat} (hk : 4 ≤ k) (g : Graph) (σ : Assignment)
    (hσ : evalCNF σ (pathConstraints g k) = true) {i : Nat} (hi : i < (cycles g k).length) :
    omittedVertex g k σ i ∈ kCycle g k i ∧
      (∀ e ∈ markedEdges g k σ i, incident (omittedVertex g k σ i) e = true) ∧
      ∀ e, e ∈ recoveredPath g k σ i ↔
        e ∈ cycleEdges (kCycle g k i) ∧ incident (omittedVertex g k σ i) e = false := by
  have hc := kCycle_isCycle g hi
  have hlt : omittedPosition g k σ i < (kCycle g k i).length := by
    rw [hc.2.1]; exact omittedPosition_lt g (by omega) σ i
  refine ⟨getD_mem _ _ hlt, omittedVertex_incident hk g σ ((evalCNF_iff σ _).mp hσ) hi, ?_⟩
  intro e
  exact mem_selected_iff_incident hc hlt e

/-! ## The recovered assignment -/

/-- If `σ` satisfies `Γ_𝓘` (and `k ≥ 4`), every overlap of the recovered paths is permitted. -/
theorem recoveredPath_permitted {k : Nat} (hk : 4 ≤ k) (g : Graph)
    (permitted : List (Nat × Nat × Edge)) (σ : Assignment)
    (hσ : ∀ cl ∈ permittedFormula g k permitted, evalClause σ cl = true) :
    ∀ u ∈ candidateOverlaps g k, violatedBy (recoveredPath g k σ) u = true → u ∈ permitted := by
  simp only [permittedFormula, List.mem_append, List.mem_map, List.mem_filter] at hσ
  have hpath : ∀ cl ∈ pathConstraints g k, evalClause σ cl = true :=
    fun cl hcl => hσ cl (Or.inl hcl)
  intro u hu hviol
  apply Classical.byContradiction
  intro hnot
  have hcl := hσ (overlapClause g k u) (Or.inr ⟨u, ⟨hu, by simpa using hnot⟩, rfl⟩)
  obtain ⟨i, i', e, hlt, hi', he, he', rfl⟩ := (mem_candidateOverlaps g k u).mp hu
  have hi : i < (cycles g k).length := by omega
  unfold overlapClause at hcl
  rw [evalClause_two_pos] at hcl
  simp only [violatedBy, List.contains_iff_mem, Bool.and_eq_true] at hviol
  rcases hcl with h | h
  · exact recoveredPath_omits hk g σ hpath i hi e he h hviol.1
  · exact recoveredPath_omits hk g σ hpath i' hi' e he' h hviol.2

/-- **Algorithm 3, path recovery**: from any truth assignment `σ` satisfying `Γ_𝓘` (the path
constraints and the overlap constraints outside `𝓘`), the recovered paths form a cycle-path
assignment of cost at most `|𝓘|` (for `k ≥ 4`). -/
theorem recoverAssignment_correct {k : Nat} (hk : 4 ≤ k) (g : Graph)
    (permitted : List (Nat × Nat × Edge)) (σ : Assignment)
    (hσ : evalCNF σ (permittedFormula g k permitted) = true) :
    ValidChoices ((cycles g k).map selectedOptions) (recoverAssignment g k σ) ∧
      cost (recoverAssignment g k σ) ≤ permitted.length := by
  have hf := recoveredPath_pathsOf g (by omega : 0 < k) σ
  have hperm := recoveredPath_permitted hk g permitted σ ((evalCNF_iff σ _).mp hσ)
  refine ⟨validChoices_of_pathsOf hf, ?_⟩
  unfold recoverAssignment
  rw [cost_eq_countP_violated g k hf, List.countP_eq_length_filter]
  apply List.Nodup.length_le_of_subset
  · exact List.filter_sublist.nodup (candidateOverlaps_nodup g k)
  · intro u hu
    have := List.mem_filter.mp hu
    exact hperm u this.1 this.2

/-! ## The overlaps deleted by Almost 2-SAT -/

/-- **Algorithm 3, the permitted overlaps**: if Almost 2-SAT keeps the clauses `kept` of `Γ'`,
deleting at most `Ψ` clause occurrences, then the candidate overlaps `𝓘` whose constraint is
deleted number at most `Ψ`, and every truth assignment satisfying `kept` satisfies `Γ_𝓘`. -/
theorem deletedOverlaps_spec (g : Graph) (k Ψ : Nat) (kept : CNF)
    (hsub : kept.Sublist (almostFormula g k Ψ))
    (hlen : (almostFormula g k Ψ).length ≤ kept.length + Ψ) :
    (deletedOverlaps g k kept).length ≤ Ψ ∧
      ∀ σ : Assignment, evalCNF σ kept = true →
        evalCNF σ (permittedFormula g k (deletedOverlaps g k kept)) = true := by
  constructor
  · -- at most `Ψ` overlap constraints are missing from `kept`
    obtain ⟨s₁, s₂, rfl, hs₁, hs₂⟩ := List.sublist_append_iff.mp hsub
    have h1 : (deletedOverlaps g k (s₁ ++ s₂)).length ≤
        ((candidateOverlaps g k).map (overlapClause g k)).countP fun cl => !s₂.contains cl := by
      rw [deletedOverlaps, ← List.countP_eq_length_filter, List.countP_map]
      apply List.countP_mono_left
      intro u _ hu
      simp only [Function.comp_def, Bool.not_eq_true', contains_eq_false_iff]
      simp only [Bool.not_eq_true', contains_eq_false_iff, List.mem_append, not_or] at hu
      exact hu.2
    have h2 : ((candidateOverlaps g k).map (overlapClause g k)).countP (fun cl => !s₂.contains cl) +
        ((candidateOverlaps g k).map (overlapClause g k)).countP (fun cl => s₂.contains cl) =
        ((candidateOverlaps g k).map (overlapClause g k)).length := by
      have := List.length_eq_countP_add_countP (fun cl => s₂.contains cl)
        (l := (candidateOverlaps g k).map (overlapClause g k))
      have hc : ((candidateOverlaps g k).map (overlapClause g k)).countP
          (fun a => ¬ s₂.contains a = true) =
          ((candidateOverlaps g k).map (overlapClause g k)).countP (fun cl => !s₂.contains cl) := by
        apply List.countP_congr; intro x _; simp
      omega
    have h3 := Sublist.length_le_countP_contains hs₂
    have h4 := hs₁.length_le
    rw [List.length_append] at hlen
    unfold almostFormula at hlen
    rw [List.length_append] at hlen
    omega
  · intro σ hσ
    rw [evalCNF_iff] at hσ ⊢
    intro cl hcl
    simp only [permittedFormula, List.mem_append, List.mem_map, List.mem_filter] at hcl
    rcases hcl with hcl | ⟨u, ⟨hu, hnot⟩, rfl⟩
    · -- every path constraint survives the deletion of at most `Ψ` clauses
      apply hσ
      have hcount := Sublist.count_add_le hsub cl
      have hΓ : (almostFormula g k Ψ).count cl ≥ Ψ + 1 := by
        unfold almostFormula
        rw [List.count_append, count_flatten_replicate]
        have h1 : (pathConstraints g k).count cl ≥ 1 := List.count_pos_iff.mpr hcl
        have h2 : (Ψ + 1) * (pathConstraints g k).count cl ≥ (Ψ + 1) * 1 :=
          Nat.mul_le_mul_left (Ψ + 1) h1
        omega
      have hpos : kept.count cl ≥ 1 := by omega
      exact List.count_pos_iff.mp hpos
    · -- a candidate overlap outside `𝓘` keeps its constraint
      apply hσ
      apply Classical.byContradiction
      intro hout
      have : u ∈ deletedOverlaps g k kept :=
        List.mem_filter.mpr ⟨hu, by simpa using hout⟩
      simp [this] at hnot

end STACS2027

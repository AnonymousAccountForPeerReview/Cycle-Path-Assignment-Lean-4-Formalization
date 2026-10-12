module

public import BoundedCost.CyclePositions

/-!
# The path constraints `Γ₁`

Marking the two edges omitted by a path satisfies `Γ₁`, since they share the omitted
vertex. Conversely (for `k ≥ 4`), a truth assignment satisfying `Γ₁` marks, on each
cycle, only edges at one common vertex, so the path omitting that vertex omits every
marked edge.
-/

@[expose] public section
namespace STACS2027
open Complexity.SAT

/-- The truth assignment of the paths `f` (indexed like `cycles g k`): `b_{C_i,e}` is true
exactly when the path of `C_i` omits `e`. -/
def assignmentOf (g : Graph) (k : Nat) (f : Nat → List Edge) : Assignment :=
  fun v => !(f (v / k)).contains (cycleEdgeAt g k (v / k) (v % k))

theorem assignmentOf_pathVariable (g : Graph) {k : Nat} (f : Nat → List Edge) (i : Nat) {j : Nat}
    (hj : j < k) :
    assignmentOf g k f (pathVariable k i j) = !(f i).contains (cycleEdgeAt g k i j) := by
  unfold assignmentOf
  rw [pathVariable_div hj, pathVariable_mod hj]

theorem assignmentOf_pathVariable_iff (g : Graph) {k : Nat} (f : Nat → List Edge) (i : Nat) {j : Nat}
    (hj : j < k) :
    assignmentOf g k f (pathVariable k i j) = true ↔ cycleEdgeAt g k i j ∉ f i := by
  rw [assignmentOf_pathVariable g f i hj]
  simp

/-! ## Membership in `Γ₁` -/

theorem mem_pathConstraints (g : Graph) (k : Nat) (cl : Clause) :
    cl ∈ pathConstraints g k ↔
      ∃ i a b, i < (cycles g k).length ∧ a < b ∧ b < k ∧
        disjointEdges (cycleEdgeAt g k i a) (cycleEdgeAt g k i b) = true ∧
        cl = [⟨pathVariable k i a, false⟩, ⟨pathVariable k i b, false⟩] := by
  simp only [pathConstraints, List.mem_flatMap, List.mem_range, List.mem_filterMap]
  constructor
  · rintro ⟨i, hi, a, ha, b, hb, hcl⟩
    split at hcl
    · rename_i h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨i, a, b, hi, h.1, hb, h.2, (Option.some.inj hcl).symm⟩
    · simp at hcl
  · rintro ⟨i, a, b, hi, hab, hb, hd, rfl⟩
    refine ⟨i, hi, a, by omega, b, hb, ?_⟩
    simp [hab, hd]

theorem evalClause_two_neg (σ : Assignment) (x y : Nat) :
    evalClause σ [⟨x, false⟩, ⟨y, false⟩] = true ↔ σ x = false ∨ σ y = false := by
  simp [evalClause, evalLiteral]

theorem evalClause_two_pos (σ : Assignment) (x y : Nat) :
    evalClause σ [⟨x, true⟩, ⟨y, true⟩] = true ↔ σ x = true ∨ σ y = true := by
  simp [evalClause, evalLiteral]

/-! ## Paths satisfy `Γ₁` -/

/-- The omission variables of paths that each omit one vertex satisfy every path constraint. -/
theorem pathConstraints_satisfied (g : Graph) {k : Nat} (f : Nat → List Edge) (ρ : Nat → Nat)
    (hρ : ∀ i, i < (cycles g k).length → ρ i < k ∧ f i = selected (kCycle g k i) (ρ i)) :
    ∀ cl ∈ pathConstraints g k, evalClause (assignmentOf g k f) cl = true := by
  intro cl hcl
  obtain ⟨i, a, b, hi, hab, hb, hd, rfl⟩ := (mem_pathConstraints g k cl).mp hcl
  have ha : a < k := by omega
  obtain ⟨hρk, hfi⟩ := hρ i hi
  have hc := kCycle_isCycle g hi
  rw [evalClause_two_neg]
  apply Classical.byContradiction
  intro hcon
  have hboth : assignmentOf g k f (pathVariable k i a) = true ∧
      assignmentOf g k f (pathVariable k i b) = true := by
    cases h1 : assignmentOf g k f (pathVariable k i a) <;>
      cases h2 : assignmentOf g k f (pathVariable k i b) <;> simp_all
  rw [assignmentOf_pathVariable_iff g f i ha, assignmentOf_pathVariable_iff g f i hb, hfi,
    cycleEdgeAt, cycleEdgeAt, mem_selected_iff_position hc hρk ha,
    mem_selected_iff_position hc hρk hb] at hboth
  rw [cycleEdgeAt, cycleEdgeAt, disjointEdges_edgeAt hc ha hb] at hd
  obtain ⟨h1, h2⟩ := hboth
  apply hd
  have na := next_spec ha
  have nb := next_spec hb
  have hρ' := hρk
  -- `¬¬` on each side gives the incidence of `a` and `b` with `ρ i`
  have h1' : ρ i = a ∨ ρ i = next k a := Classical.byContradiction (fun h => h1 (fun h' => h h'))
  have h2' : ρ i = b ∨ ρ i = next k b := Classical.byContradiction (fun h => h2 (fun h' => h h'))
  omega

/-! ## Decoding a satisfying assignment (`k ≥ 4`) -/

/-- A truth assignment satisfying `Γ₁` marks, on `C_i`, only edges at one vertex, so the path
omitting that vertex omits every marked edge. -/
theorem decode_of_satisfied (g : Graph) {k : Nat} (hk : 4 ≤ k) (σ : Assignment)
    (hσ : ∀ cl ∈ pathConstraints g k, evalClause σ cl = true) {i : Nat}
    (hi : i < (cycles g k).length) :
    ∃ i₀, i₀ < k ∧ ∀ j, j < k → σ (pathVariable k i j) = true →
      cycleEdgeAt g k i j ∉ selected (kCycle g k i) i₀ := by
  have hc := kCycle_isCycle g hi
  let S := (List.range k).filter fun j => σ (pathVariable k i j)
  have hS : ∀ x ∈ S, x < k := fun x hx => List.mem_range.mp (List.mem_filter.mp hx).1
  have hpair : ∀ x ∈ S, ∀ y ∈ S, x = y ∨ x = next k y ∨ y = next k x := by
    intro x hx y hy
    have hxk := hS x hx
    have hyk := hS y hy
    have hxσ : σ (pathVariable k i x) = true := (List.mem_filter.mp hx).2
    have hyσ : σ (pathVariable k i y) = true := (List.mem_filter.mp hy).2
    apply Classical.byContradiction
    intro hnot
    -- the smaller position first: the clause of the disjoint pair is in `Γ₁`
    have hne : x ≠ y := fun e => hnot (Or.inl e)
    have key : ∀ a b, a < b → b < k → σ (pathVariable k i a) = true → σ (pathVariable k i b) = true →
        ¬ (a = b ∨ a = next k b ∨ b = next k a) → False := by
      intro a b hab hbk haσ hbσ hnd
      have hd : disjointEdges (cycleEdgeAt g k i a) (cycleEdgeAt g k i b) = true := by
        rw [cycleEdgeAt, cycleEdgeAt, disjointEdges_edgeAt hc (by omega) hbk]
        exact hnd
      have hmem : [⟨pathVariable k i a, false⟩, ⟨pathVariable k i b, false⟩] ∈ pathConstraints g k :=
        (mem_pathConstraints g k _).mpr ⟨i, a, b, hi, hab, hbk, hd, rfl⟩
      have := hσ _ hmem
      rw [evalClause_two_neg] at this
      rcases this with h | h
      · rw [haσ] at h; cases h
      · rw [hbσ] at h; cases h
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · exact key x y hlt hyk hxσ hyσ hnot
    · apply key y x hgt hxk hyσ hxσ
      intro h
      apply hnot
      rcases h with h | h | h
      · exact Or.inl h.symm
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl h)
  obtain ⟨i₀, hi₀, hall⟩ := common_vertex_positions hk S hS hpair
  refine ⟨i₀, hi₀, ?_⟩
  intro j hj hσj
  have hjS : j ∈ S := List.mem_filter.mpr ⟨List.mem_range.mpr hj, hσj⟩
  rw [cycleEdgeAt, mem_selected_iff_position hc hi₀ hj]
  intro hnot
  apply hnot
  rcases hall j hjS with h | h
  · exact Or.inl h.symm
  · exact Or.inr h

end STACS2027

module

public import Outerplanar.GeneralAlgorithm
public import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Tactic

@[expose] public section
namespace STACS2027
namespace TriangleMatching


def triangle (g : Graph) (i : Nat) : Cycle := (cycles g 3).getD i []

theorem triangle_isCycle (g : Graph) {i : Nat} (hi : i < (cycles g 3).length) :
    IsCycle g 3 (triangle g i) := by
  apply enumerated_isCycle
  rw [triangle, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  exact List.getElem_mem hi

theorem triangle_shape {g : Graph} {c : Cycle} (hc : IsCycle g 3 c) :
    ∃ a b u, c = [a, b, u] ∧ a ≠ b ∧ a ≠ u ∧ b ≠ u := by
  obtain ⟨_, hlen, hnodup, _⟩ := hc
  match c, hlen with
  | [a, b, u], _ =>
    refine ⟨a, b, u, rfl, ?_⟩
    simp only [List.nodup_cons, List.mem_cons, not_or, not_false_eq_true, List.nodup_nil,
      and_true, List.mem_nil_iff] at hnodup
    omega

theorem mem_triangle_paths (a b u : Nat) (q : List Edge) :
    q ∈ selectedOptions [a,b,u] ↔ ∃ e ∈ cycleEdges [a,b,u], q = [e] := by
  have hc : cycleEdges [a,b,u] = [edge a b,edge b u,edge u a] := by
    simp [cycleEdges,pathEdges]
  have hp : selectedOptions [a,b,u] = [[edge b u],[edge u a],[edge a b]] := by
    simp [selectedOptions,List.range_succ,selected,pathEdges]
  rw [hp,hc]
  simp only [List.mem_cons,List.not_mem_nil,or_false]
  constructor
  · rintro (rfl | rfl | rfl)
    · exact ⟨edge b u,by simp,rfl⟩
    · exact ⟨edge u a,by simp,rfl⟩
    · exact ⟨edge a b,by simp,rfl⟩
  · rintro ⟨e,he,rfl⟩
    rcases he with rfl | rfl | rfl <;> simp

theorem getD_map_range {α : Type} (t : Nat) (f : Nat → α) (d : α) {i : Nat} (hi : i < t) :
    ((List.range t).map f).getD i d = f i := by
  rw [List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_eq_getElem (by simpa using hi)]
  simp

theorem validChoices_of_getD {cs : List Cycle} {ps : List (List Edge)}
    (hlen : ps.length = cs.length)
    (hall : ∀ i,i < cs.length → ps.getD i [] ∈ selectedOptions (cs.getD i [])) :
    ValidChoices (cs.map selectedOptions) ps := by
  induction cs generalizing ps with
  | nil =>
    cases ps with
    | nil => trivial
    | cons p ps => simp at hlen
  | cons c cs ih =>
    cases ps with
    | nil => simp at hlen
    | cons p ps =>
      refine ⟨by simpa using hall 0 (by simp),?_⟩
      apply ih (by simpa using hlen)
      intro i hi
      simpa using hall (i+1) (by simpa using hi)

/-- The three sides of an enumerated triangle. -/
def triangleSides (g : Graph) (i : Fin (cycles g 3).length) : Finset Edge :=
  (cycleEdges (triangle g i.val)).toFinset

/-- The exact finite-family inequality needed for a triangle-side matching. -/
def TriangleSideHall (g : Graph) : Prop :=
  ∀ S : Finset (Fin (cycles g 3).length), S.card ≤ (S.biUnion (triangleSides g)).card

/-- Hall's theorem produces one distinct edge of each enumerated triangle. -/
theorem triangle_distinct_sides_iff (g : Graph) : TriangleSideHall g ↔
    ∃ f : Fin (cycles g 3).length → Edge, Function.Injective f ∧
      ∀ i, f i ∈ cycleEdges (triangle g i.val) := by
  unfold TriangleSideHall
  rw [Finset.all_card_le_biUnion_card_iff_existsInjective']
  simp only [triangleSides, List.mem_toFinset]

/-- Distinct triangle sides give a valid path family of cost zero. -/
theorem triangle_assignment_of_distinct_sides {g : Graph}
    (f : Fin (cycles g 3).length → Edge) (hinj : Function.Injective f)
    (hmem : ∀ i, f i ∈ cycleEdges (triangle g i.val)) : HasAssignment g 3 0 := by
  classical
  let p : Nat → List Edge := fun i => if hi : i < (cycles g 3).length then [f ⟨i, hi⟩] else []
  let ps := (List.range (cycles g 3).length).map p
  have hv : ValidChoices ((cycles g 3).map selectedOptions) ps := by
    apply validChoices_of_getD
    · simp [ps]
    · intro i hi
      rw [getD_map_range _ p [] hi]
      obtain ⟨a, b, u, hc, _⟩ := triangle_shape (triangle_isCycle g hi)
      change p i ∈ selectedOptions (triangle g i)
      rw [hc, mem_triangle_paths]
      exact ⟨f ⟨i, hi⟩, hc ▸ hmem ⟨i, hi⟩, by simp [p, hi]⟩
  have hz : cost ps = 0 := by
    apply cost_eq_zero_of_pairwise
    dsimp [ps]
    rw [List.pairwise_map]
    apply List.pairwise_lt_range.imp_of_mem
    intro i j hi hj hij
    have hi' := List.mem_range.mp hi
    have hj' := List.mem_range.mp hj
    apply overlap_eq_zero_of_disjoint
    intro e he he'
    simp only [p, hi', hj', dite_eq_left, List.mem_cons, List.not_mem_nil, or_false] at he he'
    have hab : f ⟨i, hi'⟩ = f ⟨j, hj'⟩ := he.symm.trans he'
    have hval := congrArg Fin.val (hinj hab)
    change i = j at hval
    omega
  exact ⟨ps, hv, hz.le⟩

/-- The finite triangle-family cardinality inequality suffices for perfect assignment. -/
theorem triangle_perfect_of_hall {g : Graph} (h : TriangleSideHall g) :
    HasAssignment g 3 0 := by
  obtain ⟨f, hinj, hmem⟩ := (triangle_distinct_sides_iff g).mp h
  exact triangle_assignment_of_distinct_sides f hinj hmem

end TriangleMatching
end STACS2027

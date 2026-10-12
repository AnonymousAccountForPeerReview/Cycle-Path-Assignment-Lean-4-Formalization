module

public import NPHardness.GlobalGraph

/-! Distinct variable gadgets, and distinct clause gadgets, have disjoint
vertex images. These are concrete facts about formulaGraph, not promises
assumed of an unspecified reduction. -/

@[expose] public section
namespace STACS2027
open Complexity.SAT

theorem BoundedOccurrence.placed_clauses_keys_disjoint {f : CNF} (hf : BoundedOccurrence f)
    {i j : Nat} (hi : i < (placeFormula [] f).length) (hj : j < (placeFormula [] f).length)
    (hne : i ≠ j) {p q : PlacedLiteral} (hp : p ∈ (placeFormula [] f)[i])
    (hq : q ∈ (placeFormula [] f)[j]) : p.key ≠ q.key := by
  have hn := hf.placement_keys_nodup
  have hflat : ((placeFormula [] f).flatMap (fun c => c.map PlacedLiteral.key)).Nodup := by
    simpa only [List.flatMap, List.map_flatten] using hn
  have hpw := (List.pairwise_flatMap.mp hflat).2
  have hpm : p.key ∈ ((placeFormula [] f)[i].map PlacedLiteral.key) := List.mem_map.mpr ⟨p,hp,rfl⟩
  have hqm : q.key ∈ ((placeFormula [] f)[j].map PlacedLiteral.key) := List.mem_map.mpr ⟨q,hq,rfl⟩
  by_cases hij : i < j
  · exact hpw.rel_getElem_of_lt hi hj hij _ hpm _ hqm
  · have hji : j < i := by omega
    exact Ne.symm (hpw.rel_getElem_of_lt hj hi hji _ hqm _ hpm)

theorem formulaGraph_variable_vertices_disjoint (k : Nat) {a b u v : Nat}
    (hne : a ≠ b) (hu : u < gadgetWidth k) (hv : v < gadgetWidth k) :
    blockVertex (gadgetWidth k) a u ≠ blockVertex (gadgetWidth k) b v :=
  fun h => hne (blockVertex_injective hu hv h).1

theorem formulaGraph_clause_vertices_disjoint {k : Nat} {f : CNF} (hf : BoundedOccurrence f)
    {i j : Nat} (hi : i < (placeFormula [] f).length) (hj : j < (placeFormula [] f).length)
    (hne : i ≠ j) {u v : Nat} (hu : u < gadgetWidth k) (hv : v < gadgetWidth k) :
    clauseVertex (gadgetWidth k) (variableBound f) i (placeFormula [] f)[i] u ≠
      clauseVertex (gadgetWidth k) (variableBound f) j (placeFormula [] f)[j] v := by
  intro he
  have hci := List.getElem_mem hi
  have hcj := List.getElem_mem hj
  have hw : 7 ≤ gadgetWidth k := by have := gadgetWidth_ge k; omega
  cases hau : attachmentAt (placeFormula [] f)[i] u with
  | none =>
    cases hav : attachmentAt (placeFormula [] f)[j] v with
    | none =>
      have htag := (blockVertex_injective hu hv (by simpa [clauseVertex, hau, hav] using he)).1
      exact hne (by omega)
    | some ps =>
      obtain ⟨p, side⟩ := ps
      obtain ⟨a, _, hap, _⟩ := attachmentAt_spec.mp hav
      have hpm := List.mem_of_getElem? hap
      have hpv := (hf.placed_clause_bounds hcj p hpm).1
      have hep : variableEndpoint p.port side < gadgetWidth k :=
        Nat.lt_of_lt_of_le (variableEndpoint_bound _ _) hw
      have htag := (blockVertex_injective hu hep (by simpa [clauseVertex, hau, hav] using he)).1
      omega
  | some ps =>
    obtain ⟨p, side⟩ := ps
    obtain ⟨a, _, hap, _⟩ := attachmentAt_spec.mp hau
    have hpm := List.mem_of_getElem? hap
    have hpv := (hf.placed_clause_bounds hci p hpm).1
    have hep : variableEndpoint p.port side < gadgetWidth k :=
      Nat.lt_of_lt_of_le (variableEndpoint_bound _ _) hw
    cases hav : attachmentAt (placeFormula [] f)[j] v with
    | none =>
      have htag := (blockVertex_injective hep hv (by simpa [clauseVertex, hau, hav] using he)).1
      omega
    | some qs =>
      obtain ⟨q, side'⟩ := qs
      obtain ⟨b, _, hbq, _⟩ := attachmentAt_spec.mp hav
      have hqm := List.mem_of_getElem? hbq
      have heq : variableEndpoint q.port side' < gadgetWidth k :=
        Nat.lt_of_lt_of_le (variableEndpoint_bound _ _) hw
      obtain ⟨hvar, hend⟩ := blockVertex_injective hep heq (by simpa [clauseVertex, hau, hav] using he)
      have hport := (variableEndpoint_injective (hf.placed_clause_bounds hci p hpm).2
        (hf.placed_clause_bounds hcj q hqm).2 _ _ hend).1
      exact hf.placed_clauses_keys_disjoint hi hj hne hpm hqm (Prod.ext hvar hport)

theorem mapGraph_disjoint {g h : Graph} {n m : Nat} (hg : VerticesBelow g n)
    (hh : VerticesBelow h m) (f t : Nat → Nat)
    (hs : ∀ a, a < n → ∀ b, b < m → f a ≠ t b) :
    ∀ e ∈ mapGraph f g, e ∉ mapGraph t h := by
  intro e he he'
  obtain ⟨d, hd, hde⟩ := List.mem_map.mp he
  obtain ⟨d', hd', hde'⟩ := List.mem_map.mp he'
  have heq : edge (f d.1) (f d.2) = edge (t d'.1) (t d'.2) := hde.trans hde'.symm
  rcases (edge_eq_iff ..).mp heq with ⟨ha, _⟩ | ⟨ha, _⟩
  · exact hs d.1 (hg d hd).1 d'.1 (hh d' hd').1 ha
  · exact hs d.1 (hg d hd).1 d'.2 (hh d' hd').2 ha

theorem formulaGraph_variable_edges_disjoint (k : Nat) {v w : Nat} (hne : v ≠ w) :
    ∀ e ∈ placedVariableGraph k v, e ∉ placedVariableGraph k w :=
  mapGraph_disjoint (variableGraph_below k) (variableGraph_below k) _ _
    (fun _ hu _ hv => formulaGraph_variable_vertices_disjoint k hne hu hv)

theorem formulaGraph_clause_edges_disjoint {k : Nat} {f : CNF} (hf : BoundedOccurrence f)
    {i j : Nat} (hi : i < (placeFormula [] f).length) (hj : j < (placeFormula [] f).length)
    (hne : i ≠ j) :
    ∀ e ∈ placedClauseGraph k (variableBound f) i (placeFormula [] f)[i],
      e ∉ placedClauseGraph k (variableBound f) j (placeFormula [] f)[j] :=
  mapGraph_disjoint (clauseGraph_below k _) (clauseGraph_below k _) _ _
    (fun _ hu _ hv => formulaGraph_clause_vertices_disjoint hf hi hj hne hu hv)

theorem overlap_zero_of_graph_disjoint {g h : Graph} (hg : ∀ e ∈ g, e ∉ h)
    {p q : List Edge} (hp : p ⊆ g) (hq : q ⊆ h) : overlap p q = 0 := by
  unfold overlap
  apply List.sum_eq_zero_iff_forall_eq_nat.mpr
  intro n hn
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hn
  exact List.count_eq_zero_of_not_mem (fun h => hg e (hp he) (hq h))

end STACS2027

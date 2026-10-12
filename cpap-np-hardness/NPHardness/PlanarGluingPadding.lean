module

public import NPHardness.PlanarGluingPath
public import NPHardness.ClausePadding
public import Complexity.Planar.Subdivide
import Lean.Elab.Tactic.Omega

/-! The actual fresh-clause padding operation preserves registered incidence
planarity. Each added two-literal clause is a disjoint two-edge path. -/

@[expose] public section
namespace STACS2027
open Complexity Complexity.SAT PlanarGluing

def incidenceVertexBound (f : CNF) : Sum Nat Nat → Prop
  | .inl v => v < variableBound f
  | .inr j => j < f.length

theorem incidence_edge_bounds (f : CNF) (e : Sum Nat Nat × Sum Nat Nat)
    (he : e ∈ incidenceGraph f) : incidenceVertexBound f e.1 ∧ incidenceVertexBound f e.2 := by
  obtain ⟨p, hp, hm⟩ := List.mem_flatMap.mp he
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hm
  exact ⟨literal_lt_variableBound (List.fst_mem_of_mem_zipIdx hp) hl,
    by have h := List.snd_lt_of_mem_zipIdx hp; simpa [incidenceVertexBound] using h⟩

theorem incidence_halfEdgeEnd_bound (f : CNF) (d : Fin (2 * (incidenceGraph f).length)) :
    ∃ v, incidenceVertexBound f v ∧ halfEdgeEnd (incidenceGraph f) d.val = some v := by
  have hi : d.val / 2 < (incidenceGraph f).length := by have := d.isLt; omega
  have he := incidence_edge_bounds f (incidenceGraph f)[d.val / 2] (List.getElem_mem hi)
  simp only [halfEdgeEnd, List.getElem?_eq_getElem hi, Option.map_some]
  cases h : Nat.beq (d.val % 2) 0 with
  | false => exact ⟨_, he.2, rfl⟩
  | true => exact ⟨_, he.1, rfl⟩

theorem incidence_addPaddingClause (f : CNF) :
    incidenceGraph (addPaddingClause f) = incidenceGraph f ++
      [(Sum.inl (variableBound f), Sum.inr f.length),
       (Sum.inl (variableBound f + 1), Sum.inr f.length)] := by
  simp [addPaddingClause, incidenceGraph, List.zipIdx_append, paddingClause]

theorem planar_incidence_addPaddingClause (f : CNF) (hp : PlanarGraph (incidenceGraph f)) :
    PlanarGraph (incidenceGraph (addPaddingClause f)) := by
  rw [incidence_addPaddingClause]
  apply planarGraph_append_spherical hp
    (sphericalTwoEdgePath (Sum.inl (variableBound f)) (Sum.inl (variableBound f + 1))
      (Sum.inr f.length) (by simp) (by simp) (by simp))
  intro d d' he
  obtain ⟨v, hv, hd⟩ := incidence_halfEdgeEnd_bound f d
  rw [hd] at he
  have hi : d'.val = 0 ∨ d'.val = 1 ∨ d'.val = 2 ∨ d'.val = 3 := by
    have hlt : d'.val < 4 := d'.isLt
    omega
  rcases v with v | j
  · change v < variableBound f at hv
    rcases hi with hi | hi | hi | hi <;> simp [halfEdgeEnd, hi] at he <;> omega
  · change j < f.length at hv
    rcases hi with hi | hi | hi | hi <;> simp [halfEdgeEnd, hi] at he <;> omega

/-- Any number of the actual budget-restoring padding clauses preserves planarity. -/
theorem planar_incidence_padFormula (r : Nat) (f : CNF) (hp : PlanarGraph (incidenceGraph f)) :
    PlanarGraph (incidenceGraph (padFormula r f)) := by
  induction r with
  | zero => exact hp
  | succ r ih => exact planar_incidence_addPaddingClause _ ih

end STACS2027

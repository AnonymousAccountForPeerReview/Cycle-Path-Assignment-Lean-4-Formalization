module

public import NPHardness.PlanarSourceEmbeddingExtract
public import NPHardness.PlanarSourceFormulaGraph
public import NPHardness.PlanarSourceFormulaSemantics

/-! Variable and clause labels of the darts of an incidence graph
(`variableAt`, `clauseAt`). -/

@[expose] public section
namespace STACS2027.PlanarSource.FromFormula
open Complexity Complexity.SAT Complexity.Planar
open STACS2027.PlanarSource.Embedding STACS2027.PlanarSource.Embedding.BipartiteRotation
open STACS2027.PlanarSource.Formula

def variableAt (f : CNF) (i : Nat) : Nat :=
  ((f.flatten[i]?).getD ⟨0, false⟩).var

def clauseAt (f : CNF) (i : Nat) : Nat :=
  match (incidenceGraph f)[i]? with
  | some (_, .inr j) => j
  | _ => 0

theorem variableAt_get (f : CNF) (i : Fin f.flatten.length) :
    variableAt f i.val = (f.flatten[i.val]).var := by
  simp [variableAt, List.getElem?_eq_getElem i.isLt]

theorem incidenceAt_first (f : CNF) (start : Nat) :
    (incidenceAt start f).map Prod.fst = f.flatten.map (fun l => Sum.inl l.var) := by
  induction f generalizing start with
  | nil => rfl
  | cons c f ih =>
    simp [incidenceAt_cons, List.map_append, List.map_map, ih]

theorem incidence_first (f : CNF) (i : Fin (incidenceGraph f).length) :
    ((incidenceGraph f)[i.val]).1 = Sum.inl (variableAt f i.val) := by
  have hi : i.val < f.flatten.length := by rw [← incidenceGraph_length_flatten]; exact i.isLt
  have hm := incidenceAt_first f 0
  have hg := congrArg (fun es => es[i.val]?) hm
  simp only [incidenceAt_zero, List.getElem?_map, List.getElem?_eq_getElem i.isLt,
    List.getElem?_eq_getElem hi, Option.map_some] at hg
  rw [variableAt_get f ⟨i.val, hi⟩]
  exact Option.some.inj hg

theorem incidence_second (f : CNF) (i : Fin (incidenceGraph f).length) :
    ((incidenceGraph f)[i.val]).2 = Sum.inr (clauseAt f i.val) ∧ clauseAt f i.val < f.length := by
  obtain ⟨j, l, hj, _, he⟩ := Complexity.Planar.Grid.mem_incidenceGraph
    (List.getElem_mem (l := incidenceGraph f) i.isLt)
  have hv : clauseAt f i.val = j := by
    simp [clauseAt, he]
  rw [he, hv]
  exact ⟨rfl, hj⟩

theorem incidence_labels (f : CNF) (i : Fin (incidenceGraph f).length) :
    (incidenceGraph f)[i.val] = (Sum.inl (variableAt f i.val), Sum.inr (clauseAt f i.val)) :=
  Prod.ext (incidence_first f i) (incidence_second f i).1

end STACS2027.PlanarSource.FromFormula

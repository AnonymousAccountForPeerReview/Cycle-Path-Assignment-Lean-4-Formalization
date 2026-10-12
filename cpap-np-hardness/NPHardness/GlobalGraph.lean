module

public import NPHardness.VertexGluing
public import NPHardness.GraphRelabel

/-!
The actual formula-to-graph map. Each variable occupies its own vertex block.
Each clause occupies a new block except at literal-port endpoints, which are
identified with the occurrence's allocated variable port. Repeated edge-list
entries denote the same undirected edge, as in the existing Graph semantics.
This module proves that every placed gadget is a subgraph of the result.
-/

@[expose] public section
namespace STACS2027
open Complexity.SAT

def gadgetWidth (k : Nat) : Nat := 24 + subdivisionCount (variableLinks k) +
  subdivisionCount (clauseThreeLinks k) + subdivisionCount (clauseTwoLinks k)

def clauseGraph (k : Nat) (c : List PlacedLiteral) : Graph :=
  if c.length = 2 then clauseTwoGraph k else clauseThreeGraph k

def placedVariableGraph (k v : Nat) : Graph :=
  mapGraph (blockVertex (gadgetWidth k) v) (variableGraph k)

def placedClauseGraph (k n j : Nat) (c : List PlacedLiteral) : Graph :=
  mapGraph (clauseVertex (gadgetWidth k) n j c) (clauseGraph k c)

def formulaGraph (k : Nat) (f : CNF) : Graph :=
  ((List.range (variableBound f)).flatMap (placedVariableGraph k)) ++
    ((placeFormula [] f).mapIdx (fun j c => placedClauseGraph k (variableBound f) j c)).flatten

theorem gadgetWidth_ge (k : Nat) : 24 ≤ gadgetWidth k := by unfold gadgetWidth; omega

theorem variableGraph_below (k : Nat) : VerticesBelow (variableGraph k) (gadgetWidth k) := by
  have h := realizeLinks_below 7 (variableLinks k) (variable_links_wellformed k).1
  apply h.mono
  unfold gadgetWidth
  omega

theorem clauseThreeGraph_below (k : Nat) : VerticesBelow (clauseThreeGraph k) (gadgetWidth k) := by
  have h := realizeLinks_below 18 (clauseThreeLinks k) (clauseThree_links_wellformed k).1
  apply h.mono
  unfold gadgetWidth
  omega

theorem clauseTwoGraph_below (k : Nat) : VerticesBelow (clauseTwoGraph k) (gadgetWidth k) := by
  have h := realizeLinks_below 24 (clauseTwoLinks k) (clauseTwo_links_wellformed k).1
  apply h.mono
  unfold gadgetWidth
  omega

theorem clauseGraph_below (k : Nat) (c : List PlacedLiteral) :
    VerticesBelow (clauseGraph k c) (gadgetWidth k) := by
  unfold clauseGraph
  split
  · exact clauseTwoGraph_below k
  · exact clauseThreeGraph_below k

theorem placeFormula_length (past : List Literal) (f : CNF) : (placeFormula past f).length = f.length := by
  have h := congrArg List.length (placeFormula_forget past f)
  simpa using h

theorem placement_literal_mem {f : CNF} {p : PlacedLiteral}
    (hp : p ∈ (placeFormula [] f).flatten) : p.literal ∈ f.flatten := by
  rw [placeFormula_flatten] at hp
  rw [← placeLiterals_forget [] f.flatten]
  exact List.mem_map.mpr ⟨p, hp, rfl⟩

theorem BoundedOccurrence.placed_clause_bounds {f : CNF} (hf : BoundedOccurrence f)
    {c : List PlacedLiteral} (hc : c ∈ placeFormula [] f) :
    ∀ p ∈ c, p.literal.var < variableBound f ∧ p.port < 3 := by
  intro p hp
  have hm := List.mem_flatten.mpr ⟨c, hc, hp⟩
  obtain ⟨d, hd, hpd⟩ := List.mem_flatten.mp (placement_literal_mem hm)
  exact ⟨literal_lt_variableBound hd hpd, hf.placement_port_lt hm⟩

theorem BoundedOccurrence.placed_clause_nodup {f : CNF} (hf : BoundedOccurrence f)
    {c : List PlacedLiteral} (hc : c ∈ placeFormula [] f) : (c.map PlacedLiteral.key).Nodup :=
  ((List.sublist_flatten_of_mem hc).map PlacedLiteral.key).nodup hf.placement_keys_nodup

theorem BoundedOccurrence.placed_clause_size {f : CNF} (hf : BoundedOccurrence f)
    {c : List PlacedLiteral} (hc : c ∈ placeFormula [] f) : c.length = 2 ∨ c.length = 3 := by
  have hm : c.map PlacedLiteral.literal ∈ f := by
    rw [← placeFormula_forget [] f]
    exact List.mem_map.mpr ⟨c, hc, rfl⟩
  simpa using hf.1 _ hm

theorem formulaGraph_variable_contains (k : Nat) (f : CNF) {v : Nat} (hv : v < variableBound f) :
    placedVariableGraph k v ⊆ formulaGraph k f := by
  intro e he
  apply List.mem_append_left
  exact List.mem_flatMap.mpr ⟨v, List.mem_range.mpr hv, he⟩

theorem formulaGraph_clause_contains (k : Nat) (f : CNF) (j : Nat)
    (hj : j < (placeFormula [] f).length) :
    placedClauseGraph k (variableBound f) j (placeFormula [] f)[j] ⊆ formulaGraph k f := by
  intro e he
  apply List.mem_append_right
  apply List.mem_flatten.mpr
  exact ⟨_, List.mem_mapIdx.mpr ⟨j, hj, rfl⟩, he⟩

theorem mapped_attachment_edge {width n j : Nat} {c : List PlacedLiteral}
    {i : Nat} (hi : i < 3) {p : PlacedLiteral} (hp : c[i]? = some p) :
    mapEdge (clauseVertex width n j c) (edge (clauseEndpoint i false) (clauseEndpoint i true)) =
      mapEdge (blockVertex width p.literal.var) (edge (variableEndpoint p.port false) (variableEndpoint p.port true)) := by
  rw [mapEdge_edge, mapEdge_edge, clauseVertex_attachment hi hp false, clauseVertex_attachment hi hp true]

theorem realizeLinks_contains_zero (next : Nat) (ls : List Link) {l : Link}
    (hl : l ∈ ls) (hz : l.subdivisions = 0) : edge l.source l.target ∈ realizeLinks next ls := by
  induction ls generalizing next with
  | nil => simp at hl
  | cons r rs ih =>
    rcases List.mem_cons.mp hl with rfl | hl
    · apply List.mem_append_left
      simp [hz, subdividedEdge]
    · exact List.mem_append_right _ (ih _ hl)

theorem variableGraph_ports (k : Nat) {p : Nat} (hp : p < 3) :
    edge (variableEndpoint p false) (variableEndpoint p true) ∈ variableGraph k := by
  have hs : p = 0 ∨ p = 1 ∨ p = 2 := by omega
  rcases hs with rfl | rfl | rfl
  · exact realizeLinks_contains_zero 7 (variableLinks k) (l := ⟨2,6,0⟩) (by simp [variableLinks]) rfl
  · exact realizeLinks_contains_zero 7 (variableLinks k) (l := ⟨4,5,0⟩) (by simp [variableLinks]) rfl
  · exact realizeLinks_contains_zero 7 (variableLinks k) (l := ⟨0,3,0⟩) (by simp [variableLinks]) rfl

end STACS2027

module

public import NPHardness.AssignmentRelabel
public import NPHardness.GlobalCompleteness

/-! Clause blocks may use any injective allocation, including unused gaps.
The computational emitter can therefore allocate blocks without first counting
which input-dependent branches emit clauses. -/

@[expose] public section
namespace STACS2027
open Complexity.SAT

def taggedFormulaGraph (k : Nat) (f : CNF) (tag : Nat → Nat) : Graph :=
  (List.range (variableBound f)).flatMap (placedVariableGraph k) ++
    ((placeFormula [] f).mapIdx
      (fun j c => placedClauseGraph k (variableBound f) (tag j) c)).flatten

def renameClauseBlocks (width n : Nat) (tag : Nat → Nat) (x : Nat) : Nat :=
  if x / width < n then x else blockVertex width (n + tag (x / width - n)) (x % width)

theorem blockVertex_div {width : Nat} (hw : 0 < width) (b v : Nat) (hv : v < width) :
    blockVertex width b v / width = b := by
  rw [blockVertex,Nat.add_comm,Nat.add_mul_div_right _ _ hw,Nat.div_eq_of_lt hv,Nat.zero_add]

theorem renameClauseBlocks_variable {width n : Nat} (hw : 0 < width)
    (tag : Nat → Nat) {b v : Nat} (hb : b < n) (hv : v < width) :
    renameClauseBlocks width n tag (blockVertex width b v) = blockVertex width b v := by
  simp only [renameClauseBlocks,blockVertex_div hw b v hv,hb,↓reduceIte]

theorem renameClauseBlocks_private {width n : Nat} (hw : 0 < width)
    (tag : Nat → Nat) (b v : Nat) (hv : v < width) :
    renameClauseBlocks width n tag (blockVertex width (n+b) v) =
      blockVertex width (n+tag b) v := by
  have hn : ¬ n+b < n := by omega
  simp [renameClauseBlocks,blockVertex_div hw (n+b) v hv,blockVertex_mod hw (n+b) v hv,hn]

theorem renameClauseBlocks_injective {width n m : Nat} (hw : 0 < width)
    (tag : Nat → Nat) (ht : ∀ a, a < m → ∀ b, b < m → tag a = tag b → a = b)
    {x y : Nat} (hx : x < (n+m)*width) (hy : y < (n+m)*width)
    (he : renameClauseBlocks width n tag x = renameClauseBlocks width n tag y) : x = y := by
  have hxq : x / width < n+m := (Nat.div_lt_iff_lt_mul hw).mpr hx
  have hyq : y / width < n+m := (Nat.div_lt_iff_lt_mul hw).mpr hy
  have hxr := Nat.mod_lt x hw
  have hyr := Nat.mod_lt y hw
  have hxe : blockVertex width (x/width) (x%width) = x := by
    simpa [blockVertex,Nat.mul_comm] using Nat.div_add_mod x width
  have hye : blockVertex width (y/width) (y%width) = y := by
    simpa [blockVertex,Nat.mul_comm] using Nat.div_add_mod y width
  unfold renameClauseBlocks at he
  by_cases hxn : x/width < n <;> by_cases hyn : y/width < n
  · simpa [hxn,hyn] using he
  · simp only [hxn,hyn,↓reduceIte] at he
    rw [← hxe] at he
    have hh := (blockVertex_injective hxr hyr he).1
    omega
  · simp only [hxn,hyn,↓reduceIte] at he
    rw [← hye] at he
    have hh := (blockVertex_injective hxr hyr he).1
    omega
  · simp only [hxn,hyn,↓reduceIte] at he
    obtain ⟨hquo,hrem⟩ := blockVertex_injective hxr hyr he
    have htag : tag (x/width-n) = tag (y/width-n) := by omega
    have hsame := ht (x/width-n) (by omega) (y/width-n) (by omega) htag
    have hq : x/width = y/width := by omega
    rw [← hxe,← hye,hq,hrem]

theorem clauseVertex_block_bound {width n j m : Nat} {c : List PlacedLiteral}
    (hw : 7 ≤ width) (hj : j < m) (hc : ∀ p ∈ c, p.literal.var < n)
    {v : Nat} (hv : v < width) : clauseVertex width n j c v < (n+m)*width := by
  unfold clauseVertex
  cases ha : attachmentAt c v with
  | none =>
    change (n+j)*width+v < (n+m)*width
    have h := Nat.mul_le_mul_right width (show n+j+1 ≤ n+m by omega)
    rw [Nat.add_mul,Nat.one_mul] at h
    omega
  | some p =>
    obtain ⟨i,_,hi,_⟩ := attachmentAt_spec.mp ha
    have hp := hc p.1 (List.mem_of_getElem? hi)
    have hvp := variableEndpoint_bound p.1.port p.2
    change p.1.literal.var*width+variableEndpoint p.1.port p.2 < (n+m)*width
    have h := Nat.mul_le_mul_right width (show p.1.literal.var+1 ≤ n+m by omega)
    rw [Nat.add_mul,Nat.one_mul] at h
    omega

theorem formulaGraph_below {k : Nat} {f : CNF} (hf : BoundedOccurrence f) :
    VerticesBelow (formulaGraph k f) ((variableBound f + f.length)*gadgetWidth k) := by
  intro e he
  rcases List.mem_append.mp he with he | he
  · obtain ⟨v,hv,he⟩ := List.mem_flatMap.mp he
    obtain ⟨d,hd,rfl⟩ := List.mem_map.mp he
    have hv' := List.mem_range.mp hv
    have hd' := variableGraph_below k d hd
    have hmul := Nat.mul_le_mul_right (gadgetWidth k)
      (show v+1 ≤ variableBound f+f.length by omega)
    rw [Nat.add_mul,Nat.one_mul] at hmul
    apply (edge_below _ _ _).mpr
    change v*gadgetWidth k+d.1 < _ ∧ v*gadgetWidth k+d.2 < _
    constructor <;> omega
  · obtain ⟨es,hes,he⟩ := List.mem_flatten.mp he
    obtain ⟨j,hj,rfl⟩ := List.mem_mapIdx.mp hes
    obtain ⟨d,hd,rfl⟩ := List.mem_map.mp he
    have hb := clauseGraph_below k (placeFormula [] f)[j] d hd
    have hj' : j < f.length := by simpa only [placeFormula_length] using hj
    have hc := hf.placed_clause_bounds (List.getElem_mem hj)
    apply (edge_below _ _ _).mpr
    exact ⟨clauseVertex_block_bound (by have := gadgetWidth_ge k; omega) hj' (fun p hp => (hc p hp).1) hb.1,
      clauseVertex_block_bound (by have := gadgetWidth_ge k; omega) hj' (fun p hp => (hc p hp).1) hb.2⟩

theorem mapGraph_normalized (t : Nat → Nat) (g : Graph) :
    ∀ e ∈ mapGraph t g, edge e.1 e.2 = e := by
  intro e he
  obtain ⟨d,_,rfl⟩ := List.mem_map.mp he
  exact edge_normalized _ _

theorem formulaGraph_normalized (k : Nat) (f : CNF) :
    ∀ e ∈ formulaGraph k f, edge e.1 e.2 = e := by
  intro e he
  rcases List.mem_append.mp he with he | he
  · obtain ⟨v,_,he⟩ := List.mem_flatMap.mp he
    exact mapGraph_normalized _ _ e he
  · obtain ⟨es,hes,he⟩ := List.mem_flatten.mp he
    obtain ⟨j,hj,rfl⟩ := List.mem_mapIdx.mp hes
    exact mapGraph_normalized _ _ e he

theorem mapGraph_comp (t u : Nat → Nat) (g : Graph) :
    mapGraph t (mapGraph u g) = mapGraph (fun x => t (u x)) g := by
  unfold mapGraph
  rw [List.map_map]
  apply List.map_congr_left
  intro e _
  exact mapEdge_edge t (u e.1) (u e.2)

theorem mapGraph_congr_on {g : Graph} {n : Nat} (hb : VerticesBelow g n)
    {t u : Nat → Nat} (he : ∀ x, x < n → t x = u x) : mapGraph t g = mapGraph u g := by
  apply List.map_congr_left
  intro e hm
  simp only [mapEdge,he e.1 (hb e hm).1,he e.2 (hb e hm).2]

theorem renameClauseBlocks_clauseVertex {width n j : Nat} {c : List PlacedLiteral}
    (hw : 7 ≤ width) (tag : Nat → Nat) (hc : ∀ p ∈ c, p.literal.var < n)
    {v : Nat} (hv : v < width) :
    renameClauseBlocks width n tag (clauseVertex width n j c v) =
      clauseVertex width n (tag j) c v := by
  unfold clauseVertex
  cases ha : attachmentAt c v with
  | none => exact renameClauseBlocks_private (by omega) tag j v hv
  | some p =>
    obtain ⟨i,_,hi,_⟩ := attachmentAt_spec.mp ha
    exact renameClauseBlocks_variable (by omega) tag (hc _ (List.mem_of_getElem? hi))
      (Nat.lt_of_lt_of_le (variableEndpoint_bound _ _) hw)

theorem taggedFormulaGraph_relabel {k : Nat} {f : CNF} (hf : BoundedOccurrence f)
    (tag : Nat → Nat) :
    mapGraph (renameClauseBlocks (gadgetWidth k) (variableBound f) tag) (formulaGraph k f) =
      taggedFormulaGraph k f tag := by
  let t := renameClauseBlocks (gadgetWidth k) (variableBound f) tag
  have hv (v : Nat) (hm : v ∈ List.range (variableBound f)) :
      mapGraph t (placedVariableGraph k v) = placedVariableGraph k v := by
    rw [placedVariableGraph,mapGraph_comp]
    apply mapGraph_congr_on (variableGraph_below k)
    intro x hx
    exact renameClauseBlocks_variable (by have := gadgetWidth_ge k; omega) tag (List.mem_range.mp hm) hx
  have hc (j : Nat) (hj : j < (placeFormula [] f).length) :
      mapGraph t (placedClauseGraph k (variableBound f) j (placeFormula [] f)[j]) =
        placedClauseGraph k (variableBound f) (tag j) (placeFormula [] f)[j] := by
    rw [placedClauseGraph,mapGraph_comp]
    apply mapGraph_congr_on (clauseGraph_below k _)
    intro x hx
    exact renameClauseBlocks_clauseVertex (by have := gadgetWidth_ge k; omega) tag
      (fun p hp => (hf.placed_clause_bounds (List.getElem_mem hj) p hp).1) hx
  change ((formulaGraph k f).map (mapEdge t)) = _
  simp only [formulaGraph,taggedFormulaGraph,List.map_append,List.map_flatMap,List.map_flatten]
  congr 1
  · exact congrArg List.flatten (List.map_congr_left hv)
  · congr 1
    apply List.ext_getElem
    · simp
    · intro j hj hj'
      have h : j < (placeFormula [] f).length := by simpa using hj
      simpa only [List.getElem_map,List.getElem_mapIdx,mapGraph] using hc j h

theorem taggedFormulaGraph_sat_iff_assignment {k : Nat} (hk : 5 ≤ k) {f : CNF}
    (hf : BoundedOccurrence f) (hd : ClauseVariablesDistinct f)
    (tag : Nat → Nat)
    (ht : ∀ a, a < f.length → ∀ b, b < f.length → tag a = tag b → a = b) :
    Satisfiable f ↔ HasAssignment (taggedFormulaGraph k f tag) k f.length := by
  rw [← taggedFormulaGraph_relabel hf tag]
  exact (formulaGraph_sat_iff_assignment hk hf hd).trans
    (hasAssignment_relabel (formulaGraph_below hf) (formulaGraph_normalized k f) _
      (fun _ hx _ hy he => renameClauseBlocks_injective
        (by have := gadgetWidth_ge k; omega) tag ht hx hy he) k f.length).symm

end STACS2027

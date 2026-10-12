module

public import NPHardness.PlanarRelabel
public import NPHardness.PlanarOperationsGadgets
public import NPHardness.OrientedGluing
public import NPHardness.TaggedGraph

/-!
Concrete quotient map for assembling the actual formula graph. Before
assembly, every clause retains all of its vertices in its own block. The
single global map below identifies exactly the allocated attachment endpoints
with their oriented variable endpoints. The resulting edge list is exactly
the existing constructor, including the repeated copies of shared edges.
-/

@[expose] public section
namespace STACS2027
open Complexity Complexity.SAT

def ungluedClauseGraph (k n j : Nat) (c : List PlacedLiteral) : Graph :=
  mapGraph (blockVertex (gadgetWidth k) (n+j)) (clauseGraph k c)

def ungluedFormulaGraph (k : Nat) (f : CNF) : Graph :=
  ((List.range (variableBound f)).flatMap (placedVariableGraph k)) ++
    ((placeFormula [] f).mapIdx (fun j c => ungluedClauseGraph k (variableBound f) j c)).flatten

def assemblyVertex (flips : EndpointChoices) (k : Nat) (f : CNF) (v : Nat) : Nat :=
  let width := gadgetWidth k
  let n := variableBound f
  let j := v / width - n
  if v / width < n then v
  else orientedClauseVertex flips width n j ((placeFormula [] f)[j]?.getD []) (v % width)

theorem assemblyVertex_variable (flips : EndpointChoices) (k : Nat) (f : CNF)
    {v u : Nat} (hv : v < variableBound f) (hu : u < gadgetWidth k) :
    assemblyVertex flips k f (blockVertex (gadgetWidth k) v u) = blockVertex (gadgetWidth k) v u := by
  have hw : 0 < gadgetWidth k := by have := gadgetWidth_ge k; omega
  simp only [assemblyVertex, blockVertex_div hw v u hu, hv, ↓reduceIte]

theorem assemblyVertex_clause (flips : EndpointChoices) (k : Nat) (f : CNF)
    (j : Nat) (hj : j < (placeFormula [] f).length) {u : Nat} (hu : u < gadgetWidth k) :
    assemblyVertex flips k f (blockVertex (gadgetWidth k) (variableBound f+j) u) =
      orientedClauseVertex flips (gadgetWidth k) (variableBound f) j (placeFormula [] f)[j] u := by
  have hw : 0 < gadgetWidth k := by have := gadgetWidth_ge k; omega
  have hn : ¬ variableBound f+j < variableBound f := by omega
  simp [assemblyVertex, hn, blockVertex_div hw (variableBound f+j) u hu,
    blockVertex_mod hw (variableBound f+j) u hu, List.getElem?_eq_getElem hj]

theorem assemblyVertex_variableGraph (flips : EndpointChoices) (k : Nat) (f : CNF)
    {v : Nat} (hv : v < variableBound f) :
    mapGraph (assemblyVertex flips k f) (placedVariableGraph k v) = placedVariableGraph k v := by
  rw [placedVariableGraph, mapGraph_comp]
  exact mapGraph_congr_on (variableGraph_below k) (fun _ hu => assemblyVertex_variable flips k f hv hu)

theorem assemblyVertex_clauseGraph (flips : EndpointChoices) (k : Nat) (f : CNF)
    (j : Nat) (hj : j < (placeFormula [] f).length) :
    mapGraph (assemblyVertex flips k f)
      (ungluedClauseGraph k (variableBound f) j (placeFormula [] f)[j]) =
      orientedPlacedClauseGraph flips k (variableBound f) j (placeFormula [] f)[j] := by
  rw [ungluedClauseGraph, mapGraph_comp]
  apply mapGraph_congr_on (clauseGraph_below k _)
  intro u hu
  exact assemblyVertex_clause flips k f j hj hu

/-- The dart-assembly quotient has exactly the existing global output list. -/
theorem assemblyVertex_formulaGraph (flips : EndpointChoices) (k : Nat) (f : CNF) :
    mapGraph (assemblyVertex flips k f) (ungluedFormulaGraph k f) = orientedFormulaGraph flips k f := by
  change ((ungluedFormulaGraph k f).map (mapEdge (assemblyVertex flips k f))) = _
  simp only [ungluedFormulaGraph, orientedFormulaGraph, Oriented.formulaGraph,
    List.map_append, List.map_flatMap, List.map_flatten]
  congr 1
  · apply congrArg List.flatten
    apply List.map_congr_left
    intro v hv
    exact assemblyVertex_variableGraph flips k f (List.mem_range.mp hv)
  · congr 1
    apply List.ext_getElem
    · simp
    · intro j hj hj'
      have h : j < (placeFormula [] f).length := by simpa using hj
      simpa only [List.getElem_map, List.getElem_mapIdx, mapGraph,
        orientedPlacedClauseGraph] using assemblyVertex_clauseGraph flips k f j h

/-- One allocated endpoint identification, directed from variable to clause. -/
def AssemblyAttachment (flips : EndpointChoices) (k : Nat) (f : CNF) (x y : Nat) : Prop :=
  ∃ j : Fin (placeFormula [] f).length, ∃ i : Fin 3, ∃ p : PlacedLiteral, ∃ s : Bool,
    (placeFormula [] f)[j.val][i.val]? = some p ∧
    x = blockVertex (gadgetWidth k) p.literal.var
      (variableEndpoint p.port (if flips p then !s else s)) ∧
    y = blockVertex (gadgetWidth k) (variableBound f+j.val) (clauseEndpoint i.val s)

theorem assemblyVertex_variable_clause_fiber (flips : EndpointChoices)
    {k : Nat} {f : CNF} {v j u w : Nat}
    (hv : v < variableBound f) (hj : j < (placeFormula [] f).length)
    (hu : u < gadgetWidth k) (hw : w < gadgetWidth k)
    (he : assemblyVertex flips k f (blockVertex (gadgetWidth k) v u) =
      assemblyVertex flips k f (blockVertex (gadgetWidth k) (variableBound f+j) w)) :
    AssemblyAttachment flips k f (blockVertex (gadgetWidth k) v u)
      (blockVertex (gadgetWidth k) (variableBound f+j) w) := by
  letI : Oriented.Orientation := ⟨flips⟩
  rw [assemblyVertex_variable flips k f hv hu, assemblyVertex_clause flips k f j hj hw] at he
  obtain ⟨p,s,hp,hv',hu'⟩ := Oriented.variable_clause_vertex_intersection
    (by have := gadgetWidth_ge k; omega) hv hu hw he
  obtain ⟨i,hi,hip,hw'⟩ := attachmentAt_spec.mp hp
  exact ⟨⟨j,hj⟩,⟨i,hi⟩,p,s,hip,by rw [hv',hu']; rfl,by rw [hw']⟩

theorem assemblyVertex_clause_injective (flips : EndpointChoices)
    {k : Nat} {f : CNF} (hf : BoundedOccurrence f) {i j u v : Nat}
    (hi : i < (placeFormula [] f).length) (hj : j < (placeFormula [] f).length)
    (hu : u < gadgetWidth k) (hv : v < gadgetWidth k)
    (he : assemblyVertex flips k f (blockVertex (gadgetWidth k) (variableBound f+i) u) =
      assemblyVertex flips k f (blockVertex (gadgetWidth k) (variableBound f+j) v)) :
    blockVertex (gadgetWidth k) (variableBound f+i) u =
      blockVertex (gadgetWidth k) (variableBound f+j) v := by
  letI : Oriented.Orientation := ⟨flips⟩
  rw [assemblyVertex_clause flips k f i hi hu, assemblyVertex_clause flips k f j hj hv] at he
  by_cases hij : i = j
  · subst j
    have hc := List.getElem_mem hi
    have huv := orientedClauseVertex_injective flips (by have := gadgetWidth_ge k; omega)
      (hf.placed_clause_nodup hc) (hf.placed_clause_bounds hc) hu hv he
    rw [huv]
  · exact False.elim (Oriented.formulaGraph_clause_vertices_disjoint hf hi hj hij hu hv he)

theorem AssemblyAttachment.identified {flips : EndpointChoices} {k : Nat} {f : CNF}
    (hf : BoundedOccurrence f) {x y : Nat} (h : AssemblyAttachment flips k f x y) :
    assemblyVertex flips k f x = assemblyVertex flips k f y := by
  obtain ⟨j,i,p,s,hp,rfl,rfl⟩ := h
  have hv := (hf.placed_clause_bounds (List.getElem_mem j.isLt) p (List.mem_of_getElem? hp)).1
  have hwidth : 7 ≤ gadgetWidth k := by have := gadgetWidth_ge k; omega
  have hu := Nat.lt_of_lt_of_le (variableEndpoint_bound p.port (if flips p then !s else s)) hwidth
  have hc : clauseEndpoint i.val s < gadgetWidth k := by
    have ht := (by decide : ∀ i : Fin 3, ∀ s : Bool, clauseEndpoint i.val s < 12) i s
    have := gadgetWidth_ge k
    omega
  rw [assemblyVertex_variable flips k f hv hu, assemblyVertex_clause flips k f j.val j.isLt hc]
  exact (@Oriented.clauseVertex_attachment ⟨flips⟩ (gadgetWidth k) (variableBound f)
    j.val (placeFormula [] f)[j.val] i.val i.isLt p hp s).symm

/-- Complete fibers on the allocated vertex blocks. Distinct clause blocks
are never collapsed together, and a nontrivial fiber is precisely one port
endpoint identification. -/
theorem assemblyVertex_fiber (flips : EndpointChoices) {k : Nat} {f : CNF}
    (hf : BoundedOccurrence f) {x y : Nat}
    (hx : x < (variableBound f + (placeFormula [] f).length) * gadgetWidth k)
    (hy : y < (variableBound f + (placeFormula [] f).length) * gadgetWidth k) :
    assemblyVertex flips k f x = assemblyVertex flips k f y ↔
    x = y ∨ AssemblyAttachment flips k f x y ∨ AssemblyAttachment flips k f y x := by
  constructor
  · intro he
    have hw : 0 < gadgetWidth k := by have := gadgetWidth_ge k; omega
    have hxr := Nat.mod_lt x hw
    have hyr := Nat.mod_lt y hw
    have hxq := (Nat.div_lt_iff_lt_mul hw).mpr hx
    have hyq := (Nat.div_lt_iff_lt_mul hw).mpr hy
    have hxe : blockVertex (gadgetWidth k) (x / gadgetWidth k) (x % gadgetWidth k) = x := by
      simpa only [blockVertex, Nat.mul_comm] using Nat.div_add_mod x (gadgetWidth k)
    have hye : blockVertex (gadgetWidth k) (y / gadgetWidth k) (y % gadgetWidth k) = y := by
      simpa only [blockVertex, Nat.mul_comm] using Nat.div_add_mod y (gadgetWidth k)
    by_cases hxn : x / gadgetWidth k < variableBound f
    · by_cases hyn : y / gadgetWidth k < variableBound f
      · left
        simpa only [assemblyVertex, hxn, hyn, ↓reduceIte] using he
      · have hyj : y / gadgetWidth k - variableBound f < (placeFormula [] f).length := by omega
        have hey : blockVertex (gadgetWidth k)
            (variableBound f+(y / gadgetWidth k-variableBound f)) (y % gadgetWidth k) = y := by
          rw [show variableBound f+(y/gadgetWidth k-variableBound f) = y/gadgetWidth k by omega]
          exact hye
        right; left
        have he' : assemblyVertex flips k f
            (blockVertex (gadgetWidth k) (x/gadgetWidth k) (x%gadgetWidth k)) =
          assemblyVertex flips k f (blockVertex (gadgetWidth k)
            (variableBound f+(y/gadgetWidth k-variableBound f)) (y%gadgetWidth k)) := by
          rw [hxe,hey]; exact he
        have ht := assemblyVertex_variable_clause_fiber flips hxn hyj hxr hyr he'
        simpa only [hxe,hey] using ht
    · have hxj : x / gadgetWidth k - variableBound f < (placeFormula [] f).length := by omega
      have hex : blockVertex (gadgetWidth k)
          (variableBound f+(x / gadgetWidth k-variableBound f)) (x % gadgetWidth k) = x := by
        rw [show variableBound f+(x/gadgetWidth k-variableBound f) = x/gadgetWidth k by omega]
        exact hxe
      by_cases hyn : y / gadgetWidth k < variableBound f
      · right; right
        have he' : assemblyVertex flips k f
            (blockVertex (gadgetWidth k) (y/gadgetWidth k) (y%gadgetWidth k)) =
          assemblyVertex flips k f (blockVertex (gadgetWidth k)
            (variableBound f+(x/gadgetWidth k-variableBound f)) (x%gadgetWidth k)) := by
          rw [hye,hex]; exact he.symm
        have ht := assemblyVertex_variable_clause_fiber flips hyn hxj hyr hxr he'
        simpa only [hye,hex] using ht
      · have hyj : y / gadgetWidth k - variableBound f < (placeFormula [] f).length := by omega
        have hey : blockVertex (gadgetWidth k)
            (variableBound f+(y / gadgetWidth k-variableBound f)) (y % gadgetWidth k) = y := by
          rw [show variableBound f+(y/gadgetWidth k-variableBound f) = y/gadgetWidth k by omega]
          exact hye
        left
        have he' : assemblyVertex flips k f (blockVertex (gadgetWidth k)
            (variableBound f+(x/gadgetWidth k-variableBound f)) (x%gadgetWidth k)) =
          assemblyVertex flips k f (blockVertex (gadgetWidth k)
            (variableBound f+(y/gadgetWidth k-variableBound f)) (y%gadgetWidth k)) := by
          rw [hex,hey]; exact he
        have ht := assemblyVertex_clause_injective flips hf hxj hyj hxr hyr he'
        simpa only [hex,hey] using ht
  · rintro (rfl | h | h)
    · rfl
    · exact h.identified hf
    · exact (h.identified hf).symm

/-- Reversing equal boundary directions aligns opposite port endpoints. -/
theorem assembly_side_alignment (a b : Bool) :
    (if a == b then !(!b) else !b) = a ∧
      (if a == b then !b else b) = !a := by
  cases a <;> cases b <;> decide

theorem clauseEndpoint_lt_gadgetWidth (k : Nat) (i : Fin 3) (s : Bool) :
    clauseEndpoint i.val s < gadgetWidth k := by
  have ht := (by decide : ∀ i : Fin 3, ∀ s : Bool, clauseEndpoint i.val s < 12) i s
  have := gadgetWidth_ge k
  omega

/-- A variable endpoint is paired with at most one clause endpoint. -/
theorem AssemblyAttachment.target_unique {flips : EndpointChoices} {k : Nat} {f : CNF}
    (hf : BoundedOccurrence f) {x y z : Nat}
    (hxy : AssemblyAttachment flips k f x y) (hxz : AssemblyAttachment flips k f x z) : y = z := by
  have hid := (hxy.identified hf).symm.trans (hxz.identified hf)
  obtain ⟨j,i,p,s,hp,hx,rfl⟩ := hxy
  obtain ⟨j',i',p',s',hp',hx',rfl⟩ := hxz
  exact assemblyVertex_clause_injective flips hf j.isLt j'.isLt
    (clauseEndpoint_lt_gadgetWidth k i s) (clauseEndpoint_lt_gadgetWidth k i' s') hid

/-- Every endpoint of the actual unglued graph lies in the allocated blocks. -/
theorem ungluedFormulaGraph_below (k : Nat) (f : CNF) :
    VerticesBelow (ungluedFormulaGraph k f)
      ((variableBound f + (placeFormula [] f).length)*gadgetWidth k) := by
  intro e he
  rcases List.mem_append.mp he with he | he
  · obtain ⟨v,hv,he⟩ := List.mem_flatMap.mp he
    obtain ⟨d,hd,rfl⟩ := List.mem_map.mp he
    have hv' := List.mem_range.mp hv
    have hd' := variableGraph_below k d hd
    have hmul := Nat.mul_le_mul_right (gadgetWidth k)
      (show v+1 ≤ variableBound f+(placeFormula [] f).length by omega)
    rw [Nat.add_mul,Nat.one_mul] at hmul
    apply (edge_below _ _ _).mpr
    change v*gadgetWidth k+d.1 < _ ∧ v*gadgetWidth k+d.2 < _
    constructor <;> omega
  · obtain ⟨es,hes,he⟩ := List.mem_flatten.mp he
    obtain ⟨j,hj,rfl⟩ := List.mem_mapIdx.mp hes
    obtain ⟨d,hd,rfl⟩ := List.mem_map.mp he
    have hb := clauseGraph_below k (placeFormula [] f)[j] d hd
    have hmul := Nat.mul_le_mul_right (gadgetWidth k)
      (show variableBound f+j+1 ≤ variableBound f+(placeFormula [] f).length by omega)
    rw [Nat.add_mul,Nat.one_mul] at hmul
    apply (edge_below _ _ _).mpr
    change (variableBound f+j)*gadgetWidth k+d.1 < _ ∧
      (variableBound f+j)*gadgetWidth k+d.2 < _
    constructor <;> omega

end STACS2027

module

public import NPHardness.TaggedGraph
public import NPHardness.GridProperties

/-! Connect the emitter's allocated, already placed clauses to the completed
global reduction. Unused private clause blocks do not affect the graph. -/

@[expose] public section
namespace STACS2027
open Complexity.SAT

abbrev LocatedClause := Nat × List PlacedLiteral

def locatedGraph (k N : Nat) (xs : List LocatedClause) : Graph :=
  (List.range N).reverse.flatMap (placedVariableGraph k) ++
    xs.flatMap (fun x => placedClauseGraph k N x.1 x.2)

def locatedTag (xs : List LocatedClause) (i : Nat) : Nat := (xs[i]?.getD (0,[])).1

theorem locatedTag_injective {xs : List LocatedClause} (hn : (xs.map Prod.fst).Nodup)
    {i j : Nat} (hi : i < xs.length) (hj : j < xs.length)
    (he : locatedTag xs i = locatedTag xs j) : i = j := by
  apply hn.eq_of_getElem?_eq (by simpa using hi)
  simp only [locatedTag,List.getElem?_eq_getElem hi,List.getElem?_eq_getElem hj,Option.getD_some] at he
  simp [List.getElem?_map,List.getElem?_eq_getElem hi,List.getElem?_eq_getElem hj,he]

theorem locatedGraph_perm (k : Nat) (f : CNF) (xs : List LocatedClause)
    (hp : placeFormula [] f = xs.map Prod.snd) :
    (locatedGraph k (variableBound f) xs).Perm (taggedFormulaGraph k f (locatedTag xs)) := by
  unfold locatedGraph taggedFormulaGraph
  rw [hp]
  apply (List.Perm.flatMap_right _ (List.reverse_perm _)).append
  have he : ((xs.map Prod.snd).mapIdx
      (fun j c => placedClauseGraph k (variableBound f) (locatedTag xs j) c)) =
        xs.map (fun x => placedClauseGraph k (variableBound f) x.1 x.2) := by
    apply List.ext_getElem
    · simp
    · intro i hi _
      have h : i < xs.length := by simpa using hi
      simp [List.getElem_mapIdx,locatedTag,List.getElem?_eq_getElem h]
  rw [he]
  exact List.Perm.refl _

theorem locatedGraph_sat_iff_assignment {k N : Nat} (hk : 5 ≤ k) {f : CNF}
    (hf : BoundedOccurrence f) (hd : ClauseVariablesDistinct f)
    (xs : List LocatedClause) (hp : placeFormula [] f = xs.map Prod.snd)
    (hn : (xs.map Prod.fst).Nodup) (hN : variableBound f = N) :
    Satisfiable f ↔ HasAssignment (locatedGraph k N xs) k f.length := by
  have hlen : f.length = xs.length := by
    have he := congrArg List.length hp
    simpa only [placeFormula_length,List.length_map] using he
  have ht : ∀ a, a < f.length → ∀ b, b < f.length → locatedTag xs a = locatedTag xs b → a = b := by
    intro a ha b hb he
    exact locatedTag_injective hn (by omega) (by omega) he
  rw [← hN]
  exact (taggedFormulaGraph_sat_iff_assignment hk hf hd (locatedTag xs) ht).trans
    (hasAssignment_graph_perm (locatedGraph_perm k f xs hp) k f.length).symm

def locateClause (r : Nat) (x : Nat × Clause) : LocatedClause :=
  (x.1,x.2.map (fun l => PlacedLiteral.mk l r))

def locateCopyClause (S : Nat) (x : Nat × Clause) : LocatedClause :=
  (x.1,(sourceCopies (gridCopyClause S x.1 x.2)).map (fun l => PlacedLiteral.mk l 1))

def gridLocated (S : Nat) (ws xs : List (Nat × Clause)) : List LocatedClause :=
  ws.map (locateClause 0) ++ xs.map (locateCopyClause S)

theorem gridLocated_placement {V S : Nat} {ws xs : List (Nat × Clause)}
    (hw : ws.map Prod.snd = gridWheelFamily V (3*S))
    (hs : ∀ x ∈ xs, x.1 < S)
    (hc : ∀ x ∈ xs, x.2.length ≤ 3 ∧ ∀ l ∈ x.2, l.var < V)
    (hn : xs.Pairwise (fun x y => y.1 < x.1)) :
    placeFormula [] (gridBoundedFormula V S xs) = (gridLocated S ws xs).map Prod.snd := by
  rw [gridBoundedFormula_placement hs hc hn]
  simp only [gridLocated,List.map_append,List.map_map,locateClause,locateCopyClause,
    gridCopyFormula,Function.comp_def]
  rw [← hw,List.map_map]
  rfl

theorem gridLocated_tags_nodup {S : Nat} {ws xs : List (Nat × Clause)}
    (hw : ws.Pairwise (fun x y => y.1 < x.1)) (hb : ∀ w ∈ ws, S ≤ w.1)
    (hx : xs.Pairwise (fun x y => y.1 < x.1)) (hs : ∀ x ∈ xs, x.1 < S) :
    ((gridLocated S ws xs).map Prod.fst).Nodup := by
  simp only [gridLocated,List.map_append,List.map_map,locateClause,locateCopyClause,Function.comp_def]
  apply List.nodup_append.mpr
  have hn : ∀ ys : List (Nat × Clause), ys.Pairwise (fun x y => y.1 < x.1) →
      (ys.map Prod.fst).Nodup := by
    intro ys hy
    rw [List.nodup_iff_pairwise_ne,List.pairwise_map]
    exact hy.imp (fun h he => by omega)
  refine ⟨hn ws hw,hn xs hx,?_⟩
  intro a ha b hb' he
  obtain ⟨w,hw',rfl⟩ := List.mem_map.mp ha
  obtain ⟨x,hx',rfl⟩ := List.mem_map.mp hb'
  have := hb w hw'
  have := hs x hx'
  omega

end STACS2027

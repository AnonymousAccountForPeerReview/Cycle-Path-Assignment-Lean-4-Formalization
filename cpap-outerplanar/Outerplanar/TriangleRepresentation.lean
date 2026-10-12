module

public import Outerplanar.TriangleFamily
public import Outerplanar.PlanarMinor
import Mathlib.Tactic

/-! Enumerated triangles are finite unordered triples with exactly the same edge union. -/

@[expose] public section
namespace STACS2027.TriangleMatching

/-- The unordered vertices of one enumerated triangle. -/
def enumeratedVertices (g : Graph) (i : Fin (cycles g 3).length) : Finset Nat :=
  (triangle g i.val).toFinset

/-- Convert a selected enumerated family to unordered triples. -/
def enumeratedFamily (g : Graph) (S : Finset (Fin (cycles g 3).length)) : Finset (Finset Nat) :=
  S.image (enumeratedVertices g)

theorem triangle_vertexSides {g : Graph} {c : Cycle} (hc : IsCycle g 3 c) :
    vertexSides c.toFinset=(cycleEdges c).toFinset := by
  obtain ⟨a,b,u,rfl,hab,hau,hbu⟩ := triangle_shape hc
  have hedge : cycleEdges [a,b,u]=[edge a b,edge b u,edge u a] := by
    simp [cycleEdges,pathEdges]
  rw [hedge]
  ext e
  simp only [vertexSides,Finset.mem_biUnion,Finset.mem_image,Finset.mem_erase,List.mem_toFinset]
  simp only [List.mem_cons,List.not_mem_nil,or_false]
  constructor
  · rintro ⟨x,hx,y,⟨hyx,hy⟩,rfl⟩
    rcases hx with rfl|rfl|rfl <;> rcases hy with rfl|rfl|rfl
    all_goals simp_all [edge_comm]
  · rintro (rfl|rfl|rfl)
    · exact ⟨a,Or.inl rfl,b,⟨Ne.symm hab,Or.inr (Or.inl rfl)⟩,rfl⟩
    · exact ⟨b,Or.inr (Or.inl rfl),u,⟨Ne.symm hbu,Or.inr (Or.inr rfl)⟩,rfl⟩
    · exact ⟨u,Or.inr (Or.inr rfl),a,⟨hau,Or.inl rfl⟩,rfl⟩

theorem enumeratedVertices_sides (g : Graph) (i : Fin (cycles g 3).length) :
    vertexSides (enumeratedVertices g i)=triangleSides g i :=
  triangle_vertexSides (triangle_isCycle g i.isLt)

theorem enumeratedVertices_injective (g : Graph) : Function.Injective (enumeratedVertices g) := by
  intro i j he
  have hs : SameCycle (triangle g i.val) (triangle g j.val) := by
    have hedge := congrArg vertexSides he
    rw [enumeratedVertices_sides,enumeratedVertices_sides] at hedge
    change (cycleEdges (triangle g i.val)).toFinset=(cycleEdges (triangle g j.val)).toFinset at hedge
    refine ⟨?_,?_⟩
    · intro e he
      exact List.mem_toFinset.mp (hedge ▸ List.mem_toFinset.mpr he)
    · intro e he
      exact List.mem_toFinset.mp (hedge.symm ▸ List.mem_toFinset.mpr he)
  have hg (k : Fin (cycles g 3).length) : triangle g k.val=(cycles g 3)[k.val] := by
    simp [triangle,List.getD_eq_getElem?_getD]
  have hpair := List.pairwise_iff_getElem.mp (cycles_pairwise_different g 3)
  apply Fin.ext
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hij|hji
  · exact hpair i.val j.val i.isLt j.isLt hij (by simpa only [hg] using hs)
  · exact hpair j.val i.val j.isLt i.isLt hji (by
      simpa only [hg] using (show SameCycle (triangle g j.val) (triangle g i.val) from ⟨hs.2,hs.1⟩))

theorem enumeratedFamily_card (g : Graph) (S : Finset (Fin (cycles g 3).length)) :
    (enumeratedFamily g S).card=S.card := Finset.card_image_of_injective S (enumeratedVertices_injective g)

theorem enumeratedFamily_triangles (g : Graph) (S : Finset (Fin (cycles g 3).length)) :
    VertexTriangleFamily (enumeratedFamily g S) := by
  intro T hT
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hT
  have hc := triangle_isCycle g i.isLt
  exact (List.toFinset_card_of_nodup hc.2.2.1).trans hc.2.1

theorem enumeratedFamily_edges (g : Graph) (S : Finset (Fin (cycles g 3).length)) :
    vertexSideUnion (enumeratedFamily g S)=S.biUnion (triangleSides g) := by
  ext e
  simp only [vertexSideUnion,enumeratedFamily,Finset.mem_biUnion,Finset.mem_image]
  constructor
  · rintro ⟨T,⟨i,hi,rfl⟩,he⟩
    exact ⟨i,hi,(enumeratedVertices_sides g i) ▸ he⟩
  · rintro ⟨i,hi,he⟩
    exact ⟨enumeratedVertices g i,⟨i,hi,rfl⟩,(enumeratedVertices_sides g i).symm ▸ he⟩

theorem vertexSides_proper {T : Finset Nat} {e : Edge} (he : e∈vertexSides T) : e.1<e.2 := by
  obtain ⟨u,hu,hv⟩ := Finset.mem_biUnion.mp he
  obtain ⟨v,hv',heq⟩ := Finset.mem_image.mp hv
  subst e
  have hne := (Finset.mem_erase.mp hv').1
  dsimp [edge]
  omega

theorem enumeratedFamily_graph_planar {g : Graph} (hp : Complexity.PlanarGraph g)
    (S : Finset (Fin (cycles g 3).length)) :
    Complexity.PlanarGraph (vertexFamilyGraph (enumeratedFamily g S)) := by
  apply hp.subperm
  apply (Finset.nodup_toList _).subperm
  intro e he
  have he' : e∈vertexSideUnion (enumeratedFamily g S) := Finset.mem_toList.mp he
  rw [enumeratedFamily_edges] at he'
  obtain ⟨i,hi,he⟩ := Finset.mem_biUnion.mp he'
  exact (triangle_isCycle g i.isLt).2.2.2 e (List.mem_toFinset.mp he)

end STACS2027.TriangleMatching

module

public import Outerplanar.TriangleFamily
public import Outerplanar.TriangleImageCard
public import Outerplanar.TriangleEdgeCount
import Mathlib.Tactic

/-! Cardinality and incidence bounds for finite triangle-family contraction. -/

@[expose] public section
namespace STACS2027.TriangleMatching

theorem edge_mem_vertexSides {T : Finset Nat} {u v : Nat}
    (hu : u∈T) (hv : v∈T) (hne : u≠v) : edge u v∈vertexSides T := by
  exact Finset.mem_biUnion.mpr ⟨u,hu,
    Finset.mem_image.mpr ⟨v,Finset.mem_erase.mpr ⟨hne.symm,hv⟩,rfl⟩⟩

theorem edge_mem_edgeVertices {E : Finset Edge} {u w : Nat}
    (he : edge u w∈E) : w∈edgeVertices E := by
  apply Finset.mem_biUnion.mpr
  refine ⟨edge u w,he,?_⟩
  by_cases h : u≤w
  · simp [edge,h]
  · simp [edge,Nat.le_of_lt (Nat.lt_of_not_ge h)]

theorem identifyTriangle_eq_of_not_mem {u v : Nat} {T : Finset Nat} (hv : v∉T) :
    identifyTriangle u v T=T := by
  change T.image (identifyVertex u v)=T
  calc
    _=T.image id := Finset.image_congr (fun x hx=>by
      have h : x≠v := fun he=>hv (he ▸ hx)
      simp [identifyVertex,h])
    _=T := by simp

theorem identifyTriangle_eq_of_mem {u v : Nat} {T : Finset Nat} (hv : v∈T) :
    identifyTriangle u v T=insert u (T.erase v) := by
  have he := identifyTriangle_eq_of_not_mem (u:=u) (v:=v)
    (T:=T.erase v) (Finset.notMem_erase v T)
  unfold identifyTriangle at he ⊢
  calc
    T.image (identifyVertex u v)=(insert v (T.erase v)).image (identifyVertex u v) := by
      exact congrArg (fun R : Finset Nat=>R.image (identifyVertex u v))
        (Finset.insert_erase hv).symm
    _=insert (identifyVertex u v v) ((T.erase v).image (identifyVertex u v)) :=
      Finset.image_insert (identifyVertex u v) v (T.erase v)
    _=insert u (T.erase v) := by rw [he];simp [identifyVertex]

theorem identifyVertex_injOn {u v : Nat} {T : Finset Nat}
    (hnot : ¬(u∈T ∧ v∈T)) : Set.InjOn (identifyVertex u v) (↑T : Set Nat) := by
  intro x hx y hy hxy
  by_cases hxv : x=v
  · subst x
    by_cases hyv : y=v
    · exact hyv.symm
    · have huy : u=y := by simpa [identifyVertex,hyv] using hxy
      exact False.elim (hnot ⟨huy ▸ hy,hx⟩)
  · by_cases hyv : y=v
    · subst y
      have hxu : x=u := by simpa [identifyVertex,hxv] using hxy
      exact False.elim (hnot ⟨hxu ▸ hx,hy⟩)
    · simpa [identifyVertex,hxv,hyv] using hxy

theorem identifyFamily_isTriangles {S : Finset (Finset Nat)} {u v : Nat}
    (hS : VertexTriangleFamily S) : VertexTriangleFamily (identifyFamily u v S) := by
  intro T hT
  obtain ⟨R,hR,rfl⟩ := Finset.mem_image.mp hT
  have hr := Finset.mem_filter.mp hR
  exact (Finset.card_image_of_injOn (identifyVertex_injOn hr.2)).trans (hS R hr.1)

theorem mixed_collision_exceptional {S : Finset (Finset Nat)} {E : Finset Edge}
    {u v : Nat} (hS : VertexTriangleFamily S) (hE : vertexSideUnion S⊆E)
    (hsmall : (commonVertices E u v).card≤2) {T U : Finset Nat}
    (hT : T∈S) (hU : U∈S) (huT : u∉T) (hvT : v∈T) (hvU : v∉U)
    (himage : identifyTriangle u v T=identifyTriangle u v U) :
    T=insert v (commonVertices E u v) := by
  have heq : insert u (T.erase v)=U := by
    rw [identifyTriangle_eq_of_mem hvT,identifyTriangle_eq_of_not_mem hvU] at himage
    exact himage
  have huU : u∈U := by rw [←heq];simp
  have hsub : T.erase v⊆commonVertices E u v := by
    intro w hw
    have hwT := (Finset.mem_erase.mp hw).2
    have hwv := (Finset.mem_erase.mp hw).1
    have hwu : w≠u := fun h=>huT (h ▸ hwT)
    have hwU : w∈U := by rw [←heq];exact Finset.mem_insert_of_mem hw
    have huw : edge u w∈E := hE (Finset.mem_biUnion.mpr
      ⟨U,hU,edge_mem_vertexSides huU hwU hwu.symm⟩)
    have hvw : edge v w∈E := hE (Finset.mem_biUnion.mpr
      ⟨T,hT,edge_mem_vertexSides hvT hwT hwv.symm⟩)
    exact Finset.mem_filter.mpr ⟨edge_mem_edgeVertices huw,hwu,hwv,huw,hvw⟩
  have hcard : (T.erase v).card=2 := by
    rw [Finset.card_erase_of_mem hvT,hS T hT]
  have he : T.erase v=commonVertices E u v :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  rw [←he,Finset.insert_erase hvT]

theorem surviving_collision {S : Finset (Finset Nat)} {E : Finset Edge} {u v : Nat}
    (hS : VertexTriangleFamily S) (hE : vertexSideUnion S⊆E)
    (hsmall : (commonVertices E u v).card≤2) {T U : Finset Nat}
    (hT : T∈S) (hU : U∈S) (hnt : ¬(u∈T ∧ v∈T)) (hnu : ¬(u∈U ∧ v∈U))
    (himage : identifyTriangle u v T=identifyTriangle u v U) :
    T=U ∨ T=insert v (commonVertices E u v) ∨ U=insert v (commonVertices E u v) := by
  by_cases hvT : v∈T
  · have huT : u∉T := fun h=>hnt ⟨h,hvT⟩
    by_cases hvU : v∈U
    · have huU : u∉U := fun h=>hnu ⟨h,hvU⟩
      have he := congrArg (fun R : Finset Nat=>R.erase u) himage
      rw [identifyTriangle_eq_of_mem hvT,identifyTriangle_eq_of_mem hvU] at he
      have huTe : u∉T.erase v := by simp [huT]
      have huUe : u∉U.erase v := by simp [huU]
      change (insert u (T.erase v)).erase u=(insert u (U.erase v)).erase u at he
      rw [Finset.erase_insert huTe,Finset.erase_insert huUe] at he
      left
      calc T=insert v (T.erase v) := (Finset.insert_erase hvT).symm
           _=insert v (U.erase v) := by rw [he]
           _=U := Finset.insert_erase hvU
    · exact Or.inr (Or.inl (mixed_collision_exceptional hS hE hsmall hT hU huT hvT hvU himage))
  · by_cases hvU : v∈U
    · have huU : u∉U := fun h=>hnu ⟨h,hvU⟩
      exact Or.inr (Or.inr (mixed_collision_exceptional hS hE hsmall hU hT huU hvU hvT himage.symm))
    · left
      simpa [identifyTriangle_eq_of_not_mem hvT,identifyTriangle_eq_of_not_mem hvU] using himage

noncomputable def thirdVertex (u v : Nat) (T : Finset Nat) : Nat :=
  ((T.erase u).erase v).toList.headD 0

theorem collapsed_shape {T : Finset Nat} {u v : Nat} (hne : u≠v)
    (hc : T.card=3) (hu : u∈T) (hv : v∈T) :
    T={u,v,thirdVertex u v T} ∧ thirdVertex u v T≠u ∧ thirdVertex u v T≠v := by
  have hv' : v∈T.erase u := Finset.mem_erase.mpr ⟨hne.symm,hv⟩
  have hcard : ((T.erase u).erase v).card=1 := by
    rw [Finset.card_erase_of_mem hv',Finset.card_erase_of_mem hu,hc]
  obtain ⟨w,hw⟩ := Finset.card_eq_one.mp hcard
  have hthird : thirdVertex u v T=w := by simp [thirdVertex,hw]
  have hwmem : w∈(T.erase u).erase v := by rw [hw];simp
  have hwv := (Finset.mem_erase.mp hwmem).1
  have hwu := (Finset.mem_erase.mp (Finset.mem_erase.mp hwmem).2).1
  refine ⟨?_,by simpa [hthird] using hwu,by simpa [hthird] using hwv⟩
  calc T=insert u (T.erase u) := (Finset.insert_erase hu).symm
       _=insert u (insert v ((T.erase u).erase v)) := by rw [Finset.insert_erase hv']
       _={u,v,thirdVertex u v T} := by rw [hw,hthird]

theorem collapsed_card_le_common {S : Finset (Finset Nat)} {E : Finset Edge} {u v : Nat}
    (hne : u≠v) (hS : VertexTriangleFamily S) (hE : vertexSideUnion S⊆E) :
    (S.filter fun T=>u∈T ∧ v∈T).card≤(commonVertices E u v).card := by
  apply Finset.card_le_card_of_injOn (thirdVertex u v)
  · intro T hT
    have ht := Finset.mem_filter.mp hT
    obtain ⟨hshape,hwu,hwv⟩ := collapsed_shape hne (hS T ht.1) ht.2.1 ht.2.2
    have hwT : thirdVertex u v T∈T :=
      (Finset.ext_iff.mp hshape (thirdVertex u v T)).mpr (by simp)
    have huw : edge u (thirdVertex u v T)∈E := hE (Finset.mem_biUnion.mpr
      ⟨T,ht.1,edge_mem_vertexSides ht.2.1 hwT hwu.symm⟩)
    have hvw : edge v (thirdVertex u v T)∈E := hE (Finset.mem_biUnion.mpr
      ⟨T,ht.1,edge_mem_vertexSides ht.2.2 hwT hwv.symm⟩)
    exact Finset.mem_filter.mpr ⟨edge_mem_edgeVertices huw,hwu,hwv,huw,hvw⟩
  · intro T hT U hU hthird
    have ht := Finset.mem_filter.mp hT
    have hu := Finset.mem_filter.mp hU
    rw [(collapsed_shape hne (hS T ht.1) ht.2.1 ht.2.2).1,
      (collapsed_shape hne (hS U hu.1) hu.2.1 hu.2.2).1,hthird]

theorem identifyFamily_card_bound {S : Finset (Finset Nat)} {E : Finset Edge} {u v : Nat}
    (hne : u≠v) (hS : VertexTriangleFamily S) (hE : vertexSideUnion S⊆E)
    (hsmall : (commonVertices E u v).card≤2) :
    S.card≤(identifyFamily u v S).card+(commonVertices E u v).card+1 := by
  have hsurv := card_le_image_add_one (S.filter fun T=>¬(u∈T ∧ v∈T))
    (identifyTriangle u v) (insert v (commonVertices E u v)) (by
      intro T hT U hU hxy
      have ht := Finset.mem_filter.mp hT
      have hu := Finset.mem_filter.mp hU
      exact surviving_collision hS hE hsmall ht.1 hu.1 ht.2 hu.2 hxy)
  have hcol := collapsed_card_le_common hne hS hE
  have hpart := Finset.card_filter_add_card_filter_not (s:=S) (p:=fun T=>u∈T ∧ v∈T)
  change (S.filter fun T=>¬(u∈T ∧ v∈T)).card≤(identifyFamily u v S).card+1 at hsurv
  omega

theorem identifyFamily_sideUnion_subset {S : Finset (Finset Nat)} {E : Finset Edge}
    {u v : Nat} (hE : vertexSideUnion S⊆E) :
    vertexSideUnion (identifyFamily u v S)⊆identifyEdges u v E := by
  intro e he
  obtain ⟨T,hT,he⟩ := Finset.mem_biUnion.mp he
  obtain ⟨R,hR,rfl⟩ := Finset.mem_image.mp hT
  have hr := Finset.mem_filter.mp hR
  obtain ⟨x,hx,hxy⟩ := Finset.mem_biUnion.mp he
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hxy
  obtain ⟨b,hb,hby⟩ := Finset.mem_image.mp (Finset.mem_erase.mp hy).2
  obtain ⟨a,ha,hax⟩ := Finset.mem_image.mp hx
  have hab : a≠b := by
    intro h
    have hxy : y=x := by rw [←hax,←hby,h]
    exact (Finset.mem_erase.mp hy).1 hxy
  have hedge : edge a b∈E := hE (Finset.mem_biUnion.mpr
    ⟨R,hr.1,edge_mem_vertexSides ha hb hab⟩)
  apply Finset.mem_image.mpr
  refine ⟨edge a b,Finset.mem_erase.mpr ⟨?_,hedge⟩,?_⟩
  · intro heq
    rcases (edge_eq_iff ..).mp heq with h | h
    · exact hr.2 ⟨h.1 ▸ ha,h.2 ▸ hb⟩
    · exact hr.2 ⟨h.2 ▸ hb,h.1 ▸ ha⟩
  · rw [identifyEdge_map,hax,hby]

end STACS2027.TriangleMatching

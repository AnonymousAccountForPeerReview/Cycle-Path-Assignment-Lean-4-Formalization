module

public import NPHardness.PlanarAssemblyIndexDarts
public import NPHardness.PlanarGluingSpherical
public import NPHardness.PlanarGluingReflection

/-! Concatenation of actual local gadget hypermaps. The prefix-offset dart
injections used by the graph constructor commute with each local permutation. -/

@[expose] public section
namespace STACS2027.PlanarAssembly
open Complexity Complexity.Planar PlanarGluing

abbrev LocalMaps (gs : List Graph) := (i : Fin gs.length) → Hypermap (2*gs[i.val].length)

def emptyMap : Hypermap 0 where
  edge := Fin.elim0
  node := Fin.elim0
  face := Fin.elim0
  edgeK d := Fin.elim0 d

def tailMaps (g : Graph) (gs : List Graph) (H : LocalMaps (g::gs)) : LocalMaps gs :=
  fun i => H ⟨i.val+1,by have := i.isLt; simp only [List.length_cons]; omega⟩

def sumCast (g : Graph) (gs : List Graph) :
    DartEquiv (2*g.length+2*gs.flatten.length) (2*(g::gs).flatten.length) :=
  DartEquiv.cast (by simp [Nat.mul_add])

def piecesMap : (gs : List Graph) → LocalMaps gs → Hypermap (2*gs.flatten.length)
  | [],_ => emptyMap
  | g::gs,H => (sumCast g gs).hypermap
      (disjointSum (H ⟨0,by simp⟩) (piecesMap gs (tailMaps g gs H)))

theorem sumCast_left (g : Graph) (gs : List Graph) (d : Fin (2*g.length)) :
    (sumCast g gs).toFun (left d) = blockDart (g::gs) ⟨0,by simp⟩ d := by
  apply Fin.ext
  simp [sumCast,DartEquiv.cast,left,blockDart,pieceOffset]

theorem sumCast_right (g : Graph) (gs : List Graph) (i : Fin gs.length)
    (d : Fin (2*gs[i.val].length)) :
    (sumCast g gs).toFun (right (blockDart gs i d)) =
      blockDart (g::gs) ⟨i.val+1,by have := i.isLt; simp only [List.length_cons]; omega⟩ d := by
  apply Fin.ext
  simp only [sumCast,DartEquiv.cast,right,blockDart,pieceOffset,List.take_succ_cons,
    List.flatten_cons,List.length_append,Nat.mul_add]
  omega

inductive MapField where
  | edge | node | face

def MapField.read (which : MapField) {n : Nat} (G : Hypermap n) : Fin n → Fin n :=
  match which with
  | .edge => G.edge
  | .node => G.node
  | .face => G.face

theorem field_transport (which : MapField) {n m : Nat} (e : DartEquiv n m)
    (G : Hypermap n) (d : Fin n) :
    which.read (e.hypermap G) (e.toFun d) = e.toFun (which.read G d) := by
  cases which <;> exact e.conjugate_toFun _ d

theorem field_left (which : MapField) {n m : Nat} (G : Hypermap n) (H : Hypermap m) (d : Fin n) :
    which.read (disjointSum G H) (left d) = left (which.read G d) := by
  cases which <;> exact sumPerm_left _ _ d

theorem field_right (which : MapField) {n m : Nat} (G : Hypermap n) (H : Hypermap m) (d : Fin m) :
    which.read (disjointSum G H) (right d) = right (which.read H d) := by
  cases which <;> exact sumPerm_right _ _ d

theorem piecesMap_field (which : MapField) (gs : List Graph) (H : LocalMaps gs)
    (i : Fin gs.length) (d : Fin (2*gs[i.val].length)) :
    which.read (piecesMap gs H) (blockDart gs i d) =
      blockDart gs i (which.read (H i) d) := by
  induction gs with
  | nil => exact Fin.elim0 i
  | cons g gs ih =>
    rcases i with ⟨i,hi⟩
    cases i with
    | zero =>
      rw [← sumCast_left]
      change which.read ((sumCast g gs).hypermap _) _ = _
      rw [field_transport,field_left,sumCast_left]
    | succ i =>
      have hi' : i < gs.length := by simpa using hi
      change which.read (piecesMap (g::gs) H) (blockDart (g::gs) ⟨i+1,hi⟩ d) = _
      rw [← sumCast_right g gs ⟨i,hi'⟩ d]
      change which.read ((sumCast g gs).hypermap _) _ = _
      rw [field_transport,field_right,ih (tailMaps g gs H),sumCast_right]
      rfl

theorem piecesMap_iterate (which : MapField) (gs : List Graph) (H : LocalMaps gs)
    (i : Fin gs.length) (k : Nat) (d : Fin (2*gs[i.val].length)) :
    iterate (which.read (piecesMap gs H)) k (blockDart gs i d) =
      blockDart gs i (iterate (which.read (H i)) k d) := by
  induction k generalizing d with
  | zero => rfl
  | succ k ih => rw [iterate,piecesMap_field,ih]; rfl

theorem blockDart_surjective (gs : List Graph) (d : Fin (2*gs.flatten.length)) :
    ∃ i : Fin gs.length, ∃ e : Fin (2*gs[i.val].length), blockDart gs i e = d := by
  induction gs with
  | nil => exact Fin.elim0 d
  | cons g gs ih =>
    have hd : (sumCast g gs).toFun ((sumCast g gs).invFun d) = d := (sumCast g gs).right_inv d
    rcases cases_dart ((sumCast g gs).invFun d) with ⟨e,he⟩ | ⟨e,he⟩
    · rw [← he,sumCast_left] at hd
      exact ⟨⟨0,by simp⟩,e,hd⟩
    · obtain ⟨i,a,ha⟩ := ih e
      rw [← he,← ha,sumCast_right] at hd
      exact ⟨⟨i.val+1,by have := i.isLt; simp only [List.length_cons]; omega⟩,a,hd⟩

theorem piecesMap_spherical (gs : List Graph) (H : LocalMaps gs)
    (h : ∀ i, 2*(H i).componentCount+2*gs[i.val].length ≤ (H i).eulerRhs) :
    2*(piecesMap gs H).componentCount+2*gs.flatten.length ≤ (piecesMap gs H).eulerRhs := by
  induction gs with
  | nil => exact Nat.le_refl 0
  | cons g gs ih =>
    have hh := h ⟨0,by simp⟩
    have ht := ih (tailMaps g gs H) (fun i => h ⟨i.val+1,by have := i.isLt; simp only [List.length_cons]; omega⟩)
    have hc := disjointSum_components_le (H ⟨0,by simp⟩) (piecesMap gs (tailMaps g gs H))
    have he := disjointSum_euler_ge (H ⟨0,by simp⟩) (piecesMap gs (tailMaps g gs H))
    have hs : 2*(disjointSum (H ⟨0,by simp⟩) (piecesMap gs (tailMaps g gs H))).componentCount +
        (2*g.length+2*gs.flatten.length) ≤
        (disjointSum (H ⟨0,by simp⟩) (piecesMap gs (tailMaps g gs H))).eulerRhs := by
      simp only [List.getElem_cons_zero] at hh
      omega
    exact (sumCast g gs).spherical _ hs

theorem piecesMap_nodes (gs : List Graph) (H : LocalMaps gs)
    (hN : ∀ i d e, Reaches (H i).node d e ↔ halfEdgeEnd gs[i.val] d.val = halfEdgeEnd gs[i.val] e.val)
    (hdisj : ∀ i j : Fin gs.length, i ≠ j → ∀ d : Fin (2*gs[i.val].length),
      ∀ e : Fin (2*gs[j.val].length), halfEdgeEnd gs[i.val] d.val ≠ halfEdgeEnd gs[j.val] e.val)
    (x y : Fin (2*gs.flatten.length)) :
    Reaches (piecesMap gs H).node x y ↔ halfEdgeEnd gs.flatten x.val = halfEdgeEnd gs.flatten y.val := by
  obtain ⟨i,d,rfl⟩ := blockDart_surjective gs x
  obtain ⟨j,e,rfl⟩ := blockDart_surjective gs y
  constructor
  · rintro ⟨k,hk⟩
    have hk' := piecesMap_iterate .node gs H i k d
    change iterate (piecesMap gs H).node k (blockDart gs i d) =
      blockDart gs i (iterate (H i).node k d) at hk'
    rw [hk'] at hk
    have hij := blockDart_block_injective gs hk
    subst j
    have he := blockDart_injective gs i hk
    rw [blockDart_end,blockDart_end]
    exact (hN i d e).mp ⟨k,he⟩
  · intro he
    rw [blockDart_end,blockDart_end] at he
    have hij : i=j := by
      apply Classical.byContradiction
      intro hne
      exact hdisj i j hne d e he
    subst j
    obtain ⟨k,hk⟩ := (hN i d e).mpr he
    refine ⟨k,?_⟩
    have ht := piecesMap_iterate .node gs H i k d
    change iterate (piecesMap gs H).node k (blockDart gs i d) =
      blockDart gs i (iterate (H i).node k d) at ht
    rw [ht,hk]

theorem piecesMap_edges (gs : List Graph) (H : LocalMaps gs)
    (hE : ∀ i d, (H i).edge d = graphEdge d) (x : Fin (2*gs.flatten.length)) :
    (piecesMap gs H).edge x = graphEdge x := by
  obtain ⟨i,d,rfl⟩ := blockDart_surjective gs x
  have h := piecesMap_field .edge gs H i d
  change (piecesMap gs H).edge (blockDart gs i d) = blockDart gs i ((H i).edge d) at h
  rw [h,hE,blockDart_graphEdge]

theorem piecesMap_embedding (gs : List Graph) (H : LocalMaps gs)
    (h : ∀ i, IsGraphEmbedding gs[i.val] (H i))
    (hs : ∀ i, 2*(H i).componentCount+2*gs[i.val].length ≤ (H i).eulerRhs)
    (hdisj : ∀ i j : Fin gs.length, i ≠ j → ∀ d : Fin (2*gs[i.val].length),
      ∀ e : Fin (2*gs[j.val].length), halfEdgeEnd gs[i.val] d.val ≠ halfEdgeEnd gs[j.val] e.val) :
    IsGraphEmbedding gs.flatten (piecesMap gs H) := by
  refine ⟨fun d => congrArg Fin.val (piecesMap_edges gs H (fun i d => Fin.ext ((h i).1 d)) d),
    piecesMap_nodes gs H (fun i => (h i).2.1) hdisj,?_⟩
  rw [planar_iff]
  have hh := piecesMap_spherical gs H hs
  omega

theorem piecesMap_step_project (gs : List Graph) (H : LocalMaps gs)
    (i : Fin gs.length) {d : Fin (2*gs[i.val].length)} {y : Fin (2*gs.flatten.length)}
    (h : Linked.Step (piecesMap gs H) (blockDart gs i d) y) :
    ∃ e, blockDart gs i e = y ∧ Linked.Step (H i) d e := by
  rcases h with h | h | h
  · exact ⟨(H i).edge d,(piecesMap_field .edge gs H i d).symm.trans h,Or.inl rfl⟩
  · exact ⟨(H i).node d,(piecesMap_field .node gs H i d).symm.trans h,Or.inr (Or.inl rfl)⟩
  · exact ⟨(H i).face d,(piecesMap_field .face gs H i d).symm.trans h,Or.inr (Or.inr rfl)⟩

theorem piecesMap_path_project (gs : List Graph) (H : LocalMaps gs)
    (i : Fin gs.length) {d : Fin (2*gs[i.val].length)} {y : Fin (2*gs.flatten.length)}
    (h : LinkedPath (piecesMap gs H) (blockDart gs i d) y) :
    ∃ e, blockDart gs i e = y ∧ LinkedPath (H i) d e := by
  obtain ⟨k,hk⟩ := h
  induction k generalizing y with
  | zero => exact ⟨d,(Linked.linked_zero _ _ _).mp hk,LinkedPath.refl _ _⟩
  | succ k ih =>
    rcases (Linked.linked_succ _ k (blockDart gs i d) y).mp hk with h | ⟨z,hz,hs⟩
    · exact ih h
    · obtain ⟨z',rfl,hz'⟩ := ih hz
      obtain ⟨e,he,hs'⟩ := piecesMap_step_project gs H i hs
      exact ⟨e,he,hz'.trans (LinkedPath.step (H i) hs')⟩

theorem piecesMap_path_same_piece (gs : List Graph) (H : LocalMaps gs)
    (i j : Fin gs.length) (d : Fin (2*gs[i.val].length)) (e : Fin (2*gs[j.val].length))
    (h : LinkedPath (piecesMap gs H) (blockDart gs i d) (blockDart gs j e)) : i=j := by
  obtain ⟨e',he',_⟩ := piecesMap_path_project gs H i h
  exact blockDart_block_injective gs he'

end STACS2027.PlanarAssembly

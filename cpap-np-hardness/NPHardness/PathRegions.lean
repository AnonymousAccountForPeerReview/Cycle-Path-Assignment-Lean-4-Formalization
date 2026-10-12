module

public import NPHardness.GlobalVertices

/-! Pulling paths back into gadgets and splitting paths at a region boundary. -/

@[expose] public section
namespace STACS2027

theorem edge_normalized (a b : Nat) : edge (edge a b).1 (edge a b).2 = edge a b := by
  unfold edge
  have h : min a b ≤ max a b := Nat.le_trans (Nat.min_le_left _ _) (Nat.le_max_left _ _)
  simp [Nat.min_eq_left h,Nat.max_eq_right h]

theorem subdividedEdge_normalized (a b next s : Nat) :
    ∀ e ∈ subdividedEdge a b next s, edge e.1 e.2 = e := by
  induction s generalizing a next with
  | zero => intro e he; have heq : e = edge a b := by simpa [subdividedEdge] using he
            subst e; exact edge_normalized _ _
  | succ s ih =>
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact edge_normalized _ _
    · exact ih _ _ _ he

theorem realizeLinks_normalized (next : Nat) (ls : List Link) :
    ∀ e ∈ realizeLinks next ls, edge e.1 e.2 = e := by
  induction ls generalizing next with
  | nil => simp [realizeLinks]
  | cons l ls ih =>
    intro e he
    rcases List.mem_append.mp he with he | he
    · exact subdividedEdge_normalized _ _ _ _ e he
    · exact ih _ e he

theorem mapGraph_pullback_edge {g : Graph} {n : Nat} (hb : VerticesBelow g n)
    (hn : ∀ e ∈ g, edge e.1 e.2 = e) (t inv : Nat → Nat)
    (hi : ∀ u, u < n → inv (t u) = u) {a b : Nat}
    (he : edge a b ∈ mapGraph t g) : edge (inv a) (inv b) ∈ g := by
  obtain ⟨e,hem,heq⟩ := List.mem_map.mp he
  change edge (t e.1) (t e.2) = edge a b at heq
  have h := congrArg (mapEdge inv) heq
  simp only [mapEdge_edge] at h
  change edge (inv (t e.1)) (inv (t e.2)) = edge (inv a) (inv b) at h
  rw [hi _ (hb e hem).1, hi _ (hb e hem).2, hn e hem] at h
  exact h ▸ hem

theorem pathEdges_normalized (p : List Nat) : ∀ e ∈ pathEdges p, edge e.1 e.2 = e := by
  induction p with
  | nil => simp [pathEdges]
  | cons x xs ih =>
    cases xs with
    | nil => simp [pathEdges]
    | cons y ys =>
      intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact edge_normalized _ _
      · exact ih e he

theorem IsSimplePath.map_into {g h : Graph} {a b : Nat} {p : List Nat}
    (hp : IsSimplePath g a b p) (t : Nat → Nat)
    (hi : ∀ u ∈ p, ∀ v ∈ p, t u = t v → u = v)
    (he : ∀ x y, edge x y ∈ pathEdges p → edge (t x) (t y) ∈ h) :
    IsSimplePath h (t a) (t b) (p.map t) := by
  refine ⟨?_,by simp [hp.2.1],by simp [hp.2.2.1],?_⟩
  · rw [List.nodup_iff_pairwise_ne,List.pairwise_map]
    exact hp.1.imp_of_mem (fun {u v} hu hv hne ht => hne (hi u hu v hv ht))
  · intro e hem
    rw [pathEdges_map] at hem
    obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hem
    have hn := pathEdges_normalized p d hd
    exact he d.1 d.2 (by rw [hn]; exact hd)

theorem blockVertex_mod {width : Nat} (_hw : 0 < width) (v u : Nat) (hu : u < width) :
    blockVertex width v u % width = u := by
  simp [blockVertex, Nat.add_mod, Nat.mod_eq_of_lt hu]

theorem variable_path_pullback {k v a b : Nat} {p : List Nat}
    (hp : IsSimplePath (placedVariableGraph k v) a b p)
    (hv : ∀ x ∈ p, VariableRegion k v x) :
    IsSimplePath (variableGraph k) (a % gadgetWidth k) (b % gadgetWidth k)
      (p.map (· % gadgetWidth k)) := by
  have hw : 0 < gadgetWidth k := by have := gadgetWidth_ge k; omega
  apply hp.map_into (fun x => x % gadgetWidth k)
  · intro u hu w hw' he
    obtain ⟨x,hx,rfl⟩ := hv u hu
    obtain ⟨y,hy,rfl⟩ := hv w hw'
    rw [blockVertex_mod hw v x hx,blockVertex_mod hw v y hy] at he
    exact congrArg _ he
  · intro x y he
    exact mapGraph_pullback_edge (variableGraph_below k)
      (realizeLinks_normalized 7 (variableLinks k)) (blockVertex (gadgetWidth k) v) (fun x => x % gadgetWidth k)
      (fun u hu => blockVertex_mod hw v u hu) (hp.2.2.2 _ he)

theorem pathEdges_suffix (pre p : List Nat) : pathEdges p ⊆ pathEdges (pre ++ p) := by
  induction pre with
  | nil => exact fun _ h => h
  | cons a pre ih =>
    intro e he
    have hm := ih he
    change e ∈ pathEdges (a :: (pre ++ p))
    cases h : pre ++ p with
    | nil => simp [h,pathEdges] at hm
    | cons b bs => exact List.mem_cons_of_mem _ (by simpa [h] using hm)

theorem pathEdges_infix {p q : List Nat} (h : List.IsInfix p q) : pathEdges p ⊆ pathEdges q := by
  obtain ⟨pre,post,rfl⟩ := h
  intro e he
  exact pathEdges_subset_append _ _ e (pathEdges_suffix pre p he)

theorem IsSimplePath.infix {g : Graph} {a b x y : Nat} {p q : List Nat}
    (hp : IsSimplePath g a b p) (hq : List.IsInfix q p)
    (hh : q.head? = some x) (ht : q.getLast? = some y) : IsSimplePath g x y q :=
  ⟨hq.sublist.nodup hp.1,hh,ht,fun _ he => hp.2.2.2 _ (pathEdges_infix hq he)⟩

theorem IsSimplePath.reverse {g : Graph} {a b : Nat} {p : List Nat}
    (hp : IsSimplePath g a b p) : IsSimplePath g b a p.reverse := by
  refine ⟨(List.reverse_perm p).symm.nodup hp.1,?_,?_,?_⟩
  · simpa only [← List.getLast?_eq_head?_reverse] using hp.2.2.1
  · simpa using hp.2.1
  · intro e he
    rw [pathEdges_reverse,List.mem_reverse] at he
    exact hp.2.2.2 e he

/-- The first vertex outside a region gives a genuine prefix path ending at
the boundary edge. No finiteness or decidability of the region is assumed. -/
theorem list_first_exit (S : Nat → Prop) {a : Nat} {xs : List Nat}
    (ha : S a) (hout : ∃ x ∈ xs, ¬ S x) :
    ∃ pre u v post, a :: xs = pre ++ [u] ++ v :: post ∧
      (∀ x ∈ pre ++ [u], S x) ∧ ¬ S v := by
  classical
  induction xs generalizing a with
  | nil => simp at hout
  | cons b bs ih =>
    by_cases hb : S b
    · have hout' : ∃ x ∈ bs, ¬ S x := by
        obtain ⟨x,hx,hn⟩ := hout
        rcases List.mem_cons.mp hx with rfl | hx
        · exact False.elim (hn hb)
        · exact ⟨x,hx,hn⟩
      obtain ⟨pre,u,v,post,he,hpre,hv⟩ := ih hb hout'
      refine ⟨a :: pre,u,v,post,by simp [he],?_,hv⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ha
      · exact hpre x hx
    · exact ⟨[],a,b,bs,rfl,by simpa using ha,hb⟩

end STACS2027

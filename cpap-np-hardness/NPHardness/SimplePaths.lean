module

public import NPHardness.SubdivisionProjection

/-! Simple paths with fixed endpoints, for the global short-cycle argument. -/

@[expose] public section
namespace STACS2027

def IsSimplePath (g : Graph) (a b : Nat) (p : List Nat) : Prop :=
  p.Nodup ∧ p.head? = some a ∧ p.getLast? = some b ∧ ∀ e ∈ pathEdges p, e ∈ g

theorem IsSimplePath.vertices {g : Graph} {a b : Nat} {p : List Nat}
    (hp : IsSimplePath g a b p) : a ∈ p ∧ b ∈ p := by
  exact ⟨List.mem_of_head? hp.2.1, List.mem_of_getLast? hp.2.2.1⟩

theorem IsSimplePath.ne_nil {g : Graph} {a b : Nat} {p : List Nat}
    (hp : IsSimplePath g a b p) : p ≠ [] := by
  intro he
  have h := hp.2.1
  simp [he] at h

theorem pathEdges_bridge (pre post : List Nat) (a b : Nat) :
    pathEdges (pre ++ a :: b :: post) =
      pathEdges (pre ++ [a]) ++ edge a b :: pathEdges (b :: post) := by
  rw [pathEdges_split pre (b :: post) a]
  rfl

theorem pathEdges_bridge_two (pre post : List Nat) (a z b : Nat) :
    pathEdges (pre ++ a :: z :: b :: post) =
      pathEdges (pre ++ [a]) ++ edge a z :: edge z b :: pathEdges (b :: post) := by
  rw [pathEdges_bridge]
  rfl

theorem remove_middle_sublist (pre post : List Nat) (a z b : Nat) :
    List.Sublist (pre ++ a :: b :: post) (pre ++ a :: z :: b :: post) := by
  apply List.Sublist.append_left
  exact List.Sublist.cons_cons a (List.Sublist.cons z (List.Sublist.refl _))

theorem IsSimplePath.internal_split {g : Graph} {a b z : Nat} {p : List Nat}
    (hp : IsSimplePath g a b p) (hz : z ∈ p) (hza : z ≠ a) (hzb : z ≠ b) :
    ∃ pre u v post, p = pre ++ u :: z :: v :: post := by
  obtain ⟨xs, ys, rfl⟩ := List.mem_iff_append.mp hz
  have hxs : xs ≠ [] := by
    intro h
    have he := hp.2.1
    simp [h] at he
    exact hza he
  have hys : ys ≠ [] := by
    intro h
    have he := hp.2.2.1
    simp [h] at he
    exact hzb he
  obtain he | ⟨pre,u,he⟩ := List.eq_nil_or_concat xs
  · exact False.elim (hxs he)
  simp only [List.concat_eq_append] at he
  subst xs
  cases ys with
  | nil => exact False.elim (hys rfl)
  | cons v post => exact ⟨pre,u,v,post,by simp [List.append_assoc]⟩

theorem IsSimplePath.remove_middle_endpoints {g : Graph} {a b u z v : Nat} {pre post : List Nat}
    (hp : IsSimplePath g a b (pre ++ u :: z :: v :: post)) :
    (pre ++ u :: v :: post).head? = some a ∧ (pre ++ u :: v :: post).getLast? = some b := by
  have hh := hp.2.1
  have ht := hp.2.2.1
  constructor
  · cases pre <;> simpa using hh
  · simpa using ht

theorem pathEdges_old_of_avoids {g : Graph} {a b z : Nat} {p : List Nat}
    (hp : ∀ e ∈ pathEdges p, e ∈ subdivideOnce g a b z) (hz : z ∉ p) :
    ∀ e ∈ pathEdges p, e ∈ g := by
  intro e he
  rcases mem_subdivideOnce.mp (hp e he) with rfl | rfl | ⟨he,_⟩
  · exact False.elim (hz (pathEdge_vertices he).2)
  · exact False.elim (hz (pathEdge_vertices he).1)
  · exact he

/-- Adding the unused edge between a simple path's distinct endpoints closes
a genuine simple cycle, including the necessary length-at-least-three proof. -/
theorem IsSimplePath.close_cycle {g : Graph} {a b : Nat} {p : List Nat}
    (hp : IsSimplePath g a b p) (hab : a ≠ b) (he : edge a b ∈ g)
    (ha : edge a b ∉ pathEdges p) : IsCycle g p.length p := by
  cases p with
  | nil => exact False.elim (hp.ne_nil rfl)
  | cons u us =>
    have hua : u = a := by simpa using hp.2.1
    subst u
    cases us with
    | nil =>
      have hab' : a = b := by simpa using hp.2.2.1
      exact False.elim (hab hab')
    | cons v vs =>
      have hvs : vs ≠ [] := by
        intro h
        subst vs
        have hvb : v = b := by simpa using hp.2.2.1
        apply ha
        simp [pathEdges, hvb]
      have hlen : 3 ≤ (a :: v :: vs).length := by
        have := List.length_pos_iff.mpr hvs
        simp only [List.length_cons]
        omega
      obtain hempty | ⟨middle,w,hw⟩ := List.eq_nil_or_concat (v :: vs)
      · simp at hempty
      simp only [List.concat_eq_append] at hw
      have hwb : w = b := by
        have hlast := hp.2.2.1
        rw [hw] at hlast
        change ((a :: middle) ++ [w]).getLast? = some b at hlast
        rw [List.getLast?_concat] at hlast
        exact Option.some.inj hlast
      refine ⟨hlen,rfl,hp.1,?_⟩
      intro e hem
      have hcycle : cycleEdges (a :: v :: vs) = pathEdges (a :: v :: vs) ++ [edge b a] := by
        rw [hw, cycleEdges_snoc, hwb]
      rw [hcycle] at hem
      rcases List.mem_append.mp hem with hem | hem
      · exact hp.2.2.2 e hem
      · have h : e = edge b a := by simpa using hem
        simpa only [h, edge_comm b a] using he

theorem subdivideOnce_path_contract {g : Graph} {a b z start stop : Nat}
    (he : edge a b ∈ g) (hf : FreshVertex g z) {p : List Nat}
    (hp : IsSimplePath (subdivideOnce g a b z) start stop p)
    (hz : z ∈ p) (hstart : z ≠ start) (hstop : z ≠ stop) :
    ∃ d, IsSimplePath g start stop d ∧ (pathEdges p).Perm (liftEdges a b z (pathEdges d)) := by
  obtain ⟨pre,u,v,post,rfl⟩ := hp.internal_split hz hstart hstop
  have hpu : edge u z ∈ subdivideOnce g a b z := hp.2.2.2 _ (by simp [pathEdges_bridge_two])
  have hpv : edge z v ∈ subdivideOnce g a b z := hp.2.2.2 _ (by simp [pathEdges_bridge_two])
  have hu := subdivideOnce_neighbor hf (by simpa only [edge_comm u z] using hpu)
  have hv := subdivideOnce_neighbor hf hpv
  have hnod := hp.1
  have htail := (List.nodup_append.mp hnod).2.1
  have huv : u ≠ v := by
    intro h
    apply (List.nodup_cons.mp htail).1
    simp [h]
  have heuv : edge u v = edge a b := by
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact False.elim (huv rfl)
    · rfl
    · exact edge_comm _ _
    · exact False.elim (huv rfl)
  have hpre : ∀ e ∈ pathEdges (pre ++ [u]), e ∈ subdivideOnce g a b z := by
    intro e he
    exact hp.2.2.2 e (by simp [pathEdges_bridge_two, he])
  have hpost : ∀ e ∈ pathEdges (v :: post), e ∈ subdivideOnce g a b z := by
    intro e he
    exact hp.2.2.2 e (by simp [pathEdges_bridge_two, he])
  have hzpre : z ∉ pre ++ [u] := by
    intro hm
    rcases List.mem_append.mp hm with hm | hm
    · exact (List.nodup_append.mp hnod).2.2 _ hm _ (by simp) rfl
    · have hzu : z = u := by simpa using hm
      exact (List.nodup_cons.mp htail).1 (by simp [hzu])
  have hzpost : z ∉ v :: post := (List.nodup_cons.mp (List.nodup_cons.mp htail).2).1
  have hn : (pre ++ u :: v :: post).Nodup := (remove_middle_sublist pre post u z v).nodup hnod
  obtain ⟨hh, ht⟩ := hp.remove_middle_endpoints
  refine ⟨pre ++ u :: v :: post, ⟨hn, hh, ht, ?_⟩, ?_⟩
  · intro e hem
    rw [pathEdges_bridge] at hem
    rcases List.mem_append.mp hem with hem | hem
    · exact pathEdges_old_of_avoids hpre hzpre e hem
    · rcases List.mem_cons.mp hem with rfl | hem
      · exact heuv ▸ he
      · exact pathEdges_old_of_avoids hpost hzpost e hem
  · have hpa : edge a b ∉ pathEdges (pre ++ [u]) :=
      fun hm => subdivideOnce_old_edge_absent hf he (hpre _ hm)
    have hpo : edge a b ∉ pathEdges (v :: post) :=
      fun hm => subdivideOnce_old_edge_absent hf he (hpost _ hm)
    rw [pathEdges_bridge_two, pathEdges_bridge]
    have hpref := liftEdges_of_absent a b z (pathEdges (pre ++ [u])) hpa
    have hpostf := liftEdges_of_absent a b z (pathEdges (v :: post)) hpo
    simp only [liftEdges, List.flatMap_append, List.flatMap_cons]
    rw [show (pathEdges (pre ++ [u])).flatMap (splitEdge a b z) = pathEdges (pre ++ [u]) from hpref,
      show (pathEdges (v :: post)).flatMap (splitEdge a b z) = pathEdges (v :: post) from hpostf]
    apply List.Perm.append_left
    change ([edge u z, edge z v] ++ pathEdges (v :: post)).Perm
      (splitEdge a b z (edge u v) ++ pathEdges (v :: post))
    apply List.Perm.append_right
    rw [splitEdge, ite_eq_left heuv]
    rcases (edge_eq_iff ..).mp heuv with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact List.Perm.refl _
    · simpa only [edge_comm u z, edge_comm z v] using List.Perm.swap (edge v z) (edge z u) []

end STACS2027

module

public import NPHardness.SelectedPaths

/-! Rotation and endpoint facts used to project cycles through subdivisions. -/

@[expose] public section
namespace STACS2027

theorem edge_comm (a b : Nat) : edge a b = edge b a := by
  simp [edge, Nat.min_comm, Nat.max_comm]

theorem edge_eq_iff (a b c d : Nat) :
    edge a b = edge c d ↔ (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  simp only [edge, Prod.mk.injEq]
  by_cases h : a ≤ b <;> by_cases h' : c ≤ d <;>
    simp [Nat.min_def, Nat.max_def, h, h'] <;> omega

theorem edge_left_inj (a b c : Nat) : edge a b = edge a c ↔ b = c := by
  rw [edge_eq_iff]
  omega

theorem IsCycle.of_perm_edges {g : Graph} {k : Nat} {c d : Cycle}
    (hc : IsCycle g k c) (hp : c.Perm d) (he : SameCycle c d) : IsCycle g k d := by
  exact ⟨hc.1, hp.length_eq.symm.trans hc.2.1, hp.nodup hc.2.2.1,
    fun e hd => hc.2.2.2 e (he.2 e hd)⟩

theorem sameCycle_append_swap (xs ys : Cycle) : SameCycle (xs ++ ys) (ys ++ xs) :=
  ⟨fun e he => (cycleEdges_append_swap xs ys e).mp he,
    fun e he => (cycleEdges_append_swap xs ys e).mpr he⟩

theorem IsCycle.append_swap {g : Graph} {k : Nat} {xs ys : Cycle}
    (hc : IsCycle g k (xs ++ ys)) : IsCycle g k (ys ++ xs) :=
  hc.of_perm_edges List.perm_append_comm (sameCycle_append_swap xs ys)

theorem IsCycle.rotate_to_vertex {g : Graph} {k : Nat} {c : Cycle}
    (hc : IsCycle g k c) {v : Nat} (hv : v ∈ c) :
    ∃ rest, IsCycle g k (v :: rest) ∧ SameCycle c (v :: rest) ∧ c.Perm (v :: rest) := by
  obtain ⟨xs, ys, rfl⟩ := List.mem_iff_append.mp hv
  exact ⟨ys ++ xs, hc.append_swap, sameCycle_append_swap xs (v :: ys),
    List.perm_append_comm⟩

theorem pathEdges_append_last (xs : List Nat) (a b : Nat) :
    pathEdges (xs ++ [a, b]) = pathEdges (xs ++ [a]) ++ [edge a b] := by
  simpa only [pathEdges] using pathEdges_split xs [b] a

theorem cycleEdges_snoc (a b : Nat) (xs : List Nat) :
    cycleEdges (a :: (xs ++ [b])) = pathEdges (a :: (xs ++ [b])) ++ [edge b a] := by
  simp only [cycleEdges, List.take_succ_cons, List.take_zero, List.cons_append,
    List.append_assoc]
  exact pathEdges_append_last (a :: xs) b a

theorem pathEdges_reverse (vs : List Nat) :
    pathEdges vs.reverse = (pathEdges vs).reverse := by
  induction vs with
  | nil => rfl
  | cons a vs ih =>
    cases vs with
    | nil => rfl
    | cons b bs =>
      simp only [List.reverse_cons, List.append_assoc, List.singleton_append] at ih ⊢
      rw [pathEdges_append_last, ih]
      simp only [pathEdges, List.reverse_cons, edge_comm b a]

theorem cycleEdges_reverse_tail (a : Nat) (vs : List Nat) :
    cycleEdges (a :: vs.reverse) = (cycleEdges (a :: vs)).reverse := by
  have h := pathEdges_reverse ((a :: vs) ++ [a])
  simpa [cycleEdges, List.reverse_append, List.reverse_cons, List.append_assoc] using h

theorem sameCycle_reverse_tail (a : Nat) (vs : List Nat) :
    SameCycle (a :: vs) (a :: vs.reverse) := by
  constructor <;> intro e he
  · simpa only [cycleEdges_reverse_tail, List.mem_reverse] using he
  · simpa only [cycleEdges_reverse_tail, List.mem_reverse] using he

theorem IsCycle.reverse_tail {g : Graph} {k a : Nat} {vs : Cycle}
    (hc : IsCycle g k (a :: vs)) : IsCycle g k (a :: vs.reverse) :=
  hc.of_perm_edges ((List.reverse_perm vs).symm.cons a) (sameCycle_reverse_tail a vs)

theorem pathEdge_vertices {vs : List Nat} {a b : Nat} (he : edge a b ∈ pathEdges vs) :
    a ∈ vs ∧ b ∈ vs := by
  have h := pathEdges_endpoints he
  by_cases hab : a ≤ b
  · simpa [edge, Nat.min_eq_left hab, Nat.max_eq_right hab] using h
  · have hba : b ≤ a := by omega
    simpa [edge, Nat.min_eq_right hba, Nat.max_eq_left hba, and_comm] using h

theorem IsCycle.edges_nodup {g : Graph} {k : Nat} {c : Cycle}
    (hc : IsCycle g k c) : (cycleEdges c).Nodup := by
  have hk := hc.1
  have hl := hc.2.1
  cases c with
  | nil => simp at hl; omega
  | cons a tail =>
    cases tail with
    | nil => simp at hl; omega
    | cons b rest =>
      cases rest with
      | nil => simp at hl; omega
      | cons x xs =>
        have hn := hc.2.2.1
        have ha := (List.nodup_cons.mp hn).1
        have hb := (List.nodup_cons.mp (List.nodup_cons.mp hn).2).1
        have ht : ((b :: x :: xs) ++ [a]).Nodup :=
          List.Perm.nodup (List.perm_append_comm (l₁ := [a]) (l₂ := b :: x :: xs)) hn
        change (edge a b :: pathEdges ((b :: x :: xs) ++ [a])).Nodup
        apply List.nodup_cons.mpr
        refine ⟨?_, pathEdges_nodup ht⟩
        intro h
        change edge a b ∈ edge b x :: pathEdges ((x :: xs) ++ [a]) at h
        rcases List.mem_cons.mp h with he | he
        · rw [edge_comm a b, edge_left_inj] at he
          apply ha; simp [he]
        · have hmem := (pathEdge_vertices he).2
          rcases List.mem_append.mp hmem with hmem | hmem
          · exact hb hmem
          · have he : b = a := by simpa using hmem
            apply ha; simp [he]
/-- Every cycle vertex has an incident cycle edge. -/
theorem IsCycle.vertex_incident {g : Graph} {k : Nat} {c : Cycle}
    (hc : IsCycle g k c) {v : Nat} (hv : v ∈ c) :
    ∃ w, w ≠ v ∧ edge v w ∈ cycleEdges c := by
  obtain ⟨rest, hr, hs, _⟩ := hc.rotate_to_vertex hv
  cases rest with
  | nil => have h := hr.2.1; have hk := hr.1; simp at h; omega
  | cons w ws =>
    have hne : w ≠ v := by
      have h := (List.nodup_cons.mp hr.2.2.1).1
      intro he; apply h; simp [he]
    refine ⟨w, hne, hs.2 _ ?_⟩
    simp [cycleEdges, pathEdges]

end STACS2027

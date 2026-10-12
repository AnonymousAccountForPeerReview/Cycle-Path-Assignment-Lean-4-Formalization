module

public import NPHardness.Enumerate
public import NPHardness.CostSearch
public import NPHardness.LoadCost

/-! Representation facts for the paths selected by a cycle-path assignment. -/

@[expose] public section
namespace STACS2027

theorem edge_left_endpoint (a b : Nat) : a = (edge a b).1 ∨ a = (edge a b).2 := by
  by_cases h : a ≤ b
  · simp [edge, Nat.min_eq_left h]
  · simp [edge, Nat.max_eq_left (by omega : b ≤ a)]

theorem edge_endpoints (a b : Nat) :
    ((edge a b).1 = a ∨ (edge a b).1 = b) ∧
    ((edge a b).2 = a ∨ (edge a b).2 = b) := by
  by_cases h : a ≤ b
  · simp [edge, Nat.min_eq_left h, Nat.max_eq_right h]
  · have h' : b ≤ a := by omega
    simp [edge, Nat.min_eq_right h', Nat.max_eq_left h']

theorem pathEdges_endpoints {vs : List Nat} {e : Edge} (h : e ∈ pathEdges vs) :
    e.1 ∈ vs ∧ e.2 ∈ vs := by
  induction vs with
  | nil => simp [pathEdges] at h
  | cons a vs ih =>
    cases vs with
    | nil => simp [pathEdges] at h
    | cons b bs =>
      rcases List.mem_cons.mp h with rfl | h
      · obtain ⟨h₁, h₂⟩ := edge_endpoints a b
        constructor
        · rcases h₁ with h₁ | h₁ <;> simp [h₁]
        · rcases h₂ with h₂ | h₂ <;> simp [h₂]
      · obtain ⟨h₁, h₂⟩ := ih h
        exact ⟨List.mem_cons_of_mem a h₁, List.mem_cons_of_mem a h₂⟩

theorem pathEdges_nodup {vs : List Nat} (h : vs.Nodup) : (pathEdges vs).Nodup := by
  induction vs with
  | nil => simp [pathEdges]
  | cons a vs ih =>
    cases vs with
    | nil => simp [pathEdges]
    | cons b bs =>
      obtain ⟨ha, ht⟩ := List.nodup_cons.mp h
      apply List.nodup_cons.mpr
      refine ⟨?_, ih ht⟩
      intro he
      have hv := pathEdges_endpoints he
      rcases edge_left_endpoint a b with h₁ | h₂
      · exact ha (h₁ ▸ hv.1)
      · exact ha (h₂ ▸ hv.2)

theorem selected_nodup {c : Cycle} (h : c.Nodup) (i : Nat) :
    (selected c i).Nodup := by
  apply pathEdges_nodup
  apply List.Sublist.nodup (List.take_sublist _ _)
  have ht : (c.take (i + 1) ++ c.drop (i + 1)).Nodup := by
    simpa only [List.take_append_drop] using h
  exact List.Perm.nodup List.perm_append_comm ht

theorem pathEdges_split (xs ys : List Nat) (a : Nat) :
    pathEdges (xs ++ a :: ys) = pathEdges (xs ++ [a]) ++ pathEdges (a :: ys) := by
  induction xs with
  | nil => simp [pathEdges]
  | cons b xs ih =>
    cases xs with
    | nil => simp [pathEdges]
    | cons c xs =>
      simpa only [List.cons_append, pathEdges] using congrArg (edge b c :: ·) ih

theorem cycleEdges_append (a b : Nat) (xs ys : List Nat) :
    cycleEdges ((a :: xs) ++ (b :: ys)) =
      pathEdges ((a :: xs) ++ [b]) ++ pathEdges ((b :: ys) ++ [a]) := by
  simp only [cycleEdges, List.cons_append, List.take_succ_cons, List.take_zero,
    List.append_assoc]
  exact pathEdges_split (a :: xs) (ys ++ [a]) b

theorem cycleEdges_append_swap (xs ys : List Nat) (e : Edge) :
    e ∈ cycleEdges (xs ++ ys) ↔ e ∈ cycleEdges (ys ++ xs) := by
  cases xs with
  | nil => simp
  | cons a xs =>
    cases ys with
    | nil => simp
    | cons b ys => simp only [cycleEdges_append, List.mem_append, or_comm]

theorem selected_mem_cycleEdges {c : Cycle} {i : Nat} {e : Edge}
    (h : e ∈ selected c i) : e ∈ cycleEdges c := by
  let r := c.drop (i + 1) ++ c.take (i + 1)
  have h₁ : e ∈ pathEdges r := by
    have ht := pathEdges_subset_append (r.take (c.length - 1)) (r.drop (c.length - 1)) e h
    simpa only [List.take_append_drop] using ht
  have h₂ : e ∈ cycleEdges r := pathEdges_subset_append r (r.take 1) e h₁
  have h₃ := (cycleEdges_append_swap (c.drop (i + 1)) (c.take (i + 1)) e).mp h₂
  simpa only [List.take_append_drop] using h₃

theorem selected_mem_graph {g : Graph} {k : Nat} {c : Cycle}
    (h : IsCycle g k c) (i : Nat) {e : Edge} (he : e ∈ selected c i) : e ∈ g :=
  h.2.2.2 e (selected_mem_cycleEdges he)

theorem validChoices_properties {cs : List Cycle} {ps : List (List Edge)}
    (hv : ValidChoices (cs.map selectedOptions) ps) {g : Graph} {k : Nat}
    (hc : ∀ c ∈ cs, IsCycle g k c) :
    ps.length = cs.length ∧
    (∀ p ∈ ps, p.Nodup) ∧
    (∀ p ∈ ps, p.length = k - 2) ∧
    (∀ p ∈ ps, ∀ e ∈ p, e ∈ g) := by
  induction cs generalizing ps with
  | nil =>
    cases ps with
    | nil => simp
    | cons p ps => exact False.elim hv
  | cons c cs ih =>
    cases ps with
    | nil => exact False.elim hv
    | cons p ps =>
      obtain ⟨hp, hv⟩ := hv
      obtain ⟨i, _hi, rfl⟩ := List.mem_map.mp hp
      have hcycle := hc c (by simp)
      obtain ⟨hlen, hn, hl, hs⟩ := ih hv (fun c' h => hc c' (by simp [h]))
      refine ⟨by simp [hlen], ?_, ?_, ?_⟩
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact selected_nodup hcycle.2.2.1 i
        · exact hn p hp
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · simpa only [hcycle.2.1] using selected_length c i
        · exact hl p hp
      · intro p hp e he
        rcases List.mem_cons.mp hp with rfl | hp
        · exact selected_mem_graph hcycle i he
        · exact hs p hp e he

/-- Assignment paths are actual simple paths in the input graph. -/
theorem enumerated_choices_properties {g : Graph} {k : Nat} {ps : List (List Edge)}
    (h : ValidChoices ((cycles g k).map selectedOptions) ps) :
    ps.length = (cycles g k).length ∧
    (∀ p ∈ ps, p.Nodup) ∧
    (∀ p ∈ ps, p.length = k - 2) ∧
    (∀ p ∈ ps, ∀ e ∈ p, e ∈ g) :=
  validChoices_properties h (fun _ hc => enumerated_isCycle hc)

theorem enumerated_cost_eq_load_sum {g : Graph} {k : Nat} {ps : List (List Edge)}
    (hg : g.Nodup) (h : ValidChoices ((cycles g k).map selectedOptions) ps) :
    cost ps = (g.map fun e => load ps e * (load ps e - 1) / 2).sum := by
  obtain ⟨_, hn, _, hs⟩ := enumerated_choices_properties h
  exact cost_eq_binomial_sum g ps hg hn hs

end STACS2027

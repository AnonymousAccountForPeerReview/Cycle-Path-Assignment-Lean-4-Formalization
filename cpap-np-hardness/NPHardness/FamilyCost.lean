module

public import NPHardness.ExpansionCost

/-! Transport of the CPAP objective across choices and cycle expansions. -/

@[expose] public section
namespace STACS2027

theorem sum_map_le {α : Type} (xs : List α) (f g : α → Nat)
    (h : ∀ x ∈ xs, f x ≤ g x) : (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => exact Nat.le_refl _
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))

theorem cost_map_le {α : Type} (xs : List α) (f g : α → List Edge)
    (h : xs.Pairwise (fun x y => overlap (f x) (f y) ≤ overlap (g x) (g y))) :
    cost (xs.map f) ≤ cost (xs.map g) := by
  induction xs with
  | nil => exact Nat.le_refl _
  | cons x xs ih =>
    obtain ⟨hh, ht⟩ := List.pairwise_cons.mp h
    simp only [List.map_cons, cost, List.map_map]
    exact Nat.add_le_add (sum_map_le xs _ _ hh) (ih ht)

theorem cost_map_eq {α : Type} (xs : List α) (f g : α → List Edge)
    (h : xs.Pairwise (fun x y => overlap (f x) (f y) = overlap (g x) (g y))) :
    cost (xs.map f) = cost (xs.map g) := by
  exact Nat.le_antisymm (cost_map_le xs f g (h.imp (fun h => Nat.le_of_eq h)))
    (cost_map_le xs g f (h.imp (fun h => Nat.le_of_eq h.symm)))

theorem overlap_perm {p q r s : List Edge} (hp : p.Perm r) (hq : q.Perm s) :
    overlap p q = overlap r s := by
  unfold overlap
  have hmap : p.map (fun e => q.count e) = p.map (fun e => s.count e) :=
    List.map_congr_left (fun e _ => hq.count_eq e)
  rw [hmap]
  exact (hp.map (fun e => s.count e)).sum_nat

def PathsPerm : List (List Edge) → List (List Edge) → Prop
  | [], [] => True
  | p :: ps, q :: qs => p.Perm q ∧ PathsPerm ps qs
  | _, _ => False

theorem PathsPerm.overlap_sums {ps qs : List (List Edge)} (h : PathsPerm ps qs)
    {p q : List Edge} (hp : p.Perm q) :
    (ps.map (overlap p)).sum = (qs.map (overlap q)).sum := by
  induction ps generalizing qs with
  | nil => cases qs with
    | nil => rfl
    | cons _ _ => exact False.elim h
  | cons r ps ih => cases qs with
    | nil => exact False.elim h
    | cons s qs =>
      obtain ⟨hh, ht⟩ := h
      simp only [List.map_cons, List.sum_cons]
      rw [overlap_perm hp hh, ih ht]

theorem PathsPerm.cost_eq {ps qs : List (List Edge)} (h : PathsPerm ps qs) :
    cost ps = cost qs := by
  induction ps generalizing qs with
  | nil => cases qs with
    | nil => rfl
    | cons _ _ => exact False.elim h
  | cons p ps ih => cases qs with
    | nil => exact False.elim h
    | cons q qs =>
      obtain ⟨hh, ht⟩ := h
      simp only [cost]
      rw [ht.overlap_sums hh, ih ht]

theorem PathsPerm.load_eq {ps qs : List (List Edge)} (h : PathsPerm ps qs) (e : Edge) :
    load ps e = load qs e := by
  induction ps generalizing qs with
  | nil => cases qs with
    | nil => rfl
    | cons _ _ => exact False.elim h
  | cons p ps ih => cases qs with
    | nil => exact False.elim h
    | cons q qs =>
      obtain ⟨hh, ht⟩ := h
      rw [load_cons, load_cons, hh.count_eq e, ih ht]

theorem vertex_choices_have_options {cs : List Cycle} {g : Graph}
    (hc : ∀ c ∈ cs, IsCycle g c.length c) (choose : Cycle → Nat)
    (hv : ∀ c ∈ cs, choose c ∈ c) :
    ∃ ps, ValidChoices (cs.map selectedOptions) ps ∧
      PathsPerm ps (cs.map fun c => selectedAt c (choose c)) := by
  induction cs with
  | nil => exact ⟨[], trivial, trivial⟩
  | cons c cs ih =>
    obtain ⟨p, hp, hperm⟩ := selectedAt_has_option (hc c (by simp)) (hv c (by simp))
    obtain ⟨ps, hvps, hpps⟩ := ih (fun d hd => hc d (by simp [hd]))
      (fun d hd => hv d (by simp [hd]))
    exact ⟨p :: ps, ⟨hp, hvps⟩, ⟨hperm, hpps⟩⟩

theorem expanded_family_normalizes {g h : Graph} {k : Nat} {ss : List SubdivisionStep}
    (hv : validSubdivision g ss) (cs : List Cycle) (expand : Cycle → Cycle)
    (hc : ∀ c ∈ cs, IsCycle g c.length c)
    (he : ∀ c ∈ cs, IsCycle h k (expand c))
    (hp : ∀ c ∈ cs, (cycleEdges (expand c)).Perm ((cycleEdges c).flatMap (expandedEdge ss)))
    (hu : cs.Pairwise (fun c d => ∀ e ∈ cycleEdges c,
      e ∈ cycleEdges d → expandedEdge ss e = [e])) (choose : Cycle → Nat) :
    cost (cs.map fun c => selectedAt c (originalChoice c (choose c))) ≤
      cost (cs.map fun c => selectedAt (expand c) (choose c)) := by
  apply cost_map_le
  apply hu.imp_of_mem
  intro c d hcm hdm hshared
  exact expanded_overlap_normalizes hv (hc c hcm) (hc d hdm) (he c hcm) (he d hdm)
    (hp c hcm) (hp d hdm) hshared (choose c) (choose d)

theorem expanded_family_cost_eq {g h : Graph} {k : Nat} {ss : List SubdivisionStep}
    (hv : validSubdivision g ss) (cs : List Cycle) (expand : Cycle → Cycle)
    (hc : ∀ c ∈ cs, IsCycle g c.length c)
    (he : ∀ c ∈ cs, IsCycle h k (expand c))
    (hp : ∀ c ∈ cs, (cycleEdges (expand c)).Perm ((cycleEdges c).flatMap (expandedEdge ss)))
    (hu : cs.Pairwise (fun c d => ∀ e ∈ cycleEdges c,
      e ∈ cycleEdges d → expandedEdge ss e = [e])) (choose : Cycle → Nat) :
    cost (cs.map fun c => selectedAt c (choose c)) =
      cost (cs.map fun c => selectedAt (expand c) (choose c)) := by
  apply cost_map_eq
  apply hu.imp_of_mem
  intro c d hcm hdm hshared
  exact expanded_overlap_same_vertices hv (hc c hcm) (hc d hdm) (he c hcm) (he d hdm)
    (hp c hcm) (hp d hdm) hshared (choose c) (choose d)

end STACS2027

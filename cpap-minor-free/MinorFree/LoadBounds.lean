module

public import MinorFree.FourCycles

/-!
The Cauchy–Schwarz lower bound of Lemma 23 on any graph: every assignment of
`t` paths of `k − 2` edges in a graph with `m` edges, with total load
`Q = (k − 2) t`, has `2 m c(τ) + m Q ≥ Q²`, i.e. `c(τ) ≥ (Q²/m − Q)/2`; and an
upper bound on the load of an edge by the number of cycles containing it.
-/

@[expose] public section
namespace STACS2027

theorem sum_map_add' {α : Type} (xs : List α) (f g : α → Nat) :
    (xs.map fun x => f x + g x).sum = (xs.map f).sum + (xs.map g).sum := sum_map_add xs f g

theorem sum_map_scale {α : Type} (xs : List α) (c : Nat) (f : α → Nat) :
    (xs.map fun x => c * f x).sum = c * (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih, Nat.mul_add]

theorem sum_map_ext {α : Type} (xs : List α) (f g : α → Nat)
    (h : ∀ x ∈ xs, f x = g x) : (xs.map f).sum = (xs.map g).sum := by
  rw [List.map_congr_left h]

/-- `2xy ≤ x² + y²`. -/
theorem schwarz_two_term (x y : Nat) : 2 * (x * y) ≤ x * x + y * y := by
  rcases Nat.le_total x y with h | h
  · obtain ⟨d, rfl⟩ := Nat.le.dest h
    have : x * x + (x + d) * (x + d) = 2 * (x * (x + d)) + d * d := by grind
    omega
  · obtain ⟨d, rfl⟩ := Nat.le.dest h
    have : (y + d) * (y + d) + y * y = 2 * ((y + d) * y) + d * d := by grind
    omega

/-- `4uv ≤ (u + v)²`. -/
theorem schwarz_four_term (u v : Nat) : 4 * (u * v) ≤ (u + v) * (u + v) := by
  have h := schwarz_two_term u v
  have : (u + v) * (u + v) = u * u + v * v + 2 * (u * v) := by grind
  omega

/-- The Cauchy–Schwarz inequality for finite sums of naturals. -/
theorem schwarz_inequality {α : Type} (xs : List α) (a b : α → Nat) :
    (xs.map fun x => a x * b x).sum * (xs.map fun x => a x * b x).sum ≤
      (xs.map fun x => a x * a x).sum * (xs.map fun x => b x * b x).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    generalize (xs.map fun x => a x * b x).sum = C at ih ⊢
    generalize (xs.map fun x => a x * a x).sum = A at ih ⊢
    generalize (xs.map fun x => b x * b x).sum = B at ih ⊢
    generalize a x = u
    generalize b x = v
    have hsq : (2 * (C * (u * v))) * (2 * (C * (u * v))) ≤
        (A * (v * v) + B * (u * u)) * (A * (v * v) + B * (u * u)) := by
      have h₁ : (2 * (C * (u * v))) * (2 * (C * (u * v))) =
          4 * ((C * C) * ((u * v) * (u * v))) := by grind
      have h₂ : 4 * ((A * B) * ((u * v) * (u * v))) = 4 * ((A * (v * v)) * (B * (u * u))) := by
        grind
      rw [h₁]
      calc 4 * ((C * C) * ((u * v) * (u * v)))
          ≤ 4 * ((A * B) * ((u * v) * (u * v))) :=
            Nat.mul_le_mul_left 4 (Nat.mul_le_mul_right _ ih)
        _ = 4 * ((A * (v * v)) * (B * (u * u))) := h₂
        _ ≤ _ := schwarz_four_term _ _
    have hcross : 2 * (C * (u * v)) ≤ A * (v * v) + B * (u * u) :=
      Nat.mul_self_le_mul_self_iff.mp hsq
    have hexp : (u * v + C) * (u * v + C) =
        (u * v) * (u * v) + 2 * (C * (u * v)) + C * C := by grind
    have hexp' : (u * u + A) * (v * v + B) =
        (u * v) * (u * v) + (A * (v * v) + B * (u * u)) + A * B := by grind
    rw [hexp, hexp']
    omega

/-- `(∑ lᵢ)² ≤ m ∑ lᵢ²` over `m` terms. -/
theorem sq_sum_le (xs : List Edge) (l : Edge → Nat) :
    (xs.map l).sum * (xs.map l).sum ≤ xs.length * (xs.map fun e => l e * l e).sum := by
  have h := schwarz_inequality xs (fun _ => 1) l
  simp only [Nat.one_mul, Nat.mul_one] at h
  rw [sum_map_const, Nat.mul_one] at h
  exact h

/-- `2 binom(n, 2) + n = n²`. -/
theorem two_pairCount_add_self (n : Nat) : 2 * pairCount n + n = n * n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [pairCount]; grind

/-- `∑_e l(e)² = 2 c(τ) + ∑_e l(e)` on a duplicate-free edge list containing every path edge. -/
theorem sq_load_sum {es : List Edge} (he : es.Nodup) (ps : List (List Edge))
    (hn : ∀ p ∈ ps, p.Nodup) (hs : ∀ p ∈ ps, ∀ e ∈ p, e ∈ es) :
    (es.map fun e => load ps e * load ps e).sum = 2 * cost ps + (es.map (load ps)).sum := by
  rw [cost_eq_load_sum es ps he hn hs, ← sum_map_scale, ← sum_map_add']
  exact sum_map_ext es _ _ (fun e _ => (two_pairCount_add_self _).symm)

/-- The total load is the total number of path edges. -/
theorem load_total {es : List Edge} (he : es.Nodup) (ps : List (List Edge))
    (hs : ∀ p ∈ ps, ∀ e ∈ p, e ∈ es) :
    (es.map (load ps)).sum = (ps.map List.length).sum := by
  induction ps with
  | nil => exact sum_map_ext es _ (fun _ => 0) (fun e _ => by simp [load]) |>.trans (sum_map_zero es)
  | cons p ps ih =>
    have hp : ∀ e ∈ p, e ∈ es := hs p (by simp)
    have ht : ∀ r ∈ ps, ∀ e ∈ r, e ∈ es := fun r hr => hs r (by simp [hr])
    have hsplit : (es.map (load (p :: ps))).sum =
        (es.map fun e => p.count e * 1).sum + (es.map (load ps)).sum := by
      rw [← sum_map_add']
      exact sum_map_ext es _ _ (fun e _ => by rw [load_cons, Nat.mul_one])
    rw [hsplit, ih ht, sum_counts es p (fun _ => 1) he hp, sum_map_const]
    simp

/-- An assignment of the `k`-cycles of `g` has total load `(k − 2) t`. -/
theorem assignment_total_load {g : Graph} {k : Nat} (hg : g.Nodup) {ps : List (List Edge)}
    (hv : ValidChoices ((cycles g k).map selectedOptions) ps) :
    (g.map (load ps)).sum = (k - 2) * (cycles g k).length := by
  obtain ⟨hlen, _, hl, hs⟩ := enumerated_choices_properties hv
  rw [load_total hg ps hs, sum_map_ext ps List.length (fun _ => k - 2) hl, sum_map_const, hlen,
    Nat.mul_comm]

/-- **Lemma 23, the lower bound, on any graph**: with `m = |E|` edges and total load
`Q = (k − 2) t`, every assignment has `Q² ≤ m (2 c(τ) + Q)`, i.e. `c(τ) ≥ (Q²/m − Q)/2`
(Cauchy–Schwarz). -/
theorem cost_lower_bound {g : Graph} {k : Nat} (hg : g.Nodup) {ps : List (List Edge)}
    (hv : ValidChoices ((cycles g k).map selectedOptions) ps) :
    ((k - 2) * (cycles g k).length) * ((k - 2) * (cycles g k).length) ≤
      g.length * (2 * cost ps + (k - 2) * (cycles g k).length) := by
  obtain ⟨_, hn, _, hs⟩ := enumerated_choices_properties hv
  have h := sq_sum_le g (load ps)
  rw [sq_load_sum hg ps hn hs, assignment_total_load hg hv] at h
  exact h

/-- The load of an edge is at most the number of enumerated cycles containing it. -/
theorem load_le_cycle_count {g : Graph} {k : Nat} {ps : List (List Edge)}
    (hv : ValidChoices ((cycles g k).map selectedOptions) ps) (e : Edge) :
    load ps e ≤ ((cycles g k).filter fun c => decide (e ∈ cycleEdges c)).length := by
  have hc : ∀ c ∈ cycles g k, IsCycle g k c := fun c hc => enumerated_isCycle hc
  generalize hcs : cycles g k = cs at hv hc ⊢
  clear hcs
  induction cs generalizing ps with
  | nil =>
    cases ps with
    | nil => simp [load]
    | cons _ _ => exact False.elim hv
  | cons c cs ih =>
    cases ps with
    | nil => exact False.elim hv
    | cons p ps =>
      obtain ⟨hp, hv⟩ := hv
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hp
      have hrest := ih hv (fun d hd => hc d (by simp [hd]))
      have hcc := hc c (by simp)
      rw [load_cons, List.filter_cons]
      by_cases hm : e ∈ cycleEdges c
      · simp only [hm, decide_true, ↓reduceIte, List.length_cons]
        have : (selected c i).count e ≤ 1 :=
          List.nodup_iff_count.mp (selected_nodup hcc.2.2.1 i) e
        omega
      · simp only [hm, decide_false, Bool.false_eq_true, ↓reduceIte]
        have : (selected c i).count e = 0 :=
          List.count_eq_zero.mpr (fun h => hm (selected_mem_cycleEdges h))
        omega

theorem pairCount_mono {a b : Nat} (h : a ≤ b) : pairCount a ≤ pairCount b := by
  induction b with
  | zero => have : a = 0 := by omega
            subst this; exact Nat.le_refl _
  | succ b ih =>
    rcases Nat.lt_or_eq_of_le h with h' | h'
    · exact Nat.le_trans (ih (by omega)) (by simp [pairCount])
    · subst h'; exact Nat.le_refl _

/-- If every edge has load at most `L`, the cost is at most `m binom(L, 2)`. -/
theorem cost_le_of_load_le {g : Graph} {k : Nat} (hg : g.Nodup) {ps : List (List Edge)}
    (hv : ValidChoices ((cycles g k).map selectedOptions) ps) {L : Nat}
    (hL : ∀ e ∈ g, load ps e ≤ L) : cost ps ≤ g.length * pairCount L := by
  obtain ⟨_, hn, _, hs⟩ := enumerated_choices_properties hv
  rw [cost_eq_load_sum g ps hg hn hs]
  calc (g.map fun e => pairCount (load ps e)).sum ≤ (g.map fun _ => pairCount L).sum :=
        sum_map_le g _ _ (fun e he => pairCount_mono (hL e he))
    _ = g.length * pairCount L := sum_map_const g _

end STACS2027

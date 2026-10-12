module

public import NPHardness.AssignmentFamilies

/-!
Arithmetic for the approximation bounds of Section 7: sums of products, the
two-term inequality `2xy ≤ x² + y²`, the Cauchy–Schwarz inequality for finite
sums of naturals, and the quadratic manipulations behind Lemma 13.
-/

@[expose] public section
namespace STACS2027

theorem sum_map_mul_left {α : Type} (xs : List α) (c : Nat) (f : α → Nat) :
    (xs.map fun x => c * f x).sum = c * (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih, Nat.mul_add]

theorem sum_map_mul_right {α : Type} (xs : List α) (c : Nat) (f : α → Nat) :
    (xs.map fun x => f x * c).sum = (xs.map f).sum * c := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih, Nat.add_mul]

theorem sum_map_congr {α : Type} (xs : List α) (f g : α → Nat)
    (h : ∀ x ∈ xs, f x = g x) : (xs.map f).sum = (xs.map g).sum := by
  rw [List.map_congr_left h]

theorem sum_map_eq_zero {α : Type} (xs : List α) (f : α → Nat)
    (h : ∀ x ∈ xs, f x = 0) : (xs.map f).sum = 0 := by
  rw [sum_map_congr xs f (fun _ => 0) h, sum_map_zero]

/-- `2xy ≤ x² + y²`. -/
theorem two_mul_le_sq_add (x y : Nat) : 2 * (x * y) ≤ x * x + y * y := by
  rcases Nat.le_total x y with h | h
  · obtain ⟨d, rfl⟩ := Nat.le.dest h
    have : x * x + (x + d) * (x + d) = 2 * (x * (x + d)) + d * d := by grind
    omega
  · obtain ⟨d, rfl⟩ := Nat.le.dest h
    have : (y + d) * (y + d) + y * y = 2 * ((y + d) * y) + d * d := by grind
    omega

/-- `4uv ≤ (u + v)²`. -/
theorem four_mul_le_sq_add (u v : Nat) : 4 * (u * v) ≤ (u + v) * (u + v) := by
  have h := two_mul_le_sq_add u v
  have : (u + v) * (u + v) = u * u + v * v + 2 * (u * v) := by grind
  omega

/-- The Cauchy–Schwarz inequality for finite sums of naturals:
`(∑ aᵢ bᵢ)² ≤ (∑ aᵢ²)(∑ bᵢ²)`. -/
theorem cauchy_schwarz {α : Type} (xs : List α) (a b : α → Nat) :
    (xs.map fun x => a x * b x).sum * (xs.map fun x => a x * b x).sum ≤
      (xs.map fun x => a x * a x).sum * (xs.map fun x => b x * b x).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    -- Abbreviations: `C = ∑ ab`, `A = ∑ a²`, `B = ∑ b²` over the tail, and `u = a x`, `v = b x`.
    generalize (xs.map fun x => a x * b x).sum = C at ih ⊢
    generalize (xs.map fun x => a x * a x).sum = A at ih ⊢
    generalize (xs.map fun x => b x * b x).sum = B at ih ⊢
    generalize a x = u
    generalize b x = v
    -- `2Cuv ≤ Av² + Bu²`: square both sides, `4C²u²v² ≤ 4ABu²v² ≤ (Av² + Bu²)²`.
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
        _ ≤ _ := four_mul_le_sq_add _ _
    have hcross : 2 * (C * (u * v)) ≤ A * (v * v) + B * (u * u) :=
      Nat.mul_self_le_mul_self_iff.mp hsq
    have hexp : (u * v + C) * (u * v + C) =
        (u * v) * (u * v) + 2 * (C * (u * v)) + C * C := by grind
    have hexp' : (u * u + A) * (v * v + B) =
        (u * v) * (u * v) + (A * (v * v) + B * (u * u)) + A * B := by grind
    rw [hexp, hexp']
    omega

/-- The quadratic step of Lemma 13: if `2c + Q = S`, `Q ≤ S'`, `c ≤ P` and `P² ≤ S S'`, then
`(S − S')² ≤ 4 S S'`; for `S ≥ S'` this says `S ≤ (3 + 2√2) S'`. -/
theorem quadratic_bound {c Q S S' P : Nat} (hS : 2 * c + Q = S) (hQ : Q ≤ S')
    (hc : c ≤ P) (hP : P * P ≤ S * S') : (S - S') * (S - S') ≤ 4 * (S * S') := by
  by_cases h : S ≤ S'
  · rw [Nat.sub_eq_zero_of_le h]; simp
  · have hd : S - S' ≤ 2 * P := by omega
    calc (S - S') * (S - S') ≤ (2 * P) * (2 * P) := Nat.mul_le_mul hd hd
      _ = 4 * (P * P) := by grind
      _ ≤ 4 * (S * S') := Nat.mul_le_mul_left 4 hP

/-- An integer consequence of `(S − S')² ≤ 4 S S'`: `S ≤ 6 S'` (as `3 + 2√2 < 6`). -/
theorem le_six_of_quadratic {S S' : Nat} (h : (S - S') * (S - S') ≤ 4 * (S * S')) :
    S ≤ 6 * S' := by
  by_cases hle : S ≤ 6 * S'
  · exact hle
  exfalso
  have h6 : 6 * S' + 1 ≤ S := by omega
  obtain ⟨d, hd⟩ := Nat.le.dest h6
  -- `S = 6S' + 1 + d`; then `(S − S')² = (5S' + 1 + d)² > 4 S S'`.
  subst hd
  have hsub : 6 * S' + 1 + d - S' = 5 * S' + 1 + d := by omega
  rw [hsub] at h
  have hexp : (5 * S' + 1 + d) * (5 * S' + 1 + d) =
      4 * ((6 * S' + 1 + d) * S') + (S' * S' + (1 + d) * (1 + d) + 6 * S' * (1 + d)) := by grind
  rw [hexp] at h
  have hpos : 1 * 1 ≤ (1 + d) * (1 + d) := Nat.mul_le_mul (by omega) (by omega)
  omega

/-- `2 · binom(n, 2) + n = n²`. -/
theorem two_pairCount_add (n : Nat) : 2 * pairCount n + n = n * n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [pairCount]; grind

end STACS2027

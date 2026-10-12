module

public import Approximation.RoundingBounds

/-!
Theorem 17: independent randomized rounding of a fractional optimum has
expected cost at most `OPT + (k − 2) t / k`. The expectation over the product
distribution is `rounded`; its value on the sum of squared loads is the scaled
expected sum `expectedSquares`, by the averaging identity applied cycle by
cycle.
-/

@[expose] public section
namespace STACS2027

theorem rounded_nil (f : List (List Edge) → Nat) (acc : List (List Edge)) :
    rounded f acc [] = f acc := rfl

theorem rounded_cons (f : List (List Edge) → Nat) (acc : List (List Edge))
    (opts : List (List Edge)) (w : List Nat) (R : List (List (List Edge) × List Nat)) :
    rounded f acc ((opts, w) :: R) = weightedSum (fun p => rounded f (acc ++ [p]) R) opts w := rfl

/-- The expectation depends only on the values at the reachable final assignments. -/
theorem rounded_congr {f g : List (List Edge) → Nat} {acc : List (List Edge)}
    {R : List (List (List Edge) × List Nat)}
    (h : ∀ chosen, ValidChoices (R.map Prod.fst) chosen → f (acc ++ chosen) = g (acc ++ chosen)) :
    rounded f acc R = rounded g acc R := by
  induction R generalizing acc with
  | nil => simpa [rounded_nil] using h [] trivial
  | cons r R ih =>
    obtain ⟨opts, w⟩ := r
    rw [rounded_cons, rounded_cons]
    apply weightedSum_congr _ w
    intro p hp
    apply ih
    intro chosen hc
    have := h (p :: chosen) ⟨hp, hc⟩
    simpa [List.append_assoc] using this

theorem rounded_add (f g : List (List Edge) → Nat) (acc : List (List Edge))
    (R : List (List (List Edge) × List Nat)) :
    rounded (fun qs => f qs + g qs) acc R = rounded f acc R + rounded g acc R := by
  induction R generalizing acc with
  | nil => rfl
  | cons r R ih =>
    obtain ⟨opts, w⟩ := r
    simp only [rounded_cons, ih, weightedSum_add]

theorem rounded_mul_left (c : Nat) (f : List (List Edge) → Nat) (acc : List (List Edge))
    (R : List (List (List Edge) × List Nat)) :
    rounded (fun qs => c * f qs) acc R = c * rounded f acc R := by
  induction R generalizing acc with
  | nil => rfl
  | cons r R ih =>
    obtain ⟨opts, w⟩ := r
    simp only [rounded_cons, ih, weightedSum_mul_left]

theorem rounded_const {D : Nat} (c : Nat) (acc : List (List Edge))
    {R : List (List (List Edge) × List Nat)} (hf : FractionalSolution D R) :
    rounded (fun _ => c) acc R = D ^ R.length * c := by
  induction R generalizing acc with
  | nil => simp [rounded_nil]
  | cons r R ih =>
    obtain ⟨opts, w⟩ := r
    rw [rounded_cons]
    have hrec : ∀ p, rounded (fun _ => c) (acc ++ [p]) R = D ^ R.length * c :=
      fun p => ih (acc ++ [p]) hf.tail
    rw [weightedSum_congr (g := fun _ => D ^ R.length * c) (fun p _ => hrec p) w,
      weightedSum_const _ hf.head.1, hf.head.2, List.length_cons, Nat.pow_succ]
    grind

/-- `D²` times the expected sum of squared loads is `D^{|R|}` times `expectedSquares`. -/
theorem rounded_sq_eq {es : List Edge} {D L : Nat} (acc : List (List Edge))
    {R : List (List (List Edge) × List Nat)} (hin : OptionsIn es L R)
    (hf : FractionalSolution D R) :
    D * D * rounded (fun qs => (es.map fun e => load qs e * load qs e).sum) acc R =
      D ^ R.length * expectedSquares D acc R es := by
  induction R generalizing acc with
  | nil => rw [rounded_nil, expectedSquares_nil]; simp
  | cons r R ih =>
    obtain ⟨opts, w⟩ := r
    rw [rounded_cons, ← weightedSum_mul_left]
    have hrec : ∀ p ∈ opts, D * D * rounded (fun qs => (es.map fun e => load qs e * load qs e).sum)
        (acc ++ [p]) R = D ^ R.length * expectedSquares D (acc ++ [p]) R es :=
      fun p _ => ih (acc ++ [p]) hin.tail hf.tail
    rw [weightedSum_congr hrec w, weightedSum_mul_left,
      average_identity_sum (fun p hp => (hin.head p hp).1) hf.head.1 hf.head.2 acc R,
      List.length_cons, Nat.pow_succ]
    grind

/-- Theorem 17: independent randomized rounding of a fractional optimum has expected cost at most
`OPT + (k − 2) t / k`: `k D^t E[c(τ)] ≤ D^t (k c(qs) + (k − 2) t)` for every assignment `qs`
(`k = L + 2`, `t` the number of cycles, `D^t E[c(τ)] = rounded cost [] R`). -/
theorem expectedCost_bound {es : List Edge} (he : es.Nodup) {D L : Nat}
    {R : List (List (List Edge) × List Nat)} (hR : CycleInstance es L R)
    (hopt : OptimalFractional es D R) {qs : List (List Edge)}
    (hq : ValidChoices (R.map Prod.fst) qs) :
    (L + 2) * rounded cost [] R ≤ D ^ R.length * ((L + 2) * cost qs + L * R.length) := by
  have hf := hopt.1
  have hD := hf.1
  have hin := hR.optionsIn
  obtain ⟨hqn, hql, hqs, hqlen⟩ := hin.choices hq
  -- The expected sum of squared loads is `2 E[c] + L t` (scaled).
  have hsq : rounded (fun qs => (es.map fun e => load qs e * load qs e).sum) [] R =
      2 * rounded cost [] R + D ^ R.length * (L * R.length) := by
    rw [← rounded_mul_left, ← rounded_const (L * R.length) [] hf, ← rounded_add]
    apply rounded_congr
    intro chosen hc
    obtain ⟨hn, hl, hs, hlen⟩ := hin.choices hc
    rw [List.nil_append, sum_sq_load_assignment he hn hl hs, hlen]
  have hmain := rounded_sq_eq [] hin hf
  rw [hsq, expectedSquares_start] at hmain
  have hlow := fractional_le_integral he hopt hq hqn hqs
  rw [sum_fractionalLoad he hin hf] at hlow
  have hvar := variance_sum_bound he hR hf
  -- Combine.
  have e1 : D * D * (2 * rounded cost [] R + D ^ R.length * (L * R.length)) =
      2 * (D * D) * rounded cost [] R + D ^ R.length * (D * D * (L * R.length)) := by grind
  have e2 : D * D * (2 * cost qs) + D * (D * L * R.length) =
      2 * (D * D) * cost qs + D * D * (L * R.length) := by grind
  have e3 : 2 * (D * D * L) * R.length = 2 * (D * D) * (L * R.length) := by grind
  rw [e1] at hmain
  rw [e2] at hlow
  rw [e3] at hvar
  generalize hE : rounded cost [] R = Ex at hmain ⊢
  generalize (es.map fun e => fractionalLoad R e * fractionalLoad R e).sum = S at hmain hlow
  generalize (es.map (varianceLoad D R)).sum = V at hmain hvar
  generalize hP : D ^ R.length = P at hmain ⊢
  generalize D * D * (L * R.length) = C at hmain hlow
  generalize hM : D * D = M at hmain hlow hvar ⊢
  -- hmain : 2 M Ex + P C = P (S + V); hlow : S ≤ 2 M c(qs) + C; hvar : (L+2) V ≤ 2 M (L t).
  have hmain' : 2 * M * Ex + P * C = P * S + P * V := by rw [hmain, Nat.mul_add]
  have h1 : (L + 2) * (2 * M * Ex) + (L + 2) * (P * C) ≤
      (L + 2) * (P * (2 * M * cost qs + C)) + P * ((L + 2) * V) := by
    have := Nat.mul_le_mul_left (L + 2) (Nat.le_of_eq hmain')
    have h2 := Nat.mul_le_mul_left ((L + 2) * P) hlow
    grind
  have h3 : P * ((L + 2) * V) ≤ P * (2 * M * (L * R.length)) := Nat.mul_le_mul_left P hvar
  have hgoal : 2 * M * ((L + 2) * Ex) ≤ 2 * M * (P * ((L + 2) * cost qs + L * R.length)) := by
    grind
  have hMpos : 0 < 2 * M := by rw [← hM]; exact Nat.mul_pos (by decide) (Nat.mul_pos hD hD)
  exact Nat.le_of_mul_le_mul_left hgoal hMpos

end STACS2027

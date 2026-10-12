module

public import Approximation.Loads

/-!
Weighted sums over the options of a cycle. A fractional solution of the
relaxation of Section 7.2 is represented with a common denominator `D`: the
option `P` of a cycle has weight `x_P ∈ ℕ` standing for the fraction `x_P / D`,
and the weights of a cycle sum to `D`.
-/

@[expose] public section
namespace STACS2027

/-- `∑_j w_j · f(P_j)`: the sum of `f` over the options `P_j`, weighted by `w_j`. -/
def weightedSum (f : List Edge → Nat) : List (List Edge) → List Nat → Nat
  | [], _ => 0
  | _ :: _, [] => 0
  | p :: ps, c :: cs => c * f p + weightedSum f ps cs

/-- The weights that give the option `q` the whole mass `1` (at its first occurrence) and every
other option the weight `0`: the integral solution choosing `q`. -/
def unitWeights : List (List Edge) → List Edge → List Nat
  | [], _ => []
  | p :: ps, q => if p = q then 1 :: ps.map (fun _ => 0) else 0 :: unitWeights ps q

theorem weightedSum_nil_left (f : List Edge → Nat) (w : List Nat) : weightedSum f [] w = 0 := by
  cases w <;> rfl

theorem weightedSum_nil_right (f : List Edge → Nat) (opts : List (List Edge)) :
    weightedSum f opts [] = 0 := by
  cases opts <;> rfl

theorem weightedSum_cons (f : List Edge → Nat) (p : List Edge) (ps : List (List Edge))
    (c : Nat) (cs : List Nat) : weightedSum f (p :: ps) (c :: cs) = c * f p + weightedSum f ps cs :=
  rfl

theorem weightedSum_congr {f g : List Edge → Nat} {opts : List (List Edge)}
    (h : ∀ p ∈ opts, f p = g p) (w : List Nat) : weightedSum f opts w = weightedSum g opts w := by
  induction opts generalizing w with
  | nil => simp [weightedSum_nil_left]
  | cons p ps ih =>
    cases w with
    | nil => simp [weightedSum_nil_right]
    | cons c cs =>
      rw [weightedSum_cons, weightedSum_cons, h p (by simp), ih (fun q hq => h q (by simp [hq]))]

theorem weightedSum_add (f g : List Edge → Nat) (opts : List (List Edge)) (w : List Nat) :
    weightedSum (fun p => f p + g p) opts w = weightedSum f opts w + weightedSum g opts w := by
  induction opts generalizing w with
  | nil => simp [weightedSum_nil_left]
  | cons p ps ih =>
    cases w with
    | nil => simp [weightedSum_nil_right]
    | cons c cs => simp only [weightedSum_cons, ih, Nat.mul_add]; omega

theorem weightedSum_mul_left (c : Nat) (f : List Edge → Nat) (opts : List (List Edge))
    (w : List Nat) : weightedSum (fun p => c * f p) opts w = c * weightedSum f opts w := by
  induction opts generalizing w with
  | nil => simp [weightedSum_nil_left]
  | cons p ps ih =>
    cases w with
    | nil => simp [weightedSum_nil_right]
    | cons d ds => simp only [weightedSum_cons, ih, Nat.mul_add]; grind

theorem weightedSum_const (c : Nat) {opts : List (List Edge)} {w : List Nat}
    (hl : w.length = opts.length) : weightedSum (fun _ => c) opts w = w.sum * c := by
  induction opts generalizing w with
  | nil => cases w with
    | nil => simp [weightedSum_nil_left]
    | cons _ _ => simp at hl
  | cons p ps ih =>
    cases w with
    | nil => simp at hl
    | cons d ds =>
      simp only [List.length_cons] at hl
      rw [weightedSum_cons, ih (by omega), List.sum_cons, Nat.add_mul]

theorem weightedSum_le (f g : List Edge → Nat) (opts : List (List Edge)) (w : List Nat)
    (h : ∀ p ∈ opts, f p ≤ g p) : weightedSum f opts w ≤ weightedSum g opts w := by
  induction opts generalizing w with
  | nil => simp [weightedSum_nil_left]
  | cons p ps ih =>
    cases w with
    | nil => simp [weightedSum_nil_right]
    | cons c cs =>
      rw [weightedSum_cons, weightedSum_cons]
      exact Nat.add_le_add (Nat.mul_le_mul_left c (h p (by simp)))
        (ih cs (fun q hq => h q (by simp [hq])))

/-- The weighted sum of a sum over edges is the sum over edges of the weighted sums. -/
theorem weightedSum_sum_swap (h : List Edge → Edge → Nat) (es : List Edge)
    (opts : List (List Edge)) (w : List Nat) :
    weightedSum (fun p => (es.map (h p)).sum) opts w =
      (es.map fun e => weightedSum (fun p => h p e) opts w).sum := by
  induction es with
  | nil => simp only [List.map_nil, List.sum_nil]; rw [← Nat.mul_zero 0, weightedSum_mul_left]; simp
  | cons e es ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [← ih, ← weightedSum_add]

/-- A weighted sum is at least the total weight times the minimum value. -/
theorem weightedSum_ge_min (f : List Edge → Nat) {opts : List (List Edge)} {w : List Nat}
    (hl : w.length = opts.length) {p : List Edge} (hp : ∀ q ∈ opts, f p ≤ f q) :
    w.sum * f p ≤ weightedSum f opts w := by
  rw [← weightedSum_const (f p) hl]
  exact weightedSum_le _ _ opts w hp

theorem unitWeights_length (opts : List (List Edge)) (q : List Edge) :
    (unitWeights opts q).length = opts.length := by
  induction opts with
  | nil => rfl
  | cons p ps ih =>
    simp only [unitWeights]
    split <;> simp [ih]

theorem unitWeights_sum {opts : List (List Edge)} {q : List Edge} (hq : q ∈ opts) :
    (unitWeights opts q).sum = 1 := by
  induction opts with
  | nil => simp at hq
  | cons p ps ih =>
    simp only [unitWeights]
    split
    · simp [sum_map_zero]
    · rename_i hne
      have hq' : q ∈ ps := by
        rcases List.mem_cons.mp hq with rfl | h
        · exact absurd rfl hne
        · exact h
      simp [ih hq']

theorem weightedSum_zeros (f : List Edge → Nat) (ps : List (List Edge)) :
    weightedSum f ps (ps.map fun _ => 0) = 0 := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [weightedSum_cons, ih]

/-- The weighted sum under the unit weights of `q` is the value at `q`. -/
theorem weightedSum_unitWeights (f : List Edge → Nat) {opts : List (List Edge)} {q : List Edge}
    (hq : q ∈ opts) : weightedSum f opts (unitWeights opts q) = f q := by
  induction opts with
  | nil => simp at hq
  | cons p ps ih =>
    simp only [unitWeights]
    split
    · rename_i heq; subst heq; simp [weightedSum_cons, weightedSum_zeros]
    · rename_i hne
      have hq' : q ∈ ps := by
        rcases List.mem_cons.mp hq with rfl | h
        · exact absurd rfl hne
        · exact h
      simp [weightedSum_cons, ih hq']

end STACS2027

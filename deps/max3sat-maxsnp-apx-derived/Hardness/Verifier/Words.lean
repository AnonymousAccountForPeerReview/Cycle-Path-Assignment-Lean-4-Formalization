module

public import ComplexityExt.PCP.Defs
import Mathlib.Tactic.Ring

/-!
# Exact counting over the words of a fixed length

Everything the PCP verifier needs about its random strings, as statements about
`List.countP` over `allWords n`:

* `allWords n` has `2 ^ n` elements, exactly the words of length `n`, each once;
* `binValue` (the value of a word read as a binary numeral, most significant bit first)
  enumerates `0, …, 2 ^ n - 1` along `allWords n` (`countP_binValue`);
* counting over `allWords (a + b)` factorises for predicates of a prefix and of the
  remaining suffix (`countP_take_drop`), hence over `k` consecutive blocks (`countP_blocks`);
* reduction modulo `m` hits every residue at least `⌊N / m⌋` times on `0, …, N - 1`
  (`countP_mod_range_mul`);
* the elementary inequality `(1 - 1/D) ^ D ≤ 1/2` in the form `gap_power`.
-/

@[expose] public section

namespace Complexity

/-! ### The list of all words of a given length -/

theorem countP_flatMap_bits (p : Word → Bool) (l : List Word) :
    (l.flatMap fun w => [false :: w, true :: w]).countP p =
      l.countP (fun w => p (false :: w)) + l.countP (fun w => p (true :: w)) := by
  induction l with
  | nil => rfl
  | cons w l ih =>
    simp only [List.flatMap_cons, List.countP_append, ih, List.countP_cons, List.countP_nil]
    cases p (false :: w) <;> cases p (true :: w) <;> simp <;> omega

/-- Counting over the words of length `n + 1`, split by the first bit. -/
theorem allWords_countP_succ (p : Word → Bool) (n : Nat) :
    (allWords (n + 1)).countP p =
      (allWords n).countP (fun w => p (false :: w)) +
        (allWords n).countP (fun w => p (true :: w)) :=
  countP_flatMap_bits p (allWords n)

/-- There are `2 ^ n` words of length `n`. -/
theorem allWords_length (n : Nat) : (allWords n).length = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h := allWords_countP_succ (fun _ => true) n
    simp only [List.countP_true] at h
    rw [h, ih, Nat.pow_succ]
    omega

theorem allWords_ne_nil (n : Nat) : allWords n ≠ [] := by
  intro h
  have := allWords_length n
  rw [h] at this
  have hpos : 0 < 2 ^ n := Nat.pow_pos (by decide)
  simp at this
  omega

/-- `allWords n` contains exactly the words of length `n`. -/
theorem mem_allWords {n : Nat} {w : Word} : w ∈ allWords n ↔ w.length = n := by
  induction n generalizing w with
  | zero => simp [allWords_zero]
  | succ n ih =>
    simp only [allWords_succ, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro ⟨v, hv, rfl | rfl⟩ <;> simp [ih.mp hv]
    · intro hw
      cases w with
      | nil => simp at hw
      | cons b w =>
        refine ⟨w, ih.mpr (by simpa using hw), ?_⟩
        cases b <;> simp

/-- No word occurs twice in `allWords n`. -/
theorem allWords_count_le_one (n : Nat) (w : Word) :
    (allWords n).countP (fun v => decide (v = w)) ≤ 1 := by
  induction n generalizing w with
  | zero => simp only [allWords_zero, List.countP_cons, List.countP_nil]; split <;> omega
  | succ n ih =>
    rw [allWords_countP_succ]
    cases w with
    | nil => simp
    | cons b w =>
      have h := ih w
      cases b <;> simpa using h

/-! ### Binary values -/

/-- The value of a binary word, most significant bit first. -/
def binValue (w : Word) : Nat :=
  w.foldl (fun acc b => 2 * acc + (if b then 1 else 0)) 0

theorem binValue_foldl (w : Word) (acc : Nat) :
    w.foldl (fun acc b => 2 * acc + (if b then 1 else 0)) acc =
      acc * 2 ^ w.length + binValue w := by
  induction w generalizing acc with
  | nil => simp [binValue]
  | cons b w ih =>
    have h1 := ih (2 * acc + (if b then 1 else 0))
    have h2 := ih (2 * 0 + (if b then 1 else 0))
    simp only [List.foldl_cons, binValue, List.length_cons] at h1 h2 ⊢
    rw [h1, h2, Nat.pow_succ]
    ring

@[simp] theorem binValue_nil : binValue [] = 0 := rfl

theorem binValue_cons (b : Bool) (w : Word) :
    binValue (b :: w) = (if b then 1 else 0) * 2 ^ w.length + binValue w := by
  have h := binValue_foldl w (2 * 0 + (if b then 1 else 0))
  simpa [binValue] using h

@[simp] theorem binValue_false_cons (w : Word) : binValue (false :: w) = binValue w := by
  simp [binValue_cons]

@[simp] theorem binValue_true_cons (w : Word) :
    binValue (true :: w) = 2 ^ w.length + binValue w := by
  simp [binValue_cons]

theorem binValue_lt (w : Word) : binValue w < 2 ^ w.length := by
  induction w with
  | nil => simp
  | cons b w ih =>
    cases b <;> simp only [binValue_false_cons, binValue_true_cons, List.length_cons,
      Nat.pow_succ] <;> omega

theorem countP_range_add (f : Nat → Bool) (a b : Nat) :
    (List.range (a + b)).countP f =
      (List.range a).countP f + (List.range b).countP (fun v => f (a + v)) := by
  rw [List.range_add, List.countP_append, List.countP_map]
  rfl

/-- Along `allWords n` the binary values run through `0, …, 2 ^ n - 1`, each once: counting
a property of the value of a random block is counting it over `List.range (2 ^ n)`. -/
theorem countP_binValue (f : Nat → Bool) (n : Nat) :
    (allWords n).countP (fun w => f (binValue w)) = (List.range (2 ^ n)).countP f := by
  induction n generalizing f with
  | zero => cases h : f 0 <;> simp [allWords_zero, h]
  | succ n ih =>
    rw [allWords_countP_succ]
    have h1 : (allWords n).countP (fun w => f (binValue (true :: w))) =
        (allWords n).countP (fun w => f (2 ^ n + binValue w)) := by
      apply List.countP_congr
      intro w hw
      rw [binValue_true_cons, mem_allWords.mp hw]
    simp only [binValue_false_cons]
    rw [h1, ih f, ih (fun v => f (2 ^ n + v)), Nat.pow_succ, Nat.mul_two, countP_range_add]

/-- `binValue` is injective on words of the same length. -/
theorem binValue_injective {v w : Word} (hlen : v.length = w.length)
    (h : binValue v = binValue w) : v = w := by
  induction v generalizing w with
  | nil =>
    cases w with
    | nil => rfl
    | cons _ _ => simp at hlen
  | cons a v ih =>
    cases w with
    | nil => simp at hlen
    | cons b w =>
      have hl : v.length = w.length := by simpa using hlen
      have hv := binValue_lt v
      have hw := binValue_lt w
      rw [binValue_cons, binValue_cons, hl] at h
      rw [hl] at hv
      cases a <;> cases b <;> simp at h
      · rw [ih hl h]
      · omega
      · omega
      · rw [ih hl h]

/-! ### Blocks -/

/-- Cut `r` into `k` consecutive blocks of `ℓ` bits. -/
def blocks (k ℓ : Nat) (r : Word) : List Word :=
  (List.range k).map (fun i => (r.drop (i * ℓ)).take ℓ)

@[simp] theorem blocks_zero (ℓ : Nat) (r : Word) : blocks 0 ℓ r = [] := rfl

@[simp] theorem blocks_length (k ℓ : Nat) (r : Word) : (blocks k ℓ r).length = k := by
  simp [blocks]

theorem blocks_succ (k ℓ : Nat) (r : Word) :
    blocks (k + 1) ℓ r = r.take ℓ :: blocks k ℓ (r.drop ℓ) := by
  simp only [blocks, List.range_succ_eq_map, List.map_cons, List.map_map, Nat.zero_mul,
    List.drop_zero]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, List.drop_drop, Nat.succ_mul]
  rw [Nat.add_comm]

/-- Counting over `allWords (a + b)` factorises for a property of the first `a` bits and a
property of the remaining `b` bits. -/
theorem countP_take_drop (P Q : Word → Bool) (a b : Nat) :
    (allWords (a + b)).countP (fun r => P (r.take a) && Q (r.drop a)) =
      (allWords a).countP P * (allWords b).countP Q := by
  induction a generalizing P with
  | zero =>
    simp only [Nat.zero_add, List.take_zero, List.drop_zero, allWords_zero, List.countP_cons,
      List.countP_nil]
    cases P [] <;> simp
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by omega, allWords_countP_succ, allWords_countP_succ]
    simp only [List.take_succ_cons, List.drop_succ_cons]
    rw [ih (fun w => P (false :: w)), ih (fun w => P (true :: w)), Nat.add_mul]

/-- The `k` blocks of a uniformly random word of length `k * ℓ` are independent and uniform:
the number of words all of whose blocks satisfy `P` is the `k`-th power of the number of
blocks satisfying `P`. -/
theorem countP_blocks (P : Word → Bool) (k ℓ : Nat) :
    (allWords (k * ℓ)).countP (fun r => (blocks k ℓ r).all P) =
      ((allWords ℓ).countP P) ^ k := by
  induction k with
  | zero => simp [allWords_zero]
  | succ k ih =>
    rw [show (k + 1) * ℓ = ℓ + k * ℓ by rw [Nat.succ_mul, Nat.add_comm]]
    simp only [blocks_succ, List.all_cons]
    rw [countP_take_drop P (fun r => (blocks k ℓ r).all P), ih, Nat.pow_succ, Nat.mul_comm]

/-! ### Residues -/

/-- On `0, …, m * q - 1` every residue modulo `m` occurs exactly `q` times. -/
theorem countP_mod_range_mul (p : Nat → Bool) (m q : Nat) :
    (List.range (m * q)).countP (fun v => p (v % m)) = q * (List.range m).countP p := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.mul_succ, countP_range_add, ih]
    have h : (List.range m).countP (fun v => p ((m * q + v) % m)) = (List.range m).countP p := by
      apply List.countP_congr
      intro v hv
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt (List.mem_range.mp hv)]
    rw [h, Nat.succ_mul]

theorem countP_range_mono (f : Nat → Bool) {a b : Nat} (h : a ≤ b) :
    (List.range a).countP f ≤ (List.range b).countP f :=
  (List.range_sublist.mpr h).countP_le

/-- A list is the list of its entries. -/
theorem map_getD_range {α : Type} (l : List α) (d : α) :
    (List.range l.length).map (fun i => l.getD i d) = l := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [List.getD_eq_getElem?_getD, h2]

/-- Counting over the entries of a list is counting over its indices. -/
theorem countP_range_getD {α : Type} (p : α → Bool) (l : List α) (d : α) :
    (List.range l.length).countP (fun i => p (l.getD i d)) = l.countP p := by
  conv_rhs => rw [← map_getD_range l d]
  rw [List.countP_map]
  rfl

/-! ### The amplification inequality -/

theorem pow_mul_add_le (a n : Nat) : a ^ n * (a + n) ≤ (a + 1) ^ n * a := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : a ^ n ≤ (a + 1) ^ n := Nat.pow_le_pow_left (Nat.le_succ a) n
    calc a ^ (n + 1) * (a + (n + 1)) = a * (a ^ n * (a + n)) + a * a ^ n := by ring
      _ ≤ a * ((a + 1) ^ n * a) + a * (a + 1) ^ n :=
        Nat.add_le_add (Nat.mul_le_mul_left a ih) (Nat.mul_le_mul_left a h1)
      _ = (a + 1) ^ (n + 1) * a := by ring

/-- `(1 - 1/(a+1)) ^ (a+1) ≤ 1/2`. -/
theorem two_mul_pow_le (a : Nat) : 2 * a ^ (a + 1) ≤ (a + 1) ^ (a + 1) := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp
  · have h := pow_mul_add_le a (a + 1)
    have h2 : a * (2 * a ^ (a + 1)) ≤ a * (a + 1) ^ (a + 1) := by
      calc a * (2 * a ^ (a + 1)) ≤ a ^ (a + 1) * (a + (a + 1)) := by
            have : a ^ (a + 1) * (a + (a + 1)) = a * (2 * a ^ (a + 1)) + a ^ (a + 1) := by ring
            omega
        _ ≤ (a + 1) ^ (a + 1) * a := h
        _ = a * (a + 1) ^ (a + 1) := Nat.mul_comm _ _
    exact Nat.le_of_mul_le_mul_left h2 ha

/-- If a single trial succeeds with probability at most `1 - 1/D` (`S` of `N` outcomes, with
`D * S + N ≤ D * N`), then `D` independent trials all succeed with probability at most
`1/2`. -/
theorem gap_power (D S N : Nat) (h : D * S + N ≤ D * N) (hN : 0 < N) :
    2 * S ^ D ≤ N ^ D := by
  cases D with
  | zero => omega
  | succ a =>
    have h1 : (a + 1) * S ≤ a * N := by
      have : (a + 1) * N = a * N + N := by ring
      omega
    have h2 : ((a + 1) * S) ^ (a + 1) ≤ (a * N) ^ (a + 1) := Nat.pow_le_pow_left h1 _
    rw [Nat.mul_pow, Nat.mul_pow] at h2
    have h3 := two_mul_pow_le a
    have h4 : (a + 1) ^ (a + 1) * (2 * S ^ (a + 1)) ≤ (a + 1) ^ (a + 1) * N ^ (a + 1) := by
      calc (a + 1) ^ (a + 1) * (2 * S ^ (a + 1)) = 2 * ((a + 1) ^ (a + 1) * S ^ (a + 1)) := by ring
        _ ≤ 2 * (a ^ (a + 1) * N ^ (a + 1)) := Nat.mul_le_mul_left 2 h2
        _ = (2 * a ^ (a + 1)) * N ^ (a + 1) := by ring
        _ ≤ (a + 1) ^ (a + 1) * N ^ (a + 1) := Nat.mul_le_mul_right _ h3
    exact Nat.le_of_mul_le_mul_left h4 (Nat.pow_pos (Nat.succ_pos a))

end Complexity

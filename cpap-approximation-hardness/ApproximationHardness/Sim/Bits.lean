module

public import Init
import Lean.Elab.Tactic.Omega

/-!
# Binary numerals

`num bs` is the value of the bit list `bs`, least significant bit first; `bin n` is the canonical
numeral of `n` (no trailing zero bits). `canon bs` says that `bs` has no trailing zero bit.
-/

@[expose] public section

namespace STACS2027.Sim

/-- The value of a bit list, least significant bit first. -/
def num : List Bool → Nat
  | [] => 0
  | b :: bs => b.toNat + 2 * num bs

/-- The binary numeral of `n`, least significant bit first, computed with fuel `f ≥ n`. -/
def binAux : Nat → Nat → List Bool
  | 0, _ => []
  | f + 1, n => if n = 0 then [] else (n % 2 == 1) :: binAux f (n / 2)

/-- The canonical binary numeral of `n`, least significant bit first. -/
def bin (n : Nat) : List Bool := binAux n n

/-- No trailing zero bit. -/
def canon : List Bool → Bool
  | [] => true
  | [b] => b
  | _ :: b :: bs => canon (b :: bs)

@[simp] theorem num_nil : num [] = 0 := rfl
@[simp] theorem num_cons (b : Bool) (bs : List Bool) : num (b :: bs) = b.toNat + 2 * num bs := rfl

theorem binAux_eq : ∀ f g n, n ≤ f → n ≤ g → binAux f n = binAux g n := by
  intro f
  induction f with
  | zero => intro g n hf _; have : n = 0 := by omega
            subst this; cases g <;> simp [binAux]
  | succ f ih =>
    intro g n hf hg
    cases g with
    | zero => have : n = 0 := by omega
              subst this; simp [binAux]
    | succ g =>
      simp only [binAux]
      split
      · rfl
      · rw [ih g (n / 2) (by omega) (by omega)]

@[simp] theorem bin_zero : bin 0 = [] := rfl

theorem bin_pos {n : Nat} (h : n ≠ 0) : bin n = (n % 2 == 1) :: bin (n / 2) := by
  unfold bin
  obtain ⟨f, hf⟩ : ∃ f, n = f + 1 := ⟨n - 1, by omega⟩
  rw [hf]
  simp only [binAux, Nat.add_one_ne_zero, ite_false]
  rw [binAux_eq f ((f + 1) / 2) ((f + 1) / 2) (by omega) (Nat.le_refl _)]

theorem num_bin : ∀ n, num (bin n) = n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases h : n = 0
    · subst h; rfl
    · rw [bin_pos h, num_cons, ih (n / 2) (by omega)]
      cases h2 : n % 2 == 1 <;> simp at h2 <;> simp <;> omega

theorem canon_cons {b : Bool} {bs : List Bool} : canon (b :: bs) = (canon bs && (bs ≠ [] || b)) := by
  cases bs with
  | nil => simp [canon]
  | cons c cs => simp [canon]

theorem canon_bin : ∀ n, canon (bin n) = true := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases h : n = 0
    · subst h; rfl
    · rw [bin_pos h, canon_cons, ih (n / 2) (by omega)]
      by_cases h2 : n / 2 = 0
      · have : n = 1 := by omega
        subst this; decide
      · rw [bin_pos h2]; simp

theorem num_ne_zero_of_canon {bs : List Bool} (hc : canon bs = true) (hne : bs ≠ []) : num bs ≠ 0 := by
  induction bs with
  | nil => exact absurd rfl hne
  | cons b bs ih =>
    rw [canon_cons] at hc
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hc
    obtain ⟨hc, hb⟩ := hc
    rw [num_cons]
    rcases hb with hb | hb
    · have := ih hc hb; omega
    · subst hb; simp

theorem bin_num {bs : List Bool} (hc : canon bs = true) : bin (num bs) = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    have hne := num_ne_zero_of_canon hc (List.cons_ne_nil b bs)
    rw [canon_cons] at hc
    simp only [Bool.and_eq_true] at hc
    rw [bin_pos hne, num_cons]
    have h1 : ((b.toNat + 2 * num bs) % 2 == 1) = b := by cases b <;> simp <;> omega
    have h2 : (b.toNat + 2 * num bs) / 2 = num bs := by cases b <;> simp <;> omega
    rw [h1, h2, ih hc.1]

theorem num_lt (bs : List Bool) : num bs < 2 ^ bs.length := by
  induction bs with
  | nil => simp
  | cons b bs ih => simp only [num_cons, List.length_cons, Nat.pow_succ]; cases b <;> simp <;> omega

theorem bin_length_le {n B : Nat} (h : n < 2 ^ B) : (bin n).length ≤ B := by
  induction B generalizing n with
  | zero =>
    have : n = 0 := by simp at h; omega
    subst this; simp
  | succ B ih =>
    by_cases hn : n = 0
    · subst hn; simp
    · rw [bin_pos hn, List.length_cons]
      have := ih (n := n / 2) (by rw [Nat.pow_succ] at h; omega)
      omega

theorem lt_pow_bin_length (n : Nat) : n < 2 ^ (bin n).length := by
  have := num_lt (bin n); rwa [num_bin] at this

theorem num_append (xs ys : List Bool) : num (xs ++ ys) = num xs + 2 ^ xs.length * num ys := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.cons_append, num_cons, ih, List.length_cons, Nat.pow_succ]
                    rw [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm 2 (2 ^ xs.length)]; omega

theorem num_replicate_false (k : Nat) : num (List.replicate k false) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, ih]

/-- The canonical numeral of a most-significant-first bit list `z`: drop its leading zeros and
reverse it. -/
theorem bin_num_reverse (z : List Bool) : bin (num z.reverse) = (z.dropWhile (· == false)).reverse := by
  induction z with
  | nil => rfl
  | cons b z ih =>
    cases b with
    | false =>
      simp only [List.reverse_cons, num_append, List.dropWhile_cons, BEq.rfl, ite_true]
      simp only [num_cons, Bool.toNat_false, num_nil]
      simpa using ih
    | true =>
      simp only [List.dropWhile_cons]
      simp only [show (true == false) = false from rfl, Bool.false_eq_true, ite_false]
      apply bin_num
      rw [List.reverse_cons]
      clear ih
      generalize z.reverse = l
      induction l with
      | nil => rfl
      | cons c l ihl =>
        simp only [List.cons_append, canon_cons, ihl, Bool.true_and]
        simp

end STACS2027.Sim

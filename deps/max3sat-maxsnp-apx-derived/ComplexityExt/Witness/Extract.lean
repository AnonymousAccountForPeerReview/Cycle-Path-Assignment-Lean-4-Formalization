module

public import Complexity.SAT
public import Complexity.PolynomialBound
import Lean.Elab.Tactic.Omega

/-!
# Reading an NP certificate out of a satisfying assignment

The ANONYMIZED–ANONYMIZED tableau of `Complexity.CookLevin` stores the initial tape in
one-hot Boolean variables. This file defines, by elementary list operations and
index arithmetic only, the function that reads the certificate part of that
initial tape from an arbitrary assignment. Nothing here mentions machines; the
connection with the tableau formula is proved in `Complexity.Witness.Tableau`.

Layout. A tableau row for window width `width` has `2 * width + 1` slots: the
control slot `0`, the left tape slots `1 … width`, and the right tape slots
`width + 1 … 2 * width`. Each slot of each row has `states + 4` one-hot
variables; the variable for "slot `p` of row `0` holds value `j`" has index
`p * (states + 4) + j`. Symbol values are `0` = blank, `1` = bit `false`,
`2` = bit `true`, `3` = separator. Certificate cell `i` is right tape cell
`pfxLen + i`, i.e. slot `width + (pfxLen + i) + 1` of row `0`.
-/

@[expose] public section

namespace Complexity.Witness

open Complexity.SAT

/-- The one-hot variable "right tape cell `pfxLen + i` of the initial tableau row
holds value `j`", for a machine with `states + 1` control states and tape window
`width`. Values: `0` blank, `1` bit `false`, `2` bit `true`. -/
def cellVar (states width pfxLen i j : Nat) : Nat :=
  (width + (pfxLen + i) + 1) * (states + 4) + j

/-- Read a certificate of at most `bound` bits: the cells `0, 1, …` up to (not
including) the first cell whose "blank" variable is true; each such cell yields
the value of its "bit `true`" variable. -/
def readCells (states width pfxLen bound : Nat) (a : Assignment) : Word :=
  ((List.range bound).takeWhile (fun i => !a (cellVar states width pfxLen i 0))).map
    (fun i => a (cellVar states width pfxLen i 2))

/-- All variables inspected by `readCells` are below this number. -/
def cellBound (states width pfxLen bound : Nat) : Nat :=
  (width + (pfxLen + bound) + 1) * (states + 4)

theorem cellVar_lt_cellBound (states width pfxLen bound : Nat) {i j : Nat}
    (hi : i < bound) (hj : j < states + 4) :
    cellVar states width pfxLen i j < cellBound states width pfxLen bound := by
  have h := Nat.mul_le_mul_right (states + 4)
    (show width + (pfxLen + i) + 1 + 1 ≤ width + (pfxLen + bound) + 1 by omega)
  rw [Nat.succ_mul] at h
  unfold cellVar cellBound
  omega

theorem takeWhile_map_congr {α β : Type} (l : List α) (p q : α → Bool) (f g : α → β)
    (h : ∀ x ∈ l, p x = q x ∧ f x = g x) :
    (l.takeWhile p).map f = (l.takeWhile q).map g := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    have hx := h x (by simp)
    have hl : ∀ y ∈ l, p y = q y ∧ f y = g y := fun y hy => h y (by simp [hy])
    simp only [List.takeWhile_cons, ← hx.1]
    cases p x with
    | true => simp [hx.2, ih hl]
    | false => simp

theorem length_takeWhile_le' {α : Type} (p : α → Bool) (l : List α) :
    (l.takeWhile p).length ≤ l.length := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.takeWhile_cons]
    cases p x <;> simp <;> omega

theorem readCells_length_le (states width pfxLen bound : Nat) (a : Assignment) :
    (readCells states width pfxLen bound a).length ≤ bound := by
  have h := length_takeWhile_le' (fun i => !a (cellVar states width pfxLen i 0))
    (List.range bound)
  simpa [readCells] using h

/-- `readCells` only inspects variables below `cellBound`. -/
theorem readCells_congr (states width pfxLen bound : Nat) (a b : Assignment)
    (h : ∀ v, v < cellBound states width pfxLen bound → a v = b v) :
    readCells states width pfxLen bound a = readCells states width pfxLen bound b := by
  unfold readCells
  apply takeWhile_map_congr
  intro i hi
  have hi' : i < bound := List.mem_range.mp hi
  rw [h _ (cellVar_lt_cellBound states width pfxLen bound hi' (by omega)),
    h _ (cellVar_lt_cellBound states width pfxLen bound hi' (by omega))]
  exact ⟨rfl, rfl⟩

/-- A descending-free description of `takeWhile` on an interval: the predicate
holds on the first `k` numbers and fails at the next one, if there is one. -/
theorem takeWhile_range'_eq (p : Nat → Bool) (k : Nat) : ∀ (s n : Nat), k ≤ n →
    (∀ i, s ≤ i → i < s + k → p i = true) → (k < n → p (s + k) = false) →
    (List.range' s n).takeWhile p = List.range' s k := by
  induction k with
  | zero =>
    intro s n _ _ h2
    cases n with
    | zero => rfl
    | succ n =>
      have h := h2 (by omega)
      simp only [Nat.add_zero] at h
      simp [List.range'_succ, h]
  | succ k ih =>
    intro s n hk h1 h2
    cases n with
    | zero => omega
    | succ n =>
      have hs : p s = true := h1 s (Nat.le_refl _) (by omega)
      have ht := ih (s + 1) n (by omega)
        (fun i hi hi' => h1 i (by omega) (by omega))
        (fun hlt => by
          have h := h2 (by omega)
          rwa [show s + (k + 1) = s + 1 + k by omega] at h)
      simp [List.range'_succ, hs, ht]

/-- If the "blank" variables mark exactly the cells from `word.length` on and the
"bit `true`" variables spell `word` before that, `readCells` returns `word`. -/
theorem readCells_eq (states width pfxLen bound : Nat) (a : Assignment) (word : Word)
    (hw : word.length ≤ bound)
    (h0 : ∀ i, i < bound → (a (cellVar states width pfxLen i 0) = true ↔ word.length ≤ i))
    (h2 : ∀ i (hi : i < word.length), a (cellVar states width pfxLen i 2) = word[i]) :
    readCells states width pfxLen bound a = word := by
  unfold readCells
  rw [List.range_eq_range', takeWhile_range'_eq _ word.length 0 bound hw]
  · apply List.ext_getElem
    · simp
    · intro i hi hi'
      simp [h2 i hi']
  · intro i _ hi
    have hn : ¬ a (cellVar states width pfxLen i 0) = true :=
      fun ht => by have := (h0 i (by omega)).mp ht; omega
    simpa using hn
  · intro hlt
    have ht := (h0 word.length hlt).mpr (Nat.le_refl _)
    simpa using ht

/-! ### The specialisation to the verifier tableau of an NP language

The input `x` of length `n` is presented to the verifier as
`pairWords x w = 1ⁿ 0 x w`, so the fixed prefix has length `2 * n + 1`; the
certificate bound is `powerBound wc wk n`, the step bound `powerBound rc rk n`. -/

/-- The tape window of the verifier tableau on inputs of length `n`. -/
def tableauWidth (wc wk rc rk n : Nat) : Nat :=
  (2 * n + 1) + powerBound wc wk n + 2 * powerBound rc rk n + 1

/-- The variable "certificate cell `i` holds value `j`" (`0` blank, `1` bit
`false`, `2` bit `true`) in the verifier tableau for inputs of length `n`. -/
def certVar (states wc wk rc rk n i j : Nat) : Nat :=
  cellVar states (tableauWidth wc wk rc rk n) (2 * n + 1) i j

theorem certVar_eq (states wc wk rc rk n i j : Nat) :
    certVar states wc wk rc rk n i j =
      (4 * n + powerBound wc wk n + 2 * powerBound rc rk n + i + 4) * (states + 4) + j := by
  unfold certVar cellVar tableauWidth
  congr 2
  omega

/-- The certificate read off an assignment: cells `0, 1, …` below the certificate
bound, up to the first cell whose "blank" variable is true; the bit of a cell is
the value of its "bit `true`" variable. -/
def extract (states wc wk rc rk n : Nat) (a : Assignment) : Word :=
  readCells states (tableauWidth wc wk rc rk n) (2 * n + 1) (powerBound wc wk n) a

theorem extract_eq (states wc wk rc rk n : Nat) (a : Assignment) :
    extract states wc wk rc rk n a =
      ((List.range (powerBound wc wk n)).takeWhile
          (fun i => !a (certVar states wc wk rc rk n i 0))).map
        (fun i => a (certVar states wc wk rc rk n i 2)) := rfl

/-- Strict upper bound on the variables inspected by `extract`. -/
def varBound (states wc wk rc rk n : Nat) : Nat :=
  cellBound states (tableauWidth wc wk rc rk n) (2 * n + 1) (powerBound wc wk n)

theorem varBound_eq (states wc wk rc rk n : Nat) :
    varBound states wc wk rc rk n =
      (4 * n + 2 * powerBound wc wk n + 2 * powerBound rc rk n + 4) * (states + 4) := by
  unfold varBound cellBound tableauWidth
  congr 1
  omega

theorem certVar_lt_varBound (states wc wk rc rk n : Nat) {i j : Nat}
    (hi : i < powerBound wc wk n) (hj : j < states + 4) :
    certVar states wc wk rc rk n i j < varBound states wc wk rc rk n :=
  cellVar_lt_cellBound _ _ _ _ hi hj

theorem extract_length_le (states wc wk rc rk n : Nat) (a : Assignment) :
    (extract states wc wk rc rk n a).length ≤ powerBound wc wk n :=
  readCells_length_le _ _ _ _ a

/-- Locality: `extract` depends only on the variables below `varBound`. -/
theorem extract_congr (states wc wk rc rk n : Nat) (a b : Assignment)
    (h : ∀ v, v < varBound states wc wk rc rk n → a v = b v) :
    extract states wc wk rc rk n a = extract states wc wk rc rk n b :=
  readCells_congr _ _ _ _ a b h

theorem varBound_polynomial (states wc wk rc rk : Nat) :
    PolynomialBound (varBound states wc wk rc rk) := by
  have hB := PolynomialBound.power wc wk
  have hS := PolynomialBound.power rc rk
  have h := (((((PolynomialBound.constant 4).mul PolynomialBound.identity).add
    ((PolynomialBound.constant 2).mul hB)).add
    ((PolynomialBound.constant 2).mul hS)).add (PolynomialBound.constant 4)).mul
    (PolynomialBound.constant (states + 4))
  exact h.weaken (fun n => Nat.le_of_eq (varBound_eq states wc wk rc rk n))

end Complexity.Witness

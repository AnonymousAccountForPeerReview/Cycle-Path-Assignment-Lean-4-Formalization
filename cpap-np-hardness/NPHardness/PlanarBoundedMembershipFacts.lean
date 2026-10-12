module
public import NPHardness.PlanarFoundation
public import Complexity.Planar.VerifierMain
import Lean.Elab.Tactic.Omega
@[expose] public section
namespace STACS2027.PlanarBoundedMembership
open Complexity Complexity.SAT Complexity.Planar

/-- Multiplicity one, stated in the finite index form checked by the program. -/
theorem count_le_one_iff {α : Type} [BEq α] [LawfulBEq α] (xs : List α) (a : α) :
    xs.count a ≤ 1 ↔
      ∀ i j (hi : i < xs.length) (hj : j < xs.length),
        xs[i] = a → xs[j] = a → i = j := by
  induction xs with
  | nil => simp
  | cons b xs ih =>
    by_cases hb : b = a
    · subst b
      have hz : (a :: xs).count a ≤ 1 ↔ xs.count a = 0 := by simp
      rw [hz, List.count_eq_zero]
      constructor
      · intro h i j hi hj hei hej
        cases i with
        | zero =>
          cases j with
          | zero => rfl
          | succ j => exact False.elim (h (hej ▸ List.getElem_mem (by simpa using hj)))
        | succ i => exact False.elim (h (hei ▸ List.getElem_mem (by simpa using hi)))
      · intro h hm
        obtain ⟨i, hi, he⟩ := List.getElem_of_mem hm
        have := h 0 (i+1) (by simp) (by simpa using hi) rfl he
        omega
    · have hc : (b :: xs).count a = xs.count a := by simp [hb]
      rw [hc, ih]
      constructor
      · intro h i j hi hj hei hej
        cases i with
        | zero => exact False.elim (hb hei)
        | succ i =>
          cases j with
          | zero => exact False.elim (hb hej)
          | succ j => exact congrArg Nat.succ (h i j (by simpa using hi) (by simpa using hj) hei hej)
      · intro h i j hi hj hei hej
        exact Nat.succ.inj (h (i+1) (j+1) (by simpa using hi) (by simpa using hj) hei hej)

/-- Multiplicity two, without assuming that literals or clauses are distinct. -/
theorem count_le_two_iff {α : Type} [BEq α] [LawfulBEq α] (xs : List α) (a : α) :
    xs.count a ≤ 2 ↔
      ∀ i j k (hi : i < xs.length) (hj : j < xs.length) (hk : k < xs.length),
        xs[i] = a → xs[j] = a → xs[k] = a → i = j ∨ i = k ∨ j = k := by
  induction xs with
  | nil => simp
  | cons b xs ih =>
    by_cases hb : b = a
    · subst b
      have hc : (a :: xs).count a ≤ 2 ↔ xs.count a ≤ 1 := by simp
      rw [hc, count_le_one_iff]
      constructor
      · intro h i j k hi hj hk hei hej hek
        cases i with
        | zero =>
          cases j with
          | zero => exact Or.inl rfl
          | succ j =>
            cases k with
            | zero => exact Or.inr (Or.inl rfl)
            | succ k => exact Or.inr (Or.inr (congrArg Nat.succ (h j k (by simpa using hj) (by simpa using hk) hej hek)))
        | succ i =>
          cases j with
          | zero =>
            cases k with
            | zero => exact Or.inr (Or.inr rfl)
            | succ k => exact Or.inr (Or.inl (congrArg Nat.succ (h i k (by simpa using hi) (by simpa using hk) hei hek)))
          | succ j => exact Or.inl (congrArg Nat.succ (h i j (by simpa using hi) (by simpa using hj) hei hej))
      · intro h i j hi hj hei hej
        have hh := h 0 (i+1) (j+1) (by simp) (by simpa using hi) (by simpa using hj) rfl hei hej
        omega
    · have hc : (b :: xs).count a = xs.count a := by simp [hb]
      rw [hc, ih]
      constructor
      · intro h i j k hi hj hk hei hej hek
        cases i with
        | zero => exact False.elim (hb hei)
        | succ i =>
          cases j with
          | zero => exact False.elim (hb hej)
          | succ j =>
            cases k with
            | zero => exact False.elim (hb hek)
            | succ k =>
              have hh := h i j k (by simpa using hi) (by simpa using hj) (by simpa using hk) hei hej hek
              omega
      · intro h i j k hi hj hk hei hej hek
        have hh := h (i+1) (j+1) (k+1) (by simpa using hi) (by simpa using hj) (by simpa using hk) hei hej hek
        omega

/-- The parse tables enumerate every literal occurrence in source order. -/
theorem parse_flatten {L : Nat} {xb : Nat → Option Bool} {t : ParseTables}
    (h : ParseOK L xb t) : t.fml.flatten = (List.range t.M).map t.lit := by
  have aux : ∀ n, n ≤ t.m → ((List.range n).map t.clause).flatten =
      (List.range (t.O n)).map t.lit := by
    intro n
    induction n with
    | zero => intro _; simp [h.O_zero]
    | succ n ih =>
      intro hn
      rw [List.range_succ, List.map_append, List.flatten_append, ih (by omega), h.O_succ n (by omega), List.range_add]
      simp [ParseTables.clause, List.map_map, Function.comp_def]
  simpa only [ParseTables.fml, h.O_last] using aux t.m (Nat.le_refl _)

end STACS2027.PlanarBoundedMembership

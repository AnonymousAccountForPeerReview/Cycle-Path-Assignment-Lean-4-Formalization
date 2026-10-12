module

public import NPHardness.GlobalReduction

/-!
# Sums over lists

Small bookkeeping lemmas about sums of natural numbers over lists, used to regroup
the cost of the Theorem 8 graph by variables, clauses and ports.
-/

@[expose] public section
namespace STACS2027

theorem sum_map_le_sum_map {α : Type} (l : List α) (f g : α → Nat) (h : ∀ x ∈ l, f x ≤ g x) :
    (l.map f).sum ≤ (l.map g).sum := sum_map_le l f g h

theorem sum_map_mul_right {α : Type} (l : List α) (f : α → Nat) (c : Nat) :
    (l.map fun x => f x * c).sum = (l.map f).sum * c := by
  induction l with
  | nil => simp
  | cons x l ih => simp only [List.map_cons, List.sum_cons, ih, Nat.add_mul]

theorem sum_map_mul_left {α : Type} (l : List α) (f : α → Nat) (c : Nat) :
    (l.map fun x => c * f x).sum = c * (l.map f).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp only [List.map_cons, List.sum_cons, ih, Nat.mul_add]

theorem sum_map_eq_zero {α : Type} (l : List α) (f : α → Nat) (h : ∀ x ∈ l, f x = 0) :
    (l.map f).sum = 0 := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons, h x List.mem_cons_self, Nat.zero_add]
    exact ih fun y hy => h y (List.mem_cons_of_mem x hy)

theorem sum_map_append {α : Type} (l l' : List α) (f : α → Nat) :
    ((l ++ l').map f).sum = (l.map f).sum + (l'.map f).sum := by
  simp [List.map_append, List.sum_append]

theorem sum_map_flatMap {α β : Type} (l : List α) (g : α → List β) (f : β → Nat) :
    ((l.flatMap g).map f).sum = (l.map fun x => ((g x).map f).sum).sum := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [List.flatMap_cons, sum_map_append, ih, List.map_cons, List.sum_cons]

/-- The sum over `i < n` of a function supported at `v < n`. -/
theorem sum_range_single (n v : Nat) (hv : v < n) (c : Nat) :
    ((List.range n).map fun i => if i = v then c else 0).sum = c := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    by_cases h : v < n
    · rw [ih h]
      have : n ≠ v := by omega
      simp [this]
    · have hn : v = n := by omega
      have hz : ((List.range n).map fun i => if i = v then c else 0).sum = 0 := by
        apply sum_map_eq_zero
        intro i hi
        have := List.mem_range.mp hi
        have : i ≠ v := by omega
        simp [this]
      rw [hz]
      simp [hn]

/-- Splitting a sum over `l` by the value of a key below `n`. -/
theorem sum_partition {α : Type} (l : List α) (key : α → Nat) (n : Nat)
    (hkey : ∀ x ∈ l, key x < n) (f : α → Nat) :
    ((List.range n).map fun v => ((l.filter fun x => key x == v).map f).sum).sum = (l.map f).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    have hx := hkey x List.mem_cons_self
    have ih' := ih fun y hy => hkey y (List.mem_cons_of_mem x hy)
    simp only [List.map_cons, List.sum_cons]
    rw [← ih']
    have hsplit : ((List.range n).map fun v => (((x :: l).filter fun y => key y == v).map f).sum) =
        (List.range n).map fun v => (if v = key x then f x else 0) +
          ((l.filter fun y => key y == v).map f).sum := by
      apply List.map_congr_left
      intro v _
      rw [List.filter_cons]
      by_cases h : key x = v
      · simp [h]
      · have h' : v ≠ key x := fun e => h e.symm
        simp [h, h']
    rw [hsplit, sum_map_add, sum_range_single n (key x) hx]

/-- A sum over a list as a sum over positions, through `getD`. -/
theorem sum_map_eq_sum_range_getD {α : Type} (l : List α) (d : α) (f : α → Nat) :
    (l.map f).sum = ((List.range l.length).map fun i => f (l.getD i d)).sum := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.length_cons, List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, List.sum_cons, List.getD_cons_zero, Function.comp_def,
      List.getD_cons_succ]
    rw [ih]

theorem sum_map_countP_eq_length {α : Type} (l : List α) (p : α → Bool) :
    (l.map fun x => if p x then 1 else 0).sum = l.countP p := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons, List.countP_cons, ih]
    cases p x <;> simp <;> omega

theorem sum_map_const_one {α : Type} (l : List α) : (l.map fun _ => 1).sum = l.length := by
  rw [sum_map_const]; omega

end STACS2027

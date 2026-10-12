module

public import NPHardness.BoundedSAT

/-! The exact counting bound underlying the manuscript's assertion m = O(n). -/

@[expose] public section
namespace STACS2027
open Complexity.SAT

theorem signed_partition (xs : List Literal) (v : Nat) :
    (xs.filter fun l => l.var == v).length =
      (xs.filter fun l => l.var == v && l.positive == true).length +
      (xs.filter fun l => l.var == v && l.positive == false).length := by
  induction xs with
  | nil => rfl
  | cons l xs ih =>
    cases hv : l.var == v <;> cases hp : l.positive <;>
      simp [hv, hp] at * <;> omega

theorem literal_count_bound (xs : List Literal) (n : Nat)
    (hb : ∀ l ∈ xs, l.var < n)
    (hp : ∀ v, (xs.filter fun l => l.var == v && l.positive == true).length ≤ 1)
    (hn : ∀ v, (xs.filter fun l => l.var == v && l.positive == false).length ≤ 2) :
    xs.length ≤ 3 * n := by
  induction n generalizing xs with
  | zero =>
    cases xs with
    | nil => simp
    | cons l xs => have := hb l (by simp); omega
  | succ n ih =>
    let ys := xs.filter fun l => !(l.var == n)
    have hyb : ∀ l ∈ ys, l.var < n := by
      intro l hl
      have hm := List.mem_filter.mp hl
      have hlt := hb l hm.1
      have hne : l.var ≠ n := by simpa using hm.2
      omega
    have hsub : List.Sublist ys xs := List.filter_sublist
    have hyp : ∀ v, (ys.filter fun l => l.var == v && l.positive == true).length ≤ 1 := by
      intro v
      exact Nat.le_trans (List.Sublist.length_le (hsub.filter _)) (hp v)
    have hyn : ∀ v, (ys.filter fun l => l.var == v && l.positive == false).length ≤ 2 := by
      intro v
      exact Nat.le_trans (List.Sublist.length_le (hsub.filter _)) (hn v)
    have hys := ih ys hyb hyp hyn
    have hlast : (xs.filter fun l => l.var == n).length ≤ 3 := by
      rw [signed_partition]
      have := hp n
      have := hn n
      omega
    have hpart := List.length_eq_countP_add_countP (fun l : Literal => l.var == n) (l := xs)
    simp only [List.countP_eq_length_filter] at hpart
    have he : xs.length = (xs.filter fun l => l.var == n).length + ys.length := by
      simpa [ys, Bool.beq_eq_decide_eq] using hpart
    omega

theorem BoundedOccurrence.literal_count {f : CNF} (h : BoundedOccurrence f)
    (n : Nat) (hb : ∀ c ∈ f, ∀ l ∈ c, l.var < n) :
    f.flatten.length ≤ 3 * n := by
  apply literal_count_bound
  · intro l hl
    obtain ⟨c, hc, hl⟩ := List.mem_flatten.mp hl
    exact hb c hc l hl
  · exact h.2.1
  · exact h.2.2

theorem clause_count_lower (f : CNF) (h : ∀ c ∈ f, 2 ≤ c.length) :
    2 * f.length ≤ f.flatten.length := by
  induction f with
  | nil => simp
  | cons c f ih =>
    have hc := h c (by simp)
    have hf := ih (by intro d hd; exact h d (by simp [hd]))
    simp only [List.length_cons, List.flatten_cons, List.length_append]
    omega

/-- The quantitative form of m = O(n): 2m ≤ 3n. -/
theorem BoundedOccurrence.clause_count {f : CNF} (h : BoundedOccurrence f)
    (n : Nat) (hb : ∀ c ∈ f, ∀ l ∈ c, l.var < n) :
    2 * f.length ≤ 3 * n := by
  have hlo := clause_count_lower f (by
    intro c hc
    rcases h.1 c hc with h | h <;> omega)
  exact Nat.le_trans hlo (h.literal_count n hb)

theorem BoundedOccurrence.clause_count_variableBound {f : CNF} (h : BoundedOccurrence f) :
    2 * f.length ≤ 3 * variableBound f :=
  h.clause_count _ (by intro c hc l hl; exact literal_lt_variableBound hc hl)

end STACS2027

module

public import NPHardness.FiniteCycles

/-!
The bridge between the pairwise-overlap cost and the manuscript's edge-load
objective. The support list must contain each edge once; each selected path
must also contain each edge at most once. Neither condition is implicit.
-/

@[expose] public section
namespace STACS2027

def load (ps : List (List Edge)) (e : Edge) : Nat :=
  (ps.map fun p => p.count e).sum

/-- Number of unordered pairs from an n-element set. -/
def pairCount : Nat → Nat
  | 0 => 0
  | n + 1 => pairCount n + n

theorem two_mul_pairCount (n : Nat) : 2 * pairCount n = n * (n - 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases n with
    | zero => rfl
    | succ n =>
      simp only [pairCount, Nat.mul_add] at ih ⊢
      simp only [Nat.add_sub_cancel] at ih ⊢
      simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one] at ih ⊢
      omega

theorem pairCount_eq (n : Nat) : pairCount n = n * (n - 1) / 2 := by
  have h := two_mul_pairCount n
  omega

theorem sum_map_add (xs : List α) (f g : α → Nat) :
    (xs.map fun x => f x + g x).sum = (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih]; omega

@[simp]
theorem sum_map_zero (xs : List α) : (xs.map fun _ => (0 : Nat)).sum = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

theorem sum_map_const (xs : List α) (n : Nat) :
    (xs.map fun _ => n).sum = xs.length * n := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, Nat.add_mul, Nat.add_comm]

theorem sum_map_swap (xs : List α) (ys : List β) (f : α → β → Nat) :
    (xs.map fun x => (ys.map (f x)).sum).sum =
      (ys.map fun y => (xs.map fun x => f x y).sum).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, sum_map_add, ih]

theorem load_cons (p : List Edge) (ps : List (List Edge)) (e : Edge) :
    load (p :: ps) e = p.count e + load ps e := by simp [load]

theorem overlap_family (p : List Edge) (ps : List (List Edge)) :
    (ps.map (overlap p)).sum = (p.map (load ps)).sum := by
  exact sum_map_swap ps p (fun q e => q.count e)

theorem sum_indicator (es : List Edge) (a : Edge) (f : Edge → Nat) :
    (es.map fun e => if a = e then f e else 0).sum = es.count a * f a := by
  induction es with
  | nil => simp
  | cons e es ih =>
    by_cases h : a = e
    · subst e; simp [ih, Nat.add_mul, Nat.add_comm]
    · have h' : e ≠ a := Ne.symm h
      simp [ih, h, h']

theorem sum_counts (es p : List Edge) (f : Edge → Nat)
    (he : es.Nodup) (hp : ∀ e ∈ p, e ∈ es) :
    (es.map fun e => p.count e * f e).sum = (p.map f).sum := by
  induction p with
  | nil => simp
  | cons a p ih =>
    have ha : a ∈ es := hp a (by simp)
    have ht : ∀ e ∈ p, e ∈ es := fun e h => hp e (by simp [h])
    have hc : ∀ e : Edge, (a :: p).count e * f e =
        p.count e * f e + (if a = e then f e else 0) := by
      intro e
      by_cases h : a = e <;> simp [h, Nat.add_mul]
    simp only [hc, sum_map_add, sum_indicator, he.count_of_mem ha, Nat.one_mul,
      ih ht, List.map_cons, List.sum_cons]
    omega

theorem pairCount_add_bit (n b : Nat) (hb : b ≤ 1) :
    pairCount (b + n) = pairCount n + b * n := by
  have : b = 0 ∨ b = 1 := by omega
  rcases this with rfl | rfl
  · simp
  · rw [Nat.add_comm 1 n]; simp [pairCount]

/-- Exact double-counting identity, with all representation assumptions explicit. -/
theorem cost_eq_load_sum (es : List Edge) (ps : List (List Edge))
    (he : es.Nodup) (hn : ∀ p ∈ ps, p.Nodup)
    (hs : ∀ p ∈ ps, ∀ e ∈ p, e ∈ es) :
    cost ps = (es.map fun e => pairCount (load ps e)).sum := by
  induction ps with
  | nil => simp [cost, load, pairCount]
  | cons p ps ih =>
    have hp : p.Nodup := hn p (by simp)
    have ht : ∀ q ∈ ps, q.Nodup := fun q h => hn q (by simp [h])
    have hsp : ∀ e ∈ p, e ∈ es := hs p (by simp)
    have hst : ∀ q ∈ ps, ∀ e ∈ q, e ∈ es := fun q h => hs q (by simp [h])
    have step : ∀ e : Edge, pairCount (load (p :: ps) e) =
        pairCount (load ps e) + p.count e * load ps e := by
      intro e
      rw [load_cons]
      exact pairCount_add_bit _ _ (List.nodup_iff_count.mp hp e)
    simp only [step, sum_map_add, cost, overlap_family, ih ht hst,
      sum_counts es p (load ps) he hsp]
    omega

theorem cost_eq_binomial_sum (es : List Edge) (ps : List (List Edge))
    (he : es.Nodup) (hn : ∀ p ∈ ps, p.Nodup)
    (hs : ∀ p ∈ ps, ∀ e ∈ p, e ∈ es) :
    cost ps = (es.map fun e => load ps e * (load ps e - 1) / 2).sum := by
  simpa only [pairCount_eq] using cost_eq_load_sum es ps he hn hs

end STACS2027

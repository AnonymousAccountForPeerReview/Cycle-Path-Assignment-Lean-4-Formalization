module

public import Approximation.Arithmetic

/-!
Edge loads of a family of paths: the load-sum of a path, the total load
`∑_e l(e) = (k − 2) t` of an assignment, and the identity
`∑_e l(e)² = 2 c(τ) + ∑_e l(e)` relating the sum of squared loads to the cost.
-/

@[expose] public section
namespace STACS2027

/-- The load-sum `∑_{e ∈ p} l(e)` of the path `p` under the loads of the paths `ps`: the cost
increase caused by adding `p` to `ps`. -/
def pathLoad (ps : List (List Edge)) (p : List Edge) : Nat :=
  (p.map (load ps)).sum

theorem pathLoad_eq_overlap_sum (ps : List (List Edge)) (p : List Edge) :
    pathLoad ps p = (ps.map (overlap p)).sum :=
  (overlap_family p ps).symm

/-- Adding a path increases the cost by its load-sum. -/
theorem cost_snoc_pathLoad (ps : List (List Edge)) (p : List Edge) :
    cost (ps ++ [p]) = cost ps + pathLoad ps p := by
  rw [cost_snoc, pathLoad_eq_overlap_sum]; omega

theorem load_append (ps qs : List (List Edge)) (e : Edge) :
    load (ps ++ qs) e = load ps e + load qs e := by
  simp [load]

theorem load_le_load_append (ps qs : List (List Edge)) (e : Edge) :
    load ps e ≤ load (ps ++ qs) e := by
  rw [load_append]; exact Nat.le_add_right _ _

theorem pathLoad_le_pathLoad_append (ps qs : List (List Edge)) (p : List Edge) :
    pathLoad ps p ≤ pathLoad (ps ++ qs) p :=
  sum_map_le p _ _ (fun e _ => load_le_load_append ps qs e)

/-- The load-sums of the paths `qs` under `ps`, summed, equal `∑_e l_ps(e) l_qs(e)` over any
duplicate-free edge list containing the edges of `qs`. -/
theorem sum_pathLoad_eq {es : List Edge} (he : es.Nodup) (ps qs : List (List Edge))
    (hs : ∀ q ∈ qs, ∀ e ∈ q, e ∈ es) :
    (qs.map (pathLoad ps)).sum = (es.map fun e => load qs e * load ps e).sum := by
  induction qs with
  | nil => simp [load]
  | cons q qs ih =>
    have hq : ∀ e ∈ q, e ∈ es := hs q (by simp)
    have ht : ∀ r ∈ qs, ∀ e ∈ r, e ∈ es := fun r hr => hs r (by simp [hr])
    simp only [List.map_cons, List.sum_cons, ih ht, load_cons, Nat.add_mul, sum_map_add]
    rw [sum_counts es q (load ps) he hq]
    rfl

/-- The total load of a family of paths is the total number of their edges. -/
theorem sum_load_eq_length {es : List Edge} (he : es.Nodup) (ps : List (List Edge))
    (hs : ∀ p ∈ ps, ∀ e ∈ p, e ∈ es) :
    (es.map (load ps)).sum = (ps.map List.length).sum := by
  induction ps with
  | nil => exact sum_map_eq_zero es _ (fun e _ => by simp [load])
  | cons p ps ih =>
    have hp : ∀ e ∈ p, e ∈ es := hs p (by simp)
    have ht : ∀ r ∈ ps, ∀ e ∈ r, e ∈ es := fun r hr => hs r (by simp [hr])
    have hsplit : (es.map (load (p :: ps))).sum =
        (es.map fun e => p.count e * 1).sum + (es.map (load ps)).sum := by
      rw [← sum_map_add]
      exact sum_map_congr es _ _ (fun e _ => by rw [load_cons, Nat.mul_one])
    rw [hsplit, ih ht, sum_counts es p (fun _ => 1) he hp, sum_map_const]
    simp

/-- Every assignment of `t` paths of `k − 2` edges has total load `(k − 2) t`. -/
theorem total_load {es : List Edge} (he : es.Nodup) {ps : List (List Edge)} {L : Nat}
    (hl : ∀ p ∈ ps, p.length = L) (hs : ∀ p ∈ ps, ∀ e ∈ p, e ∈ es) :
    (es.map (load ps)).sum = L * ps.length := by
  rw [sum_load_eq_length he ps hs, sum_map_congr ps List.length (fun _ => L) hl, sum_map_const]
  exact Nat.mul_comm _ _

/-- `∑_e l(e)² = 2 c(τ) + ∑_e l(e)`, from `c(τ) = ∑_e binom(l(e), 2)`. -/
theorem sum_sq_load {es : List Edge} (he : es.Nodup) (ps : List (List Edge))
    (hn : ∀ p ∈ ps, p.Nodup) (hs : ∀ p ∈ ps, ∀ e ∈ p, e ∈ es) :
    (es.map fun e => load ps e * load ps e).sum = 2 * cost ps + (es.map (load ps)).sum := by
  rw [cost_eq_load_sum es ps he hn hs, ← sum_map_mul_left, ← sum_map_add]
  exact sum_map_congr es _ _ (fun e _ => (two_pairCount_add _).symm)

/-- The sum of squared loads of an assignment of `t` paths of `k − 2` edges is `2 c(τ) + (k − 2) t`. -/
theorem sum_sq_load_assignment {es : List Edge} (he : es.Nodup) {ps : List (List Edge)} {L : Nat}
    (hn : ∀ p ∈ ps, p.Nodup) (hl : ∀ p ∈ ps, p.length = L) (hs : ∀ p ∈ ps, ∀ e ∈ p, e ∈ es) :
    (es.map fun e => load ps e * load ps e).sum = 2 * cost ps + L * ps.length := by
  rw [sum_sq_load he ps hn hs, total_load he hl hs]

end STACS2027

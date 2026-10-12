module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Approximation.Theorems
import Mathlib.Tactic

/-!
# Lemma 16: the instance of the relaxation

The convex relaxation of Section 7.2 on an abstract instance: `t` cycles `c ∈ [t]`, `k` options `j ∈ [k]` per cycle, edges `Fin m`; option `j` of cycle
`c` is the edge list `opt c j` (`P_{c,j}`; in a valid instance duplicate-free with `k − 2` edges).

* `cnt c j e` (the multiplicity of `e` in `P_{c,j}`) and the overlap matrix
  `H (c,j) (c',j') = ∑_e cnt c j e · cnt c' j' e`.
* Over any commutative semiring: the loads `lam x e = λ(x)_e = ∑_{c,j} cnt c j e · x_{c,j}`, the
  path loads `L x c j = ∑_e cnt c j e · λ(x)_e` (`= (H x)_{c,j}`, `L_eq_H`) and the pairing
  `inner`. Over a linearly ordered commutative ring: `pi x c = min_j L x c j` and the Frank–Wolfe
  gap `gap x = ∑_{c,j} x_{c,j} (L x c j − pi x c)`.
* Over `ℝ`: `F x = ½ ∑_e λ_e²`, the manuscript's objective `Phi x = ∑_e (λ_e² − λ_e)/2`, the
  polytope `InX` (`x ≥ 0`, `∑_j x_{c,j} = 1`) and the Frank–Wolfe vertex `vtx x` (in each cycle
  the least `j` with `L x c j = pi x c`).
* The constants used by the exact rounding: `dimKKT t k = (k+1)t`, `entryBound k = k − 2`,
  `bigE t k = 2(d²+1)·d!·A₀^{d+1}`, `eps t k = 1/E`; and `curv t k = C₀ = 2(k−2)t²`,
  `Phi0 t k = ½(k−2)²t²`.
* **The bridge to Section 7** (`relaxationObjective_eq_Phi`, `optimalFractional_of_min`): for the
  option lists `opts` of the cycles over the edge list `es` (`ofOpts es k opts`) and a list `R` of
  weighted options with `R.map Prod.fst = opts`, `relaxationObjective D R es = 2 D² Φ(W/D)` with
  `W = weightsOf R`; hence a minimizer `W/D` of `Φ` over `InX` gives
  `OptimalFractional es D (opts.zip (wlists W))`. For the enumerated cycles of a graph the
  instance is valid (`ofOpts_valid_cycles`).
-/

@[expose] public section

namespace STACS2027.Runtimes.ConvexQP

open Finset

/-- An instance of the relaxation: `t` cycles with `k` options each over the edges `Fin m`;
option `j` of cycle `c` is the edge list `opt c j`. -/
structure Inst where
  /-- The number of cycles. -/
  t : ℕ
  /-- The number of options per cycle (the cycle length). -/
  k : ℕ
  /-- The number of edges. -/
  m : ℕ
  /-- The options: `opt c j` is the path `P_{c,j}`. -/
  opt : Fin t → Fin k → List (Fin m)

namespace Inst

variable (I : Inst)

/-- A valid instance: `k ≥ 3`, every option duplicate-free with `k − 2` edges. -/
def Valid : Prop :=
  3 ≤ I.k ∧ ∀ c j, (I.opt c j).Nodup ∧ (I.opt c j).length = I.k - 2

/-- The multiplicity of the edge `e` in the option `P_{c,j}`. -/
def cnt (c : Fin I.t) (j : Fin I.k) (e : Fin I.m) : ℕ := (I.opt c j).count e

/-- The overlap matrix `H_{(c,j),(c',j')} = |P_{c,j} ∩ P_{c',j'}|` (with multiplicities). -/
def H (c : Fin I.t) (j : Fin I.k) (c' : Fin I.t) (j' : Fin I.k) : ℕ :=
  ∑ e, I.cnt c j e * I.cnt c' j' e

section Semiring

variable {R : Type*} [CommSemiring R]

/-- The loads `λ(x)_e = ∑_{(c,j)} cnt c j e · x_{c,j}`. -/
def lam (x : Fin I.t → Fin I.k → R) (e : Fin I.m) : R :=
  ∑ c, ∑ j, (I.cnt c j e : R) * x c j

/-- The path loads `L(x)_{c,j} = ∑_{e ∈ P_{c,j}} λ(x)_e` (the gradient of `F`). -/
def L (x : Fin I.t → Fin I.k → R) (c : Fin I.t) (j : Fin I.k) : R :=
  ∑ e, (I.cnt c j e : R) * I.lam x e

/-- The pairing `⟨u, w⟩ = ∑_{(c,j)} u_{c,j} w_{c,j}`. -/
def inner (u w : Fin I.t → Fin I.k → R) : R := ∑ c, ∑ j, u c j * w c j

theorem L_eq_H (x : Fin I.t → Fin I.k → R) (c : Fin I.t) (j : Fin I.k) :
    I.L x c j = ∑ c', ∑ j', (I.H c j c' j' : R) * x c' j' := by
  simp only [L, lam, H, Nat.cast_sum, Nat.cast_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c' _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j' _ => ?_
  refine Finset.sum_congr rfl fun e _ => ?_
  ring

/-- Ring homomorphisms commute with the loads. -/
theorem lam_map {S : Type*} [CommSemiring S] (f : R →+* S) (x : Fin I.t → Fin I.k → R)
    (e : Fin I.m) : I.lam (fun c j => f (x c j)) e = f (I.lam x e) := by
  simp [lam, map_sum, map_mul, map_natCast]

/-- Ring homomorphisms commute with the path loads. -/
theorem L_map {S : Type*} [CommSemiring S] (f : R →+* S) (x : Fin I.t → Fin I.k → R)
    (c : Fin I.t) (j : Fin I.k) : I.L (fun c j => f (x c j)) c j = f (I.L x c j) := by
  simp [L, lam_map, map_sum, map_mul, map_natCast]

theorem lam_add (x y : Fin I.t → Fin I.k → R) (e : Fin I.m) :
    I.lam (fun c j => x c j + y c j) e = I.lam x e + I.lam y e := by
  simp only [lam, mul_add, Finset.sum_add_distrib]

theorem lam_smul (a : R) (x : Fin I.t → Fin I.k → R) (e : Fin I.m) :
    I.lam (fun c j => a * x c j) e = a * I.lam x e := by
  simp only [lam, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem L_add (x y : Fin I.t → Fin I.k → R) (c : Fin I.t) (j : Fin I.k) :
    I.L (fun c j => x c j + y c j) c j = I.L x c j + I.L y c j := by
  simp only [L, lam_add, mul_add, Finset.sum_add_distrib]

theorem L_smul (a : R) (x : Fin I.t → Fin I.k → R) (c : Fin I.t) (j : Fin I.k) :
    I.L (fun c j => a * x c j) c j = a * I.L x c j := by
  simp only [L, lam_smul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  ring

end Semiring

section Ring

variable {R : Type*} [CommRing R]

theorem lam_sub (x y : Fin I.t → Fin I.k → R) (e : Fin I.m) :
    I.lam (fun c j => x c j - y c j) e = I.lam x e - I.lam y e := by
  simp only [lam, mul_sub, Finset.sum_sub_distrib]

theorem L_sub (x y : Fin I.t → Fin I.k → R) (c : Fin I.t) (j : Fin I.k) :
    I.L (fun c j => x c j - y c j) c j = I.L x c j - I.L y c j := by
  simp only [L, lam_sub, mul_sub, Finset.sum_sub_distrib]

variable [LinearOrder R]

/-- `π(x)_c = min_j L(x)_{c,j}` (`0` if `k = 0`). -/
def pi (x : Fin I.t → Fin I.k → R) (c : Fin I.t) : R :=
  if h : 0 < I.k then Finset.univ.inf' ⟨⟨0, h⟩, Finset.mem_univ _⟩ (I.L x c) else 0

/-- The Frank–Wolfe duality gap `gap(x) = ∑_{(c,j)} x_{c,j} (L(x)_{c,j} − π(x)_c)`. -/
def gap (x : Fin I.t → Fin I.k → R) : R :=
  ∑ c, ∑ j, x c j * (I.L x c j - I.pi x c)

theorem pi_le (x : Fin I.t → Fin I.k → R) (c : Fin I.t) (j : Fin I.k) :
    I.pi x c ≤ I.L x c j := by
  have h : 0 < I.k := Nat.lt_of_le_of_lt (Nat.zero_le _) j.2
  simp only [pi, h, ↓reduceDIte]
  exact Finset.inf'_le _ (Finset.mem_univ j)

theorem exists_L_eq_pi (x : Fin I.t → Fin I.k → R) (c : Fin I.t) (hk : 0 < I.k) :
    ∃ j, I.L x c j = I.pi x c := by
  simp only [pi, hk, ↓reduceDIte]
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_inf' ⟨⟨0, hk⟩, Finset.mem_univ _⟩ (I.L x c)
  exact ⟨j, hj.symm⟩

/-- `π` is characterized as the attained lower bound of the path loads of the cycle. -/
theorem pi_eq_of (x : Fin I.t → Fin I.k → R) (c : Fin I.t) {a : R}
    (hle : ∀ j, a ≤ I.L x c j) (hex : ∃ j, I.L x c j = a) : I.pi x c = a := by
  obtain ⟨j, hj⟩ := hex
  obtain ⟨j', hj'⟩ := I.exists_L_eq_pi x c (Nat.lt_of_le_of_lt (Nat.zero_le _) j.2)
  apply le_antisymm
  · rw [← hj]; exact I.pi_le x c j
  · rw [← hj']; exact hle j'

end Ring

/-- `F(x) = ½ ∑_e λ(x)_e²`. -/
noncomputable def F (x : Fin I.t → Fin I.k → ℝ) : ℝ := (∑ e, I.lam x e ^ 2) / 2

/-- The manuscript's objective `Φ(x) = ∑_e (λ(x)_e² − λ(x)_e)/2`. -/
noncomputable def Phi (x : Fin I.t → Fin I.k → ℝ) : ℝ := ∑ e, (I.lam x e ^ 2 - I.lam x e) / 2

/-- The feasible polytope `𝒳`: `x ≥ 0` and `∑_j x_{c,j} = 1` for every cycle. -/
def InX (x : Fin I.t → Fin I.k → ℝ) : Prop :=
  (∀ c j, 0 ≤ x c j) ∧ ∀ c, ∑ j, x c j = 1

/-- The Frank–Wolfe vertex `v(x)`: in each cycle, weight `1` on the least `j` with
`L(x)_{c,j} = π(x)_c`. -/
noncomputable def vtx (x : Fin I.t → Fin I.k → ℝ) (c : Fin I.t) (j : Fin I.k) : ℝ :=
  if I.L x c j = I.pi x c ∧ ∀ j' : Fin I.k, j' < j → I.L x c j' ≠ I.pi x c then 1 else 0

/-! ### Integer data and their real values -/

/-- Casting integer data to `ℝ` commutes with the path loads. -/
theorem L_intCast (x : Fin I.t → Fin I.k → ℤ) (c : Fin I.t) (j : Fin I.k) :
    I.L (fun c j => (x c j : ℝ)) c j = ((I.L x c j : ℤ) : ℝ) :=
  I.L_map (Int.castRingHom ℝ) x c j

theorem lam_intCast (x : Fin I.t → Fin I.k → ℤ) (e : Fin I.m) :
    I.lam (fun c j => (x c j : ℝ)) e = ((I.lam x e : ℤ) : ℝ) :=
  I.lam_map (Int.castRingHom ℝ) x e

/-- Scaling integer data by `1/q` (`q > 0`) scales `L` and `π`. -/
theorem L_div (x : Fin I.t → Fin I.k → ℤ) (q : ℝ) (c : Fin I.t) (j : Fin I.k) :
    I.L (fun c j => (x c j : ℝ) / q) c j = ((I.L x c j : ℤ) : ℝ) / q := by
  have h := I.L_smul (q⁻¹) (fun c j => (x c j : ℝ)) c j
  simp only [L_intCast] at h
  simpa [div_eq_inv_mul] using h

theorem lam_div (x : Fin I.t → Fin I.k → ℤ) (q : ℝ) (e : Fin I.m) :
    I.lam (fun c j => (x c j : ℝ) / q) e = ((I.lam x e : ℤ) : ℝ) / q := by
  have h := I.lam_smul (q⁻¹) (fun c j => (x c j : ℝ)) e
  simp only [lam_intCast] at h
  simpa [div_eq_inv_mul] using h

theorem pi_div (x : Fin I.t → Fin I.k → ℤ) {q : ℝ} (hq : 0 < q) (c : Fin I.t) :
    I.pi (fun c j => (x c j : ℝ) / q) c = ((I.pi x c : ℤ) : ℝ) / q := by
  rcases Nat.eq_zero_or_pos I.k with hk | hk
  · simp [pi, hk]
  · apply I.pi_eq_of
    · intro j
      rw [I.L_div]
      exact div_le_div_of_nonneg_right (by exact_mod_cast I.pi_le x c j) hq.le
    · obtain ⟨j, hj⟩ := I.exists_L_eq_pi x c hk
      exact ⟨j, by rw [I.L_div, hj]⟩

theorem gap_div (x : Fin I.t → Fin I.k → ℤ) {q : ℝ} (hq : 0 < q) :
    I.gap (fun c j => (x c j : ℝ) / q) = ((I.gap x : ℤ) : ℝ) / q ^ 2 := by
  simp only [gap, I.L_div, I.pi_div x hq, Int.cast_sum, Int.cast_mul, Int.cast_sub,
    Finset.sum_div]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun j _ => ?_
  field_simp

/-! ### Multiplicities in a valid instance -/

theorem sum_count_fin {m : ℕ} (l : List (Fin m)) : ∑ e, l.count e = l.length := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.count_cons, Finset.sum_add_distrib, ih]

theorem sum_cnt (c : Fin I.t) (j : Fin I.k) : ∑ e, I.cnt c j e = (I.opt c j).length :=
  sum_count_fin _

theorem cnt_le_one {I : Inst} (hI : I.Valid) (c : Fin I.t) (j : Fin I.k) (e : Fin I.m) :
    I.cnt c j e ≤ 1 :=
  List.nodup_iff_count_le_one.mp (hI.2 c j).1 e

theorem sum_cnt_valid {I : Inst} (hI : I.Valid) (c : Fin I.t) (j : Fin I.k) :
    ∑ e, I.cnt c j e = I.k - 2 := by
  rw [I.sum_cnt, (hI.2 c j).2]

/-- The overlaps are at most `k − 2`. -/
theorem H_le {I : Inst} (hI : I.Valid) (c : Fin I.t) (j : Fin I.k) (c' : Fin I.t) (j' : Fin I.k) :
    I.H c j c' j' ≤ I.k - 2 := by
  rw [← sum_cnt_valid hI c j]
  unfold H
  exact Finset.sum_le_sum fun e _ =>
    (Nat.mul_le_mul_left _ (cnt_le_one hI c' j' e)).trans (Nat.mul_one _).le

end Inst

/-! ### Constants -/

/-- `d = (k + 1) t`: the number of variables `(x, π)` of the KKT system. -/
def dimKKT (t k : ℕ) : ℕ := (k + 1) * t

/-- `A₀ = k − 2`: the bound on the entries of the KKT matrix. -/
def entryBound (k : ℕ) : ℕ := k - 2

/-- `E = 2 (d² + 1) d! A₀^{d+1}`. -/
def bigE (t k : ℕ) : ℕ :=
  2 * (dimKKT t k ^ 2 + 1) * (dimKKT t k).factorial * entryBound k ^ (dimKKT t k + 1)

/-- `ε = 1/E`; Phase E must deliver a feasible point with `gap ≤ ε²` (`g₀`). -/
noncomputable def eps (t k : ℕ) : ℝ := 1 / (bigE t k : ℝ)

/-- `C₀ = 2 (k − 2) t²`: the curvature bound (Lemma A2(c)). -/
def curv (t k : ℕ) : ℕ := 2 * (k - 2) * t ^ 2

/-- `Φ₀ = ½ (k − 2)² t²`: the range of `F` on `𝒳` (Lemma A2(b)). -/
noncomputable def Phi0 (t k : ℕ) : ℝ := ((k - 2 : ℕ) : ℝ) ^ 2 * (t : ℝ) ^ 2 / 2

theorem entryBound_pos {k : ℕ} (hk : 3 ≤ k) : 0 < entryBound k := by
  unfold entryBound; omega

theorem bigE_pos (t : ℕ) {k : ℕ} (hk : 3 ≤ k) : 0 < bigE t k := by
  unfold bigE
  have := entryBound_pos hk
  positivity

theorem eps_pos (t : ℕ) {k : ℕ} (hk : 3 ≤ k) : 0 < eps t k := by
  unfold eps
  have : (0 : ℝ) < bigE t k := by exact_mod_cast bigE_pos t hk
  positivity

/-! ### The interface between Phase E and the exact rounding -/

/-- The real point `Xs / q` of integer data `Xs` with denominator `q`. -/
noncomputable def ptOf {I : Inst} (Xs : Fin I.t → Fin I.k → ℤ) (q : ℕ) :
    Fin I.t → Fin I.k → ℝ :=
  fun c j => (Xs c j : ℝ) / q

/-- **What Phase E (Part B, Theorem B10) must provide.** A procedure returning, on every valid
instance with at least one cycle, integer data `Xs` and a denominator `q > 0` such that
`x̂ = Xs/q` lies in `𝒳` and has Frank–Wolfe gap at most `ε² = g₀`. The exact rounding
(`Exact.lean`) turns such a point into an exact optimum. -/
def PhaseESpec (phaseE : (I : Inst) → Option ((Fin I.t → Fin I.k → ℤ) × ℕ)) : Prop :=
  ∀ I : Inst, I.Valid → 0 < I.t → ∃ Xs q, phaseE I = some (Xs, q) ∧ 0 < q ∧
    I.InX (ptOf Xs q) ∧ I.gap (ptOf Xs q) ≤ eps I.t I.k ^ 2

/-! ### The bridge to Section 7's option lists -/

/-- Option `j` of cycle `c` in the option lists `opts` (`[]` out of range). -/
def path (opts : List (List (List Edge))) (c j : ℕ) : List Edge := (opts.getD c []).getD j []

/-- The instance of the option lists `opts` (`k` options per cycle) over the edge list `es`: edge
`i` is `es[i]`, and option `j` of cycle `c` lists the indices of the edges of `es` on the path
`path opts c j`. Edges of the paths outside `es` are ignored, as in `relaxationObjective`. -/
abbrev ofOpts (es : List Edge) (k : ℕ) (opts : List (List (List Edge))) : Inst where
  t := opts.length
  k := k
  m := es.length
  opt c j := (List.finRange es.length).filter fun i => decide (es[(i : ℕ)] ∈ path opts c j)

/-- The weight of option `j` of cycle `c` in a list of weighted options (`0` out of range). -/
def weightsOf (R : List (List (List Edge) × List ℕ)) (c j : ℕ) : ℕ :=
  ((R.getD c ([], [])).2).getD j 0

/-- The weight lists of a weight matrix, cycle by cycle. -/
def wlists {t k : ℕ} (W : Fin t → Fin k → ℕ) : List (List ℕ) :=
  List.ofFn fun c => List.ofFn (W c)

theorem getD_of_lt {α : Type*} (l : List α) (d : α) {i : ℕ} (h : i < l.length) :
    l.getD i d = l[i] :=
  (List.getElem_eq_getD d).symm

/-- A weighted sum over `k` options as a sum over `Fin k`. -/
theorem weightedSum_eq_sum (f : List Edge → ℕ) :
    ∀ (o : List (List Edge)) (w : List ℕ) (k : ℕ), o.length = k →
      weightedSum f o w = ∑ j : Fin k, w.getD j 0 * f (o.getD j [])
  | [], w, k, hk => by subst hk; simp [weightedSum_nil_left]
  | p :: ps, w, k, hk => by
    obtain rfl : k = ps.length + 1 := by simp at hk; omega
    rw [Fin.sum_univ_succ]
    cases w with
    | nil => simp [weightedSum_nil_right]
    | cons c cs =>
      rw [weightedSum_cons, weightedSum_eq_sum f ps cs ps.length rfl]
      simp

theorem sum_getD_eq_sum (w : List ℕ) {k : ℕ} (hw : w.length = k) :
    ∑ j : Fin k, w.getD j 0 = w.sum := by
  subst hw
  rw [← List.sum_ofFn]
  congr 1
  apply List.ext_getElem
  · simp
  · intro n _ _
    simp only [List.getElem_ofFn]
    rw [getD_of_lt]

/-- `D λ_e` of Section 7 as a double sum over cycles and options. -/
theorem fractionalLoad_eq_sum {k : ℕ} :
    ∀ (R : List (List (List Edge) × List ℕ)) (n : ℕ), R.length = n →
      (∀ r ∈ R, r.1.length = k) → ∀ e : Edge,
      fractionalLoad R e =
        ∑ c : Fin n, ∑ j : Fin k, weightsOf R c j * (path (R.map Prod.fst) c j).count e
  | [], n, hn, _, e => by subst hn; simp [fractionalLoad]
  | r :: R, n, hn, hk, e => by
    obtain rfl : n = R.length + 1 := by simp at hn; omega
    rw [fractionalLoad_cons, Fin.sum_univ_succ,
      fractionalLoad_eq_sum R R.length rfl (fun r' hr' => hk r' (by simp [hr'])) e]
    congr 1
    simp only [optionLoad]
    rw [weightedSum_eq_sum _ r.1 r.2 k (hk r (by simp))]
    simp [weightsOf, path]

theorem path_mem {opts : List (List (List Edge))} {c j : ℕ} (hc : c < opts.length)
    (hj : j < (opts[c]).length) : path opts c j ∈ opts[c] := by
  unfold path
  rw [getD_of_lt _ _ hc, getD_of_lt _ _ hj]
  exact List.getElem_mem hj

theorem cnt_ofOpts (es : List Edge) (k : ℕ) (opts : List (List (List Edge)))
    (c : Fin opts.length) (j : Fin k) (i : Fin es.length) (hp : (path opts c j).Nodup) :
    (ofOpts es k opts).cnt c j i = (path opts c j).count es[(i : ℕ)] := by
  change ((List.finRange es.length).filter fun i : Fin es.length =>
    decide (es[(i : ℕ)] ∈ path opts c j)).count i = _
  by_cases h : es[(i : ℕ)] ∈ path opts c j
  · rw [List.count_filter (by simpa using h), List.count_finRange, List.count_eq_one_of_mem hp h]
  · rw [List.count_eq_zero_of_not_mem (by simp [h]), List.count_eq_zero_of_not_mem h]

/-- `D λ_e = λ(W)_e`: Section 7's fractional load of the edge `es[i]` is the load of the weights. -/
theorem fractionalLoad_get {es : List Edge} {k : ℕ} {opts : List (List (List Edge))}
    (hk : ∀ o ∈ opts, o.length = k ∧ ∀ p ∈ o, p.Nodup)
    {R : List (List (List Edge) × List ℕ)} (hR : R.map Prod.fst = opts) (i : Fin es.length) :
    fractionalLoad R es[(i : ℕ)] = (ofOpts es k opts).lam (fun c j => weightsOf R c j) i := by
  have hlen : R.length = opts.length := by rw [← hR, List.length_map]
  rw [fractionalLoad_eq_sum R opts.length hlen
    (fun r hr => (hk r.1 (hR ▸ List.mem_map_of_mem hr)).1) es[(i : ℕ)], hR]
  unfold Inst.lam
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun j _ => ?_
  have hp : (path opts c j).Nodup := by
    have hc := (hk _ (List.getElem_mem c.2))
    exact hc.2 _ (path_mem c.2 (by rw [hc.1]; exact j.2))
  rw [cnt_ofOpts es k opts c j i hp, Nat.cast_id, Nat.mul_comm]

/-- **Bridge.** Section 7's scaled objective is `2 D²` times `Φ` at the weights over `D`. -/
theorem relaxationObjective_eq_Phi {es : List Edge} {k : ℕ} {opts : List (List (List Edge))}
    (hk : ∀ o ∈ opts, o.length = k ∧ ∀ p ∈ o, p.Nodup) {D : ℕ} (hD : 0 < D)
    {R : List (List (List Edge) × List ℕ)} (hR : R.map Prod.fst = opts) :
    (relaxationObjective D R es : ℝ) =
      2 * (D : ℝ) ^ 2 * (ofOpts es k opts).Phi (fun c j => (weightsOf R c j : ℝ) / D) := by
  have hD' : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have hlam : ∀ i : Fin es.length,
      (ofOpts es k opts).lam (fun c j => (weightsOf R c j : ℝ) / D) i =
        (fractionalLoad R es[(i : ℕ)] : ℝ) / D := by
    intro i
    have h1 := (ofOpts es k opts).lam_smul ((D : ℝ)⁻¹)
      (fun c j => (weightsOf R c j : ℝ)) i
    have h2 := (ofOpts es k opts).lam_map (Nat.castRingHom ℝ) (fun c j => weightsOf R c j) i
    simp only [Nat.coe_castRingHom] at h2
    rw [fractionalLoad_get hk hR i]
    simp only [div_eq_inv_mul]
    rw [h1, h2]
  unfold relaxationObjective Inst.Phi
  rw [← Fin.sum_univ_fun_getElem es]
  push_cast
  simp only [hlam]
  change ∑ i : Fin es.length, _ = 2 * (D : ℝ) ^ 2 * ∑ i : Fin es.length, _
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  field_simp

theorem weightsOf_zip {opts : List (List (List Edge))} {k : ℕ} (W : Fin opts.length → Fin k → ℕ)
    (c : Fin opts.length) (j : Fin k) : weightsOf (opts.zip (wlists W)) c j = W c j := by
  unfold weightsOf wlists
  rw [getD_of_lt (opts.zip _) _ (by simp)]
  simp only [List.getElem_zip, List.getElem_ofFn]
  rw [getD_of_lt _ _ (by simp)]
  simp

theorem map_fst_zip_wlists (opts : List (List (List Edge))) {k : ℕ}
    (W : Fin opts.length → Fin k → ℕ) : (opts.zip (wlists W)).map Prod.fst = opts :=
  List.map_fst_zip (by simp [wlists])

/-- **Bridge.** If `W/D` minimizes `Φ` over `𝒳` (with `∑_j W_{c,j} = D`), then
`opts.zip (wlists W)` with denominator `D` is an optimal fractional solution in Section 7's
sense. -/
theorem optimalFractional_of_min {es : List Edge} {k : ℕ} {opts : List (List (List Edge))}
    (hk : ∀ o ∈ opts, o.length = k ∧ ∀ p ∈ o, p.Nodup) {D : ℕ} (hD : 0 < D)
    (W : Fin opts.length → Fin k → ℕ) (hW : ∀ c, ∑ j, W c j = D)
    (hmin : ∀ x, (ofOpts es k opts).InX x →
      (ofOpts es k opts).Phi (fun c j => (W c j : ℝ) / D) ≤ (ofOpts es k opts).Phi x) :
    OptimalFractional es D (opts.zip (wlists W)) := by
  set R := opts.zip (wlists W) with hRdef
  have hRfst : R.map Prod.fst = opts := map_fst_zip_wlists opts W
  refine ⟨⟨hD, ?_⟩, ?_⟩
  · intro r hr
    obtain ⟨c, hc, rfl⟩ := List.getElem_of_mem hr
    have hc' : c < opts.length := by simpa [R, wlists] using hc
    simp only [R, List.getElem_zip, wlists, List.getElem_ofFn, List.length_ofFn,
      List.sum_ofFn]
    exact ⟨(hk _ (List.getElem_mem hc')).1.symm, hW ⟨c, hc'⟩⟩
  · intro D' R' hf' hR'
    rw [hRfst] at hR'
    have hD'pos := hf'.1
    have hlen : R'.length = opts.length := by rw [← hR', List.length_map]
    -- the competitor as a point of `𝒳`
    have hX : (ofOpts es k opts).InX (fun c j => (weightsOf R' c j : ℝ) / D') := by
      refine ⟨fun c j => by positivity, fun c => ?_⟩
      have hc : (c : ℕ) < R'.length := hlen ▸ c.2
      have hr := hf'.2 R'[(c : ℕ)] (List.getElem_mem hc)
      have hfst : R'[(c : ℕ)].1 = opts[(c : ℕ)] := by
        simp only [← hR', List.getElem_map]
      have hwk : R'[(c : ℕ)].2.length = k := by
        rw [hr.1, hfst]; exact (hk _ (List.getElem_mem c.2)).1
      have hs : ∑ j : Fin k, (weightsOf R' c j : ℝ) = D' := by
        have := sum_getD_eq_sum R'[(c : ℕ)].2 hwk
        rw [hr.2] at this
        unfold weightsOf
        rw [getD_of_lt _ _ hc]
        exact_mod_cast this
      change ∑ j : Fin k, (weightsOf R' c j : ℝ) / D' = 1
      rw [← Finset.sum_div, hs]
      exact div_self (by exact_mod_cast hD'pos.ne')
    have h1 := relaxationObjective_eq_Phi (es := es) hk hD hRfst
    have h2 := relaxationObjective_eq_Phi (es := es) hk hD'pos hR'
    have hWR : (fun (c : Fin opts.length) (j : Fin k) => (weightsOf R c j : ℝ) / D) =
        fun (c : Fin opts.length) (j : Fin k) => (W c j : ℝ) / D := by
      funext c j; rw [weightsOf_zip]
    rw [hWR] at h1
    have hm := hmin _ hX
    have key : ((D' : ℤ) * D' * relaxationObjective D R es : ℝ) ≤
        ((D : ℤ) * D * relaxationObjective D' R' es : ℝ) := by
      push_cast
      rw [h1, h2]
      have hDD : (0 : ℝ) ≤ 2 * (D : ℝ) ^ 2 * (D' : ℝ) ^ 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hm hDD]
    exact_mod_cast key

/-- The option lists of the enumerated `k`-cycles: `k` options per cycle, each a duplicate-free
path of `k − 2` edges of `g`. -/
theorem cycles_opts (g : Graph) (k : ℕ) :
    ∀ o ∈ (cycles g k).map selectedOptions, o.length = k ∧
      ∀ p ∈ o, p.Nodup ∧ p.length = k - 2 ∧ ∀ e ∈ p, e ∈ g := by
  intro o ho
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ho
  have hcyc := enumerated_isCycle hc
  refine ⟨by simp [selectedOptions, hcyc.2.1], ?_⟩
  intro p hp
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hp
  exact ⟨selected_nodup hcyc.2.2.1 i, by rw [selected_length, hcyc.2.1],
    fun e he => selected_mem_graph hcyc i he⟩

theorem length_filter_finRange_mem {es p : List Edge} (hes : es.Nodup) (hp : p.Nodup)
    (hsub : ∀ e ∈ p, e ∈ es) :
    ((List.finRange es.length).filter fun i : Fin es.length =>
      decide (es[(i : ℕ)] ∈ p)).length = p.length := by
  have hmap : ((List.finRange es.length).filter fun i : Fin es.length =>
      decide (es[(i : ℕ)] ∈ p)).map es.get =
      es.filter fun e => decide (e ∈ p) := by
    conv_rhs => rw [← List.map_get_finRange es]
    rw [List.filter_map]
    rfl
  rw [← List.length_map (f := es.get), hmap]
  apply List.Perm.length_eq
  rw [List.perm_ext_iff_of_nodup (hes.filter _) hp]
  intro e
  simp only [List.mem_filter, decide_eq_true_eq]
  exact ⟨fun h => h.2, fun h => ⟨hsub e h, h⟩⟩

/-- The instance of the option lists of valid cycles over a duplicate-free edge list is valid. -/
theorem ofOpts_valid {es : List Edge} (hes : es.Nodup) {k : ℕ} (hk3 : 3 ≤ k)
    {opts : List (List (List Edge))}
    (hk : ∀ o ∈ opts, o.length = k ∧ ∀ p ∈ o, p.Nodup ∧ p.length = k - 2 ∧ ∀ e ∈ p, e ∈ es) :
    (ofOpts es k opts).Valid := by
  refine ⟨hk3, fun c j => ⟨(List.nodup_finRange _).filter _, ?_⟩⟩
  have hc := hk _ (List.getElem_mem c.2)
  have hpm := hc.2 _ (path_mem c.2 (by rw [hc.1]; exact j.2))
  change ((List.finRange es.length).filter fun i : Fin es.length =>
    decide (es[(i : ℕ)] ∈ path opts c j)).length = k - 2
  rw [length_filter_finRange_mem hes hpm.1 hpm.2.2, hpm.2.1]

/-- The instance of the enumerated `k`-cycles of a duplicate-free graph, when there is a cycle, is
valid. -/
theorem ofOpts_valid_cycles {g : Graph} (hg : g.Nodup) {k : ℕ} (ht : cycles g k ≠ []) :
    (ofOpts g k ((cycles g k).map selectedOptions)).Valid :=
  ofOpts_valid hg (cycles_k_ge ht) (cycles_opts g k)


end STACS2027.Runtimes.ConvexQP

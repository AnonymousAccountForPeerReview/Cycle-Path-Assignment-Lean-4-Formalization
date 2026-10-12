module

public import ComplexityExt.Approx.Defs
public import ComplexityExt.Reg.Closure
public import Complexity.Composition
import Lean.Elab.Tactic.Omega

/-!
# L-reductions

Basic theory of L-reducibility (`Complexity.LReducible`): it is reflexive and transitive, and
it transfers approximation schemes backwards: if `P` L-reduces to `Q` and `Q` can be
approximated within every ratio `1 + 1 / (k + 1)` then so can `P`. Consequently MaxSNP-hardness
moves forwards along L-reductions and membership in MaxSNP moves backwards.
-/

@[expose] public section

namespace Complexity

open Complexity.Reg

/-! ### Arithmetic of `absDiff` -/

theorem absDiff_self (a : Nat) : absDiff a a = 0 := by
  simp [absDiff]

theorem absDiff_of_le {a b : Nat} (h : b ≤ a) : absDiff a b = a - b := by
  unfold absDiff; omega

theorem absDiff_of_ge {a b : Nat} (h : a ≤ b) : absDiff a b = b - a := by
  unfold absDiff; omega

namespace OptProblem

/-- The value of a solution is on the right side of the optimum. -/
theorem IsOpt.absDiff_eq {P : OptProblem} {x y : Word} {opt v : Nat} (h : P.IsOpt x opt)
    (hs : P.Sol x y v) :
    (P.maximize = true → v ≤ opt ∧ absDiff opt v = opt - v) ∧
      (P.maximize = false → opt ≤ v ∧ absDiff opt v = v - opt) := by
  have h' := h.2 y v hs
  constructor
  · intro hm
    exact ⟨h'.1 hm, absDiff_of_le (h'.1 hm)⟩
  · intro hm
    exact ⟨h'.2 hm, absDiff_of_ge (h'.2 hm)⟩

/-- A solution within the factor `1 + 1 / (j + 1)` of the optimum differs from the optimum by
at most `opt / (j + 1)`. -/
theorem IsOpt.mul_absDiff_le {P : OptProblem} {x y : Word} {opt v j : Nat} (h : P.IsOpt x opt)
    (hs : P.Sol x y v) (hr : P.WithinRatio (j + 2) (j + 1) opt v) :
    (j + 1) * absDiff opt v ≤ opt := by
  have h' := h.absDiff_eq hs
  have e : ∀ a : Nat, (j + 2) * a = (j + 1) * a + a := fun a => by
    rw [show j + 2 = (j + 1) + 1 from rfl, Nat.add_mul, Nat.one_mul]
  cases hm : P.maximize with
  | true =>
    obtain ⟨hle, he⟩ := h'.1 hm
    have h1 := hr.1 hm
    rw [he, Nat.mul_sub]
    rw [e] at h1
    omega
  | false =>
    obtain ⟨hle, he⟩ := h'.2 hm
    have h1 := hr.2 hm
    rw [he, Nat.mul_sub]
    rw [e] at h1
    omega

/-- A solution differing from the optimum by at most `opt / (k + 2)` is within the factor
`1 + 1 / (k + 1)` of the optimum. -/
theorem IsOpt.withinRatio_of_mul_absDiff_le {P : OptProblem} {x y : Word} {opt v k : Nat}
    (h : P.IsOpt x opt) (hs : P.Sol x y v) (hd : (k + 2) * absDiff opt v ≤ opt) :
    P.WithinRatio (k + 2) (k + 1) opt v := by
  have h' := h.absDiff_eq hs
  have e : ∀ a : Nat, (k + 2) * a = (k + 1) * a + a := fun a => by
    rw [show k + 2 = (k + 1) + 1 from rfl, Nat.add_mul, Nat.one_mul]
  constructor
  · intro hm
    obtain ⟨hle, he⟩ := h'.1 hm
    rw [he, Nat.mul_sub, e opt] at hd
    omega
  · intro hm
    obtain ⟨hle, he⟩ := h'.2 hm
    rw [he, Nat.mul_sub, e v, e opt] at hd
    rw [e opt]
    omega

end OptProblem

/-- The arithmetic core of the approximation transfer: if `(a (k + 2) + 1) d ≤ a opt` then
`(k + 2) d ≤ opt` (also when `a = 0`). -/
theorem mul_le_of_scaled_le {a k d opt : Nat} (h : (a * (k + 2) + 1) * d ≤ a * opt) :
    (k + 2) * d ≤ opt := by
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha
    have hd : d = 0 := by simpa using h
    subst hd
    simp
  · have h2 : a * ((k + 2) * d) ≤ a * opt := by
      rw [← Nat.mul_assoc]
      exact Nat.le_trans (Nat.mul_le_mul_right d (Nat.le_succ _)) h
    exact Nat.le_of_mul_le_mul_left h2 ha

/-! ### Reflexivity and transitivity -/

/-- L-reducibility is reflexive. -/
theorem LReducible.refl (P : OptProblem) : LReducible P P := by
  refine ⟨fun x => x, fun w => (unpair w).2, 1, 1, polyTime_id, polyTime_pair_snd, ?_⟩
  intro x opt hopt
  refine ⟨opt, hopt, by omega, ?_⟩
  intro y v' hy
  refine ⟨v', ?_, by omega⟩
  show P.Sol x (unpair (pairWords x y)).2 v'
  rw [unpair_pairWords]
  exact hy

/-- L-reducibility is transitive: the instance maps compose, the solution maps compose in the
opposite direction, and the constants multiply. -/
theorem LReducible.trans {P Q R : OptProblem} (h₁ : LReducible P Q) (h₂ : LReducible Q R) :
    LReducible P R := by
  obtain ⟨f₁, g₁, α₁, β₁, hf₁, hg₁, h₁⟩ := h₁
  obtain ⟨f₂, g₂, α₂, β₂, hf₂, hg₂, h₂⟩ := h₂
  refine ⟨fun x => f₂ (f₁ x),
    fun w => g₁ (pairWords (unpair w).1 (g₂ (pairWords (f₁ (unpair w).1) (unpair w).2))),
    α₂ * α₁, β₁ * β₂, polyTime_comp hf₂ hf₁, ?_, ?_⟩
  · exact polyTime_comp hg₁ (polyTime_pair polyTime_pair_fst
      (polyTime_comp hg₂ (polyTime_pair (polyTime_comp hf₁ polyTime_pair_fst)
        polyTime_pair_snd)))
  · intro x opt hopt
    obtain ⟨opt', hopt', hle', hsol'⟩ := h₁ x opt hopt
    obtain ⟨opt'', hopt'', hle'', hsol''⟩ := h₂ (f₁ x) opt' hopt'
    refine ⟨opt'', hopt'', ?_, ?_⟩
    · rw [Nat.mul_assoc]
      exact Nat.le_trans hle'' (Nat.mul_le_mul_left α₂ hle')
    · intro y v'' hy
      obtain ⟨v', hv', hd'⟩ := hsol'' y v'' hy
      obtain ⟨v, hv, hd⟩ := hsol' _ v' hv'
      refine ⟨v, ?_, ?_⟩
      · simp only [unpair_pairWords]
        exact hv
      · rw [Nat.mul_assoc]
        exact Nat.le_trans hd (Nat.mul_le_mul_left β₁ hd')

/-! ### Transfer of approximation algorithms -/

/-- If `P` L-reduces to `Q` with constants `α`, `β`, then an approximation algorithm for `Q`
with ratio `1 + 1 / (αβ(k + 2) + 1)` gives one for `P` with ratio `1 + 1 / (k + 1)`. -/
theorem LReducible.approximable_of {P Q : OptProblem} {f g : Word → Word} {α β : Nat}
    (hf : PolyTime f) (hg : PolyTime g)
    (h : ∀ x opt, P.IsOpt x opt →
      ∃ opt', Q.IsOpt (f x) opt' ∧ opt' ≤ α * opt ∧
        ∀ y v', Q.Sol (f x) y v' →
          ∃ v, P.Sol x (g (pairWords x y)) v ∧ absDiff opt v ≤ β * absDiff opt' v')
    (k : Nat) (hQ : Q.ApproximableWithin (β * α * (k + 2) + 2) (β * α * (k + 2) + 1)) :
    P.ApproximableWithin (k + 2) (k + 1) := by
  obtain ⟨B, hB, hB'⟩ := hQ
  refine ⟨fun x => g (pairWords x (B (f x))),
    polyTime_comp hg (polyTime_pair polyTime_id (polyTime_comp hB hf)), ?_⟩
  intro x opt hopt
  obtain ⟨opt', hopt', hle, hsol⟩ := h x opt hopt
  obtain ⟨v', hv', hr⟩ := hB' (f x) opt' hopt'
  obtain ⟨v, hv, hd⟩ := hsol _ v' hv'
  refine ⟨v, hv, hopt.withinRatio_of_mul_absDiff_le hv ?_⟩
  have h1 : (β * α * (k + 2) + 1) * absDiff opt' v' ≤ opt' := hopt'.mul_absDiff_le hv' hr
  refine mul_le_of_scaled_le (a := β * α) ?_
  calc (β * α * (k + 2) + 1) * absDiff opt v
      ≤ (β * α * (k + 2) + 1) * (β * absDiff opt' v') := Nat.mul_le_mul_left _ hd
    _ = β * ((β * α * (k + 2) + 1) * absDiff opt' v') := Nat.mul_left_comm _ _ _
    _ ≤ β * opt' := Nat.mul_le_mul_left _ h1
    _ ≤ β * (α * opt) := Nat.mul_le_mul_left _ hle
    _ = β * α * opt := (Nat.mul_assoc _ _ _).symm

/-- L-reductions transfer polynomial-time approximation within every ratio `1 + 1 / (k + 1)`
(a non-uniform approximation scheme) backwards. -/
theorem LReducible.approximable {P Q : OptProblem} (h : LReducible P Q)
    (hQ : ∀ k, Q.ApproximableWithin (k + 2) (k + 1)) :
    ∀ k, P.ApproximableWithin (k + 2) (k + 1) := by
  obtain ⟨f, g, α, β, hf, hg, h⟩ := h
  intro k
  exact LReducible.approximable_of hf hg h k (hQ _)

/-! ### MaxSNP -/

/-- MaxSNP-hardness moves forwards along L-reductions. -/
theorem MaxSNPHard.of_lReducible {P Q : OptProblem} (hP : MaxSNPHard P) (h : LReducible P Q) :
    MaxSNPHard Q :=
  fun R hR => (hP R hR).trans h

/-- Membership in MaxSNP moves backwards along L-reductions, to problems in NPO. -/
theorem InMaxSNP.of_lReducible {P Q : OptProblem} (hP : NPO P) (h : LReducible P Q)
    (hQ : InMaxSNP Q) : InMaxSNP P := by
  obtain ⟨-, ga, sa, k, φ, hφ, hQ⟩ := hQ
  exact ⟨hP, ga, sa, k, φ, hφ, h.trans hQ⟩

/-- A MaxSNP-hard problem that can be approximated within every ratio `1 + 1 / (k + 1)` makes
every problem of MaxSNP approximable within every such ratio. -/
theorem MaxSNPHard.approximable {P Q : OptProblem} (hP : MaxSNPHard P)
    (h : ∀ k, P.ApproximableWithin (k + 2) (k + 1)) (hQ : InMaxSNP Q) :
    ∀ k, Q.ApproximableWithin (k + 2) (k + 1) :=
  (hP Q hQ).approximable h

end Complexity

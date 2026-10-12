module

public import Hardness.APX.Defs
public import Hardness.MaxSNP.LReduction
public import PT.Words
public import PT.RawMore
import Lean.Elab.Tactic.Omega

/-!
# Uniform polynomial time from the `PT` framework, and PTAS-reductions along L-reductions

* `uniformPolyTime_of_PT`: a family `f k x` that is polynomial-time jointly in `(k, x)`, with
  `k` in unary, is uniformly polynomial-time in the sense of `UniformPolyTime`.
* `computableNat_of_PT`: a polynomial-time function on unary numbers is `ComputableNat`.
* `StrongPTASReducible.ptasReducible`: the strong form of PTAS-reducibility implies
  `PTASReducible`.
* `StrongPTASReducible.trans_lReducible`: a strong PTAS-reduction from `P` to `Q` composed with
  an L-reduction from `Q` to `R` is a strong PTAS-reduction from `P` to `R` (for maximization
  and minimization problems alike); hence `StrongAPXHard.of_lReducible` and
  `APXHard.of_lReducible_max`.
-/

@[expose] public section

namespace Complexity

open Complexity.PT Complexity.Reg

/-- Joint polynomial time in `(k, x)` (with `k` in unary) gives `UniformPolyTime`. -/
theorem uniformPolyTime_of_PT {f : Nat → Word → Word}
    (hf : PT (fun p : Nat × Word => f p.1 p.2)) : UniformPolyTime f := by
  have h : PT (fun p : Word × Word => f p.1.length p.2) := by fun_prop
  obtain ⟨M, c, e, hM⟩ := PT.polyTime_pairWords_word (h := fun u x : Word => f u.length x) h
  refine ⟨M, fun k => ⟨c * (2 * k + 2) ^ e, e, fun x => ?_⟩⟩
  obtain ⟨time, tape, ht, hr, ho⟩ := hM (pairWords (unary k) x)
  refine ⟨time, tape, Nat.le_trans ht ?_, hr, ?_⟩
  · have hlen : (pairWords (unary k) x).length + 1 ≤ (2 * k + 2) * (x.length + 1) := by
      simp only [pairWords, unary, List.length_append, List.length_cons, List.length_replicate,
        Nat.add_mul, Nat.mul_add]
      omega
    have hpow : ((pairWords (unary k) x).length + 1) ^ e ≤
        (2 * k + 2) ^ e * (x.length + 1) ^ e := by
      rw [← Nat.mul_pow]
      exact Nat.pow_le_pow_left hlen e
    rw [powerBound_eq, powerBound_eq, Nat.mul_assoc]
    exact Nat.mul_le_mul_left c hpow
  · rw [ho]
    simp [unary]

/-- A polynomial-time function on unary numbers is computable in the sense of
`ComputableNat`. -/
theorem computableNat_of_PT {c : Nat → Nat} (hc : PT c) : ComputableNat c := by
  have h : PT (fun w : Word => unary (c w.length)) := by fun_prop
  obtain ⟨M, d, e, hM⟩ := PT.polyTime_word h
  refine ⟨M, fun k => ?_⟩
  obtain ⟨time, tape, -, hr, ho⟩ := hM (unary k)
  refine ⟨time, tape, hr, ?_⟩
  rw [ho]
  simp [unary]

/-- The strong form of PTAS-reducibility implies PTAS-reducibility. -/
theorem StrongPTASReducible.ptasReducible {P Q : OptProblem} (h : StrongPTASReducible P Q) :
    PTASReducible P Q := by
  obtain ⟨f, g, c, hf, hg, hc, h⟩ := h
  exact ⟨f, g, c, uniformPolyTime_of_PT hf, uniformPolyTime_of_PT hg, computableNat_of_PT hc, h⟩

/-- A strong PTAS-reduction followed by an L-reduction is a strong PTAS-reduction. No
assumption on the goals (maximization or minimization) of the three problems is needed. -/
theorem StrongPTASReducible.trans_lReducible {P Q R : OptProblem}
    (h₁ : StrongPTASReducible P Q) (h₂ : LReducible Q R) : StrongPTASReducible P R := by
  obtain ⟨f, g, c, hf, hg, hc, h⟩ := h₁
  obtain ⟨fL, gL, α, β, hfL, hgL, hL⟩ := h₂
  have hfL' : PT fL := PT.of_polyTime hfL
  have hgL' : PT gL := PT.of_polyTime hgL
  refine ⟨fun k x => fL (f k x),
    fun k z => g k (pairWords (unpair z).1 (gL (pairWords (f k (unpair z).1) (unpair z).2))),
    fun k => β * α * (c k + 2), by fun_prop, ?_, by fun_prop, ?_⟩
  · have h0 : PT (fun q : Nat × (Word × Word) =>
        g q.1 (pairWords q.2.1 (gL (pairWords (f q.1 q.2.1) q.2.2)))) := by fun_prop
    exact h0.comp (PT.pair PT.fst' (PT.unpair PT.snd'))
  intro k x opt hopt
  obtain ⟨opt', hopt', hsol⟩ := h k x opt hopt
  obtain ⟨opt'', hopt'', hle, hsolL⟩ := hL (f k x) opt' hopt'
  refine ⟨opt'', hopt'', fun y v'' hy => ?_⟩
  obtain ⟨v', hv', hd⟩ := hsolL y v'' hy
  obtain ⟨v, hv, hr⟩ := hsol _ v' hv'
  refine ⟨v, by simpa only [unpair_pairWords] using hv, fun hr'' => hr ?_⟩
  refine hopt'.withinRatio_of_mul_absDiff_le hv' ?_
  have h1 : (β * α * (c k + 2) + 1) * absDiff opt'' v'' ≤ opt'' :=
    hopt''.mul_absDiff_le hy hr''
  refine mul_le_of_scaled_le (a := β * α) ?_
  calc (β * α * (c k + 2) + 1) * absDiff opt' v'
      ≤ (β * α * (c k + 2) + 1) * (β * absDiff opt'' v'') := Nat.mul_le_mul_left _ hd
    _ = β * ((β * α * (c k + 2) + 1) * absDiff opt'' v'') := Nat.mul_left_comm _ _ _
    _ ≤ β * opt'' := Nat.mul_le_mul_left _ h1
    _ ≤ β * (α * opt') := Nat.mul_le_mul_left _ hle
    _ = β * α * opt' := (Nat.mul_assoc _ _ _).symm

/-- Strong APX-hardness implies APX-hardness. -/
theorem StrongAPXHard.apxHard {P : OptProblem} (h : StrongAPXHard P) : APXHard P :=
  fun Q hQ => (h Q hQ).ptasReducible

/-- Strong APX-hardness moves forwards along L-reductions. -/
theorem StrongAPXHard.of_lReducible {P Q : OptProblem} (hP : StrongAPXHard P)
    (h : LReducible P Q) : StrongAPXHard Q :=
  fun R hR => (hP R hR).trans_lReducible h

/-- A PTAS-reduction whose maps are jointly polynomial-time, composed with an L-reduction, is a
PTAS-reduction: if every problem of APX is PTAS-reducible to `P` by jointly polynomial-time
maps and `P` is L-reducible to `Q`, then `Q` is APX-hard. (The statement holds for
maximization and minimization problems alike; see `StrongPTASReducible.trans_lReducible`.) -/
theorem APXHard.of_lReducible_max {P Q : OptProblem}
    (hP : ∀ R, InAPX R → StrongPTASReducible R P) (h : LReducible P Q) : APXHard Q :=
  (StrongAPXHard.of_lReducible hP h).apxHard

end Complexity

module

public import Hardness.Occ.Basic

/-!
# 3-OCCURRENCE MAX-3-SAT is in APX

* `npo_max3SAT3`: feasibility and value are computed by an explicit polynomial-time program
  (`max3Feas3`); only the variables below `variableBound f` need to be checked for the
  occurrence bound (`isThreeOcc_iff`).
* `max3SAT3_inAPX`: the better of the all-true and the all-false assignment (`max3Approx` of
  `Hardness.APX.Membership`) is a 2-approximation, since on instances of `max3SAT3` the
  problems `max3SAT3` and `max3SAT` have the same solutions.
-/

@[expose] public section

set_option linter.dupNamespace false

namespace Complexity

open Complexity.PT Complexity.Reg Complexity.Occ

theorem isThreeOcc_iff (f : SAT.CNF) :
    SAT.IsThreeOcc f ↔ ∀ u ∈ List.range (SAT.variableBound f), occ f u ≤ 3 := by
  constructor
  · intro h u _
    rw [← occurrences_eq_occ]
    exact h u
  · intro h u
    rw [occurrences_eq_occ]
    by_cases hu : u < SAT.variableBound f
    · exact h u (List.mem_range.mpr hu)
    · rw [occ_eq_zero_of_le (by omega)]
      omega

/-- The feasibility and value function of `max3SAT3`. -/
def max3Feas3 (x y : Word) : Word :=
  if SAT.encode (parseCNF x) = x ∧ (∀ cl ∈ parseCNF x, cl.length ≤ 3) ∧
      (∀ u ∈ List.range (SAT.variableBound (parseCNF x)), occ (parseCNF x) u ≤ 3) ∧
      y.length ≤ x.length then
    true :: natBits (SAT.satCount (SAT.assignmentOf y) (parseCNF x))
  else [false]

theorem max3Feas3_iff (x y : Word) (v : Nat) :
    max3SAT3.Sol x y v ↔ max3Feas3 x y = true :: natBits v := by
  constructor
  · rintro ⟨f, rfl, h3, ho, hlen, rfl⟩
    rw [max3Feas3, parseCNF_encode, ite_eq_left ⟨rfl, h3, (isThreeOcc_iff f).mp ho, hlen⟩]
  · intro h
    rw [max3Feas3] at h
    split at h
    · next hc =>
      obtain ⟨hx, h3, ho, hlen⟩ := hc
      exact ⟨parseCNF x, hx, h3, (isThreeOcc_iff _).mpr ho, hlen,
        natBits_injective (List.cons.inj h).2.symm⟩
    · cases h

theorem pt_max3Feas3 : PT (fun p : Word × Word => max3Feas3 p.1 p.2) := by
  unfold max3Feas3
  fun_prop

theorem npo_max3SAT3 : NPO max3SAT3 := by
  refine ⟨⟨1, 1, ?_⟩, fun z => max3Feas3 (unpair z).1 (unpair z).2,
    PT.polyTime_pairWords_word (h := max3Feas3) pt_max3Feas3, fun x y v => ?_⟩
  · rintro x y v ⟨f, -, -, -, hlen, -⟩
    rw [powerBound_eq, Nat.pow_one]
    omega
  · simp only [unpair_pairWords]
    exact max3Feas3_iff x y v

/-- On an instance of `max3SAT3`, the solutions of `max3SAT` are solutions of `max3SAT3`. -/
theorem max3SAT3_sol_of_max3SAT_sol {x y₀ y : Word} {v₀ v : Nat} (h₀ : max3SAT3.Sol x y₀ v₀)
    (h : max3SAT.Sol x y v) : max3SAT3.Sol x y v := by
  obtain ⟨f, hf, h3, ho, -, -⟩ := h₀
  obtain ⟨f', hf', -, hlen, hv⟩ := h
  obtain rfl := SAT.encode_injective _ _ (hf'.trans hf.symm)
  exact ⟨f', hf', h3, ho, hlen, hv⟩

theorem max3SAT_sol_of_max3SAT3_sol {x y : Word} {v : Nat} (h : max3SAT3.Sol x y v) :
    max3SAT.Sol x y v := by
  obtain ⟨f, hf, h3, -, hlen, hv⟩ := h
  exact ⟨f, hf, h3, hlen, hv⟩

theorem max3SAT_isOpt_of_max3SAT3 {x : Word} {opt : Nat} (h : max3SAT3.IsOpt x opt) :
    max3SAT.IsOpt x opt := by
  obtain ⟨⟨y₀, hy₀⟩, hmax⟩ := h
  exact ⟨⟨y₀, max3SAT_sol_of_max3SAT3_sol hy₀⟩,
    fun y v h => hmax y v (max3SAT3_sol_of_max3SAT_sol hy₀ h)⟩

/-- The better of the all-true and the all-false assignment is a 2-approximation. -/
theorem max3Approx_spec3 : max3SAT3.ApproxAlgorithm 2 1 max3Approx := by
  refine ⟨max3Approx_spec.1, fun x opt hopt => ?_⟩
  obtain ⟨v, hv, hr⟩ := max3Approx_spec.2 x opt (max3SAT_isOpt_of_max3SAT3 hopt)
  obtain ⟨⟨y₀, hy₀⟩, -⟩ := hopt
  exact ⟨v, max3SAT3_sol_of_max3SAT_sol hy₀ hv, hr⟩

/-- **3-OCCURRENCE MAX-3-SAT is in APX.** -/
theorem max3SAT3_inAPX : InAPX max3SAT3 :=
  ⟨npo_max3SAT3, 2, 1, by omega, max3Approx, max3Approx_spec3⟩

end Complexity

module

public import ApproximationHardness.LReduction
public import ApproximationHardness.PolarizeLReduction

/-!
# Composing the L-reductions, and what an L-reduction transfers

L-reductions compose, the parameters multiplying (ANONYMIZED and ANONYMIZED). Composed
with Lemma 10, Theorem 11's reduction is an L-reduction from 3-OCCURRENCE MAX-3-SAT, a
MaxSNP-complete problem, to `CPAP(G, k)`, with `α = 5/3` and `β = 1`. An L-reduction
turns a `(1 + ε)`-approximate solution of the target into a `(1 − αβε)`-approximate
solution of the source (`approximation_transfer`), the mechanism behind Corollary 12.
Corollary 12 itself, and the MaxSNP- and APX-hardness of Theorem 11, are proved in
`ApproximationHardness/Hardness/` from Max3SAT-MaxSNP-APX-Lean4 (the PCP theorem and the hardness of
3-OCCURRENCE MAX-3-SAT).
-/

@[expose] public section
namespace STACS2027
open Complexity.SAT

/-- L-reductions compose: a MAX-SAT-to-MAX-SAT L-reduction followed by a MAX-SAT-to-CPAP
L-reduction is an L-reduction with the products of the parameters. -/
theorem LReductionSat.comp_cpap {Source Source' : CNF → Prop} {T : CNF → CNF} {F : CNF → Graph}
    {k αn αd βn βd αn' αd' βn' βd' : Nat}
    (h1 : LReductionSat Source T αn αd βn βd) (hT : ∀ f, Source f → Source' (T f))
    (h2 : LReductionToCPAP Source' F k αn' αd' βn' βd') :
    LReductionToCPAP Source (fun f => F (T f)) k (αn * αn') (αd * αd') (βn * βn') (βd * βd') := by
  intro f hf S C hS hC
  obtain ⟨S', hS'⟩ := maxSat_exists (T f)
  obtain ⟨hα1, hβ1⟩ := h1 f hf S S' hS hS'
  obtain ⟨hα2, hβ2⟩ := h2 (T f) (hT f hf) S' C hS' hC
  refine ⟨?_, ?_⟩
  · -- `αd αd' C ≤ αd αn' S' ≤ αn αn' S`
    calc αd * αd' * C = αd * (αd' * C) := Nat.mul_assoc _ _ _
      _ ≤ αd * (αn' * S') := Nat.mul_le_mul_left _ hα2
      _ = αn' * (αd * S') := by rw [Nat.mul_left_comm]
      _ ≤ αn' * (αn * S) := Nat.mul_le_mul_left _ hα1
      _ = αn * αn' * S := by rw [Nat.mul_left_comm, Nat.mul_assoc]
  · intro ps hv
    obtain ⟨b, hb⟩ := hβ2 ps hv
    obtain ⟨a, ha⟩ := hβ1 b
    refine ⟨a, ?_⟩
    -- `βd' ·` (second) and `βn ·` (first), added, cancel the terms in `b` and `S'`
    have h1' := Nat.mul_le_mul_left βd' ha
    have h2' := Nat.mul_le_mul_left βn hb
    -- expand the products
    have e1 : βd' * (βd * S + βn * satisfiedCount b (T f)) = βd * βd' * S + βn * βd' * satisfiedCount b (T f) := by
      rw [Nat.mul_add]; ac_rfl
    have e2 : βd' * (βd * satisfiedCount a f + βn * S') = βd * βd' * satisfiedCount a f + βn * βd' * S' := by
      rw [Nat.mul_add]; ac_rfl
    have e3 : βn * (βd' * S' + βn' * C) = βn * βd' * S' + βn * βn' * C := by
      rw [Nat.mul_add]; ac_rfl
    have e4 : βn * (βd' * satisfiedCount b (T f) + βn' * cost ps) =
        βn * βd' * satisfiedCount b (T f) + βn * βn' * cost ps := by
      rw [Nat.mul_add]; ac_rfl
    rw [e1, e2] at h1'
    rw [e3, e4] at h2'
    omega

/-- **Lemma 10**: the transformation maps 3-OCCURRENCE MAX-3-SAT instances to MAX-(≤1,≤2)-SAT
instances of Definition 7, and is an L-reduction with `α = β = 1`. -/
theorem leOneLeTwo_lreduction : (∀ f, ThreeOccurrence f → LeOneLeTwoCNF (polarize f)) ∧
    LReductionSat ThreeOccurrence polarize 1 1 1 1 :=
  ⟨fun _ hf => polarize_leOneLeTwo hf, polarize_lreduction⟩

/-- **Theorem 11 with Lemma 10**: for every `k ≥ 5`, 3-OCCURRENCE MAX-3-SAT L-reduces to
`CPAP(G, k)` with `α = 5/3` and `β = 1`, through the Lemma 10 transformation and the
Theorem 8 graph. -/
theorem threeOccurrence_cpap_lreduction {k : Nat} (hk : 5 ≤ k) :
    LReductionToCPAP ThreeOccurrence (fun f => formulaGraph k (polarize f)) k 5 3 1 1 := by
  have h := LReductionSat.comp_cpap polarize_lreduction (fun f hf => polarize_leOneLeTwo hf) (cpap_lreduction hk)
  simpa using h

/-- What an L-reduction transfers: a solution of the target instance within a factor
`1 + εn/εd` of `C*` decodes to a solution of the source within a factor `1 − (αβ) εn/εd` of
`S*`, written as `αd βd εd · S* ≤ αd βd εd · s(a) + αn βn εn · S*`. -/
theorem approximation_transfer {Source : CNF → Prop} {F : CNF → Graph} {k αn αd βn βd : Nat}
    (h : LReductionToCPAP Source F k αn αd βn βd) {f : CNF} (hf : Source f) {S C : Nat}
    (hS : IsMaxSat f S) (hC : IsMinCost (F f) k C) (ps : List (List Edge))
    (hv : ValidChoices ((cycles (F f) k).map selectedOptions) ps) (εn εd : Nat)
    (happrox : εd * cost ps ≤ (εd + εn) * C) :
    ∃ a : Assignment, αd * βd * εd * S ≤ αd * βd * εd * satisfiedCount a f + αn * βn * εn * S := by
  obtain ⟨hα, hβ⟩ := h f hf S C hS hC
  obtain ⟨a, ha⟩ := hβ ps hv
  refine ⟨a, ?_⟩
  -- `εd ·` the β inequality, then bound `εd · cost ps` by the approximation guarantee
  have h1 := Nat.mul_le_mul_left εd ha
  have h2 : βn * (εd * cost ps) ≤ βn * ((εd + εn) * C) := Nat.mul_le_mul_left βn happrox
  have h3 := Nat.mul_le_mul_left (βn * εn) hα
  -- normalize the products
  have e1 : εd * (βd * S + βn * C) = βd * εd * S + βn * εd * C := by
    rw [Nat.mul_add]; ac_rfl
  have e2 : εd * (βd * satisfiedCount a f + βn * cost ps) = βd * εd * satisfiedCount a f + βn * (εd * cost ps) := by
    rw [Nat.mul_add]; ac_rfl
  have e3 : βn * ((εd + εn) * C) = βn * εd * C + βn * εn * C := by
    rw [Nat.add_mul, Nat.mul_add]; ac_rfl
  have e4 : βn * εn * (αd * C) = αd * (βn * εn * C) := by ac_rfl
  have e5 : βn * εn * (αn * S) = αn * βn * εn * S := by ac_rfl
  rw [e1, e2] at h1
  rw [e3] at h2
  rw [e4, e5] at h3
  -- `βd εd S ≤ βd εd s(a) + βn εn C`, then multiply by `αd` and use `αd C ≤ αn S`
  have h4 : βd * εd * S ≤ βd * εd * satisfiedCount a f + βn * εn * C := by omega
  have h5 := Nat.mul_le_mul_left αd h4
  have e6 : αd * (βd * εd * S) = αd * βd * εd * S := by ac_rfl
  have e7 : αd * (βd * εd * satisfiedCount a f + βn * εn * C) =
      αd * βd * εd * satisfiedCount a f + αd * (βn * εn * C) := by
    rw [Nat.mul_add]; ac_rfl
  rw [e6, e7] at h5
  omega

end STACS2027

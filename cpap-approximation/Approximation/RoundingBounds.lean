module

public import Approximation.RoundingSteps

/-!
The two bounds behind Theorems 16 and 17: the variance of the rounded load of
one cycle, summed over its `k` edges, is at most `2(k − 2)/k` (Cauchy–Schwarz),
and the fractional optimum is at most the integral optimum.
-/

@[expose] public section
namespace STACS2027

/-- The cycles of `R`: each has duplicate-free option paths of `L` edges inside an edge list of
`L + 2` edges (its `k = L + 2` cycle edges) contained in `es`. -/
def CycleInstance (es : List Edge) (L : Nat) (R : List (List (List Edge) × List Nat)) : Prop :=
  ∀ r ∈ R, ∃ U : List Edge, U.length = L + 2 ∧ (∀ e ∈ U, e ∈ es) ∧
    ∀ p ∈ r.1, p.Nodup ∧ p.length = L ∧ ∀ e ∈ p, e ∈ U

theorem CycleInstance.optionsIn {es : List Edge} {L : Nat}
    {R : List (List (List Edge) × List Nat)} (h : CycleInstance es L R) : OptionsIn es L R := by
  intro r hr p hp
  obtain ⟨U, _, hU, hopt⟩ := h r hr
  exact ⟨(hopt p hp).1, (hopt p hp).2.1, fun e he => hU e ((hopt p hp).2.2 e he)⟩

theorem CycleInstance.tail {es : List Edge} {L : Nat} {r : List (List Edge) × List Nat}
    {R : List (List (List Edge) × List Nat)} (h : CycleInstance es L (r :: R)) :
    CycleInstance es L R :=
  fun r' hr' => h r' (by simp [hr'])

/-- The indicator of membership in `U`. -/
def indicator (U : List Edge) (e : Edge) : Nat := if e ∈ U then 1 else 0

theorem sum_indicator_le {es U : List Edge} (he : es.Nodup) :
    (es.map fun e => indicator U e * indicator U e).sum ≤ U.length := by
  have h : (es.map fun e => indicator U e * indicator U e).sum =
      (es.filter fun e => decide (e ∈ U)).length := by
    induction es with
    | nil => simp
    | cons e es ih =>
      have ht := ih (List.nodup_cons.mp he).2
      simp only [List.map_cons, List.sum_cons, List.filter_cons, ht]
      by_cases hm : e ∈ U
      · have hi : indicator U e = 1 := by simp [indicator, hm]
        rw [hi]; simp [hm] <;> omega
      · have hi : indicator U e = 0 := by simp [indicator, hm]
        rw [hi]; simp [hm]
  rw [h]
  apply List.Nodup.length_le_of_subset (List.Nodup.sublist List.filter_sublist he)
  intro e hm
  exact of_decide_eq_true (List.mem_filter.mp hm).2

/-- Cauchy–Schwarz on one cycle: `k ∑_e Var ≤ 2 D² (k − 2)`, where `k = L + 2` and the
option paths have `L` edges. -/
theorem variance_bound {es : List Edge} (he : es.Nodup) {D L : Nat} {opts : List (List Edge)}
    {w : List Nat} {U : List Edge} (hUk : U.length = L + 2)
    (hUs : ∀ e ∈ U, e ∈ es) (hopt : ∀ p ∈ opts, p.Nodup ∧ p.length = L ∧ ∀ e ∈ p, e ∈ U)
    (hl : w.length = opts.length) (hw : w.sum = D) :
    (L + 2) * (es.map fun e => optionLoad opts w e * (D - optionLoad opts w e)).sum ≤
      2 * (D * D * L) := by
  have hn : ∀ p ∈ opts, p.Nodup := fun p hp => (hopt p hp).1
  have hq : ∀ e, optionLoad opts w e ≤ D := fun e => hw ▸ optionLoad_le_sum hn hl e
  -- `T = ∑_e D p_e = D L`.
  have hT : (es.map (optionLoad opts w)).sum = D * L := by
    rw [sum_optionLoad he (fun p hp => ⟨(hopt p hp).2.1,
      fun e hep => hUs e ((hopt p hp).2.2 e hep)⟩) hl, hw]
  -- `X + Y = D T` with `X = ∑ p(D − p)`, `Y = ∑ p²`.
  have hXY : (es.map fun e => optionLoad opts w e * (D - optionLoad opts w e)).sum +
      (es.map fun e => optionLoad opts w e * optionLoad opts w e).sum = D * (D * L) := by
    rw [← hT, ← sum_map_add, ← sum_map_mul_left]
    apply sum_map_congr
    intro e _
    obtain ⟨d, hd⟩ := Nat.le.dest (hq e)
    rw [← hd, Nat.add_sub_cancel_left]
    grind
  -- Cauchy–Schwarz with the indicator of `U`: `T² ≤ |U| Y`.
  have hind : ∀ e ∈ es, indicator U e * optionLoad opts w e = optionLoad opts w e := by
    intro e _
    unfold indicator
    by_cases hm : e ∈ U
    · simp [hm]
    · simp [hm, optionLoad_eq_zero w (fun p hp => (hopt p hp).2.2) hm]
  have hcs := cauchy_schwarz es (indicator U) (optionLoad opts w)
  rw [sum_map_congr es _ _ hind, hT] at hcs
  have hY : (D * L) * (D * L) ≤ (L + 2) *
      (es.map fun e => optionLoad opts w e * optionLoad opts w e).sum := by
    calc (D * L) * (D * L) ≤ _ := hcs
      _ ≤ (L + 2) * (es.map fun e => optionLoad opts w e * optionLoad opts w e).sum :=
        Nat.mul_le_mul_right _ (hUk ▸ sum_indicator_le he)
  -- Conclude: `(L + 2) X = (L + 2) D² L − (L + 2) Y ≤ (L + 2) D² L − D² L² = 2 D² L`.
  generalize (es.map fun e => optionLoad opts w e * (D - optionLoad opts w e)).sum = X at hXY ⊢
  generalize (es.map fun e => optionLoad opts w e * optionLoad opts w e).sum = Y at hXY hY
  have h1 : (L + 2) * X + (L + 2) * Y = L * (D * D * L) + 2 * (D * D * L) := by
    rw [← Nat.mul_add, hXY]; grind
  have h2 : L * (D * D * L) ≤ (L + 2) * Y := by
    calc L * (D * D * L) = (D * L) * (D * L) := by grind
      _ ≤ _ := hY
  omega

/-- The variance term summed over all cycles: `k ∑_e Var[l(e)] ≤ 2 D² (k − 2) t`. -/
theorem variance_sum_bound {es : List Edge} (he : es.Nodup) {D L : Nat}
    {R : List (List (List Edge) × List Nat)} (hR : CycleInstance es L R)
    (hf : FractionalSolution D R) :
    (L + 2) * (es.map (varianceLoad D R)).sum ≤ 2 * (D * D * L) * R.length := by
  induction R with
  | nil => rw [sum_map_eq_zero es (varianceLoad D []) (fun _ _ => rfl)]; simp
  | cons r R ih =>
    have hsplit : (es.map (varianceLoad D (r :: R))).sum =
        (es.map fun e => optionLoad r.1 r.2 e * (D - optionLoad r.1 r.2 e)).sum +
          (es.map (varianceLoad D R)).sum := by
      rw [← sum_map_add]
      exact sum_map_congr es _ _ (fun e _ => varianceLoad_cons D r R e)
    obtain ⟨U, hUk, hUs, hopt⟩ := hR r (by simp)
    have h₁ := variance_bound he hUk hUs hopt hf.head.1 hf.head.2
    have h₂ := ih hR.tail hf.tail
    rw [hsplit, Nat.mul_add, List.length_cons, Nat.mul_succ]
    omega

/-- `∑_e D λ_e = D (k − 2) t`. -/
theorem sum_fractionalLoad {es : List Edge} (he : es.Nodup) {D L : Nat}
    {R : List (List (List Edge) × List Nat)} (hR : OptionsIn es L R)
    (hf : FractionalSolution D R) : (es.map (fractionalLoad R)).sum = D * L * R.length := by
  induction R with
  | nil => rw [sum_map_eq_zero es (fractionalLoad []) (fun _ _ => rfl)]; simp
  | cons r R ih =>
    have hsplit : (es.map (fractionalLoad (r :: R))).sum =
        (es.map (optionLoad r.1 r.2)).sum + (es.map (fractionalLoad R)).sum := by
      rw [← sum_map_add]
      exact sum_map_congr es _ _ (fun e _ => fractionalLoad_cons r R e)
    rw [hsplit, ih hR.tail hf.tail, sum_optionLoad he
      (fun p hp => ⟨(hR.head p hp).2.1, (hR.head p hp).2.2⟩) hf.head.1, hf.head.2,
      List.length_cons, Nat.mul_succ]
    omega

theorem int_sum_map_sub {α : Type} (xs : List α) (f g : α → Int) :
    (xs.map fun x => f x - g x).sum = (xs.map f).sum - (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih]; omega

theorem int_sum_map_mul_left {α : Type} (xs : List α) (c : Int) (f : α → Int) :
    (xs.map fun x => c * f x).sum = c * (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih, Int.mul_add]

theorem int_natCast_sum {α : Type} (xs : List α) (f : α → Nat) :
    (((xs.map f).sum : Nat) : Int) = (xs.map fun x => ((f x : Nat) : Int)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, Int.natCast_add, ih]

theorem relaxationObjective_eq (D : Nat) (R : List (List (List Edge) × List Nat))
    (es : List Edge) :
    relaxationObjective D R es =
      (((es.map fun e => fractionalLoad R e * fractionalLoad R e).sum : Nat) : Int) -
        (D : Int) * (((es.map (fractionalLoad R)).sum : Nat) : Int) := by
  unfold relaxationObjective
  rw [int_sum_map_sub, int_natCast_sum, int_natCast_sum, int_sum_map_mul_left]
  simp only [Int.natCast_mul]

theorem integralSolution_fst (options : List (List (List Edge))) (ps : List (List Edge))
    (hv : ValidChoices options ps) :
    (integralSolution options ps).map Prod.fst = options := by
  induction options generalizing ps with
  | nil =>
    cases ps with
    | nil => rfl
    | cons _ _ => exact False.elim hv
  | cons opts options ih =>
    cases ps with
    | nil => exact False.elim hv
    | cons p ps => simp [integralSolution, ih ps hv.2]

theorem integralSolution_fractional (options : List (List (List Edge))) (ps : List (List Edge))
    (hv : ValidChoices options ps) : FractionalSolution 1 (integralSolution options ps) := by
  refine ⟨Nat.one_pos, ?_⟩
  induction options generalizing ps with
  | nil =>
    cases ps with
    | nil => simp [integralSolution]
    | cons _ _ => exact False.elim hv
  | cons opts options ih =>
    cases ps with
    | nil => exact False.elim hv
    | cons p ps =>
      intro r hr
      simp only [integralSolution, List.mem_cons] at hr
      rcases hr with rfl | hr
      · exact ⟨unitWeights_length opts p, unitWeights_sum hv.1⟩
      · exact ih ps hv.2 r hr

theorem integralSolution_load (options : List (List (List Edge))) (ps : List (List Edge))
    (hv : ValidChoices options ps) (e : Edge) :
    fractionalLoad (integralSolution options ps) e = load ps e := by
  induction options generalizing ps with
  | nil =>
    cases ps with
    | nil => simp [integralSolution, fractionalLoad, load]
    | cons _ _ => exact False.elim hv
  | cons opts options ih =>
    cases ps with
    | nil => exact False.elim hv
    | cons p ps =>
      simp only [integralSolution, fractionalLoad_cons, load_cons, ih ps hv.2]
      unfold optionLoad
      rw [weightedSum_unitWeights _ hv.1]

/-- The fractional optimum is at most the value of any integral assignment:
`∑_e (D λ_e)² ≤ 2 D² c(qs) + D ∑_e D λ_e`. -/
theorem fractional_le_integral {es : List Edge} (he : es.Nodup) {D : Nat}
    {R : List (List (List Edge) × List Nat)} (hopt : OptimalFractional es D R)
    {qs : List (List Edge)} (hq : ValidChoices (R.map Prod.fst) qs)
    (hqn : ∀ p ∈ qs, p.Nodup) (hqs : ∀ p ∈ qs, ∀ e ∈ p, e ∈ es) :
    (es.map fun e => fractionalLoad R e * fractionalLoad R e).sum ≤
      D * D * (2 * cost qs) + D * (es.map (fractionalLoad R)).sum := by
  have h := hopt.2 1 (integralSolution (R.map Prod.fst) qs)
    (integralSolution_fractional _ qs hq) (integralSolution_fst _ qs hq)
  rw [relaxationObjective_eq, relaxationObjective_eq] at h
  have hload : (es.map (fractionalLoad (integralSolution (R.map Prod.fst) qs))) = es.map (load qs) :=
    List.map_congr_left (fun e _ => integralSolution_load _ qs hq e)
  have hload2 : (es.map fun e => fractionalLoad (integralSolution (R.map Prod.fst) qs) e *
      fractionalLoad (integralSolution (R.map Prod.fst) qs) e) =
      es.map fun e => load qs e * load qs e :=
    List.map_congr_left (fun e _ => by rw [integralSolution_load _ qs hq e])
  rw [hload, hload2, sum_sq_load he qs hqn hqs] at h
  have hsq : ((2 * cost qs + (es.map (load qs)).sum : Nat) : Int) =
      (2 * cost qs : Nat) + ((es.map (load qs)).sum : Nat) := Int.natCast_add _ _
  rw [hsq] at h
  -- Clear the casts.
  simp only [Int.natCast_one, Int.one_mul, Int.add_sub_cancel] at h
  have hX : ((D * (es.map (fractionalLoad R)).sum : Nat) : Int) =
      (D : Int) * (((es.map (fractionalLoad R)).sum : Nat) : Int) := Int.natCast_mul _ _
  have hY : ((D * D * (2 * cost qs) : Nat) : Int) =
      (D : Int) * D * ((2 * cost qs : Nat) : Int) := by
    rw [Int.natCast_mul, Int.natCast_mul]
  rw [← hX, ← hY] at h
  omega

/-- The paths of a valid choice of an `OptionsIn` instance are duplicate-free paths of `L`
edges in `es`, one per cycle. -/
theorem OptionsIn.choices {es : List Edge} {L : Nat} {R : List (List (List Edge) × List Nat)}
    (hin : OptionsIn es L R) {rs : List (List Edge)} (hv : ValidChoices (R.map Prod.fst) rs) :
    (∀ p ∈ rs, p.Nodup) ∧ (∀ p ∈ rs, p.length = L) ∧ (∀ p ∈ rs, ∀ e ∈ p, e ∈ es) ∧
      rs.length = R.length := by
  induction R generalizing rs with
  | nil =>
    cases rs with
    | nil => simp
    | cons _ _ => exact False.elim hv
  | cons r R ih =>
    cases rs with
    | nil => exact False.elim hv
    | cons p ps =>
      obtain ⟨hp, hv⟩ := hv
      obtain ⟨h₁, h₂, h₃, h₄⟩ := ih hin.tail hv
      have hhead := hin.head p hp
      refine ⟨?_, ?_, ?_, by simp [h₄]⟩
      · intro p' hp'
        rcases List.mem_cons.mp hp' with rfl | hp'
        · exact hhead.1
        · exact h₁ p' hp'
      · intro p' hp'
        rcases List.mem_cons.mp hp' with rfl | hp'
        · exact hhead.2.1
        · exact h₂ p' hp'
      · intro p' hp'
        rcases List.mem_cons.mp hp' with rfl | hp'
        · exact hhead.2.2
        · exact h₃ p' hp'

/-- A run of Algorithm 2 on a fractional optimum of the relaxation has cost at most
`OPT + (k − 2) t / k`: `k c(ps) ≤ k c(qs) + (k − 2) t` for every assignment `qs`
(Theorem 18, with `k = L + 2` and `t` the number of cycles). -/
theorem roundingRun_cost_bound {es : List Edge} (he : es.Nodup) {D L : Nat}
    {R : List (List (List Edge) × List Nat)} (hR : CycleInstance es L R)
    (hopt : OptimalFractional es D R) {ps qs : List (List Edge)}
    (hrun : RoundingRun D [] R ps) (hq : ValidChoices (R.map Prod.fst) qs) :
    (L + 2) * cost ps ≤ (L + 2) * cost qs + L * R.length := by
  have hf := hopt.1
  have hD := hf.1
  obtain ⟨hpn, hpl, hps, hplen⟩ := hR.optionsIn.choices hrun.valid
  obtain ⟨hqn, hql, hqs, hqlen⟩ := hR.optionsIn.choices hq
  -- The scaled expected sum of squared loads decreases along the run.
  have hrun' := hrun.expectedSquares_le he hR.optionsIn hf
  rw [List.nil_append, expectedSquares_nil, expectedSquares_start,
    sum_sq_load_assignment he hpn hpl hps, hplen] at hrun'
  -- Its initial value is bounded by the fractional optimum plus the variance term.
  have hlow := fractional_le_integral he hopt hq hqn hqs
  rw [sum_fractionalLoad he hR.optionsIn hf] at hlow
  have hvar := variance_sum_bound he hR hf
  -- Combine: `2 D² k c(ps) ≤ 2 D² k c(qs) + 2 D² L t`.
  have hmain : (L + 2) * (2 * (D * D) * cost ps) ≤
      (L + 2) * (2 * (D * D) * cost qs) + 2 * (D * D) * (L * R.length) := by
    have e1 : D * D * (2 * cost ps + L * R.length) =
        2 * (D * D) * cost ps + D * D * (L * R.length) := by grind
    have e2 : D * D * (2 * cost qs) + D * (D * L * R.length) =
        2 * (D * D) * cost qs + D * D * (L * R.length) := by grind
    have e3 : 2 * (D * D * L) * R.length = 2 * (D * D) * (L * R.length) := by grind
    rw [e1] at hrun'
    rw [e2] at hlow
    rw [e3] at hvar
    generalize 2 * (D * D) * cost ps = A at hrun' ⊢
    generalize 2 * (D * D) * cost qs = B at hlow ⊢
    generalize D * D * (L * R.length) = C at hrun' hlow
    generalize 2 * (D * D) * (L * R.length) = C2 at hvar ⊢
    generalize (es.map fun e => fractionalLoad R e * fractionalLoad R e).sum = S at hrun' hlow
    generalize (es.map (varianceLoad D R)).sum = V at hrun' hvar
    have hAB : A ≤ B + V := by omega
    have hAB' := Nat.mul_le_mul_left (L + 2) hAB
    rw [Nat.mul_add] at hAB'
    omega
  have hpos : 0 < 2 * (D * D) := Nat.mul_pos (by decide) (Nat.mul_pos hD hD)
  have hmain' : 2 * (D * D) * ((L + 2) * cost ps) ≤ 2 * (D * D) * ((L + 2) * cost qs + L * R.length) := by
    have e : ∀ c : Nat, (L + 2) * (2 * (D * D) * c) = 2 * (D * D) * ((L + 2) * c) := by
      intro c; grind
    rw [e, e, ← Nat.mul_add] at hmain
    exact hmain
  exact Nat.le_of_mul_le_mul_left hmain' hpos

end STACS2027

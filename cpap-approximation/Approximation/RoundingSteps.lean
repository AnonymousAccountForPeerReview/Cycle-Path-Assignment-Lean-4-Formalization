module

public import Approximation.Rounding

/-!
The conditional-expectation step of Algorithm 2. Fixing a path `P` of the
current cycle changes the scaled expected sum of squared loads by
`2 D ∑_{e ∈ P} μ_e + D² |P|`, so the path of minimum expected load-sum
minimizes it; and the weighted average over the cycle's options of the
expected sums after fixing equals the expected sum before fixing. Hence no
step of Algorithm 2 increases the expected sum of squared loads.
-/

@[expose] public section
namespace STACS2027

/-- The options of every cycle of `R` are duplicate-free paths of `L` edges in `es`. -/
def OptionsIn (es : List Edge) (L : Nat) (R : List (List (List Edge) × List Nat)) : Prop :=
  ∀ r ∈ R, ∀ p ∈ r.1, p.Nodup ∧ p.length = L ∧ ∀ e ∈ p, e ∈ es

theorem OptionsIn.tail {es : List Edge} {L : Nat} {r : List (List Edge) × List Nat}
    {R : List (List (List Edge) × List Nat)} (h : OptionsIn es L (r :: R)) : OptionsIn es L R :=
  fun r' hr' => h r' (by simp [hr'])

theorem OptionsIn.head {es : List Edge} {L : Nat} {r : List (List Edge) × List Nat}
    {R : List (List (List Edge) × List Nat)} (h : OptionsIn es L (r :: R)) :
    ∀ p ∈ r.1, p.Nodup ∧ p.length = L ∧ ∀ e ∈ p, e ∈ es :=
  h r (by simp)

theorem FractionalSolution.tail {D : Nat} {r : List (List Edge) × List Nat}
    {R : List (List (List Edge) × List Nat)} (h : FractionalSolution D (r :: R)) :
    FractionalSolution D R :=
  ⟨h.1, fun r' hr' => h.2 r' (by simp [hr'])⟩

theorem FractionalSolution.head {D : Nat} {r : List (List Edge) × List Nat}
    {R : List (List (List Edge) × List Nat)} (h : FractionalSolution D (r :: R)) :
    r.2.length = r.1.length ∧ r.2.sum = D :=
  h.2 r (by simp)

theorem count_le_one_of_nodup {p : List Edge} (hp : p.Nodup) (e : Edge) : p.count e ≤ 1 :=
  List.nodup_iff_count.mp hp e

theorem count_sq_of_nodup {p : List Edge} (hp : p.Nodup) (e : Edge) :
    p.count e * p.count e = p.count e := by
  have h := count_le_one_of_nodup hp e
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h with h0 | h1
  · rw [h0]
  · rw [h1]

/-- `D p_{C,e} ≤ D`. -/
theorem optionLoad_le_sum {opts : List (List Edge)} {w : List Nat}
    (hn : ∀ p ∈ opts, p.Nodup) (hl : w.length = opts.length) (e : Edge) :
    optionLoad opts w e ≤ w.sum := by
  unfold optionLoad
  calc weightedSum (fun p => p.count e) opts w ≤ weightedSum (fun _ => 1) opts w :=
        weightedSum_le _ _ opts w (fun p hp => count_le_one_of_nodup (hn p hp) e)
    _ = w.sum := by rw [weightedSum_const 1 hl, Nat.mul_one]

/-- Edges outside every option of a cycle carry no weight. -/
theorem optionLoad_eq_zero {opts : List (List Edge)} (w : List Nat) {U : List Edge}
    (hs : ∀ p ∈ opts, ∀ e ∈ p, e ∈ U) {e : Edge} (he : e ∉ U) : optionLoad opts w e = 0 := by
  unfold optionLoad
  rw [weightedSum_congr (g := fun _ => 0) (fun p hp => ?_) w]
  · rw [← Nat.mul_zero 0, weightedSum_mul_left]; simp
  · exact List.count_eq_zero.mpr (fun h => he (hs p hp e h))

/-- `∑_e D p_{C,e} = D · (k − 2)`: every option has `L = k − 2` edges. -/
theorem sum_optionLoad {es : List Edge} (he : es.Nodup) {opts : List (List Edge)} {w : List Nat}
    {L : Nat} (hopt : ∀ p ∈ opts, p.length = L ∧ ∀ e ∈ p, e ∈ es) (hl : w.length = opts.length) :
    (es.map (optionLoad opts w)).sum = w.sum * L := by
  unfold optionLoad
  rw [← weightedSum_sum_swap (fun p e => p.count e) es opts w]
  rw [weightedSum_congr (g := fun _ => L) (fun p hp => ?_) w, weightedSum_const L hl]
  have h := sum_counts es p (fun _ => 1) he (hopt p hp).2
  simp only [Nat.mul_one] at h
  rw [h, sum_map_const, (hopt p hp).1, Nat.mul_one]

theorem fractionalLoad_cons (r : List (List Edge) × List Nat)
    (R : List (List (List Edge) × List Nat)) (e : Edge) :
    fractionalLoad (r :: R) e = optionLoad r.1 r.2 e + fractionalLoad R e := by
  simp [fractionalLoad]

theorem varianceLoad_cons (D : Nat) (r : List (List Edge) × List Nat)
    (R : List (List (List Edge) × List Nat)) (e : Edge) :
    varianceLoad D (r :: R) e =
      optionLoad r.1 r.2 e * (D - optionLoad r.1 r.2 e) + varianceLoad D R e := by
  simp [varianceLoad]

theorem meanLoad_snoc (D : Nat) (ps : List (List Edge)) (p : List Edge)
    (R : List (List (List Edge) × List Nat)) (e : Edge) :
    meanLoad D (ps ++ [p]) R e = meanLoad D ps R e + D * p.count e := by
  have hp : load [p] e = p.count e := by simp [load]
  simp only [meanLoad, load_append, hp, Nat.mul_add]
  omega

theorem meanLoad_cons_mem (D : Nat) (ps : List (List Edge)) (r : List (List Edge) × List Nat)
    (R : List (List (List Edge) × List Nat)) (e : Edge) :
    meanLoad D ps (r :: R) e = meanLoad D ps R e + optionLoad r.1 r.2 e := by
  simp only [meanLoad, fractionalLoad_cons]; omega

/-- The per-edge averaging identity: the weighted average, over the options `P` of the current
cycle, of `D²E[l(e)²]` after fixing `P` equals `D²E[l(e)²]` before fixing (times `D`, as the
weights sum to `D`). -/
theorem average_identity {D : Nat} {opts : List (List Edge)} {w : List Nat}
    (hn : ∀ p ∈ opts, p.Nodup) (hl : w.length = opts.length) (hw : w.sum = D)
    (ps : List (List Edge)) (R : List (List (List Edge) × List Nat)) (e : Edge) :
    weightedSum (fun p => meanLoad D (ps ++ [p]) R e * meanLoad D (ps ++ [p]) R e +
      varianceLoad D R e) opts w =
    D * (meanLoad D ps ((opts, w) :: R) e * meanLoad D ps ((opts, w) :: R) e +
      varianceLoad D ((opts, w) :: R) e) := by
  have hq : optionLoad opts w e ≤ D := hw ▸ optionLoad_le_sum hn hl e
  obtain ⟨d, hd⟩ := Nat.le.dest hq
  -- Expand the square after fixing `p` as a quadratic in `count e p`.
  have hexp : ∀ p ∈ opts, meanLoad D (ps ++ [p]) R e * meanLoad D (ps ++ [p]) R e +
      varianceLoad D R e =
      (meanLoad D ps R e * meanLoad D ps R e + varianceLoad D R e) +
        (2 * meanLoad D ps R e * D) * p.count e + (D * D) * (p.count e * p.count e) := by
    intro p _
    rw [meanLoad_snoc]
    grind
  rw [weightedSum_congr hexp w, weightedSum_add, weightedSum_add, weightedSum_mul_left,
    weightedSum_mul_left, weightedSum_const _ hl, hw,
    weightedSum_congr (g := fun p => p.count e) (fun p hp => count_sq_of_nodup (hn p hp) e) w]
  have hoq : weightedSum (fun p => p.count e) opts w = optionLoad opts w e := rfl
  rw [hoq, meanLoad_cons_mem, varianceLoad_cons]
  change _ = D * ((meanLoad D ps R e + optionLoad opts w e) *
    (meanLoad D ps R e + optionLoad opts w e) +
    (optionLoad opts w e * (D - optionLoad opts w e) + varianceLoad D R e))
  rw [← hd, Nat.add_sub_cancel_left]
  grind

/-- Fixing the path `p` changes the scaled expected sum of squared loads by
`2 D ∑_{e ∈ p} μ_e + D² |p|`. -/
theorem expectedSquares_snoc {es : List Edge} (he : es.Nodup) (D : Nat) (ps : List (List Edge))
    (R : List (List (List Edge) × List Nat)) {p : List Edge} (hp : p.Nodup)
    (hs : ∀ e ∈ p, e ∈ es) :
    expectedSquares D (ps ++ [p]) R es =
      expectedSquares D ps R es + 2 * D * meanLoadSum D ps R p + D * D * p.length := by
  unfold expectedSquares
  have hexp : ∀ e ∈ es, meanLoad D (ps ++ [p]) R e * meanLoad D (ps ++ [p]) R e +
      varianceLoad D R e =
      (meanLoad D ps R e * meanLoad D ps R e + varianceLoad D R e) +
        p.count e * (2 * D * meanLoad D ps R e) + p.count e * (D * D) := by
    intro e _
    rw [meanLoad_snoc]
    have := count_sq_of_nodup hp e
    grind
  rw [sum_map_congr es _ _ hexp, sum_map_add, sum_map_add,
    sum_counts es p _ he hs, sum_counts es p _ he hs, sum_map_const, sum_map_mul_left]
  unfold meanLoadSum
  grind

theorem expectedSquares_le_of_meanLoadSum_le {es : List Edge} (he : es.Nodup) (D : Nat)
    (ps : List (List Edge)) (R : List (List (List Edge) × List Nat)) {p q : List Edge}
    (hp : p.Nodup) (hps : ∀ e ∈ p, e ∈ es) (hq : q.Nodup) (hqs : ∀ e ∈ q, e ∈ es)
    (hl : p.length = q.length) (hle : meanLoadSum D ps R p ≤ meanLoadSum D ps R q) :
    expectedSquares D (ps ++ [p]) R es ≤ expectedSquares D (ps ++ [q]) R es := by
  rw [expectedSquares_snoc he D ps R hp hps, expectedSquares_snoc he D ps R hq hqs, hl]
  have := Nat.mul_le_mul_left (2 * D) hle
  omega

/-- The averaging identity summed over the edges. -/
theorem average_identity_sum {es : List Edge} {D : Nat} {opts : List (List Edge)} {w : List Nat}
    (hn : ∀ p ∈ opts, p.Nodup) (hl : w.length = opts.length) (hw : w.sum = D)
    (ps : List (List Edge)) (R : List (List (List Edge) × List Nat)) :
    weightedSum (fun p => expectedSquares D (ps ++ [p]) R es) opts w =
      D * expectedSquares D ps ((opts, w) :: R) es := by
  unfold expectedSquares
  rw [weightedSum_sum_swap (fun p e => meanLoad D (ps ++ [p]) R e * meanLoad D (ps ++ [p]) R e +
    varianceLoad D R e) es opts w, ← sum_map_mul_left]
  exact sum_map_congr es _ _ (fun e _ => average_identity hn hl hw ps R e)

/-- One step of Algorithm 2 does not increase the scaled expected sum of squared loads. -/
theorem expectedSquares_step {es : List Edge} (he : es.Nodup) {D : Nat} (hD : 0 < D)
    {opts : List (List Edge)} {w : List Nat} {L : Nat}
    (hopt : ∀ p ∈ opts, p.Nodup ∧ p.length = L ∧ ∀ e ∈ p, e ∈ es)
    (hl : w.length = opts.length) (hw : w.sum = D)
    (ps : List (List Edge)) (R : List (List (List Edge) × List Nat)) {p : List Edge}
    (hp : p ∈ opts) (hmin : ∀ q ∈ opts, meanLoadSum D ps R p ≤ meanLoadSum D ps R q) :
    expectedSquares D (ps ++ [p]) R es ≤ expectedSquares D ps ((opts, w) :: R) es := by
  have hn : ∀ q ∈ opts, q.Nodup := fun q hq => (hopt q hq).1
  have hmin' : ∀ q ∈ opts, expectedSquares D (ps ++ [p]) R es ≤
      expectedSquares D (ps ++ [q]) R es := by
    intro q hq
    exact expectedSquares_le_of_meanLoadSum_le he D ps R (hopt p hp).1 (hopt p hp).2.2
      (hopt q hq).1 (hopt q hq).2.2 ((hopt p hp).2.1.trans (hopt q hq).2.1.symm) (hmin q hq)
  have h := weightedSum_ge_min (fun q => expectedSquares D (ps ++ [q]) R es) hl hmin'
  rw [average_identity_sum hn hl hw ps R, hw] at h
  exact Nat.le_of_mul_le_mul_left h hD

/-- Along a run of Algorithm 2, the scaled expected sum of squared loads never increases: at the
end it is `D²` times the sum of squared loads of the output. -/
theorem RoundingRun.expectedSquares_le {es : List Edge} (he : es.Nodup) {D : Nat} {L : Nat}
    {acc : List (List Edge)} {R : List (List (List Edge) × List Nat)} {chosen : List (List Edge)}
    (hrun : RoundingRun D acc R chosen) (hopt : OptionsIn es L R) (hf : FractionalSolution D R) :
    expectedSquares D (acc ++ chosen) [] es ≤ expectedSquares D acc R es := by
  induction R generalizing acc chosen with
  | nil =>
    cases chosen with
    | nil => simp
    | cons _ _ => exact False.elim hrun
  | cons r R ih =>
    obtain ⟨opts, w⟩ := r
    cases chosen with
    | nil => exact False.elim hrun
    | cons p ps =>
      obtain ⟨hp, hmin, hrest⟩ := hrun
      have h₁ := ih hrest hopt.tail hf.tail
      rw [List.append_assoc, List.singleton_append] at h₁
      have h₂ := expectedSquares_step he hf.1 hopt.head hf.head.1 hf.head.2 acc R hp hmin
      exact Nat.le_trans h₁ h₂

/-- A run of Algorithm 2 chooses an option for every cycle. -/
theorem RoundingRun.valid {D : Nat} {acc : List (List Edge)}
    {R : List (List (List Edge) × List Nat)} {chosen : List (List Edge)}
    (h : RoundingRun D acc R chosen) : ValidChoices (R.map Prod.fst) chosen := by
  induction R generalizing acc chosen with
  | nil =>
    cases chosen with
    | nil => trivial
    | cons _ _ => exact False.elim h
  | cons r R ih =>
    obtain ⟨opts, w⟩ := r
    cases chosen with
    | nil => exact False.elim h
    | cons p ps => exact ⟨h.1, ih h.2.2⟩

/-- `conditionalRounding` is a run of Algorithm 2 whenever every cycle has an option. -/
theorem roundFrom_run (D : Nat) (acc : List (List Edge)) (R : List (List (List Edge) × List Nat))
    (h : ∀ r ∈ R, r.1 ≠ []) : RoundingRun D acc R (roundFrom D acc R) := by
  induction R generalizing acc with
  | nil => trivial
  | cons r R ih =>
    obtain ⟨opts, w⟩ := r
    show _ ∈ opts ∧ (∀ q ∈ opts, _ ≤ _) ∧ RoundingRun D _ R _
    exact ⟨chooseMin_mem _ (h (opts, w) (by simp)), chooseMin_le _ opts,
      ih _ (fun r' hr' => h r' (by simp [hr']))⟩

theorem conditionalRounding_run (D : Nat) (R : List (List (List Edge) × List Nat))
    (h : ∀ r ∈ R, r.1 ≠ []) : RoundingRun D [] R (conditionalRounding D R) :=
  roundFrom_run D [] R h

/-- With no cycle left, the scaled expected sum of squared loads is `D²` times the actual one. -/
theorem expectedSquares_nil (D : Nat) (ps : List (List Edge)) (es : List Edge) :
    expectedSquares D ps [] es = D * D * (es.map fun e => load ps e * load ps e).sum := by
  unfold expectedSquares
  rw [← sum_map_mul_left]
  apply sum_map_congr
  intro e _
  simp only [meanLoad, varianceLoad, fractionalLoad, List.map_nil, List.sum_nil, Nat.add_zero]
  grind

/-- Before any path is fixed, the scaled expected sum of squared loads is
`∑_e (D λ_e)² + D² ∑_e Var[l(e)]`. -/
theorem expectedSquares_start (D : Nat) (R : List (List (List Edge) × List Nat)) (es : List Edge) :
    expectedSquares D [] R es =
      (es.map fun e => fractionalLoad R e * fractionalLoad R e).sum +
        (es.map (varianceLoad D R)).sum := by
  unfold expectedSquares
  rw [← sum_map_add]
  apply sum_map_congr
  intro e _
  simp [meanLoad, load]

end STACS2027

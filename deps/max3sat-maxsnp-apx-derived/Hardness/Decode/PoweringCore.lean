module

public import OAI.Computability.UniqueGames.PCP.PoweringTableSemanticsLemmas

/-!
# Powering soundness for an arbitrary heavy decoding

`PoweringSoundness.rejection_lower_bound` and `PoweringGap.uniform_count_gap` are proved in the
vendored development for the labeling `PoweringOpinions.decoded`, which picks a most frequent
opinion with `Classical.choose`.  The proofs only use that the decoded letter has mass at
least `1 / |A|` among the sampled opinions.  This file restates them for an arbitrary
`dec : V → A` with that property, and in pointwise form: the bound is in terms of the number of
base constraints rejected by `dec` itself (`count_bound_of_mass`).

The proofs are adaptations of the vendored ones (`PoweringOpinions.matchFn`,
`decoded_modal_baseline`, `PoweringSoundness.witness_bit_eq`, `modal_witness_mean`,
`rejection_lower_bound`, `PoweringGap.uniform_count_gap`).
-/

@[expose] public section

namespace OAI.UniqueGamesTheorem.Foundations.PCP.Decode

noncomputable section

open scoped BigOperators
open PoweringWalks PoweringLabels PoweringOpinions PoweringTest
open SpectralReturn PoweringWitness PoweringMomentBound PoweringSoundness PoweringCounting
open PoweringMoment (bit hits)

variable {V D A : Type*}

/-- Indicator that the opinion of `v` about `u` is the decoded letter of `u`. -/
def matchWith (G : PortGraph V D) (t : Nat)
    (selectors : ∀ v, AddressSelector G t v) (labels : V → PaddedLabel D t A)
    (fallback : A) (dec : V → A) (u v : V) : ℝ :=
  bit (opinionAt G t selectors labels fallback u v = dec u)

theorem matchWith_mem_Icc (G : PortGraph V D) (t : Nat)
    (selectors : ∀ v, AddressSelector G t v) (labels : V → PaddedLabel D t A)
    (fallback : A) (dec : V → A) (u v : V) :
    matchWith G t selectors labels fallback dec u v ∈ Set.Icc (0 : ℝ) 1 := by
  classical
  constructor
  · exact PoweringMoment.bit_nonneg _
  · unfold matchWith bit
    split <;> simp

variable [Fintype D] [Nonempty D] [Fintype A] [Nonempty A]

omit [Nonempty A] in
/-- The mass hypothesis is the reference-length modal lower bound. -/
theorem modal_baseline_of_mass (G : PortGraph V D) (t N : Nat)
    (selectors : ∀ v, AddressSelector G t v) (labels : V → PaddedLabel D t A)
    (fallback : A) (dec : V → A) (u : V)
    (hmass : 1 / (Fintype.card A : ℝ) ≤
      PoweringDecoding.mass (sampleOpinion G t N selectors labels fallback u) (dec u)) :
    1 / (Fintype.card A : ℝ) ≤
      iterateOperator G N (matchWith G t selectors labels fallback dec u) u := by
  have h := hmass
  change 1 / (Fintype.card A : ℝ) ≤ mean (fun p : Fin N → D =>
    matchWith G t selectors labels fallback dec u (wordEnd G N u p)) at h
  rwa [PoweringReturn.mean_wordEnd] at h

omit [Fintype D] [Nonempty D] [Fintype A] [Nonempty A] in
theorem witness_bit_eq_matchWith (G : PortGraph V D) (accepts : Edge V D → A → A → Bool)
    (n : Nat) (selectors : ∀ v, AddressSelector G (n + 1) v)
    (labels : V → PaddedLabel D (n + 1) A) (fallback : A) (dec : V → A)
    (w : Walk V D (n + 1)) (k : Fin (n + 1)) :
    bit (witness G accepts n selectors labels fallback dec w k) =
      vertexWitness G (decodedBad G accepts dec)
        (matchWith G (n + 1) selectors labels fallback dec) n k w := by
  simp only [witness, vertexWitness, endpointWitness, matchWith,
    PoweringMoment.bit_mul, next, and_assoc]

variable [Fintype V]

theorem modal_witness_mean_of_mass (G : PortGraph V D) (M : Nat) (hM : 1 ≤ M)
    (accepts : Edge V (Bool × D) → A → A → Bool)
    (selectors : ∀ v, AddressSelector (lazyGraph G) (2 * center (Fintype.card A) M + 1) v)
    (labels : V → PaddedLabel (Bool × D) (2 * center (Fintype.card A) M + 1) A)
    (fallback : A) (dec : V → A)
    (hmass : ∀ u, 1 / (Fintype.card A : ℝ) ≤
      PoweringDecoding.mass (sampleOpinion (lazyGraph G) (2 * center (Fintype.card A) M + 1)
        (center (Fintype.card A) M) selectors labels fallback u) (dec u))
    (k : Fin (2 * center (Fintype.card A) M + 1))
    (hlo : center (Fintype.card A) M - M ≤ k.val)
    (hhi : k.val ≤ center (Fintype.card A) M + M) :
    edgeDensity (decodedBad (lazyGraph G) accepts dec) / (4 * (Fintype.card A : ℝ) ^ 2) ≤
      mean (fun w => bit (witness (lazyGraph G) accepts (2 * center (Fintype.card A) M)
        selectors labels fallback dec w k)) := by
  have h := lazy_middle_witness_mean G (Fintype.card A) M Fintype.card_pos hM k hlo hhi
    (decodedBad (lazyGraph G) accepts dec)
    (matchWith (lazyGraph G) (2 * center (Fintype.card A) M + 1) selectors labels fallback dec)
    (matchWith_mem_Icc (lazyGraph G) (2 * center (Fintype.card A) M + 1)
      selectors labels fallback dec)
    (fun u => modal_baseline_of_mass (lazyGraph G) (2 * center (Fintype.card A) M + 1)
      (center (Fintype.card A) M) selectors labels fallback dec u (hmass u))
  simp_rw [witness_bit_eq_matchWith]
  convert h using 1
  rfl

variable [Nonempty V]

/-- `PoweringSoundness.rejection_lower_bound` for an arbitrary decoding whose letters have
mass at least `1 / |A|` among the opinions sampled by lazy walks of the reference length. -/
theorem rejection_lower_bound_of_mass (G : PortGraph V D) (lambda : ℝ)
    (certificate : SpectralCertificate (lazyGraph G) lambda)
    (accepts : Edge V (Bool × D) → A → A → Bool)
    (reverse_accepts : ∀ e a b, accepts ((lazyGraph G).rot e) b a = accepts e a b)
    (M : Nat) (hM : 1 ≤ M)
    (selectors : ∀ v, AddressSelector (lazyGraph G) (2 * center (Fintype.card A) M + 1) v)
    (labels : V → PaddedLabel (Bool × D) (2 * center (Fintype.card A) M + 1) A)
    (fallback : A) (dec : V → A)
    (hmass : ∀ u, 1 / (Fintype.card A : ℝ) ≤
      PoweringDecoding.mass (sampleOpinion (lazyGraph G) (2 * center (Fintype.card A) M + 1)
        (center (Fintype.card A) M) selectors labels fallback u) (dec u))
    (hε : 0 < edgeDensity (decodedBad (lazyGraph G) accepts dec)) :
    gain (Fintype.card A) M lambda *
        min (edgeDensity (decodedBad (lazyGraph G) accepts dec))
          (1 / ((2 * center (Fintype.card A) M + 1 : Nat) : ℝ)) ≤
      poweredRejection (lazyGraph G) accepts (2 * center (Fintype.card A) M) selectors labels := by
  let q := Fintype.card A
  let N := center q M
  let n := 2 * N
  let m := 2 * M + 1
  let start := N - M
  let L := lazyGraph G
  let assignment := dec
  let bad := decodedBad L accepts assignment
  let ε := edgeDensity bad
  let α : ℝ := 1 / (2 * (q : ℝ))
  let C : ℝ := 1 + 2 / (1 - lambda)
  have hNM : M ≤ N := le_center q M Fintype.card_pos hM
  have hw : start + m ≤ n + 1 := by dsimp [start, m, n]; omega
  let E := windowEvent L bad n start m hw
  let W : Fin m → Walk V (Bool × D) (n + 1) → Prop := fun i w =>
    witness L accepts n selectors labels fallback assignment w (windowIndex n start m hw i)
  let R : Walk V (Bool × D) (n + 1) → Prop := fun w =>
    pathAccepts L accepts n selectors w (labels w.1) (labels (endpoint L w)) = false
  have hWE : ∀ i w, W i w → E i w := by
    intro i w h
    exact h.1
  have hWR : ∀ i w, W i w → R w := by
    intro i w h
    exact witness_implies_path_rejection L accepts n selectors labels fallback assignment w
      (windowIndex n start m hw i) h
  have hpoint (i : Fin m) : ε / (4 * (q : ℝ) ^ 2) ≤ mean (fun w => bit (W i w)) := by
    have hlo : N - M ≤ (windowIndex n start m hw i).val := by
      dsimp [windowIndex, start]
      omega
    have hhi : (windowIndex n start m hw i).val ≤ N + M := by
      have hi := i.isLt
      dsimp [windowIndex, start]
      dsimp [m] at hi
      omega
    exact modal_witness_mean_of_mass G M hM accepts selectors labels fallback dec hmass
      (windowIndex n start m hw i) hlo hhi
  have hfirst : α ^ 2 * (m : ℝ) * ε ≤ mean (hits W) := by
    change α ^ 2 * (m : ℝ) * ε ≤ PoweringMoment.mean (hits W)
    rw [PoweringMoment.mean_hits]
    calc
      _ = ∑ _i : Fin m, ε / (4 * (q : ℝ) ^ 2) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        dsimp [α]
        ring
      _ ≤ _ := Finset.sum_le_sum (fun i _ => hpoint i)
  have hsecond : mean (fun w => hits E w ^ 2) ≤
      (m : ℝ) * ε * (C + ((m : ℝ) - 1) * ε) :=
    window_second_moment_le L lambda certificate bad
      (decodedBad_rot L accepts reverse_accepts assignment) n start m hw
  have hε' : 0 < ε := hε
  have hm : 0 < m := by dsimp [m]; omega
  have hmReal : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hqReal : (0 : ℝ) < q := Nat.cast_pos.mpr Fintype.card_pos
  have hden : 0 < 1 - lambda := sub_pos.mpr certificate.lt_one
  have hC : 0 < C := by dsimp [C]; positivity
  have hmOne : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hα : 0 < α := by dsimp [α]; positivity
  have ha : 0 < α ^ 2 * (m : ℝ) * ε := by positivity
  have hb : 0 < (m : ℝ) * ε * (C + ((m : ℝ) - 1) * ε) := by
    have hdiff : 0 ≤ (m : ℝ) - 1 := sub_nonneg.mpr hmOne
    positivity
  have hCS := PoweringMoment.rejection_lower_bound E W R hWE hWR
    (α ^ 2 * (m : ℝ) * ε) ((m : ℝ) * ε * (C + ((m : ℝ) - 1) * ε))
    ha hb hfirst hsecond
  have ht : (0 : ℝ) < ((n + 1 : Nat) : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos n)
  have hmn : m ≤ n + 1 := by dsimp [m, n]; omega
  have hmt : (m : ℝ) - 1 ≤ ((n + 1 : Nat) : ℝ) := by
    have hmnReal : (m : ℝ) ≤ ((n + 1 : Nat) : ℝ) := by exact_mod_cast hmn
    linarith
  have hratio := PoweringNumeric.count_moment_ratio_lower α ε C ((n + 1 : Nat) : ℝ)
    m hm hε' hC ht hmt
  change (α ^ 4 * (m : ℝ) / (C + 1)) * min ε (1 / ((n + 1 : Nat) : ℝ)) ≤ _
  change _ ≤ mean (fun d : Dart V (Bool × D) n =>
    bit ((poweredGraph L accepts n selectors).edgeSatisfied labels d = false))
  rw [rejection_mean_eq_path_mean]
  exact hratio.trans hCS

/-- Pointwise count form: the powered graph rejects at least `gain · min(ε, cap)` of its darts
under `labels`, where `ε` is the fraction of base darts rejected by the decoding `dec`. -/
theorem count_bound_of_mass (G : PortGraph V D) (lambda : ℝ)
    (certificate : SpectralCertificate (lazyGraph G) lambda)
    (accepts : Edge V (Bool × D) → A → A → Bool)
    (reverse_accepts : ∀ e a b, accepts ((lazyGraph G).rot e) b a = accepts e a b)
    (M : Nat) (hM : 1 ≤ M)
    (selectors : ∀ v, AddressSelector (lazyGraph G)
      (2 * center (Fintype.card A) M + 1) v)
    (labels : V → PaddedLabel (Bool × D) (2 * center (Fintype.card A) M + 1) A)
    (fallback : A) (dec : V → A)
    (hmass : ∀ u, 1 / (Fintype.card A : ℝ) ≤
      PoweringDecoding.mass (sampleOpinion (lazyGraph G) (2 * center (Fintype.card A) M + 1)
        (center (Fintype.card A) M) selectors labels fallback u) (dec u)) :
    (gain (Fintype.card A) M lambda *
      min (((baseGraph (lazyGraph G) accepts reverse_accepts).rejectionCount dec : ℝ) /
          (Fintype.card (Edge V (Bool × D)) : ℝ))
        (1 / ((2 * center (Fintype.card A) M + 1 : Nat) : ℝ))) *
        (Fintype.card (Dart V (Bool × D) (2 * center (Fintype.card A) M)) : ℝ) ≤
      ((poweredGraph (lazyGraph G) accepts (2 * center (Fintype.card A) M)
        selectors).rejectionCount labels : ℝ) := by
  classical
  let L := lazyGraph G
  let N := center (Fintype.card A) M
  let n := 2 * N
  let H := poweredGraph L accepts n selectors
  rw [← base_edgeDensity_eq_rejection_count L accepts reverse_accepts dec]
  change (gain (Fintype.card A) M lambda *
      min (edgeDensity (decodedBad L accepts dec)) (1 / ((n + 1 : Nat) : ℝ))) *
        (Fintype.card (Dart V (Bool × D) n) : ℝ) ≤
      (H.rejectionCount labels : ℝ)
  have hnonneg : 0 ≤ edgeDensity (decodedBad L accepts dec) := by
    rw [base_edgeDensity_eq_rejection_count L accepts reverse_accepts dec]
    positivity
  rcases eq_or_lt_of_le hnonneg with hzero | hpositive
  · rw [← hzero]
    have hcap : (0 : ℝ) ≤ 1 / ((n + 1 : Nat) : ℝ) := by positivity
    rw [min_eq_left hcap, mul_zero, zero_mul]
    exact Nat.cast_nonneg _
  · have hsound := rejection_lower_bound_of_mass G lambda certificate
      accepts reverse_accepts M hM selectors labels fallback dec hmass hpositive
    exact (constraint_rejection_lower_iff H labels Fintype.card_pos
      (gain (Fintype.card A) M lambda *
        min (edgeDensity (decodedBad L accepts dec)) (1 / ((n + 1 : Nat) : ℝ)))).mp hsound

end

end OAI.UniqueGamesTheorem.Foundations.PCP.Decode

module

public import Hardness.Decode.Cloud
public import Hardness.Decode.PoweringTable
public import Hardness.Decode.Alphabet
public import OAI.Computability.UniqueGames.PCP.RawInitialTablesLemmas

/-!
# Decoding one amplification round

`roundDecode H t L` turns a labeling `L` of the round output `RoundTables.build H t` into a
labeling of the round input `t`, by composing the three stage decoders:

1. `alphabetDecode` (least nearest long-code word) gives a labeling of
   `RoundTables.powered H t` with labels in `Fin RoundTables.alphabet`;
2. `powerDecode` (least most frequent opinion over the walks of `FinalConstants.endpointLength`
   steps in `PreprocessingTables.preprocess H t`) gives a labeling of the preprocessed table;
3. `roundPreprocessed` (restriction to the regular vertices, then least most frequent label of
   every padded cloud) gives the labeling of `t`.

`roundDecode_bound` is the pointwise form of `RoundTableGap.build_count_gap`: with
`viol = rejectionCount / darts`,
`min (2 * viol_t (roundDecode H t L)) cap ≤ viol_(build H t) L`.
-/

@[expose] public section

namespace OAI.UniqueGamesTheorem.Foundations.PCP.Decode

noncomputable section

open RoundTables PoweringWalks SpectralReturn

/-- The decoder of one round. -/
def roundDecode (H : BaseTable) (t : GraphTables.Table)
    (L : Fin (build H t).vertices → GraphTables.Label) : Fin t.vertices → GraphTables.Label :=
  roundPreprocessed t
    (powerDecode (PreprocessingTables.preprocess H t) walkParameter
      FinalConstants.endpointLength
      (alphabetDecode alphabet_positive (powered H t) L))

/-- Pointwise soundness of one round, in count form. -/
theorem roundDecode_bound (H : BaseTable)
    (certificate : SpectralCertificate (ExpanderTables.graph H) (1 / 100 : ℝ))
    (t : GraphTables.Table) (ht : 0 < t.darts)
    (L : Fin (build H t).vertices → GraphTables.Label) :
    min (2 * (((GraphTables.semantics t).rejectionCount (roundDecode H t L) : ℝ) /
        (t.darts : ℝ))) FinalConstants.cap * ((build H t).darts : ℝ) ≤
      ((GraphTables.semantics (build H t)).rejectionCount L : ℝ) := by
  let old := PreprocessingOverlayTables.overlay
    (PreprocessingTables.padded H t) (PreprocessingTables.overlayFamily H t)
  have hd : 0 < (PreprocessingRegularTables.internalDegree + 1) +
      PreprocessingRegularTables.internalDegree := by omega
  let : Nonempty (Fin ((PreprocessingRegularTables.internalDegree + 1) +
      PreprocessingRegularTables.internalDegree)) := ⟨⟨0, hd⟩⟩
  have spectral : SpectralCertificate (lazyGraph (PortTables.portGraph old)) (31 / 32 : ℝ) :=
    LazySpectral.lazy_certificate_31_32 (PortTables.portGraph old)
      (PreprocessingGuarantees.overlay_certificate H certificate t)
  have hn : walkParameter = 2 * PoweringSoundness.center 64 FinalConstants.windowHalf :=
    walkParameter_eq
  have hw : walkParameter + 1 = FinalConstants.walkLength := by
    rw [walkParameter_eq]
    rfl
  -- the three stage labelings
  let ell : Fin (powered H t).vertices → Fin alphabet :=
    alphabetDecode alphabet_positive (powered H t) L
  let sigma : Fin (PreprocessingTables.vertices t) → GraphTables.Label :=
    powerDecode (PreprocessingTables.preprocess H t) walkParameter
      FinalConstants.endpointLength ell
  -- stage bounds
  have hround : (GraphTables.semantics t).rejectionCount (roundDecode H t L) ≤
      (PortTables.baseGraph (PreprocessingTables.preprocess H t)).rejectionCount sigma :=
    roundPreprocessed_soundness H certificate t sigma
  have hpow : (PoweringSoundness.gain 64 FinalConstants.windowHalf (31 / 32) *
      min (((PortTables.baseGraph (PreprocessingTables.preprocess H t)).rejectionCount sigma : ℝ) /
          ((PreprocessingTables.vertices t * PreprocessingTables.degree : Nat) : ℝ))
        (1 / ((walkParameter + 1 : Nat) : ℝ))) * ((powered H t).darts : ℝ) ≤
      ((GenericGraphTables.semantics (powered H t)).rejectionCount ell : ℝ) :=
    powerDecode_bound old (PreprocessingTables.vertices_positive t) hd (31 / 32) spectral
      FinalConstants.windowHalf FinalConstants.windowHalf_positive walkParameter hn ell
  have halph : AlphabetGraphBounds.localEventFactor alphabet *
      (GenericGraphTables.semantics (powered H t)).rejectionCount ell ≤
      1024 * (GraphTables.semantics (build H t)).rejectionCount L :=
    alphabetDecode_bound alphabet_positive (powered H t) L
  have hdarts : (build H t).darts =
      (powered H t).darts * (12 * AlphabetGraphBounds.localEventFactor alphabet) :=
    AlphabetTableBounds.build_darts (powered H t)
  have hcount : PreprocessingTables.vertices t * PreprocessingTables.degree ≤
      Preprocessing.sizeFactor * t.darts := by
    calc
      _ ≤ (ExpanderFamily.growth ^ 2 * t.darts) * PreprocessingTables.degree :=
        Nat.mul_le_mul_right _ (PreprocessingTables.vertices_le_of_positive t ht)
      _ = _ := by
        rw [PreprocessingTables.degree_eq]; unfold Preprocessing.sizeFactor; ring
  have hVD : 0 < PreprocessingTables.vertices t * PreprocessingTables.degree :=
    Nat.mul_pos (PreprocessingTables.vertices_positive t) degree_positive
  -- real arithmetic
  generalize (GraphTables.semantics t).rejectionCount (roundDecode H t L) = r at hround ⊢
  generalize (PortTables.baseGraph (PreprocessingTables.preprocess H t)).rejectionCount sigma =
    rP at hround hpow
  generalize (GenericGraphTables.semantics (powered H t)).rejectionCount ell = rPw at hpow halph
  generalize (GraphTables.semantics (build H t)).rejectionCount L = rT at halph ⊢
  rw [hdarts]
  generalize (powered H t).darts = W at hpow ⊢
  generalize AlphabetGraphBounds.localEventFactor alphabet = F at halph ⊢
  generalize PreprocessingTables.vertices t * PreprocessingTables.degree = VD at hpow hcount hVD
  rw [hw] at hpow
  have hm : (0 : ℝ) < t.darts := Nat.cast_pos.mpr ht
  have hS : (0 : ℝ) < Preprocessing.sizeFactor :=
    Nat.cast_pos.mpr Preprocessing.sizeFactor_positive
  have hVDr : (0 : ℝ) < VD := Nat.cast_pos.mpr hVD
  have hr : (r : ℝ) ≤ rP := Nat.cast_le.mpr hround
  have hcountr : (VD : ℝ) ≤ (Preprocessing.sizeFactor : ℝ) * t.darts := by exact_mod_cast hcount
  have hε : (0 : ℝ) ≤ (r : ℝ) / t.darts := by positivity
  have hfrac : (r : ℝ) / t.darts / Preprocessing.sizeFactor ≤ (rP : ℝ) / VD := by
    rw [div_div, div_le_div_iff₀ (mul_pos hm hS) hVDr]
    calc (r : ℝ) * VD ≤ rP * ((Preprocessing.sizeFactor : ℝ) * t.darts) :=
          mul_le_mul hr hcountr hVDr.le (Nat.cast_nonneg _)
      _ = rP * (t.darts * Preprocessing.sizeFactor) := by ring
  have hgain : 0 ≤ FinalConstants.gain :=
    (mul_nonneg zero_le_two (Nat.cast_nonneg _)).trans FinalConstants.gain_large
  have hscalar : min (2 * ((r : ℝ) / t.darts)) FinalConstants.cap ≤
      FinalConstants.gain * min ((rP : ℝ) / VD) (1 / (FinalConstants.walkLength : ℝ)) :=
    (FinalConstants.composed_gap _ hε).trans
      (mul_le_mul_of_nonneg_left (min_le_min hfrac le_rfl) hgain)
  rw [← PoweringFinalConstants.gain_eq] at hscalar
  have halphr : (F : ℝ) * rPw ≤ 1024 * rT := by exact_mod_cast halph
  have hWF : (0 : ℝ) ≤ (W : ℝ) * (12 * F) := by positivity
  push_cast
  calc min (2 * ((r : ℝ) / t.darts)) FinalConstants.cap * ((W : ℝ) * (12 * F))
      ≤ (PoweringSoundness.gain 64 FinalConstants.windowHalf (31 / 32) / 12288 *
          min ((rP : ℝ) / VD) (1 / (FinalConstants.walkLength : ℝ))) * ((W : ℝ) * (12 * F)) :=
        mul_le_mul_of_nonneg_right hscalar hWF
    _ = ((PoweringSoundness.gain 64 FinalConstants.windowHalf (31 / 32) *
          min ((rP : ℝ) / VD) (1 / (FinalConstants.walkLength : ℝ))) * W) * F / 1024 := by ring
    _ ≤ (rPw : ℝ) * F / 1024 := by
        apply div_le_div_of_nonneg_right _ (by norm_num)
        exact mul_le_mul_of_nonneg_right hpow (Nat.cast_nonneg _)
    _ ≤ rT := by
        rw [div_le_iff₀ (by norm_num)]
        linarith

/-- Pointwise soundness of one round, for violated fractions:
`min (2 * viol_t (roundDecode H t L)) cap ≤ viol_(build H t) L`. -/
theorem roundDecode_viol (H : BaseTable)
    (certificate : SpectralCertificate (ExpanderTables.graph H) (1 / 100 : ℝ))
    (t : GraphTables.Table) (ht : 0 < t.darts)
    (L : Fin (build H t).vertices → GraphTables.Label) :
    min (2 * (((GraphTables.semantics t).rejectionCount (roundDecode H t L) : ℝ) /
        (t.darts : ℝ))) FinalConstants.cap ≤
      ((GraphTables.semantics (build H t)).rejectionCount L : ℝ) /
        ((build H t).darts : ℝ) := by
  rw [le_div_iff₀ (Nat.cast_pos.mpr (build_darts_positive H t))]
  exact roundDecode_bound H certificate t ht L

end

end OAI.UniqueGamesTheorem.Foundations.PCP.Decode

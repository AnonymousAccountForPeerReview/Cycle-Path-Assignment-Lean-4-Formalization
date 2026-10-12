module

public import Hardness.Decode.Selectors
public import OAI.Computability.UniqueGames.PCP.PreprocessingTablesLemmas

/-!
# Decoding the preprocessing stage: least most-frequent label of each padded cloud

`roundPreprocessed t labels` turns a labeling of the preprocessed port table
`PreprocessingTables.preprocess H t` (vertices `Fin (PreprocessingTables.vertices t)`) into a
labeling of the table `t`:

1. restrict to the first `regularVertices t` vertices (the vertices of `regularize H t`; the
   remaining ones are padding vertices);
2. the label of an original vertex `v` is the least `a : Fin 64` maximising
   `cloudCount t labels v a`, the number of regular vertices `z` owned by `v`
   (`regularOwner t z = v`) with `labels z = a`.

The pointwise soundness statement is `roundPreprocessed_soundness`: the decoded labeling
rejects at most as many darts of `t` as `labels` rejects darts of `preprocess H t`.

The proofs are those of `CloudRounding.rounded_mismatch_expansion`, `replacement_soundness`,
`padded_replacement_soundness`, `PreprocessingRegularSoundness.soundness` and
`PreprocessingGuarantees.soundness`, with the rounding function abstracted to any function
choosing a most frequent colour in every cloud.
-/

@[expose] public section

namespace OAI.UniqueGamesTheorem.Foundations.PCP.Decode

open DegreeReplacement PoweringWalks SpectralReturn CloudRounding

section Generic

variable {V E A D : Type*} [Fintype V] [Fintype E] [Fintype A] [Fintype D]
variable [DecidableEq V] [DecidableEq E] [DecidableEq A]

/-- `CloudRounding.rounded_mismatch_expansion` for an arbitrary rounding that picks a most
frequent colour in every cloud. -/
theorem rounded_mismatch_expansion_of_maximal
    (G : ConstraintGraph V E A) (H : ∀ v, PortGraph (Cloud G v) D)
    (ell : E → A) (rounded : V → A) (h : ℚ)
    (maximal : ∀ v a, (colorSet (fun e : Cloud G v => ell e.val) a).card ≤
      (colorSet (fun e : Cloud G v => ell e.val) (rounded v)).card)
    (expansion : ∀ v (S : Finset (Cloud G v)),
      S.card ≤ Fintype.card (Cloud G v) / 2 →
      h * (S.card : ℚ) ≤ ((directedCut (fun ed => ((H v).rot ed).1) S).card : ℚ)) :
    h * ((mismatchSet G ell rounded).card : ℚ) ≤
      ((innerDisagreementSet G H ell).card : ℚ) := by
  rw [mismatch_card_eq_sum, disagreement_card_eq_sum, Nat.cast_sum, Nat.cast_sum,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v _
  exact minority_expansion_bound (fun e : Cloud G v => ell e.val)
    (fun ed => ((H v).rot ed).1) (rounded v) h (maximal v) (expansion v)

/-- `CloudRounding.replacement_soundness` for an arbitrary rounding that picks a most
frequent colour in every cloud. -/
theorem replacement_soundness_of_maximal
    (G : ConstraintGraph V E A) (H : ∀ v, PortGraph (Cloud G v) D)
    (expansion : ∀ v (S : Finset (Cloud G v)),
      S.card ≤ Fintype.card (Cloud G v) / 2 →
      2 * S.card ≤ (directedCut (fun ed => ((H v).rot ed).1) S).card)
    (ell : E → A) (rounded : V → A)
    (maximal : ∀ v a, (colorSet (fun e : Cloud G v => ell e.val) a).card ≤
      (colorSet (fun e : Cloud G v => ell e.val) (rounded v)).card) :
    G.rejectionCount rounded ≤ (replacementGraph G H).rejectionCount ell := by
  have hc := rounded_mismatch_expansion_of_maximal G H ell rounded 2 maximal (by
    intro v S hS
    exact_mod_cast expansion v S hS)
  have hcNat : 2 * (mismatchSet G ell rounded).card ≤
      (innerDisagreementSet G H ell).card := by exact_mod_cast hc
  rw [replacement_rejection_split]
  exact (rounded_endpoint_bound G ell rounded).trans (Nat.add_le_add_left hcNat _)

/-- `CloudRounding.padded_replacement_soundness` for an arbitrary rounding that picks a most
frequent colour in every padded cloud. -/
theorem padded_replacement_soundness_of_maximal
    (G : ConstraintGraph V E A) (dummy : V → Type*) [∀ v, Fintype (dummy v)]
    [∀ v, DecidableEq (dummy v)]
    (H : ∀ v, PortGraph (Cloud (paddedGraph G dummy) v) D)
    (expansion : ∀ v (S : Finset (Cloud (paddedGraph G dummy) v)),
      S.card ≤ Fintype.card (Cloud (paddedGraph G dummy) v) / 2 →
      2 * S.card ≤ (directedCut (fun ed => ((H v).rot ed).1) S).card)
    (ell : PaddedDart G dummy → A) (rounded : V → A)
    (maximal : ∀ v a,
      (colorSet (fun e : Cloud (paddedGraph G dummy) v => ell e.val) a).card ≤
      (colorSet (fun e : Cloud (paddedGraph G dummy) v => ell e.val) (rounded v)).card) :
    G.rejectionCount rounded ≤ (paddedReplacementGraph G dummy H).rejectionCount ell := by
  simpa only [paddedReplacementGraph, padded_rejectionCount] using
    replacement_soundness_of_maximal (paddedGraph G dummy) H expansion ell rounded maximal

end Generic

open PreprocessingRegularTables PreprocessingTables

/-- The original vertex owning a vertex of the regularised table: the tail of the dart for an
original dart `z < t.darts`, and the vertex `v` for the dummy darts added to the cloud of `v`. -/
def regularOwner (t : GraphTables.Table) (z : Fin (vertexCount t (padding t))) :
    Fin t.vertices :=
  paddedOwner (GraphTables.semantics t) (fun v => Fin (padding t v))
    ((vertexOrder t (padding t)).symm z)

/-- An original dart `e` (regular vertex number `e`) is owned by its tail. -/
theorem regularOwner_original (t : GraphTables.Table) (e : Fin t.darts) :
    regularOwner t (vertexOrder t (padding t) (Sum.inl e)) = t.rows[e].tail := by
  unfold regularOwner
  rw [Equiv.symm_apply_apply]
  rfl

/-- The `k`-th dummy dart of `v` (regular vertex number
`t.darts + offset (padding t) v + k`, see `PreprocessingPaddingOffsets.vertexOrder_dummy_val`)
is owned by `v`. -/
theorem regularOwner_dummy (t : GraphTables.Table) (v : Fin t.vertices)
    (k : Fin (padding t v)) :
    regularOwner t (vertexOrder t (padding t) (Sum.inr ⟨v, k⟩)) = v := by
  unfold regularOwner
  rw [Equiv.symm_apply_apply]
  rfl

/-- Number of vertices of the padded cloud of `v` carrying the label `a`. -/
def cloudCount (t : GraphTables.Table)
    (labels : Fin (vertexCount t (padding t)) → GraphTables.Label)
    (v : Fin t.vertices) (a : GraphTables.Label) : Nat :=
  (Finset.univ.filter (fun z : Fin (vertexCount t (padding t)) =>
    regularOwner t z = v ∧ labels z = a)).card

/-- Stage decoder for regularisation: the least most frequent label of every padded cloud. -/
def roundRegular (t : GraphTables.Table)
    (labels : Fin (vertexCount t (padding t)) → GraphTables.Label) :
    Fin t.vertices → GraphTables.Label :=
  fun v => leastArgMax (by decide : 0 < 64) (cloudCount t labels v)

theorem cloudCount_eq_colorSet (t : GraphTables.Table)
    (labels : Fin (vertexCount t (padding t)) → GraphTables.Label)
    (v : Fin t.vertices) (a : GraphTables.Label) :
    (colorSet (fun e : Cloud (paddedGraph (GraphTables.semantics t)
        (fun v => Fin (padding t v))) v => labels (vertexOrder t (padding t) e.val)) a).card =
      cloudCount t labels v a := by
  classical
  unfold cloudCount colorSet
  apply Finset.card_bij (fun e _ => vertexOrder t (padding t) e.val)
  · intro e he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
    refine ⟨?_, he⟩
    unfold regularOwner
    rw [Equiv.symm_apply_apply]
    exact e.property
  · intro e _ f _ h
    exact Subtype.ext ((vertexOrder t (padding t)).injective h)
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
    refine ⟨⟨(vertexOrder t (padding t)).symm z, hz.1⟩, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.apply_symm_apply]
      exact hz.2
    · exact (vertexOrder t (padding t)).apply_symm_apply z

theorem roundRegular_maximal (t : GraphTables.Table)
    (labels : Fin (vertexCount t (padding t)) → GraphTables.Label)
    (v : Fin t.vertices) (a : GraphTables.Label) :
    cloudCount t labels v a ≤ cloudCount t labels v (roundRegular t labels v) :=
  leastArgMax_max _ _ a

/-- Pointwise soundness of regularisation with the deterministic rounding. -/
theorem roundRegular_soundness (H : PreprocessingTables.BaseTable)
    (certificate : SpectralCertificate (ExpanderTables.graph H) (1 / 100 : ℝ))
    (t : GraphTables.Table)
    (labels : Fin (vertexCount t (padding t)) → GraphTables.Label) :
    (GraphTables.semantics t).rejectionCount (roundRegular t labels) ≤
      (PortTables.baseGraph (regularize H t)).rejectionCount labels := by
  rw [regularize, rejectionCount_ofCloudTables]
  apply padded_replacement_soundness_of_maximal (GraphTables.semantics t)
    (fun v => Fin (padding t v)) (cloudGraphs t (padding t) (familyCloudTable H t))
    (PreprocessingRegularSoundness.cloud_expansion H certificate t)
    (fun z => labels (vertexOrder t (padding t) z)) (roundRegular t labels)
  intro v a
  rw [cloudCount_eq_colorSet, cloudCount_eq_colorSet]
  exact roundRegular_maximal t labels v a

/-- Stage decoder for the whole preprocessing (regularise, pad, overlay, lazy): restrict to the
regular vertices, then take the least most frequent label of every padded cloud. -/
def roundPreprocessed (t : GraphTables.Table)
    (labels : Fin (vertices t) → GraphTables.Label) : Fin t.vertices → GraphTables.Label :=
  roundRegular t (PreprocessingGuarantees.restrictedLabel t labels)

/-- Pointwise soundness of preprocessing with the deterministic rounding. -/
theorem roundPreprocessed_soundness (H : PreprocessingTables.BaseTable)
    (certificate : SpectralCertificate (ExpanderTables.graph H) (1 / 100 : ℝ))
    (t : GraphTables.Table) (labels : Fin (vertices t) → GraphTables.Label) :
    (GraphTables.semantics t).rejectionCount (roundPreprocessed t labels) ≤
      (PortTables.baseGraph (preprocess H t)).rejectionCount labels := by
  rw [PreprocessingGuarantees.rejectionCount_eq_regularized]
  exact roundRegular_soundness H certificate t
    (PreprocessingGuarantees.restrictedLabel t labels)

end OAI.UniqueGamesTheorem.Foundations.PCP.Decode

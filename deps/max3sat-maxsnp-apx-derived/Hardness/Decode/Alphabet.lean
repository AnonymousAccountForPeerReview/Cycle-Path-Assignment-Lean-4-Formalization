module

public import Hardness.Decode.Selectors
public import OAI.Computability.UniqueGames.PCP.AlphabetTableBoundsLemmas

/-!
# Decoding the alphabet-reduction stage: least nearest long-code word

For a table `input` over the alphabet `Fin q` (`0 < q`), `alphabetDecode hq input labeling`
turns a labeling of `AlphabetTable.Table.build input` into a labeling of `input`:

* `blockBit input labeling v tape` is coordinate `0` of the six-bit label of the address
  vertex `(v, tape)` of the built table, for `tape : Fin q → Bool`;
* `codeDistance input labeling v a` is the number of tapes with
  `blockBit input labeling v tape ≠ tape a`;
* `alphabetDecode hq input labeling v` is the least `a : Fin q` minimising that number.

`alphabetDecode_bound` is the pointwise soundness statement.  The proofs are those of
`CodeComposition.distance_from_other_codeword`, `rejected_pair_far`,
`AlphabetReduction.rejected_edge_tester_bound`, `AlphabetGraph.local_gap`, `average_gap`,
`rejection_count_bound`, `AlphabetGraphBounds.gap_transfer_real` and
`AlphabetTableBounds.gap_transfer_real`, with the nearest-code-word decoding abstracted.
-/

@[expose] public section

namespace OAI.UniqueGamesTheorem.Foundations.PCP.Decode

noncomputable section

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Hastad
open CodeComposition AlphabetReduction AlphabetGraph

section Generic

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- `m` is a nearest long-code word of `f`. -/
def IsNearest (f : Cube A → Bool) (m : A) : Prop :=
  ∀ b : A, relativeDistance f (codeword m) ≤ relativeDistance f (codeword b)

theorem distance_from_other_codeword_of_nearest (f : Cube A → Bool) {m a : A}
    (hm : IsNearest f m) (ha : a ≠ m) : 1 / 4 ≤ relativeDistance f (codeword a) := by
  have htri := relativeDistance_triangle (codeword m) f (codeword a)
  rw [codeword_distance (Ne.symm ha), relativeDistance_comm (codeword m) f] at htri
  have hmin := hm a
  linarith

theorem rejected_pair_far_of_nearest (accepts : A → A → Bool) (left right : Cube A → Bool)
    {l r : A} (hl : IsNearest left l) (hr : IsNearest right r)
    (hbad : accepts l r = false) (a b : A) (hgood : accepts a b = true) :
    1 / 8 ≤ relativeDistance (pairWord left right) (pairWord (codeword a) (codeword b)) := by
  rw [pairWord_distance]
  have hleft := relativeDistance_nonnegative left (codeword a)
  have hright := relativeDistance_nonnegative right (codeword b)
  by_cases ha : a = l
  · have hb : b ≠ r := by
      intro hb
      rw [ha, hb, hbad] at hgood
      cases hgood
    have hsep := distance_from_other_codeword_of_nearest right hr hb
    linarith
  · have hsep := distance_from_other_codeword_of_nearest left hl ha
    linarith

theorem rejected_edge_tester_bound_of_nearest (accepts : A → A → Bool)
    (left right : Cube A → Bool) (F : Cube (LegalPair accepts) → Bool)
    {l r : A} (hl : IsNearest left l) (hr : IsNearest right r)
    (hbad : accepts l r = false) :
    1 / 2048 ≤ edgeTesterReject accepts left right F := by
  have hfar (p : LegalPair accepts) :
      (1 / 8 : ℝ) ≤ AssignmentTester.distance (pairWord left right) (pairEncoding accepts p) := by
    have h := rejected_pair_far_of_nearest accepts left right hl hr hbad p.1.1 p.1.2 p.2
    convert h using 1
    rfl
  have h := AssignmentTester.explicit_proximity_soundness (pairEncoding accepts)
    (pairWord left right) F (δ := 1 / 8) (by norm_num) (by norm_num) hfar
  norm_num at h
  exact h

variable {V E : Type*}

theorem local_gap_of_nearest (G : ConstraintGraph V E A)
    (assignment : Address V E A → Bool) (dec : V → A)
    (hdec : ∀ v, IsNearest (vertexBlock assignment v) (dec v)) (e : E) :
    AssignmentTester.truth (!(G.edgeSatisfied dec e)) / 2048 ≤
      localAverage G assignment e := by
  cases h : G.edgeSatisfied dec e with
  | false =>
      rw [localAverage_eq_tester]
      simpa [AssignmentTester.truth] using
        rejected_edge_tester_bound_of_nearest (G.accepts e)
          (vertexBlock assignment (G.tail e)) (vertexBlock assignment (G.head e))
          (edgeOracle G assignment e) (hdec (G.tail e)) (hdec (G.head e)) h
  | true =>
      simp only [Bool.not_true, AssignmentTester.truth, Bool.false_eq_true, ite_false, zero_div]
      apply Finset.expect_nonneg
      intro sample _
      exact AssignmentTester.truth_nonneg _

theorem average_gap_of_nearest [Fintype E] (G : ConstraintGraph V E A)
    (assignment : Address V E A → Bool) (dec : V → A)
    (hdec : ∀ v, IsNearest (vertexBlock assignment v) (dec v)) :
    (𝔼 e : E, AssignmentTester.truth (!(G.edgeSatisfied dec e))) / 2048 ≤
      average G assignment := by
  unfold average
  rw [expect_prod, Finset.expect_div]
  exact Finset.expect_le_expect (fun e _ => local_gap_of_nearest G assignment dec hdec e)

/-- `AlphabetGraph.rejection_count_bound` for an arbitrary nearest-code-word decoding. -/
theorem rejection_count_bound_of_nearest [Fintype E] (G : ConstraintGraph V E A)
    (assignment : Address V E A → Bool) (dec : V → A)
    (hdec : ∀ v, IsNearest (vertexBlock assignment v) (dec v)) :
    Fintype.card (LocalEvent A) * G.rejectionCount dec ≤
      2048 * QueryIncidence.verifierRejectionCount (verifier G) assignment := by
  classical
  cases isEmpty_or_nonempty E with
  | inl empty =>
      let := empty
      simp [ConstraintGraph.rejectionCount, ConstraintGraph.rejectedDarts]
  | inr inhabited =>
      let := inhabited
      have h := average_gap_of_nearest G assignment dec hdec
      rw [average_eq_count, expect_rejection_eq_count, card_event, Nat.cast_mul,
        div_div] at h
      have he : (0 : ℝ) < Fintype.card E := by exact_mod_cast Fintype.card_pos
      have hl : (0 : ℝ) < Fintype.card (LocalEvent A) := by
        exact_mod_cast Fintype.card_pos
      have hc := (div_le_div_iff₀ (mul_pos he (by norm_num)) (mul_pos he hl)).mp h
      have hc' :
          ((Fintype.card (LocalEvent A) : ℝ) * (G.rejectionCount dec : ℝ)) * Fintype.card E ≤
          (2048 * (QueryIncidence.verifierRejectionCount (verifier G) assignment : ℝ)) *
            Fintype.card E := by
        simpa only [ConstraintGraph.rejectionCount, ConstraintGraph.rejectedDarts,
          mul_assoc, mul_comm, mul_left_comm] using hc
      have result := (mul_le_mul_iff_left₀ he).mp hc'
      exact_mod_cast result

/-- Pointwise form of `AlphabetGraphBounds.gap_transfer_real`: tester loss `2048` and
incidence gain `2`. -/
theorem graph_count_bound_of_nearest [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : ConstraintGraph V E A)
    (labeling : AlphabetGraphBounds.OutputVertex V E A → QueryIncidence.Label 6) (dec : V → A)
    (hdec : ∀ v, IsNearest (vertexBlock
      (QueryIncidence.decodedAssignment (by decide : 0 < 6) labeling) v) (dec v)) :
    Fintype.card (LocalEvent A) * G.rejectionCount dec ≤
      1024 * (AlphabetGraph.graph G).rejectionCount labeling := by
  have htest := rejection_count_bound_of_nearest G
    (QueryIncidence.decodedAssignment (by decide : 0 < 6) labeling) dec hdec
  have hinc := QueryIncidence.rejection_count_bound
    (AlphabetGraph.verifier G) (by decide : 0 < 6) labeling
  change 2 * _ ≤ (AlphabetGraph.graph G).rejectionCount labeling at hinc
  omega

/-- Relative distance to a code word is the normalised number of disagreeing tapes. -/
theorem relativeDistance_codeword_eq_count (f : Cube A → Bool) (a : A) :
    relativeDistance f (codeword a) =
      ((Finset.univ.filter (fun x : Cube A => f x ≠ x a)).card : ℝ) /
        (Fintype.card (Cube A) : ℝ) := by
  unfold relativeDistance
  rw [Fintype.expect_eq_sum_div_card]
  congr 1
  rw [← Finset.sum_boole]
  apply Finset.sum_congr rfl
  intro x _
  unfold disagreement codeword
  by_cases h : f x = x a <;> simp [h]

end Generic

section Table

open AlphabetTable

variable {q : Nat}

/-- Coordinate `0` of the six-bit label of the address vertex `(v, tape)` of the built table. -/
def blockBit (input : GenericGraphTables.Table q)
    (labeling : Fin (Table.build input).vertices → GraphTables.Label)
    (v : Fin input.vertices) (tape : Cube (Fin q)) : Bool :=
  QueryIncidence.decodeRight (by decide : 0 < 6)
    (Enumeration.labelEquiv.symm
      (labeling (Enumeration.vertexEquiv input.vertices input.darts q (.inr (.inl (v, tape))))))

/-- `blockBit` is the least significant binary digit of the numeric label of the address
vertex `(v, tape)`, whose number is `eventCount + (v * 2 ^ q + rank tape)` by
`Enumeration.vertexEquiv_vertexAddress_val`. -/
theorem blockBit_bitValue (input : GenericGraphTables.Table q)
    (labeling : Fin (Table.build input).vertices → GraphTables.Label)
    (v : Fin input.vertices) (tape : Cube (Fin q)) :
    Enumeration.bitValue (blockBit input labeling v tape) =
      (labeling (Enumeration.vertexEquiv input.vertices input.darts q
        (.inr (.inl (v, tape))))).val % 2 := by
  have h := Enumeration.cubeUnrank_digit (q := 6)
    (labeling (Enumeration.vertexEquiv input.vertices input.darts q (.inr (.inl (v, tape)))))
    (QueryIncidence.zeroSlot (by decide : 0 < 6))
  simp only [QueryIncidence.zeroSlot, pow_zero, Nat.div_one] at h
  exact h

/-- Number of tapes on which the block of `v` disagrees with the long-code word of `a`. -/
def codeDistance (input : GenericGraphTables.Table q)
    (labeling : Fin (Table.build input).vertices → GraphTables.Label)
    (v : Fin input.vertices) (a : Fin q) : Nat :=
  (Finset.univ.filter (fun tape : Cube (Fin q) => blockBit input labeling v tape ≠ tape a)).card

/-- Stage decoder for alphabet reduction: the least nearest long-code word of every block. -/
def alphabetDecode (hq : 0 < q) (input : GenericGraphTables.Table q)
    (labeling : Fin (Table.build input).vertices → GraphTables.Label) :
    Fin input.vertices → Fin q :=
  fun v => leastArgMin hq (codeDistance input labeling v)

/-- Pointwise soundness of alphabet reduction with the deterministic decoder. -/
theorem alphabetDecode_bound (hq : 0 < q) (input : GenericGraphTables.Table q)
    (labeling : Fin (Table.build input).vertices → GraphTables.Label) :
    AlphabetGraphBounds.localEventFactor q *
        (GenericGraphTables.semantics input).rejectionCount (alphabetDecode hq input labeling) ≤
      1024 * (GraphTables.semantics (Table.build input)).rejectionCount labeling := by
  classical
  let : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  let lifted := fun vertex => Enumeration.labelEquiv.symm
    (labeling (Enumeration.vertexEquiv input.vertices input.darts q vertex))
  have h := graph_count_bound_of_nearest (GenericGraphTables.semantics input) lifted
    (alphabetDecode hq input labeling) (by
      intro v b
      rw [relativeDistance_codeword_eq_count, relativeDistance_codeword_eq_count]
      have hc : (0 : ℝ) < Fintype.card (Cube (Fin q)) := Nat.cast_pos.mpr Fintype.card_pos
      rw [div_le_div_iff_of_pos_right hc]
      exact_mod_cast leastArgMin_min hq (codeDistance input labeling v) b)
  have counts := Table.rejectionCount_build input lifted
  have restored : (fun v : Fin (Table.build input).vertices => Enumeration.labelEquiv
      (lifted ((Enumeration.vertexEquiv input.vertices input.darts q).symm v))) = labeling := by
    funext v
    dsimp only [lifted]
    rw [Enumeration.labelEquiv.apply_symm_apply]
    exact congrArg labeling
      ((Enumeration.vertexEquiv input.vertices input.darts q).apply_symm_apply v)
  rw [restored] at counts
  rw [← counts] at h
  rw [AlphabetGraph.card_localEvent, Fintype.card_fin] at h
  exact h

end Table

end

end OAI.UniqueGamesTheorem.Foundations.PCP.Decode

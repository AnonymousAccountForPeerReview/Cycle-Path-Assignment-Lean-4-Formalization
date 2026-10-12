module

public import Hardness.Witness.Pipeline
public import Hardness.DecodeList.Alphabet
public import Hardness.DecodeList.Powering
public import Hardness.DecodeList.Cloud
public import Hardness.DecodeList.Endpoints
public import Hardness.Decode.Main

/-!
# The witness decoder computes the gap decoder

For the concrete constants of the gap-amplification round and word functions `I`, `B`, `Pp`
that agree with the vendored machines on table codes, `decoder_eq` identifies the list program
`decoder` of `Hardness.Witness.Pipeline` with the certificate extracted from the assignment
`Decode.gapDecode H F τ`, `τ i = SAT.assignmentOf y i`.

* Table codes: `GraphTables.tableBits t` is the unary code of `tableWords t`
  (`unaryWords_tableBits`); the header and the tail column are read off it
  (`header_tableBits_zero`, `header_tableBits_one`, `column_tableWords_tail`), and the
  reverse-index column of a port table is its rotation list (`column_portTableWords`).
* One round: `roundStep_spec` (alphabet reduction, powering, cloud majority:
  `alphaList_spec`, `powerList_spec`, `cloudList_spec`).
* All rounds: `foldRounds_spec`, by induction with `runDecode_succ`.
* Sizes: `tableBits_runTables_le` bounds every intermediate table code by the vendored
  polynomial `tableBitsPolynomial` in the length of the formula code.
-/

@[expose] public section

set_option linter.dupNamespace false

namespace Complexity.WitnessDecode

open Complexity.PT Complexity.PT.Code
open Complexity.DecodeList
open OAI.UniqueGamesTheorem.Foundations
open OAI.UniqueGamesTheorem.Foundations.PCP
open OAI.UniqueGamesTheorem.Foundations.PCP.Decode
open OAI.UniqueGamesTheorem.Foundations.PCP.RoundTables
open OAI.UniqueGamesTheorem.Foundations.PCP.TableIteration

/-! ### Table codes -/

theorem encodeWords_eq_unaryCode (ns : List Nat) :
    OAI.UniqueGamesTheorem.Foundations.Complexity.encodeWords ns = unaryCode ns := by
  induction ns with
  | nil => rfl
  | cons n ns ih =>
    rw [OAI.UniqueGamesTheorem.Foundations.Complexity.encodeWords, ih]
    simp [unaryCode, OAI.UniqueGamesTheorem.Foundations.Complexity.encodeWord]

theorem unaryWords_tableBits (t : GraphTables.Table) :
    unaryWords (GraphTables.tableBits t) = GraphTables.tableWords t := by
  rw [GraphTables.tableBits, encodeWords_eq_unaryCode, unaryWords_code]

theorem header_tableBits_zero (t : GraphTables.Table) :
    header (GraphTables.tableBits t) 0 = t.vertices := by
  simp [header, unaryWords_tableBits, GraphTables.tableWords]

theorem header_tableBits_one (t : GraphTables.Table) :
    header (GraphTables.tableBits t) 1 = t.darts := by
  simp [header, unaryWords_tableBits, GraphTables.tableWords]

/-- Word `2 + 4098 * e + j` of the code of a table is word `j` of row `e`. -/
theorem tableWords_getD_row (t : GraphTables.Table) {e : Nat} (he : e < t.darts) {j : Nat}
    (hj : j < 4098) :
    (GraphTables.tableWords t).getD (2 + 4098 * e + j) 0 =
      (GraphTables.rowWords (t.rows[e])).getD j 0 := by
  have hrows : ∀ b ∈ GraphTables.rowList t, (GraphTables.rowWords b).length = 4098 :=
    fun b _ => GraphTables.rowWords_length b
  have hlen : e < (GraphTables.rowList t).length := by
    rw [GraphTables.rowList_length]
    exact he
  have h := getD_flatMap_of_length (GraphTables.rowList t) GraphTables.rowWords 4098 hrows e j hlen hj
  have hrow : (GraphTables.rowList t)[e] = t.rows[e] := by
    simp [GraphTables.rowList]
  rw [hrow] at h
  rw [← h, GraphTables.tableWords, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by simp only [List.length_cons, List.length_nil]; omega)]
  congr 2
  simp only [List.length_cons, List.length_nil]
  omega

theorem tableWords_getD_tail (t : GraphTables.Table) {e : Nat} (he : e < t.darts) :
    (GraphTables.tableWords t).getD (2 + 4098 * e) 0 = (t.rows[e].tail).val := by
  have h := tableWords_getD_row t he (j := 0) (by omega)
  rw [Nat.add_zero] at h
  rw [h]
  simp [GraphTables.rowWords]

theorem tableWords_getD_reverse (t : GraphTables.Table) {e : Nat} (he : e < t.darts) :
    (GraphTables.tableWords t).getD (3 + 4098 * e) 0 = (t.rows[e].reverseIndex).val := by
  have h := tableWords_getD_row t he (j := 1) (by omega)
  have e3 : 2 + 4098 * e + 1 = 3 + 4098 * e := by omega
  rw [e3] at h
  rw [h]
  simp [GraphTables.rowWords]

/-- The tail column of the code of a table. -/
theorem column_tableWords_tail (t : GraphTables.Table) :
    column (GraphTables.tableWords t) 2 4098 t.darts = tailList t := by
  apply List.ext_getElem
  · simp
  · intro e h1 h2
    have he : e < t.darts := by simpa using h1
    simp only [column, List.getElem_map, List.getElem_range, tailList, List.getElem_ofFn]
    exact tableWords_getD_tail t he

/-- The reverse-index column of the code of a port table is its rotation list. -/
theorem column_portTableWords {V d : Nat} (P : PortTables.Table V d) :
    column (GraphTables.tableWords (PortTables.graphTable P)) 3 4098 (V * d) = rotList P := by
  apply List.ext_getElem
  · simp [rotList]
  · intro e h1 h2
    have he : e < V * d := by simpa using h1
    simp only [column, List.getElem_map, List.getElem_range, rotList, List.getElem_ofFn]
    rw [tableWords_getD_reverse (PortTables.graphTable P) (e := e) he]
    have h := PortTables.reverseAt_flatRows P ⟨e, he⟩
    unfold GraphTables.reverseAt at h
    exact congrArg Fin.val h

/-! ### Round data -/

/-- The round data of the round input `t`. -/
noncomputable def roundData (H : BaseTable) (t : GraphTables.Table) : RoundData :=
  (t.vertices, tailList t, PreprocessingTables.vertices t,
    rotList (PreprocessingTables.preprocess H t))

/-- The data read off the table codes are the round data. -/
theorem dataOf_tableBits (H : BaseTable) {Pp : Word → Word}
    (hPp : ∀ t, Pp (GraphTables.tableBits t) =
      PortTables.tableBits (PreprocessingTables.preprocess H t))
    (t : GraphTables.Table) : dataOf Pp (GraphTables.tableBits t) = roundData H t := by
  unfold dataOf roundData
  rw [hPp, PortTables.tableBits, header_tableBits_zero, header_tableBits_one, unaryWords_tableBits,
    header_tableBits_zero, header_tableBits_one, unaryWords_tableBits, column_tableWords_tail]
  have h := column_portTableWords (PreprocessingTables.preprocess H t)
  simp only [PortTables.graphTable] at h ⊢
  rw [h]

/-! ### One round -/

theorem two_mul_mul_eq (V X : Nat) : 2 * V * X = V * (2 * X) := by
  rw [Nat.mul_comm 2 V, Nat.mul_assoc]

/-- The number of darts of the powered table is `vertices * (2 * D ^ (n + 1))`.  (The factor
is kept as an explicit expression: a definition for it would invite the unifier to evaluate
`PreprocessingTables.degree`.) -/
theorem powered_darts_eq (H : BaseTable) (t : GraphTables.Table) :
    (powered H t).darts = PreprocessingTables.vertices t *
      (2 * PreprocessingTables.degree ^ (walkParameter + 1)) :=
  (powered_darts H t).trans (two_mul_mul_eq _ _)

/-- **One round of the list program is `roundDecode`.** -/
theorem roundStep_spec (H : BaseTable) (t : GraphTables.Table)
    (L : Fin (build H t).vertices → GraphTables.Label) :
    roundStep alphabet PreprocessingTables.degree walkParameter FinalConstants.endpointLength
        (2 * PreprocessingTables.degree ^ (walkParameter + 1)) (roundData H t) (labelList L) =
      labelList (roundDecode H t L) := by
  have h1 : alphaList alphabet (PreprocessingTables.vertices t)
      (PreprocessingTables.vertices t * (2 * PreprocessingTables.degree ^ (walkParameter + 1)))
      (labelList L) =
      labelList (alphabetDecode alphabet_positive (powered H t) L) := by
    rw [← powered_darts_eq]
    exact alphaList_spec alphabet_positive (powered H t) L
  have h2 : powerList PreprocessingTables.degree walkParameter FinalConstants.endpointLength
      (PreprocessingTables.vertices t) (rotList (PreprocessingTables.preprocess H t))
      (labelList (alphabetDecode alphabet_positive (powered H t) L)) =
      labelList (powerDecode (PreprocessingTables.preprocess H t) walkParameter
        FinalConstants.endpointLength (alphabetDecode alphabet_positive (powered H t) L)) :=
    powerList_spec (PreprocessingTables.preprocess H t) walkParameter
      FinalConstants.endpointLength (alphabetDecode alphabet_positive (powered H t) L)
  have h3 := cloudList_spec t (powerDecode (PreprocessingTables.preprocess H t) walkParameter
    FinalConstants.endpointLength (alphabetDecode alphabet_positive (powered H t) L))
  unfold roundStep roundData roundDecode
  dsimp only
  rw [h1, h2, h3]

/-! ### All rounds -/

/-- **The fold of the list round program is `runDecode`.** -/
theorem foldRounds_spec (H : BaseTable) (t₀ : GraphTables.Table) (n : Nat)
    (L : Fin (runTables H n t₀).vertices → GraphTables.Label) :
    foldRounds alphabet PreprocessingTables.degree walkParameter FinalConstants.endpointLength
        (2 * PreprocessingTables.degree ^ (walkParameter + 1))
        (((List.range n).map fun i => roundData H (runTables H i t₀)).reverse)
        (labelList L) = labelList (runDecode H t₀ n L) := by
  induction n with
  | zero =>
    rw [runDecode_zero]
    rfl
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.reverse_append, runDecode_succ]
    simp only [List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.singleton_append]
    unfold foldRounds
    rw [List.foldl_cons]
    have hstep := roundStep_spec H (runTables H n t₀) L
    exact (congrArg (fun ℓ => List.foldl (fun s d => roundStep alphabet PreprocessingTables.degree
      walkParameter FinalConstants.endpointLength
      (2 * PreprocessingTables.degree ^ (walkParameter + 1)) d s) ℓ
      ((List.range n).map fun i => roundData H (runTables H i t₀)).reverse) hstep).trans
      (ih (roundDecode H (runTables H n t₀) L))

/-! ### Iterated table codes -/

theorem iterate_tableBits (H : BaseTable) {B : Word → Word}
    (hB : ∀ t, B (GraphTables.tableBits t) = GraphTables.tableBits (build H t)) :
    ∀ (i : Nat) (t : GraphTables.Table),
      B^[i] (GraphTables.tableBits t) = GraphTables.tableBits (runTables H i t) := by
  intro i
  induction i with
  | zero => intro t; rfl
  | succ i ih =>
    intro t
    rw [Function.iterate_succ_apply', ih, hB]
    rfl

theorem roundCount_initial (F : Target.Formula) :
    roundCount (GraphTables.tableBits (RawInitialTables.table F)) = iterationCount F := by
  rw [roundCount, header_tableBits_zero, header_tableBits_one]
  rfl

/-- Every intermediate table code is bounded by the vendored polynomial `tableBitsPolynomial`
in the length of the formula code. -/
theorem tableBits_runTables_le (H : BaseTable) (F : Target.Formula) {i : Nat}
    (hi : i ≤ iterationCount F) :
    (GraphTables.tableBits (runTables H i (RawInitialTables.table F))).length ≤
      tableBitsPolynomial.eval
        (OAI.UniqueGamesTheorem.Foundations.Complexity.formulaBits F).length := by
  have h1 := TableIteration.run_size H i (RoundTables.initial F)
  have h2 : RoundTables.sizeFactor ^ i ≤ RoundTables.sizeFactor ^ iterationCount F :=
    Nat.pow_le_pow_right RoundTables.sizeFactor_positive hi
  have h3 : RoundTables.sizeFactor ^ iterationCount F ≤ (2 * RoundTables.size (RoundTables.initial F)) ^ polynomialDegree :=
    AmplificationIteration.blowup_rounds_le (RoundTables.size_positive (RoundTables.initial F)) sizeFactor_le_power
  have h4 := TableIteration.initial_size_le F
  have h5 : (2 * RoundTables.size (RoundTables.initial F)) ^ polynomialDegree ≤
      (14 * (OAI.UniqueGamesTheorem.Foundations.Complexity.formulaBits F).length) ^
        polynomialDegree :=
    Nat.pow_le_pow_left (by omega) _
  have hrun : RoundTables.size (TableIteration.run H i (RoundTables.initial F)) ≤
      (14 * (OAI.UniqueGamesTheorem.Foundations.Complexity.formulaBits F).length) ^
        polynomialDegree * (7 * (OAI.UniqueGamesTheorem.Foundations.Complexity.formulaBits F).length) :=
    h1.trans (Nat.mul_le_mul (h2.trans (h3.trans h5)) h4)
  have hval := run_val H i (RoundTables.initial F)
  have hsz : RoundTables.size (TableIteration.run H i (RoundTables.initial F)) =
      (runTables H i (RawInitialTables.table F)).vertices +
        (runTables H i (RawInitialTables.table F)).darts := by
    unfold RoundTables.size
    rw [hval]
    rfl
  rw [hsz] at hrun
  rw [tableBitsPolynomial, Polynomial.eval_comp, tableSizePolynomial_eval]
  exact GraphTableComplexity.bits_le_of_size_le _ hrun

/-! ### The decoder computes the gap decoder -/

/-- **The list decoder computes the certificate of the gap decoder.** -/
theorem decoder_eq (H : BaseTable) {fb : Word → Word} {nv : Word → Nat} {I B Pp : Word → Word}
    (hB : ∀ t, B (GraphTables.tableBits t) = GraphTables.tableBits (build H t))
    (hPp : ∀ t, Pp (GraphTables.tableBits t) =
      PortTables.tableBits (PreprocessingTables.preprocess H t))
    (states wc wk rc rk : Nat) (x y : Word) (F : Target.Formula)
    (hI : I (fb x) = GraphTables.tableBits (RawInitialTables.table F))
    (hnv : nv x = F.variables) :
    decoder fb nv I B Pp alphabet PreprocessingTables.degree walkParameter
        FinalConstants.endpointLength (2 * PreprocessingTables.degree ^ (walkParameter + 1))
        states wc wk rc rk x y =
      Witness.extract states wc wk rc rk x.length
        (SAT.assignmentOf (List.ofFn (gapDecode H F (fun i => SAT.assignmentOf y i.val)))) := by
  have hit := iterate_tableBits H hB
  have hdata : ((iterList B (iterationCount F)
      (GraphTables.tableBits (RawInitialTables.table F))).2.reverse.map (dataOf Pp)) =
      ((List.range (iterationCount F)).map fun i =>
        roundData H (runTables H i (RawInitialTables.table F))).reverse := by
    rw [iterList_eq, List.map_reverse, List.map_map]
    congr 1
    apply List.map_congr_left
    intro i _
    simp only [Function.comp_apply]
    rw [hit, dataOf_tableBits H hPp]
  have hlast : header (iterList B (iterationCount F)
      (GraphTables.tableBits (RawInitialTables.table F))).1 0 =
      (runTables H (iterationCount F) (RawInitialTables.table F)).vertices := by
    rw [iterList_eq, hit, header_tableBits_zero]
  have hfinal : finalList (runTables H (iterationCount F) (RawInitialTables.table F)).vertices y =
      labelList (finalDecode (outputTable H F) (fun i => SAT.assignmentOf y i.val)) :=
    finalList_spec (outputTable H F) y
  have hfold : foldRounds alphabet PreprocessingTables.degree walkParameter
      FinalConstants.endpointLength (2 * PreprocessingTables.degree ^ (walkParameter + 1))
      ((List.range (iterationCount F)).map fun i =>
        roundData H (runTables H i (RawInitialTables.table F))).reverse
      (labelList (finalDecode (outputTable H F) (fun i => SAT.assignmentOf y i.val))) =
      labelList (runDecode H (RawInitialTables.table F) (iterationCount F)
        (finalDecode (outputTable H F) (fun i => SAT.assignmentOf y i.val))) :=
    foldRounds_spec H (RawInitialTables.table F) (iterationCount F)
      (finalDecode (outputTable H F) (fun i => SAT.assignmentOf y i.val))
  have hinit := initialList_spec F (runDecode H (RawInitialTables.table F) (iterationCount F)
    (finalDecode (outputTable H F) (fun i => SAT.assignmentOf y i.val)))
  have hgap : gapDecode H F (fun i => SAT.assignmentOf y i.val) =
      initialDecode F (runDecode H (RawInitialTables.table F) (iterationCount F)
        (finalDecode (outputTable H F) (fun i => SAT.assignmentOf y i.val))) := rfl
  unfold decoder
  rw [hI, hnv, roundCount_initial, hdata, hlast, hfinal, hfold, hinit, hgap]

end Complexity.WitnessDecode

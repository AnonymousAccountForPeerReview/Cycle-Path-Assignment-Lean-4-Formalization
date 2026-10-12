module

public import Hardness.Witness.Spec
public import Hardness.Final.Converters
public import Hardness.Final.Max3SAT
public import Hardness.Occ.Main
public import Bridge.Total
public import ComplexityExt.Witness.Main

/-!
# The witness-recovering PCP gap theorem, and APX-completeness of MAX-3-SAT

`witnessGap`: for every polynomial-time verifier `M` and certificate bound `powerBound c e`,

* `g x = ofOAI (gapMap H (toOAI (g₀ x)))`, where `g₀ = Witness.threeCNF M c e rc rk` is the
  ANONYMIZED–ANONYMIZED 3-CNF and `gapMap H` the vendored gap-amplification map (its code is computed by
  the converters of `Hardness.Final.Converters` around the bridged gap machine);
* `dec (pairWords x y)` is the list program `WitnessDecode.decoder` (polynomial-time by
  `pt_decoder`, with the bridged initial, round and preprocessing machines and the size bound
  `tableBits_runTables_le`); by `decoder_eq` it is the certificate `Witness.extract` read off the
  assignment `Decode.gapDecode H (toOAI (g₀ x)) τ`, `τ i = SAT.assignmentOf y i`.

Soundness: if `y` satisfies more than the fraction `1 - 1 / den` of the clauses of `g x`
(`den = walkLength * 40960`), it fails fewer than one clause in `den` of `gapMap H F`, so
`gapDecode` satisfies `F = toOAI (g₀ x)` (`Decode.gapDecode_satisfies`), hence `g₀ x`
(`ofOAI_toOAI`, `evalCNF_padCNF`), and `Witness.verifier_threeCNF` turns this into an accepted
certificate.

Corollaries: `max3SAT_apxComplete`, `max3SAT3_apxComplete`, `max3SAT_apxHard`,
`max3SAT3_apxHard`.
-/

@[expose] public section

set_option linter.dupNamespace false

namespace Complexity

open Complexity.PT Complexity.PT.Code Complexity.WitnessDecode
open OAI.UniqueGamesTheorem
open OAI.UniqueGamesTheorem.Foundations.PCP
open OAI.UniqueGamesTheorem.Foundations.PCP.RoundTables
open OAI.UniqueGamesTheorem.Foundations.PCP.TableIteration

namespace WitnessDecode

/-! ### The machines as total polynomial-time word functions -/

theorem exists_initialWord : ∃ I : Word → Word, PolyTime I ∧
    ∀ F : Foundations.Target.Formula,
      I (Foundations.Complexity.formulaBits F) =
        GraphTables.tableBits (RawInitialTables.table F) := by
  obtain ⟨I, hI, hI'⟩ := Bridge.exists_polyTime_of_tm2
    Foundations.Complexity.MachineTableIteration.initialCertificate
    (fun k => Foundations.Complexity.TableIterationFiniteAlphabet.initial k)
  exact ⟨I, hI, fun F => hI' F⟩

theorem exists_roundWord (H : BaseTable) : ∃ B : Word → Word, PolyTime B ∧
    ∀ t : GraphTables.Table, B (GraphTables.tableBits t) = GraphTables.tableBits (build H t) := by
  obtain ⟨B, hB, hB'⟩ := Bridge.exists_polyTime_of_tm2 (GapTheorem.roundMachine H)
    (GapTheorem.roundMachine_finite H)
  exact ⟨B, hB, hB'⟩

theorem exists_preprocessWord (H : BaseTable) : ∃ Pp : Word → Word, PolyTime Pp ∧
    ∀ t : GraphTables.Table, Pp (GraphTables.tableBits t) =
      PortTables.tableBits (PreprocessingTables.preprocess H t) := by
  obtain ⟨Pp, hPp, hPp'⟩ := Bridge.exists_polyTime_of_tm2
    (PreprocessingRuntime.tablePolynomialTime H) (PreprocessingRuntime.finiteAlphabet H)
  exact ⟨Pp, hPp, hPp'⟩

theorem exists_gapWord (H : BaseTable) : ∃ G : Word → Word, PolyTime G ∧
    ∀ F : Foundations.Target.Formula, G (Foundations.Complexity.formulaBits F) =
      Foundations.Complexity.formulaBits (gapMap H F) := by
  obtain ⟨G, hG, hG'⟩ := Bridge.exists_polyTime_of_tm2 (GapTheorem.gapMachine H)
    (GapTheorem.gapMachine_finite H)
  exact ⟨G, hG, hG'⟩

/-! ### Arithmetic and assignments -/

/-- The clause bookkeeping of the soundness direction. -/
theorem failed_lt_of_sat (den m sat failed : Nat) (hcount : sat + failed = m)
    (h : den * m < den * sat + 1 * m) : den * failed < m := by
  have hmul := Nat.mul_add den sat failed
  rw [hcount] at hmul
  omega

theorem assignmentOf_ofFn {n : Nat} (f : Fin n → Bool) (i : Fin n) :
    SAT.assignmentOf (List.ofFn f) i.val = f i := by
  simp [SAT.assignmentOf, List.getD_eq_getElem?_getD]

/-- An assignment of `F` satisfying every clause satisfies `ofOAI F`. -/
theorem evalCNF_ofOAI_of_forall (F : Foundations.Target.Formula) (A : Fin F.variables → Bool)
    (hA : ∀ cl ∈ F.clauses, cl.eval A = true) :
    SAT.evalCNF (SAT.assignmentOf (List.ofFn A)) (ofOAI F) = true := by
  have hrestrict : (fun i : Fin F.variables => SAT.assignmentOf (List.ofFn A) i.val) = A :=
    funext fun i => assignmentOf_ofFn A i
  unfold SAT.evalCNF
  refine List.all_eq_true.mpr fun d hd => ?_
  obtain ⟨cl, hcl, rfl⟩ := List.mem_map.mp hd
  rw [evalClause_ofClause, hrestrict]
  exact hA cl hcl

end WitnessDecode

open WitnessDecode

/-- **The witness-recovering PCP gap theorem**, with gap `1 / (walkLength * 40960)`. -/
theorem witnessGap : ∃ num den : Nat, 0 < num ∧ WitnessGap num den := by
  obtain ⟨H, certificate⟩ := ExpanderTables.exists_base_table
  obtain ⟨c₁, hc₁, hc₁'⟩ := exists_converterIn
  obtain ⟨c₂, hc₂, hc₂'⟩ := exists_converterOut
  obtain ⟨Gm, hGm, hGm'⟩ := exists_gapWord H
  obtain ⟨I, hI, hI'⟩ := exists_initialWord
  obtain ⟨B, hB, hB'⟩ := exists_roundWord H
  obtain ⟨Pp, hPp, hPp'⟩ := exists_preprocessWord H
  refine ⟨1, FinalConstants.walkLength * 40960, Nat.one_pos, ?_⟩
  intro M c e hM
  obtain ⟨tc, tk, hMt⟩ := hM
  -- the ANONYMIZED–ANONYMIZED formula
  have hpoly₀ := Witness.polyTime_threeCNF M c e (Witness.stepCoefficient tc tk c)
    (Witness.stepExponent tk e)
  have hg₀ : PT (fun x => Witness.threeCNF M c e (Witness.stepCoefficient tc tk c)
      (Witness.stepExponent tk e) x) := PT.of_polyTime_enc hpoly₀
  have h3 : ∀ x, SAT.IsThreeCNF (Witness.threeCNF M c e (Witness.stepCoefficient tc tk c)
      (Witness.stepExponent tk e) x) :=
    Witness.threeCNF_isThreeCNF M c e _ _
  -- its serialisation and number of variables
  obtain ⟨fb, hfb, hfbF⟩ : ∃ fb : Word → Word, PT fb ∧ ∀ x, fb x =
      Foundations.Complexity.formulaBits (toOAI (Witness.threeCNF M c e
        (Witness.stepCoefficient tc tk c) (Witness.stepExponent tk e) x)) := by
    refine ⟨fun x => (Code.enc (convInData (Witness.threeCNF M c e
      (Witness.stepCoefficient tc tk c) (Witness.stepExponent tk e) x)) : Word),
      PT.enc (pt_convInData.comp hg₀), fun x => ?_⟩
    dsimp only
    rw [enc_convInData, formulaBits_toOAI]
  obtain ⟨nv, hnv, hnvF⟩ : ∃ nv : Word → Nat, PT nv ∧ ∀ x, nv x =
      (toOAI (Witness.threeCNF M c e (Witness.stepCoefficient tc tk c)
        (Witness.stepExponent tk e) x)).variables :=
    ⟨fun x => (Code.enc (Witness.threeCNF M c e (Witness.stepCoefficient tc tk c)
      (Witness.stepExponent tk e) x) : Word).length, PT.length (PT.enc hg₀), fun _ => rfl⟩
  -- the size bound of the iterated tables
  obtain ⟨cf, ef, hcf⟩ := hfb.size_le
  obtain ⟨c', e', hc'⟩ := (Bridge.polynomialBound_eval tableBitsPolynomial).comp
    (PolynomialBound.power cf ef)
  have hsize : ∀ x i, i ≤ roundCount (I (fb x)) →
      (B^[i] (I (fb x))).length ≤ powerBound c' e' (size x) := by
    intro x i hi
    rw [hfbF x, hI', roundCount_initial] at hi
    rw [hfbF x, hI', iterate_tableBits H hB']
    refine (tableBits_runTables_le H _ hi).trans ?_
    refine le_trans (OAI.UniqueGamesTheorem.Foundations.Complexity.MachineComposition.natPolynomial_eval_mono
      _ ?_) (hc' (size x))
    have h1 := hcf x
    rw [hfbF x, size_word] at h1
    omega
  -- the decoder
  have hdec := pt_decoder hfb hnv hI hB hPp alphabet PreprocessingTables.degree walkParameter
    FinalConstants.endpointLength (2 * PreprocessingTables.degree ^ (walkParameter + 1))
    M.states c e (Witness.stepCoefficient tc tk c) (Witness.stepExponent tk e) c' e' hsize
  obtain ⟨G, hG, hG'⟩ := PT.exists_polyTime_pairWords_raw_raw_word hdec
  refine ⟨fun x => ofOAI (gapMap H (toOAI (Witness.threeCNF M c e
    (Witness.stepCoefficient tc tk c) (Witness.stepExponent tk e) x))), G, ?_, hG,
    fun x => ⟨ofOAI_isThreeCNF _, ?_, ?_, ?_⟩⟩
  · -- the code of the gap formula is polynomial-time
    have hin := polyTime_comp hc₁ hpoly₀
    have hmid := polyTime_comp hGm hin
    have hout := polyTime_comp hc₂ hmid
    refine polyTime_congr (fun x => ?_) hout
    show c₂ (Gm (c₁ (SAT.encode (Witness.threeCNF M c e (Witness.stepCoefficient tc tk c)
      (Witness.stepExponent tk e) x)))) = _
    rw [hc₁' _ (h3 x), hGm', hc₂']
  · -- nonempty
    intro hnil
    exact gapMap_nonempty H _ (List.map_eq_nil_iff.mp hnil)
  · -- completeness
    intro hx
    exact satisfiable_ofOAI _ (gapMap_completeness H _
      ((toOAI_satisfiable_iff _ (h3 x)).mpr ((Witness.verifier_threeCNF M c e tc tk hMt x).1 hx)))
  · -- soundness
    intro y hy
    rw [hG' x y, decoder_eq H hB' hPp' M.states c e _ _ x y _ (by rw [hfbF x, hI']) (hnvF x)]
    apply (Witness.verifier_threeCNF M c e tc tk hMt x).2
    have hcount := satCount_ofOAI_add_failedCount (gapMap H (toOAI (Witness.threeCNF M c e
      (Witness.stepCoefficient tc tk c) (Witness.stepExponent tk e) x))) (SAT.assignmentOf y)
    rw [ofOAI_length] at hy
    have hτ := failed_lt_of_sat _ _ _ _ hcount hy
    have hsat := Decode.gapDecode_satisfies H certificate _ _ hτ
    have hcnf := evalCNF_ofOAI_of_forall _ _ hsat
    rw [ofOAI_toOAI, evalCNF_padCNF _ _ (h3 x)] at hcnf
    exact hcnf

/-- **MAX-3-SAT is APX-complete.** -/
theorem max3SAT_apxComplete : APXComplete max3SAT := by
  obtain ⟨num, den, hnum, h⟩ := witnessGap
  exact max3SAT_apxComplete_of_witnessGap hnum h

/-- **3-OCCURRENCE MAX-3-SAT is APX-complete.** -/
theorem max3SAT3_apxComplete : APXComplete max3SAT3 := by
  obtain ⟨num, den, hnum, h⟩ := witnessGap
  exact max3SAT3_apxComplete_of_witnessGap hnum h

/-- **MAX-3-SAT is APX-hard.** -/
theorem max3SAT_apxHard : APXHard max3SAT := max3SAT_apxComplete.2

/-- **3-OCCURRENCE MAX-3-SAT is APX-hard.** -/
theorem max3SAT3_apxHard : APXHard max3SAT3 := max3SAT3_apxComplete.2

end Complexity

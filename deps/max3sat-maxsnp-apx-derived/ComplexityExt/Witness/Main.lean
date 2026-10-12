module

public import ComplexityExt.Witness.Tableau
public import Complexity.NPCompleteness
import Lean.Elab.Tactic.Omega

/-!
# ANONYMIZED-reduction form of ANONYMIZED–ANONYMIZED for 3-SAT

The polynomial-time reduction of `InNP.polyRed_threeSAT` is the composition of
the tableau emitter `CookLevinEmitter.verifierProgram` with the implication-chain
conversion `ChainThreeSAT.reduceWord`. Here its output formula is named
(`Witness.threeCNF`), and it is proved that *every* satisfying assignment of it
yields an accepted certificate through the explicit list function
`Witness.extract` of `Complexity.Witness.Extract`.
-/

@[expose] public section

namespace Complexity.Witness

open Complexity.SAT Complexity.StackTableauEmitter

/-- The CNF tableau emitted for the verifier `M` on input `x`: certificate bound
`powerBound wc wk |x|`, step bound `powerBound rc rk |x|`. -/
def cnf (M : Machine) (wc wk rc rk : Nat) (x : Word) : CNF :=
  (CookLevinEmitter.verifierProgram M wc wk rc rk).emit x (CookLevinEmitter.inputEnv x)

/-- The 3-CNF produced by the reduction: the implication-chain conversion of
`cnf`, with fresh variables starting at the length of the encoding of `cnf`.
The variables of `cnf` keep their indices. -/
def threeCNF (M : Machine) (wc wk rc rk : Nat) (x : Word) : CNF :=
  ChainThreeSAT.chainCNF (SAT.encode (cnf M wc wk rc rk x)).length (cnf M wc wk rc rk x)

theorem reduceWord_encode (F : CNF) :
    ChainThreeSAT.reduceWord (SAT.encode F) =
      SAT.encode (ChainThreeSAT.chainCNF (SAT.encode F).length F) := by
  simp [ChainThreeSAT.reduceWord]

/-- `threeCNF` is literally the output of the reduction used in
`InNP.polyRed_threeSAT`. -/
theorem encode_threeCNF (M : Machine) (wc wk rc rk : Nat) (x : Word) :
    SAT.encode (threeCNF M wc wk rc rk x) =
      ChainThreeSAT.reduceWord (SAT.encode
        ((CookLevinEmitter.verifierProgram M wc wk rc rk).emit x (fun _ => x.length))) :=
  (reduceWord_encode _).symm

theorem polyTime_threeCNF (M : Machine) (wc wk rc rk : Nat) :
    PolyTime (fun x => SAT.encode (threeCNF M wc wk rc rk x)) := by
  have h := polyTime_comp chainThreeSAT_polyTime
    (StackTableauEmitter.polyTime_emitter (CookLevinEmitter.verifierProgram M wc wk rc rk))
  exact polyTime_congr (fun x => (encode_threeCNF M wc wk rc rk x).symm) h

theorem threeCNF_isThreeCNF (M : Machine) (wc wk rc rk : Nat) (x : Word) :
    IsThreeCNF (threeCNF M wc wk rc rk x) :=
  ChainThreeSAT.chainCNF_three _ _

/-- Satisfying assignments of the 3-CNF satisfy the tableau CNF unchanged. -/
theorem cnf_of_threeCNF (M : Machine) (wc wk rc rk : Nat) (x : Word) (a : Assignment)
    (ha : evalCNF a (threeCNF M wc wk rc rk x) = true) :
    evalCNF a (cnf M wc wk rc rk x) = true :=
  ChainThreeSAT.chainCNF_sound _ _ a ha

/-- Soundness of the emitted tableau with the explicit certificate. -/
theorem cnf_sound (M : Machine) (wc wk rc rk : Nat) (x : Word) (a : Assignment)
    (ha : evalCNF a (cnf M wc wk rc rk x) = true) :
    ∃ tape, runInput M (powerBound rc rk x.length)
      (pairWords x (extract M.states wc wk rc rk x.length a)) = some (true, tape) := by
  have hc := (CookLevinEmitter.verifierProgram_correct M wc wk rc rk x a).mp ha
  obtain ⟨tape, ht⟩ := compile_sound M _ _ _ a hc
  rw [CookLevin.verifierPrefix_append] at ht
  have hx : readCells M.states
      (CookLevin.windowWidth (powerBound rc rk x.length) (CookLevin.verifierPrefix x)
        (powerBound wc wk x.length))
      (CookLevin.verifierPrefix x).length (powerBound wc wk x.length) a =
      extract M.states wc wk rc rk x.length a := by
    simp only [extract, tableauWidth, CookLevin.windowWidth, CookLevin.verifierPrefix_length]
  rw [hx] at ht
  exact ⟨tape, ht⟩

/-- Soundness of the 3-CNF with the explicit certificate. -/
theorem threeCNF_sound (M : Machine) (wc wk rc rk : Nat) (x : Word) (a : Assignment)
    (ha : evalCNF a (threeCNF M wc wk rc rk x) = true) :
    (extract M.states wc wk rc rk x.length a).length ≤ powerBound wc wk x.length ∧
      Accepts M (pairWords x (extract M.states wc wk rc rk x.length a)) := by
  refine ⟨extract_length_le _ _ _ _ _ _ a, ?_⟩
  obtain ⟨tape, ht⟩ := cnf_sound M wc wk rc rk x a (cnf_of_threeCNF M wc wk rc rk x a ha)
  exact ⟨_, tape, ht⟩

/-- Completeness: a certificate accepted within the step bound makes the 3-CNF
satisfiable. -/
theorem threeCNF_complete (M : Machine) (wc wk rc rk : Nat) (x w : Word)
    (hw : w.length ≤ powerBound wc wk x.length) (tape : Tape)
    (hrun : runInput M (powerBound rc rk x.length) (pairWords x w) = some (true, tape)) :
    Satisfiable (threeCNF M wc wk rc rk x) := by
  have hsat : SAT.SAT (CookLevinEmitter.verifierWord M wc wk rc rk x) :=
    (CookLevinEmitter.verifierWord_correct M wc wk rc rk x).mpr ⟨w, hw, tape, hrun⟩
  have h3 := (ChainThreeSAT.reduceWord_correct _).mp hsat
  rw [CookLevinEmitter.verifierWord, reduceWord_encode, ThreeSAT_encode_iff] at h3
  exact h3.2

/-- The step bound obtained from a time bound `powerBound tc tk` of the verifier
and the certificate bound `powerBound wc wk`. -/
def stepCoefficient (tc tk wc : Nat) : Nat := tc * (wc + 4) ^ tk

def stepExponent (tk wk : Nat) : Nat := (wk + 1) * tk

/-- ANONYMIZED reduction for an explicit polynomial-time verifier. -/
theorem verifier_threeCNF (M : Machine) (wc wk tc tk : Nat)
    (hM : ∀ input : Word, ∃ time decision tape,
      time ≤ powerBound tc tk input.length ∧
      runInput M time input = some (decision, tape)) (x : Word) :
    ((∃ w : Word, w.length ≤ powerBound wc wk x.length ∧ Accepts M (pairWords x w)) →
      Satisfiable (threeCNF M wc wk (stepCoefficient tc tk wc) (stepExponent tk wk) x)) ∧
    (∀ a : Assignment,
      evalCNF a (threeCNF M wc wk (stepCoefficient tc tk wc) (stepExponent tk wk) x) = true →
      (extract M.states wc wk (stepCoefficient tc tk wc) (stepExponent tk wk)
          x.length a).length ≤ powerBound wc wk x.length ∧
        Accepts M (pairWords x
          (extract M.states wc wk (stepCoefficient tc tk wc) (stepExponent tk wk) x.length a))) := by
  refine ⟨?_, fun a ha => threeCNF_sound M wc wk _ _ x a ha⟩
  rintro ⟨w, hw, ha⟩
  obtain ⟨tape, ht⟩ := (paired_accepts_iff_at_clock M tc tk wc wk hM x w hw).mp ha
  exact threeCNF_complete M wc wk _ _ x w hw tape
    (run_mono M (verifierClock_le_powerBound tc tk wc wk x.length)
      (initial M (pairWords x w)) _ ht)

end Complexity.Witness

namespace Complexity

open Complexity.SAT

/-- ANONYMIZED-reduction form of ANONYMIZED–ANONYMIZED for 3-SAT, with every object explicit:
the 3-CNF is `Witness.threeCNF`, the certificate is `Witness.extract`. -/
theorem InNP.threeSAT_witness_explicit {L : Language} (hL : InNP L) :
    ∃ (M : Machine) (wc wk rc rk : Nat),
      PolynomialTimeMachine M ∧
      (∀ x, L x ↔ ∃ w : Word, w.length ≤ powerBound wc wk x.length ∧
        Accepts M (pairWords x w)) ∧
      PolyTime (fun x => SAT.encode (Witness.threeCNF M wc wk rc rk x)) ∧
      (∀ x, IsThreeCNF (Witness.threeCNF M wc wk rc rk x)) ∧
      (∀ x, L x → Satisfiable (Witness.threeCNF M wc wk rc rk x)) ∧
      (∀ x a, evalCNF a (Witness.threeCNF M wc wk rc rk x) = true →
        (Witness.extract M.states wc wk rc rk x.length a).length ≤ powerBound wc wk x.length ∧
        Accepts M (pairWords x (Witness.extract M.states wc wk rc rk x.length a))) := by
  obtain ⟨M, wc, wk, ⟨tc, tk, hM⟩, hL⟩ := hL
  refine ⟨M, wc, wk, Witness.stepCoefficient tc tk wc, Witness.stepExponent tk wk,
    ⟨tc, tk, hM⟩, hL, Witness.polyTime_threeCNF M wc wk _ _,
    Witness.threeCNF_isThreeCNF M wc wk _ _, ?_, ?_⟩
  · intro x hx
    exact (Witness.verifier_threeCNF M wc wk tc tk hM x).1 ((hL x).mp hx)
  · intro x a ha
    exact (Witness.verifier_threeCNF M wc wk tc tk hM x).2 a ha

/-- ANONYMIZED-reduction form of ANONYMIZED–ANONYMIZED for 3-SAT. From any satisfying assignment
`a` of the 3-CNF `g x`, the word `ext x a` is an accepted certificate. The last
three conjuncts say that `ext` is elementary: it is the list expression of
`Witness.extract_eq` in the explicit variable indices `Witness.certVar`, it only
inspects variables below `N |x|`, and `N` is polynomially bounded. -/
theorem InNP.threeSAT_witness {L : Language} (hL : InNP L) :
    ∃ (M : Machine) (wc wk : Nat) (g : Word → CNF) (ext : Word → Assignment → Word),
      PolynomialTimeMachine M ∧
      (∀ x, L x ↔ ∃ w : Word, w.length ≤ powerBound wc wk x.length ∧
        Accepts M (pairWords x w)) ∧
      PolyTime (fun x => SAT.encode (g x)) ∧
      (∀ x, IsThreeCNF (g x)) ∧
      (∀ x, L x → Satisfiable (g x)) ∧
      (∀ x a, evalCNF a (g x) = true →
        (ext x a).length ≤ powerBound wc wk x.length ∧ Accepts M (pairWords x (ext x a))) ∧
      ∃ (rc rk : Nat) (N : Nat → Nat),
        (∀ x, g x = Witness.threeCNF M wc wk rc rk x) ∧
        (∀ x a, ext x a =
          ((List.range (powerBound wc wk x.length)).takeWhile
              (fun i => !a (Witness.certVar M.states wc wk rc rk x.length i 0))).map
            (fun i => a (Witness.certVar M.states wc wk rc rk x.length i 2))) ∧
        (∀ n i j, Witness.certVar M.states wc wk rc rk n i j =
          (4 * n + powerBound wc wk n + 2 * powerBound rc rk n + i + 4) * (M.states + 4) + j) ∧
        (∀ n, N n =
          (4 * n + 2 * powerBound wc wk n + 2 * powerBound rc rk n + 4) * (M.states + 4)) ∧
        PolynomialBound N ∧
        (∀ x a b, (∀ v, v < N x.length → a v = b v) → ext x a = ext x b) := by
  obtain ⟨M, wc, wk, rc, rk, hM, hL, hpoly, h3, hcomplete, hsound⟩ :=
    hL.threeSAT_witness_explicit
  refine ⟨M, wc, wk, Witness.threeCNF M wc wk rc rk,
    fun x a => Witness.extract M.states wc wk rc rk x.length a,
    hM, hL, hpoly, h3, hcomplete, hsound,
    rc, rk, Witness.varBound M.states wc wk rc rk,
    fun _ => rfl, fun _ _ => rfl, Witness.certVar_eq M.states wc wk rc rk,
    Witness.varBound_eq M.states wc wk rc rk,
    Witness.varBound_polynomial M.states wc wk rc rk, ?_⟩
  intro x a b h
  exact Witness.extract_congr M.states wc wk rc rk x.length a b h

end Complexity

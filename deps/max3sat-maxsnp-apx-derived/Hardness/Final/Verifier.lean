module

public import Hardness.Verifier.Main
public import PT.All

/-!
# The two polynomial-time obligations of the verifier form of the PCP theorem

`Hardness.Verifier.Main.pcp_theorem_of` assumes that the clause-sampling verifiers
`samplingVerifier g k B` and the exhaustive checkers `pcpChecker V c` of polynomial-time `g`,
`V` are polynomial-time computable.  Both are list programs covered by the `PT` framework:

* `polyTime_samplingVerifier`: the only step with a side condition is the value `binValue b` of
  a block `b` of `B * log₂ (|x| + 2)` bits, which is below `2 ^ (B * log₂ (|x| + 2)) ≤
  (|x| + 3) ^ B` (`PT.binValue_foldl`, `two_pow_mul_log2_le`);
* `polyTime_pcpChecker`: the `2 ^ (c * log₂ (|x| + 2))` random strings are enumerated by
  `PT.allWords_mul_log2`.
-/

@[expose] public section

set_option linter.dupNamespace false

namespace Complexity

open Complexity.PT Complexity.PT.Code

/-- The value of the `i`-th block of `B * log₂ (|x| + 2)` bits of `r` is polynomial-time
computable in `((x, r), i)`. -/
theorem pt_blockValue (B : Nat) :
    PT (fun q : (Word × Word) × Nat =>
      binValue ((q.1.2.drop (q.2 * (B * Nat.log2 (q.1.1.length + 2)))).take
        (B * Nat.log2 (q.1.1.length + 2)))) := by
  refine PT.binValue_foldl
    (w := fun q : (Word × Word) × Nat =>
      (q.1.2.drop (q.2 * (B * Nat.log2 (q.1.1.length + 2)))).take
        (B * Nat.log2 (q.1.1.length + 2)))
    (by fun_prop) (fun N => (N + 3) ^ B)
    ((PolynomialBound.identity.add (PolynomialBound.constant 3)).pow B) fun q => ?_
  have h1 : 2 ^ ((q.1.2.drop (q.2 * (B * Nat.log2 (q.1.1.length + 2)))).take
      (B * Nat.log2 (q.1.1.length + 2))).length ≤ 2 ^ (B * Nat.log2 (q.1.1.length + 2)) :=
    Nat.pow_le_pow_right (by omega) (List.length_take_le _ _)
  have h2 := two_pow_mul_log2_le (q.1.1.length + 2) B
  have h3 : (q.1.1.length + 2 + 1) ^ B ≤ (size q + 3) ^ B := by
    apply Nat.pow_le_pow_left
    simp only [size_prod, size_word, size_nat]
    omega
  exact Nat.le_trans h1 (Nat.le_trans h2 h3)

/-- The clause-sampling verifier of a polynomial-time formula-valued map is polynomial-time
computable. -/
theorem polyTime_samplingVerifier (g : Word → SAT.CNF) (k B : Nat)
    (hg : PolyTime (fun x => SAT.encode (g x))) :
    PolyTime (fun w => SAT.encode (samplingVerifier g k B w)) := by
  have hg' : PT g := PT.of_polyTime_enc hg
  have hgx : PT (fun p : Word × Nat => g (Reg.unpair p.1).1) :=
    hg'.comp (PT.fst (PT.unpair PT.fst'))
  have hb : PT (fun p : Word × Nat =>
      binValue (((Reg.unpair p.1).2.drop
        (p.2 * (B * Nat.log2 ((Reg.unpair p.1).1.length + 2)))).take
        (B * Nat.log2 ((Reg.unpair p.1).1.length + 2)))) :=
    (pt_blockValue B).comp
      (PT.pair (PT.unpair PT.fst') PT.snd' : PT (fun p : Word × Nat => (Reg.unpair p.1, p.2)))
  have hstep : PT (fun p : Word × Nat =>
      (g (Reg.unpair p.1).1).getD
        (binValue (((Reg.unpair p.1).2.drop
          (p.2 * (B * Nat.log2 ((Reg.unpair p.1).1.length + 2)))).take
          (B * Nat.log2 ((Reg.unpair p.1).1.length + 2))) %
          (g (Reg.unpair p.1).1).length) []) :=
    PT.listGetD hgx (PT.mod hb (PT.length hgx)) (PT.const [])
  have hV : PT (fun w : Word => samplingVerifier g k B w) := by
    refine (PT.map (l := fun _ : Word => List.range k)
      (f := fun (w : Word) (i : Nat) =>
        (g (Reg.unpair w).1).getD
          (binValue (((Reg.unpair w).2.drop
            (i * (B * Nat.log2 ((Reg.unpair w).1.length + 2)))).take
            (B * Nat.log2 ((Reg.unpair w).1.length + 2))) %
            (g (Reg.unpair w).1).length) [])
      hstep (PT.const _)).of_eq fun w => ?_
    simp only [samplingVerifier, blocks, List.map_map]
    rfl
  exact PT.polyTime_encode hV

/-- The exhaustive checker of a polynomial-time verifier with logarithmic randomness is
polynomial-time computable. -/
theorem polyTime_pcpChecker (V : Word → SAT.CNF) (c : Nat)
    (hV : PolyTime (fun w => SAT.encode (V w))) : PolyTime (pcpChecker V c) := by
  have hV' : PT V := PT.of_polyTime_enc hV
  have h : PT (fun p : Word × Word =>
      (allWords (c * Nat.log2 (p.1.length + 2))).all
        (fun r => SAT.evalCNF (SAT.assignmentOf p.2) (V (pairWords p.1 r)))) := by
    fun_prop
  exact PT.polyTime_bool_pairWords
    (f := fun x π : Word => (allWords (c * Nat.log2 (x.length + 2))).all
      (fun r => SAT.evalCNF (SAT.assignmentOf π) (V (pairWords x r)))) h

end Complexity

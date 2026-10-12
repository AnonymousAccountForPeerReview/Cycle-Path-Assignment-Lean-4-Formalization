module

public import Hardness.Verifier.Words
public import ComplexityExt.Reg.Closure
public import ComplexityExt.Reg.Decide
public import Complexity.SATBounds

/-!
# From a PCP verifier to an NP verifier

A PCP verifier with `O(log n)` random bits has only polynomially many random strings, so an
NP verifier can try them all: the certificate is the proof, cut down to the polynomially many
bits that the verifier can address at all (variable indices are written in unary, so they
are smaller than the length of the code of the verifier's output).  Completeness of the PCP
verifier gives a certificate; conversely a certificate is a proof accepted for *all* random
strings, which soundness (at most half accepted) excludes for non-members.

The polynomial-time computability of the checking function is a hypothesis (`hχ`) here.
-/

@[expose] public section

namespace Complexity

/-- The NP checker of a PCP verifier `V` with `c * log₂ (|x| + 2)` random bits.
With `(x, π) = unpair w`: `[true]` if the assignment `SAT.assignmentOf π` satisfies
`V (pairWords x r)` for every `r` in `allWords (c * Nat.log2 (x.length + 2))`, else `[false]`. -/
def pcpChecker (V : Word → SAT.CNF) (c : Nat) (w : Word) : Word :=
  if (allWords (c * Nat.log2 ((Reg.unpair w).1.length + 2))).all
      (fun r => SAT.evalCNF (SAT.assignmentOf (Reg.unpair w).2)
        (V (pairWords (Reg.unpair w).1 r)))
  then [true] else [false]

theorem pcpChecker_pairWords_eq_true (V : Word → SAT.CNF) (c : Nat) (x π : Word) :
    pcpChecker V c (pairWords x π) = [true] ↔
      ∀ r ∈ allWords (c * Nat.log2 (x.length + 2)),
        SAT.evalCNF (SAT.assignmentOf π) (V (pairWords x r)) = true := by
  simp [pcpChecker]

/-- The word listing the first `n` values of an assignment writes that assignment below `n`. -/
theorem assignmentOf_map_range (a : SAT.Assignment) (n i : Nat) (h : i < n) :
    SAT.assignmentOf ((List.range n).map a) i = a i := by
  simp [SAT.assignmentOf, List.getD_eq_getElem?_getD, h]

/-- All variables that a polynomial-time verifier with logarithmic randomness can mention are
below a polynomial in the input length. -/
theorem exists_query_bound {V : Word → SAT.CNF} (hV : PolyTime (fun w => SAT.encode (V w)))
    (c : Nat) :
    ∃ c' e', ∀ x r, r ∈ allWords (c * Nat.log2 (x.length + 2)) →
      SAT.variableBound (V (pairWords x r)) ≤ powerBound c' e' x.length := by
  obtain ⟨cV, eV, hc⟩ := Reg.TimeBounded.of_polyTime hV
  have hW : PolynomialBound (fun n => 2 * n + 1 + c * (n + 2)) :=
    (((PolynomialBound.constant 2).mul PolynomialBound.identity).add
      (PolynomialBound.constant 1)).add
      ((PolynomialBound.constant c).mul (PolynomialBound.identity.add (PolynomialBound.constant 2)))
  obtain ⟨c', e', h⟩ := hW.add
    ((PolynomialBound.constant 2).mul ((PolynomialBound.power cV eV).comp hW))
  refine ⟨c', e', fun x r hr => ?_⟩
  have h1 := SATBounds.variableBound_le_encode_length (V (pairWords x r))
  have h2 := hc.length_le (pairWords x r)
  have hlen : r.length = c * Nat.log2 (x.length + 2) := mem_allWords.mp hr
  have hlog : c * Nat.log2 (x.length + 2) ≤ c * (x.length + 2) :=
    Nat.mul_le_mul_left c (Nat.log2_le_self _)
  have h3 : (pairWords x r).length ≤ 2 * x.length + 1 + c * (x.length + 2) := by
    rw [pairWords_length]
    omega
  have h4 := powerBound_mono cV eV h3
  have h5 := h x.length
  simp only at h5
  omega

/-- **PCP ⊆ NP.**  If `V` is a PCP verifier for `L` with `c * log₂ (|x| + 2)` random bits
and its checking function `pcpChecker V c` is polynomial-time computable, then `L ∈ NP`. -/
theorem inNP_of_inPCP_checker {c q : Nat} {L : Language} {V : Word → SAT.CNF}
    (hV : PolyTime (fun w => SAT.encode (V w)))
    (hspec : ∀ x : Word,
      (∀ r ∈ allWords (c * Nat.log2 (x.length + 2)), QueriesAtMost q (V (pairWords x r))) ∧
      (L x → ∃ proof : SAT.Assignment,
        ∀ r ∈ allWords (c * Nat.log2 (x.length + 2)),
          SAT.evalCNF proof (V (pairWords x r)) = true) ∧
      (¬ L x → ∀ proof : SAT.Assignment,
        2 * ((allWords (c * Nat.log2 (x.length + 2))).countP fun r =>
            SAT.evalCNF proof (V (pairWords x r))) ≤
          (allWords (c * Nat.log2 (x.length + 2))).length))
    (hχ : PolyTime (pcpChecker V c)) : InNP L := by
  obtain ⟨c', e', hbound⟩ := exists_query_bound hV c
  refine Reg.inNP_of_polyTime hχ c' e' (fun x => ?_)
  obtain ⟨-, hyes, hno⟩ := hspec x
  constructor
  · intro hx
    obtain ⟨proof, hp⟩ := hyes hx
    refine ⟨(List.range (powerBound c' e' x.length)).map proof, by simp, ?_⟩
    rw [pcpChecker_pairWords_eq_true]
    intro r hr
    rw [← hp r hr]
    apply ThreeSAT.evalCNF_agrees (n := powerBound c' e' x.length)
    · intro cl hcl l hl
      exact Nat.lt_of_lt_of_le (SAT.literal_lt_variableBound hcl hl) (hbound x r hr)
    · intro i hi
      exact assignmentOf_map_range proof _ i hi
  · rintro ⟨π, -, hacc⟩
    rw [pcpChecker_pairWords_eq_true] at hacc
    refine Classical.byContradiction fun hx => ?_
    have h := hno hx (SAT.assignmentOf π)
    have hall : (allWords (c * Nat.log2 (x.length + 2))).countP
        (fun r => SAT.evalCNF (SAT.assignmentOf π) (V (pairWords x r))) =
        (allWords (c * Nat.log2 (x.length + 2))).length := List.countP_eq_length.mpr hacc
    rw [hall, allWords_length] at h
    have hpos : 0 < 2 ^ (c * Nat.log2 (x.length + 2)) := Nat.pow_pos (by decide)
    omega

end Complexity

module

public import Hardness.Verifier.Words
public import ComplexityExt.Reg.Closure
public import Complexity.SATBounds
import Mathlib.Tactic.Ring

/-!
# From a gap reduction to a PCP verifier

Given a gap reduction `g` from `L` to 3-SAT with gap `num / den`, the *clause-sampling
verifier* reads its random string as `k = 2 * den` blocks of `ℓ = B * log₂ (|x| + 2)` bits,
turns each block into a clause index of `φ = g x` by reduction modulo the number of clauses,
and outputs the conjunction of the `k` sampled clauses.  It queries at most `3 * k` proof bits.

* If `x ∈ L`, a satisfying assignment of `φ` is accepted for every random string.
* If `x ∉ L`, every assignment leaves at least `num / den` of the `m` clauses unsatisfied.
  As `m ≤ 2 ^ ℓ`, every clause index has at least `⌊2 ^ ℓ / m⌋ ≥ 2 ^ ℓ / (2 * m)` preimages,
  so one block hits an unsatisfied clause with probability at least `num / (2 * den) ≥ 1 / k`,
  and all `k` independent blocks miss with probability at most `(1 - 1/k) ^ k ≤ 1/2`.

The polynomial-time computability of the verifier is a hypothesis (`hV`) here.
-/

@[expose] public section

namespace Complexity

/-- The clause-sampling verifier: with `(x, r) = unpair w`, `φ = g x` and block length
`ℓ = B * Nat.log2 (x.length + 2)`, it outputs the list of the `k` clauses
`φ.getD (binValue b % φ.length) []` for the blocks `b` of `r`. -/
def samplingVerifier (g : Word → SAT.CNF) (k B : Nat) (w : Word) : SAT.CNF :=
  (blocks k (B * Nat.log2 ((Reg.unpair w).1.length + 2)) (Reg.unpair w).2).map
    (fun b => (g (Reg.unpair w).1).getD (binValue b % (g (Reg.unpair w).1).length) [])

theorem samplingVerifier_pairWords (g : Word → SAT.CNF) (k B : Nat) (x r : Word) :
    samplingVerifier g k B (pairWords x r) =
      (blocks k (B * Nat.log2 (x.length + 2)) r).map
        (fun b => (g x).getD (binValue b % (g x).length) []) := by
  simp [samplingVerifier]

theorem getD_mem {α : Type} (l : List α) (i : Nat) (h : i < l.length) (d : α) :
    l.getD i d ∈ l := by
  simp [List.getD_eq_getElem?_getD, h]

/-! ### Queries -/

theorem length_flatMap_vars_le (f : SAT.CNF) (h3 : ∀ c ∈ f, c.length ≤ 3) :
    (f.flatMap fun c => c.map SAT.Literal.var).length ≤ 3 * f.length := by
  induction f with
  | nil => simp
  | cons c f ih =>
    have hc := h3 c (by simp)
    have hf := ih (fun d hd => h3 d (by simp [hd]))
    simp only [List.flatMap_cons, List.length_append, List.length_map, List.length_cons]
    omega

/-- A formula with at most `k` clauses of at most three literals mentions at most `3 * k`
variables. -/
theorem queriesAtMost_of_clauses (f : SAT.CNF) (k : Nat) (hlen : f.length ≤ k)
    (h3 : ∀ c ∈ f, c.length ≤ 3) : QueriesAtMost (3 * k) f := by
  refine ⟨f.flatMap fun c => c.map SAT.Literal.var, ?_, ?_⟩
  · have := length_flatMap_vars_le f h3
    omega
  · intro c hc l hl
    exact List.mem_flatMap.mpr ⟨c, hc, List.mem_map.mpr ⟨l, hl, rfl⟩⟩

/-! ### Soundness: the counting argument -/

theorem countP_add_countP_not {α : Type} (p : α → Bool) (l : List α) :
    l.countP p + l.countP (fun a => !p a) = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.countP_cons, List.length_cons]
    cases p a <;> simp <;> omega

/-- One block: if at most the fraction `1 - num / den` of the `m` entries is good and
`m ≤ N`, then at most the fraction `1 - 1 / (2 * den)` of the values `v < N` has a good
residue `v % m`. -/
theorem sampling_count (sat : Nat → Bool) (m N num den : Nat) (hm : 0 < m) (hmN : m ≤ N)
    (hnum : 0 < num)
    (hgap : den * (List.range m).countP sat + num * m ≤ den * m) :
    2 * den * (List.range N).countP (fun v => sat (v % m)) + N ≤ 2 * den * N := by
  have hST := countP_add_countP_not (fun v => sat (v % m)) (List.range N)
  have hU := countP_add_countP_not sat (List.range m)
  rw [List.length_range] at hST hU
  have hq : 0 < N / m := Nat.div_pos hmN hm
  have hdm := Nat.div_add_mod N m
  have hmod := Nat.mod_lt N hm
  have hle : m * (N / m) ≤ N := Nat.mul_div_le N m
  have hT : N / m * (List.range m).countP (fun a => !sat a) ≤
      (List.range N).countP (fun v => !sat (v % m)) := by
    rw [← countP_mod_range_mul (fun a => !sat a) m (N / m)]
    exact countP_range_mono _ hle
  generalize (List.range N).countP (fun v => sat (v % m)) = S at *
  generalize (List.range N).countP (fun v => !sat (v % m)) = T at *
  generalize (List.range m).countP sat = s at *
  generalize (List.range m).countP (fun a => !sat a) = U at *
  generalize N / m = q at *
  -- `num * m ≤ den * U`
  have h1 : num * m ≤ den * U := by
    have : den * m = den * s + den * U := by rw [← hU]; ring
    omega
  have h2 : m ≤ m * q := Nat.le_mul_of_pos_right m hq
  have h3 : N ≤ 2 * (m * q) := by omega
  have h4 : N ≤ 2 * den * T := by
    calc N ≤ num * N := Nat.le_mul_of_pos_left N hnum
      _ ≤ num * (2 * (m * q)) := Nat.mul_le_mul_left num h3
      _ = 2 * q * (num * m) := by ring
      _ ≤ 2 * q * (den * U) := Nat.mul_le_mul_left _ h1
      _ = 2 * den * (q * U) := by ring
      _ ≤ 2 * den * T := Nat.mul_le_mul_left _ hT
  have h5 : 2 * den * N = 2 * den * S + 2 * den * T := by rw [← hST]; ring
  omega

/-- **NP ⊆ PCP from a gap reduction.**  The clause-sampling verifier with `2 * den` blocks
is a PCP verifier for `L` using `2 * den * B * log₂ (|x| + 2)` random bits and at most
`3 * (2 * den)` queries, provided `B` is large enough that a block can address every clause,
and provided the verifier is polynomial-time computable. -/
theorem inPCP_of_gapReduction {num den : Nat} {L : Language} {g : Word → SAT.CNF}
    (hnum : 0 < num) (hg : GapReduction num den L g) (B : Nat)
    (hB : ∀ x, (g x).length ≤ 2 ^ (B * Nat.log2 (x.length + 2)))
    (hV : PolyTime (fun w => SAT.encode (samplingVerifier g (2 * den) B w))) :
    InPCP (2 * den * B) (3 * (2 * den)) L := by
  obtain ⟨-, hspec⟩ := hg
  refine ⟨samplingVerifier g (2 * den) B, hV, fun x => ?_⟩
  obtain ⟨h3, hne, hyes, hno⟩ := hspec x
  have hm : 0 < (g x).length := List.length_pos_iff.mpr hne
  have hclause : ∀ v, (g x).getD (v % (g x).length) [] ∈ g x :=
    fun v => getD_mem _ _ (Nat.mod_lt _ hm) _
  refine ⟨?_, ?_, ?_⟩
  · intro r _
    rw [samplingVerifier_pairWords]
    apply queriesAtMost_of_clauses
    · simp
    · intro c hc
      obtain ⟨b, _, rfl⟩ := List.mem_map.mp hc
      exact h3 _ (hclause _)
  · intro hx
    obtain ⟨a, ha⟩ := hyes hx
    refine ⟨a, fun r _ => ?_⟩
    rw [samplingVerifier_pairWords]
    simp only [SAT.evalCNF, List.all_eq_true] at ha ⊢
    intro c hc
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hc
    exact ha _ (hclause _)
  · intro hx a
    have hgap := hno hx a
    have hcount : (allWords (2 * den * B * Nat.log2 (x.length + 2))).countP
          (fun r => SAT.evalCNF a (samplingVerifier g (2 * den) B (pairWords x r))) =
        ((List.range (2 ^ (B * Nat.log2 (x.length + 2)))).countP
          (fun v => SAT.evalClause a ((g x).getD (v % (g x).length) []))) ^ (2 * den) := by
      rw [Nat.mul_assoc (2 * den) B,
        ← countP_binValue (fun v => SAT.evalClause a ((g x).getD (v % (g x).length) [])),
        ← countP_blocks]
      congr 1
      funext r
      rw [samplingVerifier_pairWords, SAT.evalCNF, List.all_map]
      rfl
    rw [hcount, allWords_length, Nat.mul_assoc (2 * den) B,
      Nat.pow_mul' 2 (2 * den) (B * Nat.log2 (x.length + 2))]
    apply gap_power _ _ _ _ (Nat.pow_pos (by decide))
    refine sampling_count (fun i => SAT.evalClause a ((g x).getD i [])) _ _ num den hm (hB x)
      hnum ?_
    rw [countP_range_getD (SAT.evalClause a) (g x) []]
    exact hgap

/-! ### Choosing the block length -/

/-- Polynomially many clauses can be addressed by `O(log n)` bits. -/
theorem exists_blockExponent (c e : Nat) :
    ∃ B, ∀ n, powerBound c e n ≤ 2 ^ (B * Nat.log2 (n + 2)) := by
  refine ⟨c + 2 * e, fun n => ?_⟩
  have h1 : 1 ≤ Nat.log2 (n + 2) := (Nat.le_log2 (by omega)).mpr (by simp)
  have h2 : n + 2 < 2 ^ (Nat.log2 (n + 2) + 1) := Nat.lt_log2_self
  generalize Nat.log2 (n + 2) = l at h1 h2 ⊢
  have h3 : 2 ^ (l + 1) ≤ 2 ^ (2 * l) := Nat.pow_le_pow_right (by decide) (by omega)
  have h4 : (n + 1) ^ e ≤ 2 ^ (2 * l * e) := by
    rw [Nat.pow_mul]
    exact Nat.pow_le_pow_left (by omega) e
  have h5 : c ≤ 2 ^ (c * l) :=
    Nat.le_trans (Nat.le_of_lt Nat.lt_two_pow_self)
      (Nat.pow_le_pow_right (by decide) (Nat.le_mul_of_pos_right c h1))
  rw [powerBound_eq, show (c + 2 * e) * l = c * l + 2 * l * e by ring, Nat.pow_add]
  exact Nat.mul_le_mul h5 h4

theorem length_le_encode_length (f : SAT.CNF) : f.length ≤ (SAT.encode f).length := by
  simp only [SAT.encode, SAT.writeList, List.length_append, SATBounds.writeNat_length]
  omega

/-- The number of clauses produced by a polynomial-time formula-valued function is
polynomially bounded. -/
theorem exists_clause_bound {g : Word → SAT.CNF} (hg : PolyTime (fun x => SAT.encode (g x))) :
    ∃ c e, ∀ x, (g x).length ≤ powerBound c e x.length := by
  obtain ⟨c, e, hc⟩ := Reg.TimeBounded.of_polyTime hg
  obtain ⟨c', e', h⟩ := PolynomialBound.identity.add
    ((PolynomialBound.constant 2).mul (PolynomialBound.power c e))
  refine ⟨c', e', fun x => ?_⟩
  have h1 := length_le_encode_length (g x)
  have h2 := hc.length_le x
  have h3 := h x.length
  simp only at h3
  omega

/-- A suitable block exponent `B` exists for every polynomial-time formula-valued function. -/
theorem exists_blockExponent_of_polyTime {g : Word → SAT.CNF}
    (hg : PolyTime (fun x => SAT.encode (g x))) :
    ∃ B, ∀ x, (g x).length ≤ 2 ^ (B * Nat.log2 (x.length + 2)) := by
  obtain ⟨c, e, hce⟩ := exists_clause_bound hg
  obtain ⟨B, hB⟩ := exists_blockExponent c e
  exact ⟨B, fun x => Nat.le_trans (hce x) (hB x.length)⟩

/-- NP ⊆ PCP from a gap reduction, with the block exponent chosen: it remains to show that
the clause-sampling verifiers are polynomial-time computable. -/
theorem exists_inPCP_of_gapReduction {num den : Nat} {L : Language} {g : Word → SAT.CNF}
    (hnum : 0 < num) (hg : GapReduction num den L g)
    (hV : ∀ B, PolyTime (fun w => SAT.encode (samplingVerifier g (2 * den) B w))) :
    ∃ c q, InPCP c q L := by
  obtain ⟨B, hB⟩ := exists_blockExponent_of_polyTime hg.1
  exact ⟨_, _, inPCP_of_gapReduction hnum hg B hB (hV B)⟩

end Complexity

module

public import ApproximationHardness.RAM.Decode.Correct
public import NPHardness.TaggedGraph
import Lean.Elab.Tactic.Omega

/-!
# The decoding program runs in linear time and space

`dec_linear`: on every input, the decoding program halts within `decConst k · (N + n + 1)` steps,
where `N` is the length of the input and `n = variableBound f`, accessing only the addresses below
`(2w + 4) · (N + n + 1)`, `w = gadgetWidth k`.

`decoder_linear_time`: on the formulas of Definition 7 and the valid choices `ps` for the cycles of
`formulaGraph k f`, it halts within `decLinConst k · (n + 1)` steps, accessing only the addresses
below `decSpaceConst k · (n + 1)`, with output the bits of `decodeAssign k ps`, which satisfies the
inequality of Theorem 11 (`cpap_lreduction_decoder`).
-/

@[expose] public section

namespace STACS2027.RAM

open Complexity.SAT

/-- The step constant of the decoding program, per input number and per variable. -/
def decConst (k : Nat) : Nat :=
  size passApre + clauseACost + size passApost + size scanPre + size skipPath + size (tabPre k) +
    gadgetWidth k * (size fillCell + 1) + size procPre + size pathPre + size flagEdge + size countEdge +
    size outPre + size outBodyD + 30

theorem pathLoop_sum (ps : List (List Edge)) :
    (ps.map fun p => pathCost p + 1).sum =
      ps.length * (size pathPre + 7) + (ps.map List.length).sum * (size flagEdge + size countEdge + 2) := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    rw [List.map_cons, List.sum_cons, ih]
    simp only [List.length_cons, pathCost, List.map_cons, List.sum_cons, Nat.succ_mul, Nat.add_mul, Nat.mul_add]
    omega

theorem decCost_le (k : Nat) (f : CNF) (ps : List (List Edge)) :
    decCost k f ps ≤ decConst k * (f.length + variableBound f + ps.length + (ps.map List.length).sum + 1) := by
  unfold decCost passACost
  rw [pathLoop_sum, sum_map_const_succ]
  unfold decConst
  generalize size passApre = a1
  generalize clauseACost = a2
  generalize size passApost = a3
  generalize size scanPre = a4
  generalize size skipPath = a5
  generalize size (tabPre k) = a6
  generalize gadgetWidth k * (size fillCell + 1) = a7
  generalize size procPre = a8
  generalize size pathPre = a9
  generalize size flagEdge = a10
  generalize size countEdge = a11
  generalize size outPre = a12
  generalize size outBodyD = a13
  generalize f.length = m
  generalize variableBound f = n
  generalize ps.length = P
  generalize (ps.map List.length).sum = Q
  simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul, Nat.mul_comm]
  omega

theorem flatMap_pathCode_length (ps : List (List Edge)) :
    (ps.flatMap pathCode).length = ps.length + 2 * (ps.map List.length).sum := by
  induction ps with
  | nil => simp
  | cons p ps ih => simp only [List.flatMap_cons, List.length_append, ih, pathCode_length, List.map_cons,
      List.sum_cons, List.length_cons]; omega

theorem ramInput_length_ge (f : CNF) : f.length + 1 ≤ (ramInput f).length := by
  unfold ramInput
  simp only [List.length_cons]
  suffices h : f.length ≤ (f.flatMap clauseCode).length by omega
  induction f with
  | nil => simp
  | cons c f ih => simp only [List.flatMap_cons, List.length_append, clauseCode_length, List.length_cons]; omega

/-- **Linear time and space.** On every formula with clauses of at most three literals and every list
of paths whose vertices are below `(m + n) · gadgetWidth k`, the decoding program halts with output
`decOutput k f ps` within `decConst k · (N + n + 1)` steps, `N` the length of the input, accessing
only the addresses below `(2 · gadgetWidth k + 4) · (N + n + 1)`. -/
theorem dec_linear (k : Nat) (f : CNF) (hf : ∀ c ∈ f, c.length ≤ 3) (ps : List (List Edge))
    (hb : PathsBelow k f ps) :
    ∃ t, ComputesIn (decProgram k) (decInput f ps) (decOutput k f ps) t
        ((2 * gadgetWidth k + 4) * ((decInput f ps).length + variableBound f + 1)) ∧
      t ≤ decConst k * ((decInput f ps).length + variableBound f + 1) := by
  obtain ⟨t, hc, ht⟩ := dec_computes k f hf ps hb
  have h1 := ramInput_length_ge f
  have hl := decInput_length f ps
  refine ⟨t, hc.mono ?_, Nat.le_trans ht (Nat.le_trans (decCost_le k f ps) (Nat.mul_le_mul_left _ ?_))⟩
  · unfold decSpace
    generalize (decInput f ps).length = N at hl ⊢
    generalize gadgetWidth k = w
    generalize variableBound f = n
    have h2 : (f.length + n) * w ≤ (N + n + 1) * w := Nat.mul_le_mul_right _ (by omega)
    have e : (2 * w + 4) * (N + n + 1) = 2 * ((N + n + 1) * w) + 4 * (N + n + 1) := by
      rw [Nat.add_mul, Nat.mul_assoc, Nat.mul_comm w]
    rw [e]; omega
  · rw [decInput_length, flatMap_pathCode_length]
    omega

/-! ### On the instances of Theorem 11 -/

theorem clauseFamily_length_le (k : Nat) (hk : 5 ≤ k) (c : List PlacedLiteral) :
    (clauseFamily k hk c).length ≤ 10 := by
  unfold clauseFamily
  split
  · split
    · simp +decide []
    · simp only [List.length_map]; decide
  · simp only [List.length_map]; decide

theorem formulaFamily_length_le (k : Nat) (hk : 5 ≤ k) (f : CNF) :
    (formulaFamily k hk f).length ≤ 2 * variableBound f + 10 * f.length := by
  unfold formulaFamily
  rw [List.length_append, List.length_flatMap]
  have hvar : ((List.range (variableBound f)).map fun v => (placedVariableFamily k hk v).length) =
      (List.range (variableBound f)).map (fun _ => 2) := by
    apply List.map_congr_left
    intro v _
    simp only [placedVariableFamily, variableFamily, List.length_map]; decide
  rw [hvar, sum_map_const, List.length_range]
  rw [mapIdx_eq_range _ [], List.length_flatten, List.map_map]
  have hle := sum_map_le (List.range (placeFormula [] f).length)
    (fun j => (placedClauseFamily k hk (variableBound f) j ((placeFormula [] f)[j]?.getD [])).length)
    (fun _ => 10) (by
      intro j _
      simp only [placedClauseFamily, List.length_map]
      exact clauseFamily_length_le k hk _)
  simp only [sum_map_const, List.length_range, placeFormula_length] at hle
  simp only [Function.comp_def, placeFormula_length]
  omega

/-- The valid choices for the cycles of `formulaGraph k f`: their number, their lengths and their
vertices. -/
theorem validChoices_shape {k : Nat} (hk : 5 ≤ k) {f : CNF} (hf : LeOneLeTwoCNF f) {ps : List (List Edge)}
    (hv : ValidChoices ((cycles (formulaGraph k f) k).map selectedOptions) ps) :
    ps.length ≤ 2 * variableBound f + 10 * f.length ∧ (ps.map List.length).sum = ps.length * (k - 2) ∧
      PathsBelow k f ps := by
  obtain ⟨-, -, hlen, hedge⟩ := validChoices_properties hv (fun _ hc => enumerated_isCycle hc)
  obtain ⟨pick, -, -, hsum⟩ := decoder_transport hk hf.1 hf.2 hv
  have hP : ps.length = (formulaFamily k hk f).length := by
    have := hsum (fun _ => 1) (fun _ _ _ => rfl)
    simpa [sum_map_const, chosenFamily, Function.comp_def] using this
  refine ⟨hP ▸ formulaFamily_length_le k hk f, ?_, ?_⟩
  · rw [List.map_congr_left hlen, sum_map_const]
  · intro p hp e he
    have := formulaGraph_below (k := k) hf.1 e (hedge p hp e he)
    rw [Nat.add_comm (variableBound f)] at this
    exact this

/-- The step constant on the instances of Theorem 11. -/
def decLinConst (k : Nat) : Nat := decConst k * (3 + 17 * (k - 1))

/-- The space constant on the instances of Theorem 11. -/
def decSpaceConst (k : Nat) : Nat := 50 + 34 * (k - 2) + 5 * gadgetWidth k

/-- On the instances of Theorem 11 the space of the decoding program is linear in `n`. -/
theorem decSpace_le {k : Nat} (hk : 5 ≤ k) {f : CNF} (hf : LeOneLeTwoCNF f) {ps : List (List Edge)}
    (hv : ValidChoices ((cycles (formulaGraph k f) k).map selectedOptions) ps) :
    decSpace k f ps ≤ decSpaceConst k * (variableBound f + 1) := by
  obtain ⟨hP, hQ, -⟩ := validChoices_shape hk hf hv
  have hm := hf.1.clause_count_variableBound
  have hN := clauseCodes_length_le f (fun c hc => by rcases hf.1.1 c hc with h | h <;> omega)
  have hK : 3 ≤ k - 2 := by omega
  unfold decSpace decSpaceConst
  rw [decInput_length, flatMap_pathCode_length, hQ]
  have hR : (ramInput f).length = 1 + (f.flatMap clauseCode).length := by simp [ramInput]; omega
  rw [hR]
  generalize (f.flatMap clauseCode).length = L at hN ⊢
  generalize ps.length = P at hP ⊢
  generalize gadgetWidth k = w
  generalize k - 2 = K at hK ⊢
  generalize f.length = m at hP hm hN ⊢
  generalize variableBound f = n at hP hm ⊢
  have h1 : P * K ≤ 17 * (K * n) :=
    Nat.le_trans (Nat.mul_le_mul_right _ (by omega : P ≤ 17 * n)) (by rw [Nat.mul_assoc, Nat.mul_comm n K]; exact Nat.le_refl _)
  have h2 : (m + n) * w + (m + n) * w ≤ 5 * (w * n) := by
    rw [← Nat.add_mul]
    exact Nat.le_trans (Nat.mul_le_mul_right _ (by omega : m + n + (m + n) ≤ 5 * n))
      (by rw [Nat.mul_assoc, Nat.mul_comm n w]; exact Nat.le_refl _)
  have e : (50 + 34 * K + 5 * w) * (n + 1) = 50 * n + 50 + 34 * (K * n) + 34 * K + 5 * (w * n) + 5 * w := by
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.mul_assoc]; omega
  rw [e]; omega

/-- **The decoding map of Theorem 11 in linear time.** For `k ≥ 5`, every formula `f` of
Definition 7 and every valid choice `ps` of paths for the cycles of `formulaGraph k f`, the decoding
program halts on `f, ps` within `decLinConst k · (n + 1)` steps, `n = variableBound f`, with output
the bits of `decodeAssign k ps`. -/
theorem decoder_linear_time {k : Nat} (hk : 5 ≤ k) {f : CNF} (hf : LeOneLeTwoCNF f) {ps : List (List Edge)}
    (hv : ValidChoices ((cycles (formulaGraph k f) k).map selectedOptions) ps) :
    ∃ t, ComputesIn (decProgram k) (decInput f ps) (decOutput k f ps) t (decSpaceConst k * (variableBound f + 1)) ∧
      t ≤ decLinConst k * (variableBound f + 1) := by
  obtain ⟨hP, hQ, hb⟩ := validChoices_shape hk hf hv
  have hf3 : ∀ c ∈ f, c.length ≤ 3 := fun c hc => by rcases hf.1.1 c hc with h | h <;> omega
  obtain ⟨t, hc, ht⟩ := dec_computes k f hf3 ps hb
  refine ⟨t, hc.mono (decSpace_le hk hf hv), Nat.le_trans ht (Nat.le_trans (decCost_le k f ps) ?_)⟩
  unfold decLinConst
  rw [Nat.mul_assoc]
  apply Nat.mul_le_mul_left
  have hm := hf.1.clause_count_variableBound
  rw [hQ]
  generalize ps.length = P at hP
  generalize f.length = m at hP hm
  generalize variableBound f = n at hP hm
  have hPK : P + P * (k - 2) = P * (k - 1) := by
    rw [show k - 1 = (k - 2) + 1 by omega, Nat.mul_add, Nat.mul_one, Nat.add_comm]
  have hle : P * (k - 1) ≤ 17 * n * (k - 1) := Nat.mul_le_mul_right _ (by omega)
  generalize k - 1 = K at hPK hle
  rw [Nat.mul_assoc] at hle
  rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_one, Nat.mul_one, Nat.mul_assoc, Nat.mul_comm K n]
  omega

/-- **Theorem 11's decoding map, computed.** Under the hypotheses of `decoder_linear_time`, the
program's output is the assignment `A = decodeAssign k ps` (bit `1` for true), and for every
optimum `S` of Max-2/3-SAT on `f` and every optimum `C` of `CPAP(formulaGraph k f, k)`,
`S + C ≤ sat(A) + cost(ps)`. -/
theorem decoder_ram {k : Nat} (hk : 5 ≤ k) {f : CNF} (hf : LeOneLeTwoCNF f) {ps : List (List Edge)}
    (hv : ValidChoices ((cycles (formulaGraph k f) k).map selectedOptions) ps) :
    (∃ t, ComputesIn (decProgram k) (decInput f ps)
        ((List.range (variableBound f)).map fun v => if decodeAssign k ps v then 1 else 0) t
        (decSpaceConst k * (variableBound f + 1)) ∧
      t ≤ decLinConst k * (variableBound f + 1)) ∧
    ∀ S C, IsMaxSat f S → IsMinCost (formulaGraph k f) k C →
      S + C ≤ satisfiedCount (decodeAssign k ps) f + STACS2027.cost ps :=
  ⟨decoder_linear_time hk hf hv, fun S C hS hC => cpap_lreduction_decoder hk f hf S C hS hC ps hv⟩

end STACS2027.RAM

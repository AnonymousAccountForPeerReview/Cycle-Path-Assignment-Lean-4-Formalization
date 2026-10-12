module

public import ApproximationHardness.RAM.Polarize.Main
import Lean.Elab.Tactic.Omega

/-!
# Lemma 10's transformation in linear time on the RAM

`pol_computes`: on `ramInput f`, for every formula whose clauses have two or three literals,
`polProgram` halts with output `ramInput (polarize f)` within `polCost f ≤ polConst (m + 1)`
steps, accessing only the addresses below `polSpace f = N + 3n` (`N = |ramInput f|`); under the
occurrence bound of 3-OCCURRENCE MAX-3-SAT, `m ≤ 3n/2`, and both are linear in `n`
(`polarize_linear_time`).
-/

@[expose] public section

namespace STACS2027.RAM

open Complexity.SAT

theorem loopFree_cntBody : LoopFree cntBody := by
  simp [cntBody, readClause, rdLit, ifThird, cntLit, seqs, LoopFree]
theorem loopFree_keepBody : LoopFree keepBody := by
  simp [keepBody, readClause, rdLit, ifThird, kpLit, delCode, tautPair, pureLit, seqs, LoopFree]
theorem loopFree_outBody : LoopFree outBody := by
  simp [outBody, readClause, rdLit, ifThird, outLit, delCode, tautPair, pureLit, seqs, LoopFree]
theorem loopFree_padBody : LoopFree padBody := by simp [padBody, seqs, LoopFree]

/-- The step count of the Lemma 10 program. -/
def polCost (f : CNF) : Nat :=
  passACost f + size polSetup + size restart + (f.length * (size cntBody + 1) + 1) + size restart +
    (f.length * (size keepBody + 1) + 1) + size restart + (f.length * (size outBody + 1) + 1) + 1 +
    (deletedCount f * (size padBody + 1) + 1)

theorem polarize_length (f : CNF) : (polarize f).length = f.length := by
  have h := List.length_eq_countP_add_countP (fun c => !deleted f c) (l := f)
  simp only [polarize, flipFormula, List.length_append, List.length_map, padding, List.length_range, kept,
    deletedCount, List.countP_eq_length_filter] at h ⊢
  have : (f.filter fun a => ¬(!deleted f a) = true).length = (f.filter (deleted f)).length := by
    congr 1; apply List.filter_congr; intro x _; cases deleted f x <;> rfl
  omega

theorem pol_computes (f : CNF) (hf : ∀ c ∈ f, c.length = 2 ∨ c.length = 3) :
    ∃ t, ComputesIn polProgram (ramInput f) (ramInput (polarize f)) t (polSpace f) ∧ t ≤ polCost f := by
  have hf3 : ∀ c ∈ f, c.length ≤ 3 := fun c hc => by rcases hf c hc with h | h <;> omega
  have hSN : (ramInput f).length ≤ polSpace f := by unfold polSpace polB polN; omega
  have hS0 : 0 < polSpace f := Nat.lt_of_lt_of_le (by simp [ramInput]) hSN
  -- the first pass
  obtain ⟨t1, e1, ht1⟩ := sat_passA f hf3 hSN _ rfl
  obtain ⟨a_mem, a_out, a_one, a_zero, a_n, a_N, a_B⟩ := passAModel_initial f
  generalize hc1 : passAModel (initial (ramInput f)) = c1 at e1 a_mem a_out a_one a_zero a_n a_N a_B
  -- the setup
  have e2 := execB_run (S := polSpace f) polSetup (by simp [polSetup, seqs, LoopFree]) c1 (AddrOK.of_memFree rfl)
  generalize hc2 : run polSetup c1 = c2 at e2
  have s_fr : ∀ r, r ≠ PR.two → r ≠ PR.three → r ≠ PR.r → c2.reg r = c1.reg r := by
    intro r a b d; rw [← hc2]; simp [polSetup, run, a, b, d]
  have s2 : c2.reg PR.two = 2 ∧ c2.reg PR.three = 3 ∧ c2.reg PR.r = 0 := by
    rw [← hc2]; simp +decide [polSetup, run]
  have s_mem : c2.mem = polBase f := by rw [← hc2]; simp [polSetup, run, a_mem]; rfl
  have s_out : c2.out = [f.length] := by rw [← hc2]; simp [polSetup, run, a_out]
  have R2 : PolRegs f c2 := ⟨⟨by rw [s_fr _ (by decide) (by decide) (by decide)]; exact a_one,
      by rw [s_fr _ (by decide) (by decide) (by decide)]; exact a_zero, s2.1, s2.2.1⟩,
    by rw [s_fr _ (by decide) (by decide) (by decide)]; exact a_N,
    by rw [s_fr _ (by decide) (by decide) (by decide), a_B]; rfl,
    by rw [s_fr _ (by decide) (by decide) (by decide)]; exact a_n⟩
  -- the count pass
  have e3 := execB_run restart (by simp [restart, seqs, LoopFree]) c2 (restart_addrOK _ hS0)
  obtain ⟨r_m, r_p, r_at, r_mem, r_out, r_fr⟩ := restart_run f c2 R2.k.one (by rw [s_mem]; intro _ _; rfl)
  generalize hc3 : run restart c2 = c3 at e3 r_m r_p r_at r_mem r_out r_fr
  have R3 : PolRegs f c3 := R2.frame (fun r hr => r_fr r hr.1.1 hr.1.2.2.1)
  have hC := sat_clausePass (S := polSpace f) f loopFree_cntBody (fun pre c => CntInv f c pre) (cnt_step f hf)
  have P3 : PassInv f (fun pre c => CntInv f c pre) c3 := ⟨[], f, rfl, r_m, r_at,
    by rw [r_mem, s_mem]; funext a; simp [cntMem], by rw [r_p]; rfl, R3,
    by rw [r_fr _ (by decide) (by decide)]; exact s2.2.2, by rw [r_out]; exact s_out⟩
  obtain ⟨t4, e4, ht4⟩ := hC.1 c3 P3
  have I4 := hC.2 c3 P3
  dsimp only at e4
  rw [r_m] at e4 I4
  generalize hc4 : iterate (run cntBody) f.length c3 = c4 at e4 I4
  obtain ⟨i4_mem, -, R4, i4_r, i4_out⟩ := I4
  -- the keep pass
  have e5 := execB_run restart (by simp [restart, seqs, LoopFree]) c4 (restart_addrOK _ hS0)
  obtain ⟨r5_m, r5_p, r5_at, r5_mem, r5_out, r5_fr⟩ := restart_run f c4 R4.k.one
    (by rw [i4_mem]; exact inputBelow_cnt f _)
  generalize hc5 : run restart c4 = c5 at e5 r5_m r5_p r5_at r5_mem r5_out r5_fr
  have R5 : PolRegs f c5 := R4.frame (fun r hr => r5_fr r hr.1.1 hr.1.2.2.1)
  have hK := sat_clausePass (S := polSpace f) f loopFree_keepBody (fun pre c => KeepInv f c pre) (keep_step f hf)
  have P5 : PassInv f (fun pre c => KeepInv f c pre) c5 := ⟨[], f, rfl, r5_m, r5_at,
    by rw [r5_mem, i4_mem]; funext a; simp [kpMem, keptOf, polMc], by rw [r5_p]; rfl, R5,
    by rw [r5_fr _ (by decide) (by decide), i4_r]; rfl, by rw [r5_out]; exact i4_out⟩
  obtain ⟨t6, e6, ht6⟩ := hK.1 c5 P5
  have I6 := hK.2 c5 P5
  dsimp only at e6
  rw [r5_m] at e6 I6
  generalize hc6 : iterate (run keepBody) f.length c5 = c6 at e6 I6
  obtain ⟨i6_mem, -, R6, i6_r, i6_out⟩ := I6
  -- the output pass
  have e7 := execB_run restart (by simp [restart, seqs, LoopFree]) c6 (restart_addrOK _ hS0)
  obtain ⟨r7_m, r7_p, r7_at, r7_mem, r7_out, r7_fr⟩ := restart_run f c6 R6.k.one
    (by rw [i6_mem]; exact inputBelow_kp f _ (polMc_input f) _)
  generalize hc7 : run restart c6 = c7 at e7 r7_m r7_p r7_at r7_mem r7_out r7_fr
  have R7 : PolRegs f c7 := R6.frame (fun r hr => r7_fr r hr.1.1 hr.1.2.2.1)
  have hO := sat_clausePass (S := polSpace f) f loopFree_outBody (fun pre c => OutInv f c pre) (out_step f hf)
  have P7 : PassInv f (fun pre c => OutInv f c pre) c7 := ⟨[], f, rfl, r7_m, r7_at,
    by rw [r7_mem, i6_mem, kept_eq], by rw [r7_p]; rfl, R7,
    by rw [r7_fr _ (by decide) (by decide), i6_r]; rfl, by rw [r7_out, i6_out]; simp [keptOf, flipFormula]⟩
  obtain ⟨t8, e8, ht8⟩ := hO.1 c7 P7
  have I8 := hO.2 c7 P7
  dsimp only at e8
  rw [r7_m] at e8 I8
  generalize hc8 : iterate (run outBody) f.length c7 = c8 at e8 I8
  obtain ⟨-, -, R8, i8_r, i8_out⟩ := I8
  -- the padding
  have e9 := execB_run (S := polSpace f) (Stmt.add PR.w Reg.n Reg.zero) trivial c8 trivial
  generalize hc9 : run (Stmt.add PR.w Reg.n Reg.zero) c8 = c9 at e9
  have w9 : c9.reg PR.w = variableBound f := by rw [← hc9]; simp [run, R8.n, R8.k.zero]
  have k9 : Consts c9 := R8.k.frame (by rw [← hc9]; simp +decide [run]) (by rw [← hc9]; simp +decide [run])
    (by rw [← hc9]; simp +decide [run]) (by rw [← hc9]; simp +decide [run])
  have r9 : c9.reg PR.r = deletedCount f := by rw [← hc9]; simp [run]; exact i8_r
  have o9 : c9.out = c8.out := by rw [← hc9]; rfl
  have hP := sat_countLoop (S := polSpace f) (a := PR.r) loopFree_padBody (deletedCount f)
    (PadInv (f.length :: (flipFormula (complemented f) (kept f)).flatMap clauseCode) (variableBound f))
    (pad_step _ _ _)
  have P9 : PadInv (f.length :: (flipFormula (complemented f) (kept f)).flatMap clauseCode) (variableBound f) 0 c9 :=
    ⟨by rw [o9, i8_out, kept_eq]; simp [padding], by rw [w9]; rfl, k9⟩
  obtain ⟨t10, e10, ht10⟩ := hP.1 c9 ⟨P9, r9⟩
  have I10 := hP.2 c9 P9 r9
  dsimp only at e10
  rw [r9] at e10
  -- assemble
  refine ⟨t1 + (cost polSetup c1 + (cost restart c2 + (t4 + (cost restart c4 + (t6 + (cost restart c6 +
    (t8 + (cost (Stmt.add PR.w Reg.n Reg.zero) c8 + t10)))))))),
    ⟨iterate (run padBody) (deletedCount f) c9, ?_, ?_⟩, ?_⟩
  · exact ExecB.seq e1 (ExecB.seq e2 (ExecB.seq e3 (ExecB.seq e4 (ExecB.seq e5
      (ExecB.seq e6 (ExecB.seq e7 (ExecB.seq e8 (ExecB.seq e9 e10))))))))
  · rw [I10.1, show ramInput (polarize f) = (polarize f).length :: (polarize f).flatMap clauseCode from rfl,
      polarize_length]
    simp only [polarize, flipFormula, List.flatMap_append, List.cons_append]
  · have := cost_le_size polSetup c1
    have := cost_le_size restart c2
    have := cost_le_size restart c4
    have := cost_le_size restart c6
    have := cost_le_size (Stmt.add PR.w Reg.n Reg.zero) c8
    simp only [size] at *
    unfold polCost; omega

/-- The constant of the linear bound. -/
def polConst : Nat :=
  size passApre + 1 + size passApost + size polSetup + 3 * size restart + 5 + (clauseACost + 1) +
    (size cntBody + 1) + (size keepBody + 1) + (size outBody + 1) + (size padBody + 1)

theorem deletedCount_le (f : CNF) : deletedCount f ≤ f.length := List.countP_le_length

theorem polCost_le (f : CNF) : polCost f ≤ polConst * (f.length + 1) := by
  have hR := deletedCount_le f
  unfold polCost polConst passACost
  generalize f.length = m at hR ⊢
  generalize deletedCount f = R at hR ⊢
  generalize size passApre = P0
  generalize size passApost = P1
  generalize size polSetup = P2
  generalize size restart = P3
  generalize clauseACost + 1 = a
  generalize size cntBody + 1 = b
  generalize size keepBody + 1 = c
  generalize size outBody + 1 = d
  generalize size padBody + 1 = e
  have h1 : R * e ≤ m * e := Nat.mul_le_mul_right _ hR
  have h2 : m * a + m * b + m * c + m * d + m * e = m * (a + b + c + d + e) := by simp only [Nat.mul_add]
  obtain ⟨S, hS⟩ : ∃ S, S = P0 + 1 + P1 + P2 + 3 * P3 + 5 + a + b + c + d + e := ⟨_, rfl⟩
  rw [← hS]
  have h3 : m * (a + b + c + d + e) ≤ m * S := Nat.mul_le_mul_left _ (by omega)
  have h4 : S * (m + 1) = m * S + S := by rw [Nat.mul_succ, Nat.mul_comm]
  rw [h4]
  omega

/-! ### Linear in the number of variables -/

theorem literal_count_bound3 (xs : List Literal) (n : Nat) (hb : ∀ l ∈ xs, l.var < n)
    (h3 : ∀ v, (xs.filter fun l => l.var == v).length ≤ 3) : xs.length ≤ 3 * n := by
  induction n generalizing xs with
  | zero =>
    cases xs with
    | nil => simp
    | cons l xs => have := hb l (by simp); omega
  | succ n ih =>
    let ys := xs.filter fun l => !(l.var == n)
    have hyb : ∀ l ∈ ys, l.var < n := by
      intro l hl
      have hm := List.mem_filter.mp hl
      have hlt := hb l hm.1
      have hne : l.var ≠ n := by simpa using hm.2
      omega
    have hsub : List.Sublist ys xs := List.filter_sublist
    have hy3 : ∀ v, (ys.filter fun l => l.var == v).length ≤ 3 := fun v =>
      Nat.le_trans (List.Sublist.length_le (hsub.filter _)) (h3 v)
    have hys := ih ys hyb hy3
    have hlast := h3 n
    have hpart := List.length_eq_countP_add_countP (fun l : Literal => l.var == n) (l := xs)
    simp only [List.countP_eq_length_filter] at hpart
    have he : xs.length = (xs.filter fun l => l.var == n).length + ys.length := by
      simpa [ys, Bool.beq_eq_decide_eq] using hpart
    omega

theorem ThreeOccurrence.clause_count {f : CNF} (h : ThreeOccurrence f) : 2 * f.length ≤ 3 * variableBound f := by
  have hlo := clause_count_lower f (by intro c hc; rcases h.1 c hc with h | h <;> omega)
  refine Nat.le_trans hlo (literal_count_bound3 _ _ ?_ ?_)
  · intro l hl
    obtain ⟨c, hc, hl⟩ := List.mem_flatten.mp hl
    exact literal_lt_variableBound hc hl
  · intro v
    rw [signed_partition]
    have := h.2.2 v
    simp only [occurrences] at this
    omega

/-- The constant of the linear time and space bound. -/
def polLinConst : Nat := 2 * polConst + 14

/-- **Lemma 10's transformation in linear time and space.** On every 3-OCCURRENCE MAX-3-SAT formula
`f` with `n = variableBound f`, the RAM program `polProgram` halts on `ramInput f` with output
`ramInput (polarize f)` within `polLinConst · (n + 1)` steps, accessing only the addresses below
`polLinConst · (n + 1)`. -/
theorem polarize_linear_time (f : CNF) (hf : ThreeOccurrence f) :
    ∃ t, ComputesIn polProgram (ramInput f) (ramInput (polarize f)) t (polLinConst * (variableBound f + 1)) ∧
      t ≤ polLinConst * (variableBound f + 1) := by
  obtain ⟨t, hc, ht⟩ := pol_computes f hf.1
  have hm := ThreeOccurrence.clause_count hf
  have hK : polLinConst * (variableBound f + 1) = 2 * polConst * (variableBound f + 1) + 14 * (variableBound f + 1) := by
    unfold polLinConst; rw [Nat.add_mul]
  have hT : polCost f ≤ 2 * polConst * (variableBound f + 1) := by
    refine Nat.le_trans (polCost_le f) ?_
    have : f.length + 1 ≤ 2 * (variableBound f + 1) := by omega
    rw [Nat.mul_comm 2 polConst, Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ this
  have hN := clauseCodes_length_le f (fun c hc => by rcases hf.1 c hc with h | h <;> omega)
  have hS : polSpace f ≤ 14 * (variableBound f + 1) := by
    unfold polSpace polB polN; simp only [ramInput, List.length_cons]; omega
  refine ⟨t, hc.mono (by rw [hK]; omega), ?_⟩
  rw [hK]; omega

end STACS2027.RAM

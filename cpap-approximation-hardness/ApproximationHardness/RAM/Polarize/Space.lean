module

public import ApproximationHardness.RAM.Polarize.Keep
import Lean.Elab.Tactic.Omega

/-!
# The memory accesses of the Lemma 10 program

Every memory access of `polProgram` is to the input (`passA`, `restart`, `readClause`), to the
count table `N + 2v + s` (`cntLit`, `pureLit`) or to the table `B + v` of the positive kept
occurrences (`kpLit`, `outLit`), for variables `v < n`; all of them are below `B + n = N + 3n`.
This file proves the address conditions (`AddrOK`) of the loop bodies: `cntBody_addrOK`,
`keepBody_addrOK`, `outBody_addrOK`.
-/

@[expose] public section

namespace STACS2027.RAM

open Complexity.SAT

/-- The slots hold the variables (below `n`) and signs of a clause of two or three literals, as
many as the length register says. -/
structure SlotsBelow (n : Nat) (c : Config) : Prop where
  v0 : c.reg PR.v0 < n
  s0 : c.reg PR.s0 ≤ 1
  v1 : c.reg PR.v1 < n
  s1 : c.reg PR.s1 ≤ 1
  len : c.reg Reg.len = 2 ∨ c.reg Reg.len = 3
  v2 : c.reg Reg.len = 3 → c.reg PR.v2 < n ∧ c.reg PR.s2 ≤ 1

theorem SlotsBelow.frame {n : Nat} {c c' : Config} (h : SlotsBelow n c)
    (hf : ∀ r, r ∈ [PR.v0, PR.s0, PR.v1, PR.s1, PR.v2, PR.s2, Reg.len] → c'.reg r = c.reg r) :
    SlotsBelow n c' := by
  have e : ∀ r, r ∈ [PR.v0, PR.s0, PR.v1, PR.s1, PR.v2, PR.s2, Reg.len] → c'.reg r = c.reg r := hf
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e _ (by simp)]; exact h.v0
  · rw [e _ (by simp)]; exact h.s0
  · rw [e _ (by simp)]; exact h.v1
  · rw [e _ (by simp)]; exact h.s1
  · rw [e _ (by simp)]; exact h.len
  · rw [e _ (by simp), e _ (by simp), e _ (by simp)]; exact h.v2

/-- After reading a clause whose variables are below `n`, the slots hold them. -/
theorem slotsBelow_read {n : Nat} (c : Config) (cl : Clause) (w : List Nat) (hcl : cl.length = 2 ∨ cl.length = 3)
    (hAt : At c (clauseCode cl ++ w)) (hk : Consts c) (hv : ∀ l ∈ cl, l.var < n) :
    SlotsBelow n (run readClause c) := by
  obtain ⟨R, hlits⟩ := readClause_result c cl w hcl hAt hk
  rcases hlits with ⟨l0, l1, rfl, L0, L1⟩ | ⟨l0, l1, l2, rfl, L0, L1, L2⟩
  · refine ⟨?_, ?_, ?_, ?_, Or.inl R.len, fun h => by rw [R.len] at h; simp at h⟩
    · rw [L0.1]; exact hv l0 (by simp)
    · rw [L0.2]; exact signCode_le l0
    · rw [L1.1]; exact hv l1 (by simp)
    · rw [L1.2]; exact signCode_le l1
  · refine ⟨?_, ?_, ?_, ?_, Or.inr R.len, fun _ => ⟨?_, ?_⟩⟩
    · rw [L0.1]; exact hv l0 (by simp)
    · rw [L0.2]; exact signCode_le l0
    · rw [L1.1]; exact hv l1 (by simp)
    · rw [L1.2]; exact signCode_le l1
    · rw [L2.1]; exact hv l2 (by simp)
    · rw [L2.2]; exact signCode_le l2

/-! ### The blocks -/

/-- `readClause` reads the cells of the clause at `p`. -/
theorem readClause_addrOK {S : Nat} (c : Config) (cl : Clause) (w : List Nat) (hcl : cl.length = 2 ∨ cl.length = 3)
    (hAt : At c (clauseCode cl ++ w)) (hk : Consts c) (hS : c.reg Reg.p + (clauseCode cl).length ≤ S) :
    AddrOK S readClause c := by
  have h0 : c.mem (c.reg Reg.p) = cl.length := hAt.head
  rw [clauseCode_length] at hS
  simp +decide [readClause, rdLit, run, hk.one, hk.two, h0]
  omega

/-- `delCode` reads the counts `N + 2v`, `N + 2v + 1` of the variables in the slots. -/
theorem delCode_addrOK {S n : Nat} (c : Config) (hk : Consts c) (hs : SlotsBelow n c)
    (hS : c.reg Reg.N + n + n ≤ S) : AddrOK S delCode c := by
  have := hs.v0; have := hs.v1; have := hs.len; have := hs.v2
  simp +decide [delCode, tautPair, pureLit, ifThird, run, hk.one, hk.two]
  omega

/-- The counting tail of `cntBody` updates the counts `N + 2v + s` of the literals in the slots. -/
theorem cntTail_addrOK {S n : Nat} (c : Config) (hk : Consts c) (hs : SlotsBelow n c)
    (hS : c.reg Reg.N + n + n ≤ S) :
    AddrOK S (seqs [cntLit PR.v0 PR.s0, cntLit PR.v1 PR.s1, ifThird (cntLit PR.v2 PR.s2)]) c := by
  have := hs.v0; have := hs.s0; have := hs.v1; have := hs.s1; have := hs.len; have := hs.v2
  simp +decide [cntLit, ifThird, run, hk.one, hk.two]
  omega

/-- The tail of `keepBody` updates the cells `B + v` of the variables in the slots. -/
theorem kpTail_addrOK {S n : Nat} (c : Config) (hk : Consts c) (hs : SlotsBelow n c) (hS : c.reg Reg.B + n ≤ S) :
    AddrOK S (Stmt.ifz PR.del (seqs [kpLit PR.v0 PR.s0, kpLit PR.v1 PR.s1, ifThird (kpLit PR.v2 PR.s2)])
      (Stmt.add PR.r PR.r Reg.one)) c := by
  have := hs.v0; have := hs.v1; have := hs.len; have := hs.v2
  simp +decide [kpLit, ifThird, run, hk.one, hk.two]
  omega

/-- The tail of `outBody` reads the cells `B + v` of the variables in the slots. -/
theorem outTail_addrOK {S n : Nat} (c : Config) (hk : Consts c) (hs : SlotsBelow n c) (hS : c.reg Reg.B + n ≤ S) :
    AddrOK S (Stmt.ifz PR.del (seqs [Stmt.write Reg.len, outLit PR.v0 PR.s0, outLit PR.v1 PR.s1,
      ifThird (outLit PR.v2 PR.s2)]) Stmt.skip) c := by
  have := hs.v0; have := hs.v1; have := hs.len; have := hs.v2
  simp +decide [outLit, ifThird, run, hk.one, hk.two]
  omega

/-- `restart` reads the clause count in cell `0`. -/
theorem restart_addrOK {S : Nat} (c : Config) (hS : 0 < S) : AddrOK S restart c := by
  simp +decide [restart, run]; exact hS

/-! ### The loop bodies -/

/-- The hypotheses of the address conditions of the three passes over the clauses. -/
structure BodyPre (n S : Nat) (cl : Clause) (w : List Nat) (c : Config) : Prop where
  len : cl.length = 2 ∨ cl.length = 3
  at_ : At c (clauseCode cl ++ w)
  k : Consts c
  vars : ∀ l ∈ cl, l.var < n
  input : c.reg Reg.p + (clauseCode cl).length ≤ S

theorem BodyPre.read {n S : Nat} {cl : Clause} {w : List Nat} {c : Config} (h : BodyPre n S cl w c) :
    AddrOK S readClause c ∧ SlotsBelow n (run readClause c) ∧ Consts (run readClause c) ∧
      ∀ r, ReadFixed r → (run readClause c).reg r = c.reg r :=
  have R := (readClause_result c cl w h.len h.at_ h.k).1
  ⟨readClause_addrOK c cl w h.len h.at_ h.k h.input, slotsBelow_read c cl w h.len h.at_ h.k h.vars,
    h.k.frame (R.fixed _ (by decide)) (R.fixed _ (by decide)) (R.fixed _ (by decide)) (R.fixed _ (by decide)),
    R.fixed⟩

theorem cntBody_addrOK {n S : Nat} {cl : Clause} {w : List Nat} {c : Config} (h : BodyPre n S cl w c)
    (hS : c.reg Reg.N + n + n ≤ S) : AddrOK S cntBody c := by
  obtain ⟨A, hs, K, fr⟩ := h.read
  rw [show cntBody = Stmt.seq readClause (seqs [cntLit PR.v0 PR.s0, cntLit PR.v1 PR.s1, ifThird (cntLit PR.v2 PR.s2)])
    from rfl]
  exact AddrOK.seq A (cntTail_addrOK _ K hs (by rw [fr _ (by decide)]; exact hS))

/-- The registers of `delCode`'s frame needed by the tails. -/
theorem delCode_keeps (c : Config) :
    (∀ r, r ∈ [PR.v0, PR.s0, PR.v1, PR.s1, PR.v2, PR.s2, Reg.len] → (run delCode c).reg r = c.reg r) ∧
      (Consts c → Consts (run delCode c)) ∧ (run delCode c).reg Reg.B = c.reg Reg.B := by
  have fr : ∀ r, r ∉ regsW delCode → (run delCode c).reg r = c.reg r := fun r h => run_reg_frame _ _ _ h
  refine ⟨?_, fun h => h.frame (fr _ (by decide)) (fr _ (by decide)) (fr _ (by decide)) (fr _ (by decide)),
    fr _ (by decide)⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact fr _ (by decide)

theorem keepBody_eq : keepBody = seqs [readClause, delCode,
    Stmt.ifz PR.del (seqs [kpLit PR.v0 PR.s0, kpLit PR.v1 PR.s1, ifThird (kpLit PR.v2 PR.s2)])
      (Stmt.add PR.r PR.r Reg.one)] := rfl

theorem outBody_eq : outBody = seqs [readClause, delCode,
    Stmt.ifz PR.del (seqs [Stmt.write Reg.len, outLit PR.v0 PR.s0, outLit PR.v1 PR.s1, ifThird (outLit PR.v2 PR.s2)])
      Stmt.skip] := rfl

theorem keepBody_addrOK {n S : Nat} {cl : Clause} {w : List Nat} {c : Config} (h : BodyPre n S cl w c)
    (hS : c.reg Reg.B + n ≤ S) (hN : c.reg Reg.N + n + n ≤ S) : AddrOK S keepBody c := by
  obtain ⟨A, hs, K, fr⟩ := h.read
  obtain ⟨d1, d2, d3⟩ := delCode_keeps (run readClause c)
  rw [keepBody_eq]
  simp only [addrOK_seqs_cons, addrOK_seqs_nil, and_true]
  exact ⟨A, delCode_addrOK _ K hs (by rw [fr _ (by decide)]; exact hN),
    kpTail_addrOK _ (d2 K) (hs.frame d1) (by rw [d3, fr _ (by decide)]; exact hS)⟩

theorem outBody_addrOK {n S : Nat} {cl : Clause} {w : List Nat} {c : Config} (h : BodyPre n S cl w c)
    (hS : c.reg Reg.B + n ≤ S) (hN : c.reg Reg.N + n + n ≤ S) : AddrOK S outBody c := by
  obtain ⟨A, hs, K, fr⟩ := h.read
  obtain ⟨d1, d2, d3⟩ := delCode_keeps (run readClause c)
  rw [outBody_eq]
  simp only [addrOK_seqs_cons, addrOK_seqs_nil, and_true]
  exact ⟨A, delCode_addrOK _ K hs (by rw [fr _ (by decide)]; exact hN),
    outTail_addrOK _ (d2 K) (hs.frame d1) (by rw [d3, fr _ (by decide)]; exact hS)⟩

end STACS2027.RAM

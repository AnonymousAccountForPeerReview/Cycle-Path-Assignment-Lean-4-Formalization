module

public import ApproximationHardness.RAM.Polarize.Passes
import Lean.Elab.Tactic.Omega

/-!
# The keep pass and the output pass of the Lemma 10 program
-/

@[expose] public section

namespace STACS2027.RAM

open Complexity.SAT

/-! ### Count tables -/

theorem count_map_inj {α β : Type} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β] (g : α → β)
    (hg : ∀ a b, g a = g b → a = b) (L : List α) (x : α) : (L.map g).count (g x) = L.count x := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    simp only [List.map_cons, List.count_cons, ih]
    by_cases h : a = x
    · subst h; simp
    · have : g a ≠ g x := fun e => h (hg a x e)
      simp [h, this]

theorem litAddr_inj (N : Nat) (a b : Literal) (h : litAddr N a = litAddr N b) : a = b := by
  unfold litAddr at h
  have ha := signCode_le a
  have hb := signCode_le b
  have hv : a.var = b.var := by omega
  have hs : signCode a = signCode b := by omega
  cases a; cases b
  simp only at hv; subst hv
  rw [signCode_inj] at hs; simp only at hs; subst hs; rfl

theorem litAddr_false (N v : Nat) : litAddr N ⟨v, false⟩ = N + v + v := by simp [litAddr, signCode]
theorem litAddr_true (N v : Nat) : litAddr N ⟨v, true⟩ = N + v + v + 1 := by simp [litAddr, signCode]

/-- The memory of the keep pass: `M` with the positive kept occurrences of every variable counted in
the cell `B + v`. -/
def kpMem (M : Nat → Nat) (B : Nat) (ks : List Literal) (a : Nat) : Nat :=
  M a + ((ks.filter (·.positive)).map (fun l => B + l.var)).count a

theorem kpMem_below (M : Nat → Nat) (B : Nat) (ks : List Literal) {a : Nat} (ha : a < B) : kpMem M B ks a = M a := by
  unfold kpMem
  rw [List.count_eq_zero_of_not_mem]
  · rfl
  · intro h
    obtain ⟨l, _, hl⟩ := List.mem_map.mp h
    omega

theorem kpMem_at (M : Nat → Nat) (B : Nat) (ks : List Literal) (v : Nat) :
    kpMem M B ks (B + v) = M (B + v) + ks.count ⟨v, true⟩ := by
  unfold kpMem
  congr 1
  induction ks with
  | nil => rfl
  | cons l ks ih =>
    obtain ⟨x, p⟩ := l
    cases p
    · simp only [List.filter_cons, Bool.false_eq_true, ite_false, ih, List.count_cons]
      simp
    · simp only [List.filter_cons, ite_true, List.map_cons, List.count_cons, ih]
      by_cases h : x = v
      · subst h; simp
      · have : B + x ≠ B + v := by omega
        simp [h]

theorem kpMem_snoc (M : Nat → Nat) (B : Nat) (ks : List Literal) (l : Literal) :
    kpMem M B (ks ++ [l]) = fun a => if l.positive ∧ a = B + l.var then kpMem M B ks a + 1 else kpMem M B ks a := by
  funext a
  unfold kpMem
  obtain ⟨x, p⟩ := l
  cases p
  · simp
  · simp only [List.filter_append, List.filter_cons, List.filter_nil, ite_true, List.map_append, List.map_cons,
      List.map_nil, List.count_append, List.count_singleton, true_and]
    by_cases h : a = B + x
    · subst h; simp; omega
    · simp [h]; intro h'; exact absurd h'.symm h

/-! ### The macros of the two passes -/

theorem kpLit_mem (c : Config) (vr sr : Nat) (_h1 : vr ≠ PR.addr) (_h2 : vr ≠ PR.x) (hone : c.reg Reg.one = 1) (a : Nat) :
    (run (kpLit vr sr) c).mem a = if c.reg sr ≠ 0 ∧ a = c.reg Reg.B + c.reg vr then c.mem a + 1 else c.mem a := by
  simp only [kpLit, run_seqs_cons, run_seqs_nil, run]
  by_cases hs : c.reg sr = 0
  · simp [hs]
  · simp +decide [hs, hone]
    split <;> simp_all

theorem kpLit_frame (c : Config) (vr sr r : Nat) (h1 : r ≠ PR.addr) (h2 : r ≠ PR.x) :
    (run (kpLit vr sr) c).reg r = c.reg r :=
  run_reg_frame _ _ _ (by simp [kpLit, regsW, h1, h2])

theorem kpLit_out (c : Config) (vr sr : Nat) : (run (kpLit vr sr) c).out = c.out :=
  run_out_frame _ _ (by simp [kpLit, hasWrite])

theorem kpLit_step (c : Config) (vr sr : Nat) (l : Literal) (hl : LitIn c vr sr l) (h1 : vr ≠ PR.addr) (h2 : vr ≠ PR.x)
    (hone : c.reg Reg.one = 1) {M : Nat → Nat} {ks : List Literal} (hm : c.mem = kpMem M (c.reg Reg.B) ks) :
    (run (kpLit vr sr) c).mem = kpMem M (c.reg Reg.B) (ks ++ [l]) := by
  funext a
  rw [kpLit_mem c vr sr h1 h2 hone a, kpMem_snoc, hm, hl.1, hl.2]
  have : (signCode l ≠ 0) ↔ l.positive = true := by unfold signCode; cases l.positive <;> simp
  simp only [this]

/-- The sign written for a literal: complemented when the count `K` is at least two. -/
def outSign (K : Nat) (l : Literal) : Nat := if 2 ≤ K then 1 - signCode l else signCode l

theorem outLit_out (c : Config) (vr sr : Nat) (l : Literal) (hl : LitIn c vr sr l)
    (h : vr ≠ PR.addr ∧ vr ≠ PR.x ∧ vr ≠ PR.y ∧ vr ≠ PR.z) (hs : sr ≠ PR.addr ∧ sr ≠ PR.x ∧ sr ≠ PR.y ∧ sr ≠ PR.z)
    (hk : Consts c) :
    (run (outLit vr sr) c).out = c.out ++ [l.var, outSign (c.mem (c.reg Reg.B + l.var)) l] := by
  obtain ⟨a1, a2, a3, a4⟩ := h
  obtain ⟨b1, b2, b3, b4⟩ := hs
  have hone := hk.one
  have hzero := hk.zero
  have htwo := hk.two
  simp only [outLit, run_seqs_cons, run_seqs_nil, run]
  simp +decide [b1, b2, b3, hone, hzero, htwo, hl.1, hl.2, outSign]
  by_cases hK : 2 ≤ c.mem (c.reg Reg.B + l.var)
  · simp [hK, show 2 - c.mem (c.reg Reg.B + l.var) = 0 by omega]
  · simp [hK, show 2 - c.mem (c.reg Reg.B + l.var) ≠ 0 by omega]

theorem outLit_mem (c : Config) (vr sr : Nat) : (run (outLit vr sr) c).mem = c.mem :=
  run_mem_frame _ _ (by simp [outLit, hasStore])

theorem outLit_frame (c : Config) (vr sr r : Nat) (h1 : r ≠ PR.addr) (h2 : r ≠ PR.x) (h3 : r ≠ PR.y) (h4 : r ≠ PR.z) :
    (run (outLit vr sr) c).reg r = c.reg r :=
  run_reg_frame _ _ _ (by simp [outLit, regsW, h1, h2, h3, h4])

theorem outSign_flip (K : Nat) (l : Literal) : litCode (if 2 ≤ K then (⟨l.var, !l.positive⟩ : Literal) else l) =
    [l.var, outSign K l] := by
  unfold outSign litCode signCode
  split <;> cases l.positive <;> simp

/-! ### Reading a clause and deciding its deletion -/

/-- The slots hold the clause `cl` of two or three literals. -/
def SlotsHold (c : Config) (cl : Clause) : Prop :=
  (∃ l0 l1, cl = [l0, l1] ∧ LitIn c PR.v0 PR.s0 l0 ∧ LitIn c PR.v1 PR.s1 l1) ∨
    (∃ l0 l1 l2, cl = [l0, l1, l2] ∧ LitIn c PR.v0 PR.s0 l0 ∧ LitIn c PR.v1 PR.s1 l1 ∧ LitIn c PR.v2 PR.s2 l2)

theorem SlotsHold.frame {c c' : Config} {cl : Clause} (h : SlotsHold c cl)
    (hf : ∀ r, r = PR.v0 ∨ r = PR.s0 ∨ r = PR.v1 ∨ r = PR.s1 ∨ r = PR.v2 ∨ r = PR.s2 → c'.reg r = c.reg r) :
    SlotsHold c' cl := by
  rcases h with ⟨l0, l1, h, L0, L1⟩ | ⟨l0, l1, l2, h, L0, L1, L2⟩
  · exact Or.inl ⟨l0, l1, h, L0.frame (hf _ (by decide)) (hf _ (by decide)),
      L1.frame (hf _ (by decide)) (hf _ (by decide))⟩
  · exact Or.inr ⟨l0, l1, l2, h, L0.frame (hf _ (by decide)) (hf _ (by decide)),
      L1.frame (hf _ (by decide)) (hf _ (by decide)), L2.frame (hf _ (by decide)) (hf _ (by decide))⟩

theorem readDel (f : CNF) (c : Config) (cl : Clause) (w : List Nat) (hcl : cl.length = 2 ∨ cl.length = 3)
    (hAt : At c (clauseCode cl ++ w)) (hk : Consts c) (hcounts : ∀ l ∈ cl, CountsAt f c l) :
    ReadResult c (run readClause c) cl w ∧ SlotsHold (run readClause c) cl ∧
      ((run delCode (run readClause c)).reg PR.del = 0 ↔ deleted f cl = false) ∧
      (run delCode (run readClause c)).mem = c.mem ∧
      ∀ r, DelScratchT r → (run delCode (run readClause c)).reg r = (run readClause c).reg r := by
  obtain ⟨R, hlits⟩ := readClause_result c cl w hcl hAt hk
  refine ⟨R, hlits, ?_⟩
  have K1 : Consts (run readClause c) := hk.frame (R.fixed _ (by decide)) (R.fixed _ (by decide))
    (R.fixed _ (by decide)) (R.fixed _ (by decide))
  have C1 : ∀ l ∈ cl, CountsAt f (run readClause c) l := fun l hl =>
    (hcounts l hl).frame R.mem (R.fixed _ (by decide))
  rcases hlits with ⟨l0, l1, rfl, L0, L1⟩ | ⟨l0, l1, l2, rfl, L0, L1, L2⟩
  · obtain ⟨d, m, fr⟩ := delCode_two f _ l0 l1 (R.len) L0 L1 K1 (C1 _ (by simp)) (C1 _ (by simp))
    exact ⟨d, m.trans R.mem, fr⟩
  · obtain ⟨d, m, fr⟩ := delCode_three f _ l0 l1 l2 (R.len) L0 L1 L2 K1 (C1 _ (by simp)) (C1 _ (by simp))
      (C1 _ (by simp))
    exact ⟨d, m.trans R.mem, fr⟩

/-! ### One clause of the keep pass -/

/-- The registers the keep and output passes leave alone. -/
abbrev KeepFixed (r : Nat) : Prop := ReadFixed r ∧ DelScratchT r ∧ r ≠ PR.r

theorem keepBody_frame (c : Config) (r : Nat) (h : KeepFixed r) : (run keepBody c).reg r = c.reg r := by
  apply run_reg_frame
  obtain ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩, ⟨⟨b1, b2, b3, b4, b5, b6⟩, b7⟩, b8⟩ := h
  simp [keepBody, readClause, rdLit, delCode, tautPair, pureLit, ifThird, kpLit, regsW,
    a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, b1, b2, b3, b4, b5, b6, b8]

theorem keepBody_out (c : Config) : (run keepBody c).out = c.out :=
  run_out_frame _ _ (by simp [keepBody, readClause, rdLit, delCode, tautPair, pureLit, ifThird, kpLit, hasWrite])

theorem run_keepBody (c : Config) : run keepBody c =
    run (Stmt.ifz PR.del (seqs [kpLit PR.v0 PR.s0, kpLit PR.v1 PR.s1, ifThird (kpLit PR.v2 PR.s2)])
      (Stmt.add PR.r PR.r Reg.one)) (run delCode (run readClause c)) := by
  simp only [keepBody, run_seqs_cons, run_seqs_nil]; try rfl

theorem keepBody_step (f : CNF) (c : Config) (cl : Clause) (w : List Nat) (hcl : cl.length = 2 ∨ cl.length = 3)
    (hAt : At c (clauseCode cl ++ w)) (hk : Consts c) (hcounts : ∀ l ∈ cl, CountsAt f c l)
    {M : Nat → Nat} {ks : List Literal} (hm : c.mem = kpMem M (c.reg Reg.B) ks) :
    (run keepBody c).mem = kpMem M (c.reg Reg.B) (if deleted f cl then ks else ks ++ cl) ∧
      (run keepBody c).reg PR.r = c.reg PR.r + (if deleted f cl then 1 else 0) ∧
      (run keepBody c).reg Reg.m = c.reg Reg.m - 1 ∧
      (run keepBody c).reg Reg.p = c.reg Reg.p + (clauseCode cl).length ∧
      (run keepBody c).out = c.out ∧ ∀ r, KeepFixed r → (run keepBody c).reg r = c.reg r := by
  obtain ⟨R, S, hd, hmem, hfr⟩ := readDel f c cl w hcl hAt hk hcounts
  refine ⟨?_, ?_, ?_, ?_, keepBody_out c, keepBody_frame c⟩
  all_goals rw [run_keepBody]
  all_goals
    generalize hc1 : run readClause c = c1 at R S hd hmem hfr
    generalize hc2 : run delCode c1 = c2 at hd hmem hfr
    have K2 : Consts c2 := hk.frame ((hfr _ (by decide)).trans (R.fixed _ (by decide)))
      ((hfr _ (by decide)).trans (R.fixed _ (by decide))) ((hfr _ (by decide)).trans (R.fixed _ (by decide)))
      ((hfr _ (by decide)).trans (R.fixed _ (by decide)))
    have B2 : c2.reg Reg.B = c.reg Reg.B := (hfr _ (by decide)).trans (R.fixed _ (by decide))
    have r2 : c2.reg PR.r = c.reg PR.r := (hfr _ (by decide)).trans (R.fixed _ (by decide))
    have m2 : c2.reg Reg.m = c.reg Reg.m - 1 := (hfr _ (by decide)).trans R.m
    have p2 : c2.reg Reg.p = c.reg Reg.p + (clauseCode cl).length := (hfr _ (by decide)).trans R.p
    have len2 : c2.reg Reg.len = cl.length := (hfr _ (by decide)).trans R.len
    have S2 : SlotsHold c2 cl := S.frame (fun r hr => hfr r (by rcases hr with h | h | h | h | h | h <;> subst h <;> decide))
    by_cases hdel : deleted f cl = true
    · have hne : c2.reg PR.del ≠ 0 := fun h => by rw [hd.mp h] at hdel; exact absurd hdel (by decide)
      simp only [run, hne, ite_false, hdel, ite_true]
      first
        | (simp; rw [hmem, hm])
        | (simp +decide; rw [r2, K2.one])
        | (simp +decide; exact m2)
        | (simp +decide; exact p2)
    · have h0 : c2.reg PR.del = 0 := hd.mpr (by simpa using hdel)
      simp only [run_ifz, h0, ite_true, hdel, Bool.false_eq_true, ite_false]
      simp only [run_seqs_cons, run_seqs_nil]
      rcases S2 with ⟨l0, l1, rfl, L0, L1⟩ | ⟨l0, l1, l2, rfl, L0, L1, L2⟩
      · have e1 := kpLit_step c2 _ _ l0 L0 (by decide) (by decide) K2.one (M := M) (ks := ks) (by rw [hmem, hm, B2])
        generalize hc3 : run (kpLit PR.v0 PR.s0) c2 = c3 at e1
        have f3 : ∀ r, r ≠ PR.addr → r ≠ PR.x → c3.reg r = c2.reg r := fun r a b => hc3 ▸ kpLit_frame c2 _ _ r a b
        have e2 := kpLit_step c3 _ _ l1 (L1.frame (f3 _ (by decide) (by decide)) (f3 _ (by decide) (by decide)))
          (by decide) (by decide) (by rw [f3 _ (by decide) (by decide)]; exact K2.one) (M := M) (ks := ks ++ [l0])
          (by rw [e1, f3 _ (by decide) (by decide)])
        generalize hc4 : run (kpLit PR.v1 PR.s1) c3 = c4 at e2
        have f4 : ∀ r, r ≠ PR.addr → r ≠ PR.x → c4.reg r = c2.reg r := fun r a b =>
          (hc4 ▸ kpLit_frame c3 _ _ r a b).trans (f3 r a b)
        rw [ifThird_skip c4 _ (by rw [f4 _ (by decide) (by decide)]; exact len2)
          (by rw [f4 _ (by decide) (by decide)]; exact K2.two)]
        first
          | (show c4.mem = _; rw [e2, f3 _ (by decide) (by decide), B2]; simp)
          | (simp +decide; rw [f4 _ (by decide) (by decide), r2])
          | (simp +decide; rw [f4 _ (by decide) (by decide)]; exact m2)
          | (simp +decide; rw [f4 _ (by decide) (by decide)]; exact p2)
      · have e1 := kpLit_step c2 _ _ l0 L0 (by decide) (by decide) K2.one (M := M) (ks := ks) (by rw [hmem, hm, B2])
        generalize hc3 : run (kpLit PR.v0 PR.s0) c2 = c3 at e1
        have f3 : ∀ r, r ≠ PR.addr → r ≠ PR.x → c3.reg r = c2.reg r := fun r a b => hc3 ▸ kpLit_frame c2 _ _ r a b
        have e2 := kpLit_step c3 _ _ l1 (L1.frame (f3 _ (by decide) (by decide)) (f3 _ (by decide) (by decide)))
          (by decide) (by decide) (by rw [f3 _ (by decide) (by decide)]; exact K2.one) (M := M) (ks := ks ++ [l0])
          (by rw [e1, f3 _ (by decide) (by decide)])
        generalize hc4 : run (kpLit PR.v1 PR.s1) c3 = c4 at e2
        have f4 : ∀ r, r ≠ PR.addr → r ≠ PR.x → c4.reg r = c2.reg r := fun r a b =>
          (hc4 ▸ kpLit_frame c3 _ _ r a b).trans (f3 r a b)
        rw [ifThird_do c4 _ (by rw [f4 _ (by decide) (by decide)]; exact len2)
          (by rw [f4 _ (by decide) (by decide)]; exact K2.two)]
        have f5 : ∀ r, r ≠ PR.addr → r ≠ PR.x → r ≠ Reg.t → (c4.setReg Reg.t 1).reg r = c2.reg r := by
          intro r a b d; simp only [setReg_reg, ite_eq_right d]; exact f4 r a b
        have e3 := kpLit_step (c4.setReg Reg.t 1) _ _ l2
          (L2.frame (f5 _ (by decide) (by decide) (by decide)) (f5 _ (by decide) (by decide) (by decide)))
          (by decide) (by decide) (by rw [f5 _ (by decide) (by decide) (by decide)]; exact K2.one) (M := M)
          (ks := ks ++ [l0] ++ [l1]) (by
            show c4.mem = _
            rw [e2, f5 _ (by decide) (by decide) (by decide), f3 _ (by decide) (by decide)])
        first
          | (rw [e3, f5 _ (by decide) (by decide) (by decide), B2]; simp)
          | (rw [kpLit_frame _ _ _ _ (by decide) (by decide), f5 _ (by decide) (by decide) (by decide), r2]; simp)
          | (rw [kpLit_frame _ _ _ _ (by decide) (by decide), f5 _ (by decide) (by decide) (by decide)]; exact m2)
          | (rw [kpLit_frame _ _ _ _ (by decide) (by decide), f5 _ (by decide) (by decide) (by decide)]; exact p2)

/-! ### One clause of the output pass -/

theorem outBody_frame (c : Config) (r : Nat) (h : KeepFixed r) : (run outBody c).reg r = c.reg r := by
  apply run_reg_frame
  obtain ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩, ⟨⟨b1, b2, b3, b4, b5, b6⟩, b7⟩, b8⟩ := h
  simp [outBody, readClause, rdLit, delCode, tautPair, pureLit, ifThird, outLit, regsW,
    a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, b1, b2, b3, b4, b5, b6]

theorem outBody_mem (c : Config) : (run outBody c).mem = c.mem :=
  run_mem_frame _ _ (by simp [outBody, readClause, rdLit, delCode, tautPair, pureLit, ifThird, outLit, hasStore])

theorem run_outBody (c : Config) : run outBody c =
    run (Stmt.ifz PR.del (seqs [Stmt.write Reg.len, outLit PR.v0 PR.s0, outLit PR.v1 PR.s1, ifThird (outLit PR.v2 PR.s2)])
      Stmt.skip) (run delCode (run readClause c)) := by
  simp only [outBody, run_seqs_cons, run_seqs_nil]; try rfl

theorem flip_code (F : Nat → Bool) (K : Nat) (l : Literal) (hF : F l.var = decide (2 ≤ K)) :
    litCode (flipLiteral F l) = [l.var, outSign K l] := by
  rw [← outSign_flip K l]
  unfold flipLiteral
  rw [hF]
  by_cases h : 2 ≤ K <;> simp [h]

theorem outBody_step (f : CNF) (F : Nat → Bool) (c : Config) (cl : Clause) (w : List Nat)
    (hcl : cl.length = 2 ∨ cl.length = 3) (hAt : At c (clauseCode cl ++ w)) (hk : Consts c)
    (hcounts : ∀ l ∈ cl, CountsAt f c l) (hF : ∀ l ∈ cl, F l.var = decide (2 ≤ c.mem (c.reg Reg.B + l.var))) :
    (run outBody c).out = c.out ++ (if deleted f cl then [] else clauseCode (cl.map (flipLiteral F))) ∧
      (run outBody c).reg Reg.m = c.reg Reg.m - 1 ∧
      (run outBody c).reg Reg.p = c.reg Reg.p + (clauseCode cl).length ∧
      (run outBody c).mem = c.mem ∧ ∀ r, KeepFixed r → (run outBody c).reg r = c.reg r := by
  obtain ⟨R, S, hd, hmem, hfr⟩ := readDel f c cl w hcl hAt hk hcounts
  refine ⟨?_, ?_, ?_, outBody_mem c, outBody_frame c⟩
  all_goals rw [run_outBody]
  all_goals
    generalize hc1 : run readClause c = c1 at R S hd hmem hfr
    generalize hc2 : run delCode c1 = c2 at hd hmem hfr
    have K2 : Consts c2 := hk.frame ((hfr _ (by decide)).trans (R.fixed _ (by decide)))
      ((hfr _ (by decide)).trans (R.fixed _ (by decide))) ((hfr _ (by decide)).trans (R.fixed _ (by decide)))
      ((hfr _ (by decide)).trans (R.fixed _ (by decide)))
    have B2 : c2.reg Reg.B = c.reg Reg.B := (hfr _ (by decide)).trans (R.fixed _ (by decide))
    have m2 : c2.reg Reg.m = c.reg Reg.m - 1 := (hfr _ (by decide)).trans R.m
    have p2 : c2.reg Reg.p = c.reg Reg.p + (clauseCode cl).length := (hfr _ (by decide)).trans R.p
    have len2 : c2.reg Reg.len = cl.length := (hfr _ (by decide)).trans R.len
    have o2 : c2.out = c.out := by
      rw [← hc2, run_out_frame _ _ (by simp [delCode, tautPair, pureLit, ifThird, hasWrite]), R.out]
    have S2 : SlotsHold c2 cl := S.frame (fun r hr => hfr r (by rcases hr with h | h | h | h | h | h <;> subst h <;> decide))
    by_cases hdel : deleted f cl = true
    · have hne : c2.reg PR.del ≠ 0 := fun h => by rw [hd.mp h] at hdel; exact absurd hdel (by decide)
      simp only [run, hne, ite_false, hdel, ite_true]
      first
        | (rw [o2]; simp)
        | exact m2
        | exact p2
    · have h0 : c2.reg PR.del = 0 := hd.mpr (by simpa using hdel)
      simp only [run_ifz, h0, ite_true, hdel, Bool.false_eq_true, ite_false]
      simp only [run_seqs_cons, run_seqs_nil]
      let c3 := run (Stmt.write Reg.len) c2
      have f3 : ∀ r, c3.reg r = c2.reg r := fun r => rfl
      have o3 : c3.out = c.out ++ [cl.length] := by simp [c3, run, o2, len2]
      have mm3 : c3.mem = c.mem := hmem
      have K3 : Consts c3 := K2.frame (f3 _) (f3 _) (f3 _) (f3 _)
      rcases S2 with ⟨l0, l1, rfl, L0, L1⟩ | ⟨l0, l1, l2, rfl, L0, L1, L2⟩
      · have o4 := outLit_out c3 _ _ l0 L0 (by decide) (by decide) K3
        generalize hc4 : run (outLit PR.v0 PR.s0) c3 = c4 at o4
        have f4 : ∀ r, r ≠ PR.addr → r ≠ PR.x → r ≠ PR.y → r ≠ PR.z → c4.reg r = c2.reg r := fun r a b d e =>
          hc4 ▸ outLit_frame c3 _ _ r a b d e
        have mm4 : c4.mem = c.mem := by rw [← hc4, outLit_mem]; exact mm3
        have o5 := outLit_out c4 _ _ l1 (L1.frame (f4 _ (by decide) (by decide) (by decide) (by decide))
          (f4 _ (by decide) (by decide) (by decide) (by decide))) (by decide) (by decide)
          (K2.frame (f4 _ (by decide) (by decide) (by decide) (by decide)) (f4 _ (by decide) (by decide) (by decide) (by decide))
            (f4 _ (by decide) (by decide) (by decide) (by decide)) (f4 _ (by decide) (by decide) (by decide) (by decide)))
        generalize hc5 : run (outLit PR.v1 PR.s1) c4 = c5 at o5
        have f5 : ∀ r, r ≠ PR.addr → r ≠ PR.x → r ≠ PR.y → r ≠ PR.z → c5.reg r = c2.reg r := fun r a b d e =>
          (hc5 ▸ outLit_frame c4 _ _ r a b d e).trans (f4 r a b d e)
        rw [ifThird_skip c5 _ (by rw [f5 _ (by decide) (by decide) (by decide) (by decide)]; exact len2)
          (by rw [f5 _ (by decide) (by decide) (by decide) (by decide)]; exact K2.two)]
        first
          | (show c5.out = _
             rw [o5, o4, o3, mm4, f4 _ (by decide) (by decide) (by decide) (by decide), B2]
             simp only [show c3.reg Reg.B = c.reg Reg.B from B2, List.map_cons, List.map_nil, clauseCode,
               List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_cons, List.length_nil,
               flip_code F _ l0 (hF l0 (by simp)), flip_code F _ l1 (hF l1 (by simp)), mm3]
             simp)
          | (simp +decide; rw [f5 _ (by decide) (by decide) (by decide) (by decide)]; exact m2)
          | (simp +decide; rw [f5 _ (by decide) (by decide) (by decide) (by decide)]; exact p2)
      · have o4 := outLit_out c3 _ _ l0 L0 (by decide) (by decide) K3
        generalize hc4 : run (outLit PR.v0 PR.s0) c3 = c4 at o4
        have f4 : ∀ r, r ≠ PR.addr → r ≠ PR.x → r ≠ PR.y → r ≠ PR.z → c4.reg r = c2.reg r := fun r a b d e =>
          hc4 ▸ outLit_frame c3 _ _ r a b d e
        have mm4 : c4.mem = c.mem := by rw [← hc4, outLit_mem]; exact mm3
        have o5 := outLit_out c4 _ _ l1 (L1.frame (f4 _ (by decide) (by decide) (by decide) (by decide))
          (f4 _ (by decide) (by decide) (by decide) (by decide))) (by decide) (by decide)
          (K2.frame (f4 _ (by decide) (by decide) (by decide) (by decide)) (f4 _ (by decide) (by decide) (by decide) (by decide))
            (f4 _ (by decide) (by decide) (by decide) (by decide)) (f4 _ (by decide) (by decide) (by decide) (by decide)))
        generalize hc5 : run (outLit PR.v1 PR.s1) c4 = c5 at o5
        have f5 : ∀ r, r ≠ PR.addr → r ≠ PR.x → r ≠ PR.y → r ≠ PR.z → c5.reg r = c2.reg r := fun r a b d e =>
          (hc5 ▸ outLit_frame c4 _ _ r a b d e).trans (f4 r a b d e)
        have mm5 : c5.mem = c.mem := by rw [← hc5, outLit_mem]; exact mm4
        rw [ifThird_do c5 _ (by rw [f5 _ (by decide) (by decide) (by decide) (by decide)]; exact len2)
          (by rw [f5 _ (by decide) (by decide) (by decide) (by decide)]; exact K2.two)]
        have f6 : ∀ r, r ≠ PR.addr → r ≠ PR.x → r ≠ PR.y → r ≠ PR.z → r ≠ Reg.t →
            (c5.setReg Reg.t 1).reg r = c2.reg r := by
          intro r a b d e g; simp only [setReg_reg, ite_eq_right g]; exact f5 r a b d e
        have o6 := outLit_out (c5.setReg Reg.t 1) _ _ l2
          (L2.frame (f6 _ (by decide) (by decide) (by decide) (by decide) (by decide))
          (f6 _ (by decide) (by decide) (by decide) (by decide) (by decide))) (by decide) (by decide)
          (K2.frame (f6 _ (by decide) (by decide) (by decide) (by decide) (by decide))
            (f6 _ (by decide) (by decide) (by decide) (by decide) (by decide))
            (f6 _ (by decide) (by decide) (by decide) (by decide) (by decide))
            (f6 _ (by decide) (by decide) (by decide) (by decide) (by decide)))
        first
          | (rw [o6]
             simp only [setReg_out, setReg_mem]
             rw [o5, o4, o3, mm5, mm4, f6 _ (by decide) (by decide) (by decide) (by decide) (by decide),
               f4 _ (by decide) (by decide) (by decide) (by decide), B2]
             simp only [show c3.reg Reg.B = c.reg Reg.B from B2, List.map_cons, List.map_nil, clauseCode,
               List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_cons, List.length_nil,
               flip_code F _ l0 (hF l0 (by simp)), flip_code F _ l1 (hF l1 (by simp)),
               flip_code F _ l2 (hF l2 (by simp)), mm3]
             simp)
          | (rw [outLit_frame _ _ _ _ (by decide) (by decide) (by decide) (by decide),
               f6 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact m2)
          | (rw [outLit_frame _ _ _ _ (by decide) (by decide) (by decide) (by decide),
               f6 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact p2)

end STACS2027.RAM

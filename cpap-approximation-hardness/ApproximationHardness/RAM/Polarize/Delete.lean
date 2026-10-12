module

public import ApproximationHardness.RAM.Polarize.Macros
import Lean.Elab.Tactic.Omega

/-!
# Deciding whether Lemma 10 deletes a clause
-/

@[expose] public section

namespace STACS2027.RAM

open Complexity.SAT

theorem signCode_inj (a b : Literal) : signCode a = signCode b ↔ a.positive = b.positive := by
  unfold signCode; cases a.positive <;> cases b.positive <;> simp

theorem signCode_le (l : Literal) : signCode l ≤ 1 := by unfold signCode; split <;> omega

theorem pureCounts_eq (f : CNF) (v : Nat) :
    pureCounts (occurrences f v false) (occurrences f v true) = pureThree f v := by
  unfold pureCounts pureThree
  cases (occurrences f v true == 3) <;> cases (occurrences f v false == 0) <;>
    cases (occurrences f v false == 3) <;> cases (occurrences f v true == 0) <;> simp [Bool.and_comm]

/-- Two literals clash: same variable, opposite signs. -/
def clash (a b : Literal) : Bool := a.var == b.var && a.positive != b.positive

theorem clash_comm (a b : Literal) : clash a b = clash b a := by
  unfold clash
  by_cases h : a.var = b.var
  · rw [h]; cases a.positive <;> cases b.positive <;> rfl
  · have h' : b.var ≠ a.var := Ne.symm h
    rw [show (a.var == b.var) = false from by simp [h], show (b.var == a.var) = false from by simp [h']]
    rfl

theorem clash_self (a : Literal) : clash a a = false := by unfold clash; simp

theorem tautological_two (l0 l1 : Literal) : tautological [l0, l1] = clash l0 l1 := by
  have h := clash_comm l1 l0
  simp only [tautological, List.any_cons, List.any_nil, Bool.or_false]
  rw [show (l0.var == l0.var && l0.positive != l0.positive) = clash l0 l0 from rfl,
    show (l0.var == l1.var && l0.positive != l1.positive) = clash l0 l1 from rfl,
    show (l1.var == l0.var && l1.positive != l0.positive) = clash l1 l0 from rfl,
    show (l1.var == l1.var && l1.positive != l1.positive) = clash l1 l1 from rfl, clash_self, clash_self, h]
  cases clash l0 l1 <;> rfl

theorem tautological_three (l0 l1 l2 : Literal) :
    tautological [l0, l1, l2] = (clash l0 l1 || clash l0 l2 || clash l1 l2) := by
  simp only [tautological, List.any_cons, List.any_nil, Bool.or_false]
  rw [show (l0.var == l0.var && l0.positive != l0.positive) = clash l0 l0 from rfl,
    show (l0.var == l1.var && l0.positive != l1.positive) = clash l0 l1 from rfl,
    show (l0.var == l2.var && l0.positive != l2.positive) = clash l0 l2 from rfl,
    show (l1.var == l0.var && l1.positive != l0.positive) = clash l1 l0 from rfl,
    show (l1.var == l1.var && l1.positive != l1.positive) = clash l1 l1 from rfl,
    show (l1.var == l2.var && l1.positive != l2.positive) = clash l1 l2 from rfl,
    show (l2.var == l0.var && l2.positive != l0.positive) = clash l2 l0 from rfl,
    show (l2.var == l1.var && l2.positive != l1.positive) = clash l2 l1 from rfl,
    show (l2.var == l2.var && l2.positive != l2.positive) = clash l2 l2 from rfl,
    clash_self, clash_self, clash_self, clash_comm l1 l0, clash_comm l2 l0, clash_comm l2 l1]
  cases clash l0 l1 <;> cases clash l0 l2 <;> cases clash l1 l2 <;> rfl

theorem deleted_two (f : CNF) (l0 l1 : Literal) :
    deleted f [l0, l1] = (clash l0 l1 || pureThree f l0.var || pureThree f l1.var) := by
  simp only [deleted, tautological_two, List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc]

theorem deleted_three (f : CNF) (l0 l1 l2 : Literal) :
    deleted f [l0, l1, l2] = (clash l0 l1 || pureThree f l0.var || pureThree f l1.var ||
      (clash l0 l2 || clash l1 l2 || pureThree f l2.var)) := by
  simp only [deleted, tautological_three, List.any_cons, List.any_nil, Bool.or_false]
  cases clash l0 l1 <;> cases clash l0 l2 <;> cases clash l1 l2 <;> cases pureThree f l0.var <;>
    cases pureThree f l1.var <;> cases pureThree f l2.var <;> rfl

/-- The count table of `f`: the cells `N + 2v` and `N + 2v + 1` hold the negative and positive
occurrence counts of every variable of the slots. -/
def CountsAt (f : CNF) (c : Config) (l : Literal) : Prop :=
  c.mem (c.reg Reg.N + l.var + l.var) = occurrences f l.var false ∧
    c.mem (c.reg Reg.N + l.var + l.var + 1) = occurrences f l.var true

theorem clash_iff (c : Config) {va sa vb sb : Nat} {a b : Literal} (ha : LitIn c va sa a) (hb : LitIn c vb sb b) :
    (c.reg va = c.reg vb ∧ c.reg sa ≠ c.reg sb) ↔ clash a b = true := by
  rw [ha.1, ha.2, hb.1, hb.2, Ne, signCode_inj]
  unfold clash; cases a.positive <;> cases b.positive <;> simp

theorem pure_iff (f : CNF) (c : Config) {vr sr : Nat} {l : Literal} (hl : LitIn c vr sr l) (hc : CountsAt f c l) :
    pureCounts (c.mem (c.reg Reg.N + c.reg vr + c.reg vr)) (c.mem (c.reg Reg.N + c.reg vr + c.reg vr + 1)) =
      pureThree f l.var := by
  rw [hl.1, hc.1, hc.2, pureCounts_eq]

/-- The step `del := 1 if b` in the computation of `delCode`. -/
theorem del_step {c' c : Config} {b : Bool} {P : Prop} [Decidable P] (h : c'.reg PR.del = if P then 1 else c.reg PR.del)
    (hP : P ↔ b = true) : c'.reg PR.del = if b then 1 else c.reg PR.del := by
  rw [h]; by_cases hp : P
  · rw [ite_eq_left hp, (hP.mp hp)]; rfl
  · rw [ite_eq_right hp]; cases hb : b
    · rfl
    · exact absurd (hP.mpr hb) hp

theorem ifThird_skip (c : Config) (s : Stmt) (hlen : c.reg Reg.len = 2) (htwo : c.reg PR.two = 2) :
    run (ifThird s) c = c.setReg Reg.t 0 := by
  simp [ifThird, run, hlen, htwo]

theorem ifThird_do (c : Config) (s : Stmt) (hlen : c.reg Reg.len = 3) (htwo : c.reg PR.two = 2) :
    run (ifThird s) c = run s (c.setReg Reg.t 1) := by
  simp [ifThird, run, hlen, htwo]

theorem LitIn.frame {c c' : Config} {vr sr : Nat} {l : Literal} (h : LitIn c vr sr l) (h1 : c'.reg vr = c.reg vr)
    (h2 : c'.reg sr = c.reg sr) : LitIn c' vr sr l := ⟨h1.trans h.1, h2.trans h.2⟩

theorem CountsAt.frame {f : CNF} {c c' : Config} {l : Literal} (h : CountsAt f c l) (hm : c'.mem = c.mem)
    (hN : c'.reg Reg.N = c.reg Reg.N) : CountsAt f c' l := by
  unfold CountsAt at *; rw [hm, hN]; exact h

/-- The scratch registers of `delCode`. -/
abbrev DelScratch (r : Nat) : Prop := r ≠ PR.addr ∧ r ≠ PR.x ∧ r ≠ PR.y ∧ r ≠ PR.z ∧ r ≠ PR.u ∧ r ≠ PR.del

theorem tautPair_frame' (c : Config) (va sa vb sb r : Nat) (h : DelScratch r) :
    (run (tautPair va sa vb sb) c).reg r = c.reg r := tautPair_frame c _ _ _ _ r h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.2

theorem pureLit_frame' (c : Config) (vr r : Nat) (h : DelScratch r) : (run (pureLit vr) c).reg r = c.reg r :=
  pureLit_frame c _ r h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2

/-- One `tautPair` step of `delCode`. -/
theorem tautPair_step (c : Config) {va sa vb sb : Nat} {a b : Literal} (ha : LitIn c va sa a) (hb : LitIn c vb sb b)
    (h1 : va ≠ PR.x ∧ va ≠ PR.y ∧ va ≠ PR.z ∧ va ≠ PR.del) (h2 : sa ≠ PR.x ∧ sa ≠ PR.y ∧ sa ≠ PR.z ∧ sa ≠ PR.del)
    (h3 : vb ≠ PR.x ∧ vb ≠ PR.y ∧ vb ≠ PR.z ∧ vb ≠ PR.del) (h4 : sb ≠ PR.x ∧ sb ≠ PR.y ∧ sb ≠ PR.z ∧ sb ≠ PR.del) :
    (run (tautPair va sa vb sb) c).reg PR.del = (if clash a b then 1 else c.reg PR.del) ∧
      (run (tautPair va sa vb sb) c).mem = c.mem ∧
      ∀ r, DelScratch r → (run (tautPair va sa vb sb) c).reg r = c.reg r :=
  ⟨del_step (tautPair_del c _ _ _ _ h1 h2 h3 h4) (clash_iff c ha hb), tautPair_mem c _ _ _ _,
    fun r hr => tautPair_frame' c _ _ _ _ r hr⟩

/-- One `pureLit` step of `delCode`. -/
theorem pureLit_step (f : CNF) (c : Config) {vr sr : Nat} {l : Literal} (hl : LitIn c vr sr l) (hc : CountsAt f c l)
    (hk : Consts c) (h : vr ≠ PR.addr ∧ vr ≠ PR.x ∧ vr ≠ PR.y ∧ vr ≠ PR.z ∧ vr ≠ PR.u ∧ vr ≠ PR.del) :
    (run (pureLit vr) c).reg PR.del = (if pureThree f l.var then 1 else c.reg PR.del) ∧
      (run (pureLit vr) c).mem = c.mem ∧ ∀ r, DelScratch r → (run (pureLit vr) c).reg r = c.reg r := by
  refine ⟨?_, pureLit_mem c _, fun r hr => pureLit_frame' c _ r hr⟩
  have := pureLit_del c vr h hk.one hk.three
  rw [pure_iff f c hl hc] at this; exact this

theorem Consts.scratch {c c' : Config} (h : Consts c) (hf : ∀ r, DelScratch r → c'.reg r = c.reg r) : Consts c' :=
  h.frame (hf _ (by decide)) (hf _ (by decide)) (hf _ (by decide)) (hf _ (by decide))

/-- The common prefix of `delCode`: the clash of the first two literals and the purity of their
variables. -/
theorem delCode_prefix (f : CNF) (c : Config) (l0 l1 : Literal)
    (h0 : LitIn c PR.v0 PR.s0 l0) (h1 : LitIn c PR.v1 PR.s1 l1) (hk : Consts c)
    (hc0 : CountsAt f c l0) (hc1 : CountsAt f c l1) :
    let c4 := run (pureLit PR.v1) (run (pureLit PR.v0) (run (tautPair PR.v0 PR.s0 PR.v1 PR.s1)
      (run (Stmt.const PR.del 0) c)))
    c4.reg PR.del = (if (clash l0 l1 || pureThree f l0.var || pureThree f l1.var) then 1 else 0) ∧
      c4.mem = c.mem ∧ ∀ r, DelScratch r → c4.reg r = c.reg r := by
  intro c4
  let c1 := run (Stmt.const PR.del 0) c
  have e1 : c1.reg PR.del = 0 := by simp [c1, run]
  have f1 : ∀ r, DelScratch r → c1.reg r = c.reg r := by intro r hr; simp [c1, run, hr.2.2.2.2.2]
  have m1 : c1.mem = c.mem := rfl
  obtain ⟨e2, m2, f2⟩ := tautPair_step c1 (h0.frame (f1 _ (by decide)) (f1 _ (by decide)))
    (h1.frame (f1 _ (by decide)) (f1 _ (by decide))) (by decide) (by decide) (by decide) (by decide)
  let c2 := run (tautPair PR.v0 PR.s0 PR.v1 PR.s1) c1
  have g2 : ∀ r, DelScratch r → c2.reg r = c.reg r := fun r hr => (f2 r hr).trans (f1 r hr)
  have mm2 : c2.mem = c.mem := m2.trans m1
  obtain ⟨e3, m3, f3⟩ := pureLit_step f c2 (h0.frame (g2 _ (by decide)) (g2 _ (by decide)))
    (hc0.frame mm2 (g2 _ (by decide))) (hk.scratch g2) (by decide)
  let c3 := run (pureLit PR.v0) c2
  have g3 : ∀ r, DelScratch r → c3.reg r = c.reg r := fun r hr => (f3 r hr).trans (g2 r hr)
  have mm3 : c3.mem = c.mem := m3.trans mm2
  obtain ⟨e4, m4, f4⟩ := pureLit_step f c3 (h1.frame (g3 _ (by decide)) (g3 _ (by decide)))
    (hc1.frame mm3 (g3 _ (by decide))) (hk.scratch g3) (by decide)
  refine ⟨?_, m4.trans mm3, fun r hr => (f4 r hr).trans (g3 r hr)⟩
  show (run (pureLit PR.v1) c3).reg PR.del = _
  rw [e4]; show (if pureThree f l1.var then 1 else c3.reg PR.del) = _
  rw [e3]; show (if pureThree f l1.var then 1 else if pureThree f l0.var then 1 else c2.reg PR.del) = _
  rw [e2]; show (if pureThree f l1.var then 1 else if pureThree f l0.var then 1 else
    if clash l0 l1 then 1 else c1.reg PR.del) = _
  rw [e1]
  cases clash l0 l1 <;> cases pureThree f l0.var <;> cases pureThree f l1.var <;> rfl

theorem run_delCode (c : Config) : run delCode c = run (ifThird (seqs [tautPair PR.v0 PR.s0 PR.v2 PR.s2,
    tautPair PR.v1 PR.s1 PR.v2 PR.s2, pureLit PR.v2])) (run (pureLit PR.v1) (run (pureLit PR.v0)
      (run (tautPair PR.v0 PR.s0 PR.v1 PR.s1) (run (Stmt.const PR.del 0) c)))) := by
  simp only [delCode, run_seqs_cons, run_seqs_nil]; try rfl

/-- The scratch registers of `delCode`, with `t`. -/
abbrev DelScratchT (r : Nat) : Prop := DelScratch r ∧ r ≠ Reg.t

/-- `delCode` on a clause of two literals. -/
theorem delCode_two (f : CNF) (c : Config) (l0 l1 : Literal) (hlen : c.reg Reg.len = 2)
    (h0 : LitIn c PR.v0 PR.s0 l0) (h1 : LitIn c PR.v1 PR.s1 l1) (hk : Consts c)
    (hc0 : CountsAt f c l0) (hc1 : CountsAt f c l1) :
    ((run delCode c).reg PR.del = 0 ↔ deleted f [l0, l1] = false) ∧ (run delCode c).mem = c.mem ∧
      ∀ r, DelScratchT r → (run delCode c).reg r = c.reg r := by
  obtain ⟨e4, m4, f4⟩ := delCode_prefix f c l0 l1 h0 h1 hk hc0 hc1
  rw [run_delCode]
  generalize hc4 : run (pureLit PR.v1) (run (pureLit PR.v0) (run (tautPair PR.v0 PR.s0 PR.v1 PR.s1)
    (run (Stmt.const PR.del 0) c))) = c4 at e4 m4 f4
  rw [ifThird_skip c4 _ (by rw [f4 _ (by decide)]; exact hlen) (by rw [f4 _ (by decide)]; exact hk.two)]
  refine ⟨?_, m4, fun r hr => by simp only [setReg_reg, ite_eq_right hr.2]; exact f4 r hr.1⟩
  simp only [setReg_reg, show PR.del ≠ Reg.t from by decide, ite_false]
  rw [e4, deleted_two]
  cases (clash l0 l1 || pureThree f l0.var || pureThree f l1.var) <;> simp

/-- `delCode` on a clause of three literals. -/
theorem delCode_three (f : CNF) (c : Config) (l0 l1 l2 : Literal) (hlen : c.reg Reg.len = 3)
    (h0 : LitIn c PR.v0 PR.s0 l0) (h1 : LitIn c PR.v1 PR.s1 l1) (h2 : LitIn c PR.v2 PR.s2 l2) (hk : Consts c)
    (hc0 : CountsAt f c l0) (hc1 : CountsAt f c l1) (hc2 : CountsAt f c l2) :
    ((run delCode c).reg PR.del = 0 ↔ deleted f [l0, l1, l2] = false) ∧ (run delCode c).mem = c.mem ∧
      ∀ r, DelScratchT r → (run delCode c).reg r = c.reg r := by
  obtain ⟨e4, m4, f4⟩ := delCode_prefix f c l0 l1 h0 h1 hk hc0 hc1
  rw [run_delCode]
  generalize hc4 : run (pureLit PR.v1) (run (pureLit PR.v0) (run (tautPair PR.v0 PR.s0 PR.v1 PR.s1)
    (run (Stmt.const PR.del 0) c))) = c4 at e4 m4 f4
  rw [ifThird_do c4 _ (by rw [f4 _ (by decide)]; exact hlen) (by rw [f4 _ (by decide)]; exact hk.two)]
  let c5 := c4.setReg Reg.t 1
  have f5 : ∀ r, DelScratchT r → c5.reg r = c.reg r := fun r hr => by
    simp only [c5, setReg_reg, ite_eq_right hr.2]; exact f4 r hr.1
  have f5' : ∀ r, DelScratch r → r ≠ Reg.t → c5.reg r = c.reg r := fun r hr ht => f5 r ⟨hr, ht⟩
  have e5 : c5.reg PR.del = c4.reg PR.del := by simp +decide [c5]
  have m5 : c5.mem = c.mem := m4
  have K5 : Consts c5 := hk.frame (f5 _ (by decide)) (f5 _ (by decide)) (f5 _ (by decide)) (f5 _ (by decide))
  obtain ⟨e6, m6, f6⟩ := tautPair_step c5 (h0.frame (f5 _ (by decide)) (f5 _ (by decide)))
    (h2.frame (f5 _ (by decide)) (f5 _ (by decide))) (by decide) (by decide) (by decide) (by decide)
  let c6 := run (tautPair PR.v0 PR.s0 PR.v2 PR.s2) c5
  have g6 : ∀ r, DelScratchT r → c6.reg r = c.reg r := fun r hr => (f6 r hr.1).trans (f5 r hr)
  obtain ⟨e7, m7, f7⟩ := tautPair_step c6 (h1.frame (g6 _ (by decide)) (g6 _ (by decide)))
    (h2.frame (g6 _ (by decide)) (g6 _ (by decide))) (by decide) (by decide) (by decide) (by decide)
  let c7 := run (tautPair PR.v1 PR.s1 PR.v2 PR.s2) c6
  have g7 : ∀ r, DelScratchT r → c7.reg r = c.reg r := fun r hr => (f7 r hr.1).trans (g6 r hr)
  have mm7 : c7.mem = c.mem := m7.trans (m6.trans m5)
  have K7 : Consts c7 := hk.frame (g7 _ (by decide)) (g7 _ (by decide)) (g7 _ (by decide)) (g7 _ (by decide))
  obtain ⟨e8, m8, f8⟩ := pureLit_step f c7 (h2.frame (g7 _ (by decide)) (g7 _ (by decide)))
    (hc2.frame mm7 (g7 _ (by decide))) K7 (by decide)
  have hrun : run (seqs [tautPair PR.v0 PR.s0 PR.v2 PR.s2, tautPair PR.v1 PR.s1 PR.v2 PR.s2, pureLit PR.v2]) c5 =
      run (pureLit PR.v2) c7 := by simp only [run_seqs_cons, run_seqs_nil]; try rfl
  rw [hrun]
  refine ⟨?_, m8.trans mm7, fun r hr => (f8 r hr.1).trans (g7 r hr)⟩
  rw [e8]; show (if pureThree f l2.var then 1 else c7.reg PR.del) = 0 ↔ _
  rw [e7]; show (if pureThree f l2.var then 1 else if clash l1 l2 then 1 else c6.reg PR.del) = 0 ↔ _
  rw [e6]; show (if pureThree f l2.var then 1 else if clash l1 l2 then 1 else if clash l0 l2 then 1 else
    c5.reg PR.del) = 0 ↔ _
  rw [e5, e4, deleted_three]
  cases (clash l0 l1 || pureThree f l0.var || pureThree f l1.var) <;> cases clash l0 l2 <;> cases clash l1 l2 <;>
    cases pureThree f l2.var <;> simp

end STACS2027.RAM

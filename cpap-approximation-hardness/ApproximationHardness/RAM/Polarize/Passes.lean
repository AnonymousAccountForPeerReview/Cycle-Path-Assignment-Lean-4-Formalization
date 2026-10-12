module

public import ApproximationHardness.RAM.Polarize.Delete
import Lean.Elab.Tactic.Omega

/-!
# The passes of the Lemma 10 program
-/

@[expose] public section

namespace STACS2027.RAM

open Complexity.SAT

/-- The cell counting the occurrences of the literal `l`. -/
def litAddr (N : Nat) (l : Literal) : Nat := N + l.var + l.var + signCode l

/-- The memory `base` with the counts of the literals `ls` added. -/
def cntMem (base : Nat → Nat) (N : Nat) (ls : List Literal) (a : Nat) : Nat :=
  base a + (ls.map (litAddr N)).count a

theorem cntMem_snoc (base : Nat → Nat) (N : Nat) (ls : List Literal) (l : Literal) :
    cntMem base N (ls ++ [l]) = fun a => if a = litAddr N l then cntMem base N ls a + 1 else cntMem base N ls a := by
  funext a
  simp only [cntMem, List.map_append, List.map_cons, List.map_nil, List.count_append, List.count_singleton]
  by_cases h : a = litAddr N l
  · subst h; simp; omega
  · simp [h]; intro h'; exact absurd h'.symm h

theorem cntLit_step (c : Config) (vr sr : Nat) (l : Literal) (hl : LitIn c vr sr l) (h1 : vr ≠ PR.addr)
    (h2 : sr ≠ PR.addr) (hone : c.reg Reg.one = 1) {base : Nat → Nat} {ls : List Literal}
    (hm : c.mem = cntMem base (c.reg Reg.N) ls) :
    (run (cntLit vr sr) c).mem = cntMem base (c.reg Reg.N) (ls ++ [l]) := by
  funext a
  rw [cntLit_mem c vr sr h1 h2 hone a, cntMem_snoc, hm, hl.1, hl.2]
  rfl

/-- The registers the count pass writes. -/
abbrev CntScratch (r : Nat) : Prop := r ≠ Reg.m ∧ r ≠ Reg.len ∧ r ≠ Reg.p ∧ r ≠ Reg.t ∧ r ≠ PR.v0 ∧ r ≠ PR.s0 ∧
  r ≠ PR.v1 ∧ r ≠ PR.s1 ∧ r ≠ PR.v2 ∧ r ≠ PR.s2 ∧ r ≠ PR.addr ∧ r ≠ PR.x

theorem cntBody_frame (c : Config) (r : Nat) (h : CntScratch r) : (run cntBody c).reg r = c.reg r := by
  apply run_reg_frame
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := h
  simp [cntBody, readClause, rdLit, ifThird, cntLit, regsW, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12]

theorem cntBody_out (c : Config) : (run cntBody c).out = c.out :=
  run_out_frame _ _ (by simp [cntBody, readClause, rdLit, ifThird, cntLit, hasWrite])

theorem run_cntBody (c : Config) : run cntBody c =
    run (ifThird (cntLit PR.v2 PR.s2)) (run (cntLit PR.v1 PR.s1) (run (cntLit PR.v0 PR.s0) (run readClause c))) := by
  simp only [cntBody, run_seqs_cons, run_seqs_nil]; try rfl

theorem cntLit_frame' (c : Config) (vr sr r : Nat) (h : CntScratch r) : (run (cntLit vr sr) c).reg r = c.reg r :=
  cntLit_frame c vr sr r h.2.2.2.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.2.2.2

theorem cntLit_frame_slot (c : Config) (vr sr r : Nat) (h1 : r ≠ PR.addr) (h2 : r ≠ PR.x) :
    (run (cntLit vr sr) c).reg r = c.reg r := cntLit_frame c vr sr r h1 h2

theorem cntMem_below (base : Nat → Nat) (N : Nat) (ls : List Literal) {a : Nat} (ha : a < N) :
    cntMem base N ls a = base a := by
  unfold cntMem
  rw [List.count_eq_zero_of_not_mem]
  · rfl
  · intro h
    obtain ⟨l, _, hl⟩ := List.mem_map.mp h
    unfold litAddr at hl; omega

theorem At.of_agree {c c' : Config} {w : List Nat} (h : At c w) (hp : c'.reg Reg.p = c.reg Reg.p)
    (hm : ∀ a, a < c.reg Reg.p + w.length → c'.mem a = c.mem a) : At c' w := by
  intro i hi
  rw [hp, hm _ (by omega)]
  exact h i hi

/-- The configuration `c` reads clauses from cells below `N`, the memory being `base` there with
counts added above. -/
def CntState (base : Nat → Nat) (ls : List Literal) (c : Config) : Prop :=
  c.mem = cntMem base (c.reg Reg.N) ls

theorem readClause_fr (c : Config) (r : Nat) (a1 : r ≠ Reg.m) (a2 : r ≠ Reg.len) (a3 : r ≠ Reg.p) (a4 : r ≠ Reg.t)
    (a5 : r ≠ PR.v0) (a6 : r ≠ PR.s0) (a7 : r ≠ PR.v1) (a8 : r ≠ PR.s1) (a9 : r ≠ PR.v2) (a10 : r ≠ PR.s2) :
    (run readClause c).reg r = c.reg r := by
  apply run_reg_frame
  simp [readClause, rdLit, regsW, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10]

/-- The registers `readClause` leaves alone. -/
abbrev ReadFixed (r : Nat) : Prop := r ≠ Reg.m ∧ r ≠ Reg.len ∧ r ≠ Reg.p ∧ r ≠ Reg.t ∧ r ≠ PR.v0 ∧ r ≠ PR.s0 ∧
  r ≠ PR.v1 ∧ r ≠ PR.s1 ∧ r ≠ PR.v2 ∧ r ≠ PR.s2

theorem readClause_fixed (c : Config) (r : Nat) (h : ReadFixed r) : (run readClause c).reg r = c.reg r :=
  readClause_fr c r h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.1
    h.2.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.2

/-- The result of reading a clause: the slots hold it. -/
structure ReadResult (c c' : Config) (cl : Clause) (w : List Nat) : Prop where
  len : c'.reg Reg.len = cl.length
  m : c'.reg Reg.m = c.reg Reg.m - 1
  p : c'.reg Reg.p = c.reg Reg.p + (clauseCode cl).length
  at_ : At c' w
  mem : c'.mem = c.mem
  out : c'.out = c.out
  fixed : ∀ r, ReadFixed r → c'.reg r = c.reg r

theorem readClause_result (c : Config) (cl : Clause) (w : List Nat) (hcl : cl.length = 2 ∨ cl.length = 3)
    (hAt : At c (clauseCode cl ++ w)) (hk : Consts c) :
    ReadResult c (run readClause c) cl w ∧
      ((∃ l0 l1, cl = [l0, l1] ∧ LitIn (run readClause c) PR.v0 PR.s0 l0 ∧ LitIn (run readClause c) PR.v1 PR.s1 l1) ∨
      (∃ l0 l1 l2, cl = [l0, l1, l2] ∧ LitIn (run readClause c) PR.v0 PR.s0 l0 ∧
        LitIn (run readClause c) PR.v1 PR.s1 l1 ∧ LitIn (run readClause c) PR.v2 PR.s2 l2)) := by
  rcases cl with _ | ⟨l0, _ | ⟨l1, _ | ⟨l2, _ | ⟨l3, rest⟩⟩⟩⟩
  · simp at hcl
  · simp at hcl
  · obtain ⟨len1, L0, L1, m1, p1, a1, mm1, o1⟩ := readClause_two c l0 l1 w hAt hk
    exact ⟨⟨len1, m1, by rw [p1]; simp [clauseCode, litCode], a1, mm1, o1, readClause_fixed c⟩,
      Or.inl ⟨l0, l1, rfl, L0, L1⟩⟩
  · obtain ⟨len1, L0, L1, L2, m1, p1, a1, mm1, o1⟩ := readClause_three c l0 l1 l2 w hAt hk
    exact ⟨⟨len1, m1, by rw [p1]; simp [clauseCode, litCode], a1, mm1, o1, readClause_fixed c⟩,
      Or.inr ⟨l0, l1, l2, rfl, L0, L1, L2⟩⟩
  · simp at hcl

/-- One clause of the count pass. -/
theorem cntBody_step (c : Config) (cl : Clause) (w : List Nat) (hcl : cl.length = 2 ∨ cl.length = 3)
    (hAt : At c (clauseCode cl ++ w)) (hk : Consts c) {base : Nat → Nat} {ls : List Literal}
    (hm : c.mem = cntMem base (c.reg Reg.N) ls)
    (hN : c.reg Reg.p + (clauseCode cl ++ w).length ≤ c.reg Reg.N) :
    (run cntBody c).mem = cntMem base (c.reg Reg.N) (ls ++ cl) ∧ (run cntBody c).reg Reg.m = c.reg Reg.m - 1 ∧
      (run cntBody c).reg Reg.p = c.reg Reg.p + (clauseCode cl).length ∧
      At (run cntBody c) w ∧ (run cntBody c).out = c.out ∧ ∀ r, CntScratch r → (run cntBody c).reg r = c.reg r := by
  obtain ⟨R, hlits⟩ := readClause_result c cl w hcl hAt hk
  have key : (run cntBody c).mem = cntMem base (c.reg Reg.N) (ls ++ cl) ∧
      (run cntBody c).reg Reg.m = c.reg Reg.m - 1 ∧
      (run cntBody c).reg Reg.p = c.reg Reg.p + (clauseCode cl).length := by
    rw [run_cntBody]
    generalize hc1 : run readClause c = c1 at R hlits
    have K1 : Consts c1 := hk.frame (R.fixed _ (by decide)) (R.fixed _ (by decide)) (R.fixed _ (by decide))
      (R.fixed _ (by decide))
    have N1 : c1.reg Reg.N = c.reg Reg.N := R.fixed _ (by decide)
    have hm1 : c1.mem = cntMem base (c1.reg Reg.N) ls := by rw [R.mem, N1, hm]
    rcases hlits with ⟨l0, l1, rfl, L0, L1⟩ | ⟨l0, l1, l2, rfl, L0, L1, L2⟩
    · have mm2 := cntLit_step c1 PR.v0 PR.s0 l0 L0 (by decide) (by decide) K1.one hm1
      generalize hc2 : run (cntLit PR.v0 PR.s0) c1 = c2 at mm2
      have f2 : ∀ r, r ≠ PR.addr → r ≠ PR.x → c2.reg r = c1.reg r := fun r a b => hc2 ▸ cntLit_frame c1 _ _ r a b
      have mm3 := cntLit_step c2 PR.v1 PR.s1 l1 (L1.frame (f2 _ (by decide) (by decide)) (f2 _ (by decide) (by decide)))
        (by decide) (by decide) (by rw [f2 _ (by decide) (by decide)]; exact K1.one)
        (by rw [f2 _ (by decide) (by decide)]; exact mm2)
      generalize hc3 : run (cntLit PR.v1 PR.s1) c2 = c3 at mm3
      have f3 : ∀ r, r ≠ PR.addr → r ≠ PR.x → c3.reg r = c2.reg r := fun r a b => hc3 ▸ cntLit_frame c2 _ _ r a b
      have g3 : ∀ r, r ≠ PR.addr → r ≠ PR.x → c3.reg r = c1.reg r := fun r a b => (f3 r a b).trans (f2 r a b)
      rw [ifThird_skip c3 _ (by rw [g3 _ (by decide) (by decide)]; exact R.len)
        (by rw [g3 _ (by decide) (by decide)]; exact K1.two)]
      refine ⟨?_, ?_, ?_⟩
      · show c3.mem = _
        rw [mm3, f2 _ (by decide) (by decide), N1]; simp
      · simp only [setReg_reg, show Reg.m ≠ Reg.t from by decide, ite_false]
        rw [g3 _ (by decide) (by decide)]; exact R.m
      · simp only [setReg_reg, show Reg.p ≠ Reg.t from by decide, ite_false]
        rw [g3 _ (by decide) (by decide)]; exact R.p
    · have mm2 := cntLit_step c1 PR.v0 PR.s0 l0 L0 (by decide) (by decide) K1.one hm1
      generalize hc2 : run (cntLit PR.v0 PR.s0) c1 = c2 at mm2
      have f2 : ∀ r, r ≠ PR.addr → r ≠ PR.x → c2.reg r = c1.reg r := fun r a b => hc2 ▸ cntLit_frame c1 _ _ r a b
      have mm3 := cntLit_step c2 PR.v1 PR.s1 l1 (L1.frame (f2 _ (by decide) (by decide)) (f2 _ (by decide) (by decide)))
        (by decide) (by decide) (by rw [f2 _ (by decide) (by decide)]; exact K1.one)
        (by rw [f2 _ (by decide) (by decide)]; exact mm2)
      generalize hc3 : run (cntLit PR.v1 PR.s1) c2 = c3 at mm3
      have f3 : ∀ r, r ≠ PR.addr → r ≠ PR.x → c3.reg r = c2.reg r := fun r a b => hc3 ▸ cntLit_frame c2 _ _ r a b
      have g3 : ∀ r, r ≠ PR.addr → r ≠ PR.x → c3.reg r = c1.reg r := fun r a b => (f3 r a b).trans (f2 r a b)
      rw [ifThird_do c3 _ (by rw [g3 _ (by decide) (by decide)]; exact R.len)
        (by rw [g3 _ (by decide) (by decide)]; exact K1.two)]
      let c4 := c3.setReg Reg.t 1
      have g4 : ∀ r, r ≠ PR.addr → r ≠ PR.x → r ≠ Reg.t → c4.reg r = c1.reg r := by
        intro r a b d; simp only [c4, setReg_reg, ite_eq_right d]; exact g3 r a b
      have mm5 := cntLit_step c4 PR.v2 PR.s2 l2
        (L2.frame (g4 _ (by decide) (by decide) (by decide)) (g4 _ (by decide) (by decide) (by decide)))
        (by decide) (by decide) (by rw [g4 _ (by decide) (by decide) (by decide)]; exact K1.one)
        (show c3.mem = cntMem base (c4.reg Reg.N) (ls ++ [l0] ++ [l1]) by
          rw [g4 _ (by decide) (by decide) (by decide), mm3, f2 _ (by decide) (by decide)])
      refine ⟨?_, ?_, ?_⟩
      · rw [mm5, g4 _ (by decide) (by decide) (by decide), N1]; simp
      · rw [cntLit_frame _ _ _ _ (by decide) (by decide), g4 _ (by decide) (by decide) (by decide)]; exact R.m
      · rw [cntLit_frame _ _ _ _ (by decide) (by decide), g4 _ (by decide) (by decide) (by decide)]; exact R.p
  obtain ⟨k1, k2, k3⟩ := key
  refine ⟨k1, k2, k3, ?_, cntBody_out c, fun r hr => cntBody_frame c r hr⟩
  apply At.of_agree (c := run readClause c) R.at_
  · rw [k3, R.p]
  · intro a ha
    have haN : a < c.reg Reg.N := by
      rw [R.p] at ha; simp only [List.length_append] at hN; omega
    rw [k1, R.mem, hm, cntMem_below _ _ _ haN, cntMem_below _ _ _ haN]

end STACS2027.RAM

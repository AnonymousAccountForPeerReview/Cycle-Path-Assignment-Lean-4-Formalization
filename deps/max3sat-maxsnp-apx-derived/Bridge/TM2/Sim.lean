module

public import Bridge.TM2.Program
public import Mathlib.Tactic.Ring

/-!
# Correctness of the Boolean-stack simulation of a TM2 machine

Every phase of `Setup.prog` is analysed with an explicit instruction count:
input translation, one TM2 statement, a run of TM2 steps, and output translation.
-/

@[expose] public section

namespace Bridge

open Turing Complexity.StackProgram
open Complexity.StackMachine (Registers set branch set_same set_other)

attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.σFin

theorem initList_stk_self (tm : FinTM2) (l : List (tm.Γ tm.k₀)) :
    TM2.Cfg.stk (initList tm l) tm.k₀ = l := by
  simp [initList]

theorem initList_stk_ne (tm : FinTM2) (l : List (tm.Γ tm.k₀)) {k : tm.K} (hk : k ≠ tm.k₀) :
    TM2.Cfg.stk (initList tm l) k = [] := by
  simp [initList, hk]

theorem haltList_stk_self (tm : FinTM2) (l : List (tm.Γ tm.k₁)) :
    TM2.Cfg.stk (haltList tm l) tm.k₁ = l := by
  simp [haltList]

namespace Setup

noncomputable section

variable (s : Setup)

/-! ### Pushing and reading unary symbol codes -/

theorem reach_pushT (k : s.tm.K) (cont : Option (s.SIdx × s.tm.σ)) (c : Nat) (hc : c ≤ s.N)
    (r : Registers s.nreg) :
    ∃ r', Reach s.prog (c + 1) (.pushT k (s.fin c) cont) r (s.contLabel cont) r' ∧
      r' (s.regOf k) = List.replicate c true ++ r (s.regOf k) ∧
      ∀ j, j ≠ s.regOf k → r' j = r j := by
  induction c generalizing r with
  | zero =>
    have hcode : s.prog.code (.pushT k (s.fin 0) cont) = .goto (s.contLabel cont) := by
      rw [code_pushT]
      simp [s.fin_val (n := 0) (Nat.zero_le _)]
    exact ⟨r, Reach.single (step_of_goto hcode r), by simp, fun _ _ => rfl⟩
  | succ c ih =>
    have hcode : s.prog.code (.pushT k (s.fin (c + 1)) cont) =
        .push (s.regOf k) true (.pushT k (s.fin c) cont) := by
      rw [code_pushT]
      simp [s.fin_val (n := c + 1) hc]
    obtain ⟨r', h, h1, h2⟩ := ih (by omega) (set r (s.regOf k) (true :: r (s.regOf k)))
    refine ⟨r', Reach.head (step_of_push hcode r) h, ?_, ?_⟩
    · rw [h1, set_same]
      simp [List.replicate_succ']
    · intro j hj
      rw [h2 j hj, set_other r hj]

theorem reach_pushF (k : s.tm.K) (cont : Option (s.SIdx × s.tm.σ)) (c : Nat) (hc : c ≤ s.N)
    (r : Registers s.nreg) :
    ∃ r', Reach s.prog (c + 2) (.pushF k (s.fin c) cont) r (s.contLabel cont) r' ∧
      r' (s.regOf k) = List.replicate c true ++ false :: r (s.regOf k) ∧
      ∀ j, j ≠ s.regOf k → r' j = r j := by
  obtain ⟨r', h, h1, h2⟩ :=
    s.reach_pushT k cont c hc (set r (s.regOf k) (false :: r (s.regOf k)))
  refine ⟨r', Reach.head (step_of_push (s.code_pushF k _ cont) r) h, ?_, ?_⟩
  · rw [h1, set_same]
  · intro j hj
    rw [h2 j hj, set_other r hj]

theorem reach_popT (q : s.St) (hq : s.Good q) (v : s.tm.σ) (m c : Nat) (hc : c + m ≤ s.N)
    (r : Registers s.nreg) (tl : List Bool)
    (hr : r (s.readReg q) = List.replicate m true ++ false :: tl) :
    ∃ r', Reach s.prog (m + 1) (.popT (s.ι q) v (s.fin c)) r (s.afterRead q v (c + m)) r' ∧
      r' (s.readReg q) = tl ∧ ∀ j, j ≠ s.readReg q → r' j = r j := by
  induction m generalizing c r with
  | zero =>
    have hstep : step s.prog (.popT (s.ι q) v (s.fin c)) r =
        .inr (s.afterRead q v c, set r (s.readReg q) tl) := by
      rw [step_of_pop (s.code_popT _ _ _) r, s.ι_val hq, hr, s.fin_val (n := c) (by omega)]
      rfl
    exact ⟨_, Reach.single hstep, set_same _ _ _, fun j hj => set_other r hj _⟩
  | succ m ih =>
    have hstep : step s.prog (.popT (s.ι q) v (s.fin c)) r =
        .inr (.popT (s.ι q) v (s.fin (c + 1)),
          set r (s.readReg q) (List.replicate m true ++ false :: tl)) := by
      rw [step_of_pop (s.code_popT _ _ _) r, s.ι_val hq, hr, s.fin_val (n := c) (by omega)]
      rfl
    obtain ⟨r', h, h1, h2⟩ := ih (c + 1) (by omega) (set r (s.readReg q) _) (set_same _ _ _)
    refine ⟨r', ?_, h1, fun j hj => by rw [h2 j hj, set_other r hj]⟩
    have e : c + 1 + m = c + (m + 1) := by omega
    rw [e] at h
    exact Reach.head hstep h

theorem reach_postP (m c : Nat) (hc : c + m ≤ s.N) (r : Registers s.nreg) (tl : List Bool)
    (hr : r (s.regOf s.tm.k₁) = List.replicate m true ++ false :: tl) :
    ∃ r', Reach s.prog (m + 1) (.postP (s.fin c)) r
        (.postA (s.outO (s.decO s.tm.k₁ (c + m)))) r' ∧
      r' (s.regOf s.tm.k₁) = tl ∧ ∀ j, j ≠ s.regOf s.tm.k₁ → r' j = r j := by
  induction m generalizing c r with
  | zero =>
    have hstep : step s.prog (.postP (s.fin c)) r =
        .inr (.postA (s.outO (s.decO s.tm.k₁ c)), set r (s.regOf s.tm.k₁) tl) := by
      rw [step_of_pop (s.code_postP _) r, hr, s.fin_val (n := c) (by omega)]
      rfl
    exact ⟨_, Reach.single hstep, set_same _ _ _, fun j hj => set_other r hj _⟩
  | succ m ih =>
    have hstep : step s.prog (.postP (s.fin c)) r =
        .inr (.postP (s.fin (c + 1)),
          set r (s.regOf s.tm.k₁) (List.replicate m true ++ false :: tl)) := by
      rw [step_of_pop (s.code_postP _) r, hr, s.fin_val (n := c) (by omega)]
      rfl
    obtain ⟨r', h, h1, h2⟩ :=
      ih (c + 1) (by omega) (set r (s.regOf s.tm.k₁) _) (set_same _ _ _)
    refine ⟨r', ?_, h1, fun j hj => by rw [h2 j hj, set_other r hj]⟩
    have e : c + 1 + m = c + (m + 1) := by omega
    rw [e] at h
    exact Reach.head hstep h

/-! ### The representation invariant -/

/-- Registers represent the TM2 stacks; the input/output and scratch registers are empty. -/
def Rep (S : ∀ k, List (s.tm.Γ k)) (r : Registers s.nreg) : Prop :=
  r 0 = [] ∧ r s.scr = [] ∧ ∀ k, r (s.regOf k) = s.encStack k (S k)

theorem Rep.update {s : Setup} {S : ∀ k, List (s.tm.Γ k)} {r : Registers s.nreg}
    (h : s.Rep S r) (k : s.tm.K) (x : List (s.tm.Γ k)) {r' : Registers s.nreg}
    (h1 : r' (s.regOf k) = s.encStack k x) (h2 : ∀ j, j ≠ s.regOf k → r' j = r j) :
    s.Rep (Function.update S k x) r' := by
  refine ⟨?_, ?_, fun k' => ?_⟩
  · rw [h2 0 (s.regOf_ne_zero k).symm]
    exact h.1
  · rw [h2 _ (s.regOf_ne_scr k).symm]
    exact h.2.1
  · by_cases hk : k' = k
    · subst hk
      rw [Function.update_self]
      exact h1
    · rw [Function.update_of_ne hk, h2 _ (fun e => hk (s.regOf_inj e))]
      exact h.2.2 k'

/-- Instruction budget per statement node. -/
def C : Nat := 2 * s.N + 6

/-- Maximal size of a function body. -/
def D : Nat := Finset.univ.sup fun l => stmtSize (s.tm.m l)

theorem size_le_D (l : s.tm.Λ) : stmtSize (s.tm.m l) ≤ s.D :=
  Finset.le_sup (f := fun l => stmtSize (s.tm.m l)) (Finset.mem_univ l)

/-- The program label at a TM2 step boundary. -/
def cfgLabel (c : TM2.Cfg s.tm.Γ s.tm.Λ s.tm.σ) : Label s :=
  match c.l with
  | some l => .exec (s.ι (s.tm.m l)) c.var
  | none => .post1

/-! ### One TM2 statement -/

theorem sim_stepAux (q : s.St) (hq : s.Good q) (v : s.tm.σ) (S : ∀ k, List (s.tm.Γ k))
    (r : Registers s.nreg) (hr : s.Rep S r) :
    ∃ r', Reach s.prog (s.C * stmtSize q) (.exec (s.ι q) v) r
        (s.cfgLabel (TM2.stepAux q v S)) r' ∧
      s.Rep (TM2.stepAux q v S).stk r' := by
  have hC : s.C = 2 * s.N + 6 := rfl
  induction q generalizing v S r with
  | push k f q ih =>
    have hcode : s.prog.code (.exec (s.ι (TM2.Stmt.push k f q)) v) =
        .goto (.pushF k (s.fin (s.idx k (f v))) (some (s.ι q, v))) := by
      rw [code_exec, s.ι_val hq]
      rfl
    have hlt := s.idx_lt k (f v)
    obtain ⟨r1, h1, h1a, h1b⟩ :=
      s.reach_pushF k (some (s.ι q, v)) (s.idx k (f v)) (by omega) r
    have hrep : s.Rep (Function.update S k (f v :: S k)) r1 :=
      hr.update k _ (by rw [h1a, hr.2.2 k]; rfl) h1b
    obtain ⟨r2, h2, h2r⟩ := ih hq.push v _ r1 hrep
    refine ⟨r2, ?_, h2r⟩
    refine (Reach.head (step_of_goto hcode r) (h1.trans h2)).mono ?_
    simp only [stmtSize, Nat.mul_succ]
    omega
  | peek k f q ih =>
    have hcode : s.prog.code (.exec (s.ι (TM2.Stmt.peek k f q)) v) =
        .peek (s.regOf k) (.exec (s.ι q) (f v none))
          (.popT (s.ι (TM2.Stmt.peek k f q)) v (s.fin 0))
          (.popT (s.ι (TM2.Stmt.peek k f q)) v (s.fin 0)) := by
      rw [code_exec, s.ι_val hq]
      rfl
    have hstep := step_of_peek hcode r
    cases hS : S k with
    | nil =>
      have hreg : r (s.regOf k) = [] := by
        rw [hr.2.2 k, hS]
        rfl
      rw [hreg] at hstep
      have e : TM2.stepAux (TM2.Stmt.peek k f q) v S = TM2.stepAux q (f v none) S := by
        simp [TM2.stepAux, hS]
      rw [e]
      obtain ⟨r2, h2, h2r⟩ := ih hq.peek (f v none) S r hr
      refine ⟨r2, (Reach.head hstep h2).mono ?_, h2r⟩
      simp only [stmtSize, Nat.mul_succ]
      omega
    | cons g rest =>
      have hreg : r (s.regOf k) =
          List.replicate (s.idx k g) true ++ false :: s.encStack k rest := by
        rw [hr.2.2 k, hS]
        rfl
      rw [hreg, branch_replicate_same] at hstep
      have hlt := s.idx_lt k g
      obtain ⟨r1, h1, h1a, h1b⟩ :=
        s.reach_popT (TM2.Stmt.peek k f q) hq v (s.idx k g) 0 (by omega) r _ hreg
      have hafter : s.afterRead (TM2.Stmt.peek k f q) v (0 + s.idx k g) =
          .pushF k (s.fin (s.idx k g)) (some (s.ι q, f v (some g))) := by
        rw [Nat.zero_add]
        show Label.pushF k (s.fin (s.idx k g)) (some (s.ι q, f v (s.decO k (s.idx k g)))) = _
        rw [s.decO_idx]
      rw [hafter] at h1
      obtain ⟨r2, h2, h2a, h2b⟩ :=
        s.reach_pushF k (some (s.ι q, f v (some g))) (s.idx k g) (by omega) r1
      have hrep : s.Rep S r2 := by
        have := hr.update k (S k) (r' := r2)
          (by rw [h2a]; rw [show r1 (s.regOf k) = s.encStack k rest from h1a, hS]; rfl)
          (fun j hj => by rw [h2b j hj]; exact h1b j hj)
        rwa [Function.update_eq_self] at this
      have e : TM2.stepAux (TM2.Stmt.peek k f q) v S = TM2.stepAux q (f v (some g)) S := by
        simp [TM2.stepAux, hS]
      rw [e]
      obtain ⟨r3, h3, h3r⟩ := ih hq.peek (f v (some g)) S r2 hrep
      refine ⟨r3, (Reach.head hstep (h1.trans (h2.trans h3))).mono ?_, h3r⟩
      simp only [stmtSize, Nat.mul_succ]
      omega
  | pop k f q ih =>
    have hcode : s.prog.code (.exec (s.ι (TM2.Stmt.pop k f q)) v) =
        .peek (s.regOf k) (.exec (s.ι q) (f v none))
          (.popT (s.ι (TM2.Stmt.pop k f q)) v (s.fin 0))
          (.popT (s.ι (TM2.Stmt.pop k f q)) v (s.fin 0)) := by
      rw [code_exec, s.ι_val hq]
      rfl
    have hstep := step_of_peek hcode r
    cases hS : S k with
    | nil =>
      have hreg : r (s.regOf k) = [] := by
        rw [hr.2.2 k, hS]
        rfl
      rw [hreg] at hstep
      have e : TM2.stepAux (TM2.Stmt.pop k f q) v S =
          TM2.stepAux q (f v none) (Function.update S k []) := by
        simp [TM2.stepAux, hS]
      rw [e]
      have hrep : s.Rep (Function.update S k []) r := hr.update k [] hreg (fun _ _ => rfl)
      obtain ⟨r2, h2, h2r⟩ := ih hq.pop (f v none) _ r hrep
      refine ⟨r2, (Reach.head hstep h2).mono ?_, h2r⟩
      simp only [stmtSize, Nat.mul_succ]
      omega
    | cons g rest =>
      have hreg : r (s.regOf k) =
          List.replicate (s.idx k g) true ++ false :: s.encStack k rest := by
        rw [hr.2.2 k, hS]
        rfl
      rw [hreg, branch_replicate_same] at hstep
      have hlt := s.idx_lt k g
      obtain ⟨r1, h1, h1a, h1b⟩ :=
        s.reach_popT (TM2.Stmt.pop k f q) hq v (s.idx k g) 0 (by omega) r _ hreg
      have hafter : s.afterRead (TM2.Stmt.pop k f q) v (0 + s.idx k g) =
          .exec (s.ι q) (f v (some g)) := by
        rw [Nat.zero_add]
        show Label.exec (s.ι q) (f v (s.decO k (s.idx k g))) = _
        rw [s.decO_idx]
      rw [hafter] at h1
      have e : TM2.stepAux (TM2.Stmt.pop k f q) v S =
          TM2.stepAux q (f v (some g)) (Function.update S k rest) := by
        simp [TM2.stepAux, hS]
      rw [e]
      have hrep : s.Rep (Function.update S k rest) r1 := hr.update k rest h1a h1b
      obtain ⟨r2, h2, h2r⟩ := ih hq.pop (f v (some g)) _ r1 hrep
      refine ⟨r2, (Reach.head hstep (h1.trans h2)).mono ?_, h2r⟩
      simp only [stmtSize, Nat.mul_succ]
      omega
  | load a q ih =>
    have hcode : s.prog.code (.exec (s.ι (TM2.Stmt.load a q)) v) =
        .goto (.exec (s.ι q) (a v)) := by
      rw [code_exec, s.ι_val hq]
      rfl
    obtain ⟨r2, h2, h2r⟩ := ih hq.load (a v) S r hr
    refine ⟨r2, (Reach.head (step_of_goto hcode r) h2).mono ?_, h2r⟩
    simp only [stmtSize, Nat.mul_succ]
    omega
  | branch f q₁ q₂ ih₁ ih₂ =>
    have hcode : s.prog.code (.exec (s.ι (TM2.Stmt.branch f q₁ q₂)) v) =
        .goto (.exec (s.ι (cond (f v) q₁ q₂)) v) := by
      rw [code_exec, s.ι_val hq]
      rfl
    have hstep := step_of_goto hcode r
    cases hf : f v with
    | true =>
      simp only [hf, Bool.cond_true] at hstep
      have e : TM2.stepAux (TM2.Stmt.branch f q₁ q₂) v S = TM2.stepAux q₁ v S := by
        simp [TM2.stepAux, hf]
      rw [e]
      obtain ⟨r2, h2, h2r⟩ := ih₁ hq.branch_left v S r hr
      refine ⟨r2, (Reach.head hstep h2).mono ?_, h2r⟩
      simp only [stmtSize, Nat.mul_succ, Nat.mul_add]
      omega
    | false =>
      simp only [hf, Bool.cond_false] at hstep
      have e : TM2.stepAux (TM2.Stmt.branch f q₁ q₂) v S = TM2.stepAux q₂ v S := by
        simp [TM2.stepAux, hf]
      rw [e]
      obtain ⟨r2, h2, h2r⟩ := ih₂ hq.branch_right v S r hr
      refine ⟨r2, (Reach.head hstep h2).mono ?_, h2r⟩
      simp only [stmtSize, Nat.mul_succ, Nat.mul_add]
      omega
  | goto f =>
    have hcode : s.prog.code (.exec (s.ι (TM2.Stmt.goto f)) v) =
        .goto (.exec (s.ι (s.tm.m (f v))) v) := by
      rw [code_exec, s.ι_val hq]
      rfl
    refine ⟨r, (Reach.single (step_of_goto hcode r)).mono ?_, hr⟩
    simp only [stmtSize]
    omega
  | halt =>
    have hcode : s.prog.code (.exec (s.ι TM2.Stmt.halt) v) = .goto .post1 := by
      rw [code_exec, s.ι_val hq]
      rfl
    refine ⟨r, (Reach.single (step_of_goto hcode r)).mono ?_, hr⟩
    simp only [stmtSize]
    omega

/-! ### A run of TM2 steps -/

theorem sim_run (t : Nat) (c c' : TM2.Cfg s.tm.Γ s.tm.Λ s.tm.σ) (r : Registers s.nreg)
    (hr : s.Rep c.stk r)
    (h : (flip bind (TM2.step s.tm.m))^[t] (some c) = some c') :
    ∃ r', Reach s.prog (t * (s.C * s.D)) (s.cfgLabel c) r (s.cfgLabel c') r' ∧
      s.Rep c'.stk r' := by
  induction t generalizing c r with
  | zero =>
    have hc : c = c' := Option.some.inj h
    subst hc
    exact ⟨r, Reach.refl _ _ _, hr⟩
  | succ t ih =>
    rw [Function.iterate_succ_apply] at h
    obtain ⟨l, v, S⟩ := c
    cases l with
    | none =>
      have hs : flip bind (TM2.step s.tm.m) (some ⟨none, v, S⟩) = none := rfl
      rw [hs, iterate_bind_none] at h
      exact absurd h (by simp)
    | some l =>
      have hs : flip bind (TM2.step s.tm.m) (some ⟨some l, v, S⟩) =
          some (TM2.stepAux (s.tm.m l) v S) := rfl
      rw [hs] at h
      obtain ⟨r1, h1, h1r⟩ := s.sim_stepAux (s.tm.m l) (s.good_m l) v S r hr
      obtain ⟨r2, h2, h2r⟩ := ih _ r1 h1r h
      refine ⟨r2, (h1.trans h2).mono ?_, h2r⟩
      have := Nat.mul_le_mul_left s.C (s.size_le_D l)
      rw [Nat.succ_mul]
      omega

/-! ### Input and output translation -/

theorem reach_pre2 (w : List Bool) (r : Registers s.nreg) (hw : r s.scr = w) :
    ∃ r', Reach s.prog ((s.N + 4) * w.length + 1) .pre2 r
        (.exec (s.ι (s.tm.m s.tm.main)) s.tm.initialState) r' ∧
      r' s.scr = [] ∧
      r' (s.regOf s.tm.k₀) =
        s.encStack s.tm.k₀ ((w.map s.inp).reverse) ++ r (s.regOf s.tm.k₀) ∧
      ∀ j, j ≠ s.scr → j ≠ s.regOf s.tm.k₀ → r' j = r j := by
  induction w generalizing r with
  | nil =>
    have hstep : step s.prog .pre2 r =
        .inr (.exec (s.ι (s.tm.m s.tm.main)) s.tm.initialState, set r s.scr []) := by
      rw [step_of_pop s.code_pre2 r, hw]
      rfl
    refine ⟨set r s.scr [], (Reach.single hstep).mono (by omega), by simp, ?_, ?_⟩
    · simp [set_other r (s.regOf_ne_scr s.tm.k₀)]
    · intro j hj _
      exact set_other r hj _
  | cons b w ih =>
    have hstep : step s.prog .pre2 r =
        .inr (.pushF s.tm.k₀ (s.fin (s.idx s.tm.k₀ (s.inp b))) none, set r s.scr w) := by
      rw [step_of_pop s.code_pre2 r, hw]
      cases b <;> rfl
    have hlt := s.idx_lt s.tm.k₀ (s.inp b)
    obtain ⟨r1, h1, h1a, h1b⟩ :=
      s.reach_pushF s.tm.k₀ none (s.idx s.tm.k₀ (s.inp b)) (by omega) (set r s.scr w)
    have hscr1 : r1 s.scr = w := by
      rw [h1b _ (s.regOf_ne_scr _).symm, set_same]
    obtain ⟨r2, h2, h2a, h2b, h2c⟩ := ih r1 hscr1
    refine ⟨r2, ?_, h2a, ?_, ?_⟩
    · refine (Reach.head hstep (h1.trans h2)).mono ?_
      simp only [List.length_cons, Nat.mul_succ]
      omega
    · rw [h2b, h1a, set_other r (s.regOf_ne_scr _)]
      simp [encStack_append, encStack_cons]
    · intro j hj hj'
      rw [h2c j hj hj', h1b j hj', set_other r hj]

theorem reach_post1 (l : List (s.tm.Γ s.tm.k₁)) (r : Registers s.nreg)
    (hl : r (s.regOf s.tm.k₁) = s.encStack s.tm.k₁ l) :
    ∃ r', Reach s.prog ((s.N + 4) * l.length + 1) .post1 r .post2 r' ∧
      r' s.scr = (l.map s.out).reverse ++ r s.scr ∧
      ∀ j, j ≠ s.scr → j ≠ s.regOf s.tm.k₁ → r' j = r j := by
  induction l generalizing r with
  | nil =>
    have hstep : step s.prog .post1 r = .inr (.post2, r) := by
      rw [step_of_peek s.code_post1 r, hl]
      rfl
    exact ⟨r, (Reach.single hstep).mono (by omega), by simp, fun _ _ _ => rfl⟩
  | cons g l ih =>
    have hreg : r (s.regOf s.tm.k₁) =
        List.replicate (s.idx s.tm.k₁ g) true ++ false :: s.encStack s.tm.k₁ l := hl
    have hstep : step s.prog .post1 r = .inr (.postP (s.fin 0), r) := by
      rw [step_of_peek s.code_post1 r, hreg, branch_replicate_same]
    have hlt := s.idx_lt s.tm.k₁ g
    obtain ⟨r1, h1, h1a, h1b⟩ := s.reach_postP (s.idx s.tm.k₁ g) 0 (by omega) r _ hreg
    rw [Nat.zero_add, s.decO_idx] at h1
    have hstep2 := step_of_push (s.code_postA (s.out g)) r1
    obtain ⟨r2, h2, h2a, h2b⟩ := ih (set r1 s.scr (s.out g :: r1 s.scr))
      (by rw [set_other r1 (s.regOf_ne_scr _), h1a])
    refine ⟨r2, ?_, ?_, ?_⟩
    · refine (Reach.head hstep (h1.trans (Reach.head hstep2 h2))).mono ?_
      simp only [List.length_cons, Nat.mul_succ]
      omega
    · rw [h2a, set_same, h1b _ (s.regOf_ne_scr _).symm]
      simp
    · intro j hj hj'
      rw [h2b j hj hj', set_other r1 hj, h1b j hj']

/-! ### The whole simulation -/

/-- Instructions used by input translation and by `t` simulated TM2 steps. -/
def preMain (n t : Nat) : Nat := (s.N + 6) * n + 2 + t * (s.C * s.D)

/-- Instructions used by the whole simulation of `t` TM2 steps on an input of length `n`. -/
def total (n t : Nat) : Nat := s.preMain n t + (s.N + 6) * s.preMain n t + 3

theorem preMain_mono (n : Nat) {t t' : Nat} (h : t ≤ t') : s.preMain n t ≤ s.preMain n t' :=
  Nat.add_le_add_left (Nat.mul_le_mul_right _ h) _

theorem total_mono (n : Nat) {t t' : Nat} (h : t ≤ t') : s.total n t ≤ s.total n t' :=
  Nat.add_le_add_right
    (Nat.add_le_add (s.preMain_mono n h) (Nat.mul_le_mul_left _ (s.preMain_mono n h))) 3

theorem total_poly (T : Nat → Nat) (hT : Complexity.PolynomialBound T) :
    Complexity.PolynomialBound (fun n => s.total n (T n)) := by
  have hX : Complexity.PolynomialBound (fun n => s.preMain n (T n)) :=
    (((Complexity.PolynomialBound.constant (s.N + 6)).mul
      Complexity.PolynomialBound.identity).add (Complexity.PolynomialBound.constant 2)).add
      (hT.mul (Complexity.PolynomialBound.constant (s.C * s.D)))
  exact (hX.add ((Complexity.PolynomialBound.constant (s.N + 6)).mul hX)).add
    (Complexity.PolynomialBound.constant 3)

theorem simulate_core (w : List Bool) (t : Nat) (o : List (s.tm.Γ s.tm.k₁))
    (h : (flip bind (TM2.step s.tm.m))^[t] (some (initList s.tm (w.map s.inp))) =
      some (haltList s.tm o))
    (r0 : Registers s.nreg) (h0 : r0 0 = w) (hn : ∀ j, j ≠ 0 → r0 j = []) :
    ∃ time r', time ≤ s.total w.length t ∧
      Complexity.StackProgram.run s.prog time .pre1 r0 = some (true, r') ∧
      r' 0 = o.map s.out := by
  obtain ⟨r1, hA, hA1, hA2, hA3⟩ := reach_move (p := s.prog) (src := 0) (dst := s.scr)
    s.scr_ne_zero.symm (la := Label.preA) s.code_pre1 s.code_preA w r0 h0
  have hscr1 : r1 s.scr = w.reverse := by
    rw [hA2, hn _ s.scr_ne_zero, List.append_nil]
  obtain ⟨r2, hB, hB1, hB2, hB3⟩ := s.reach_pre2 w.reverse r1 hscr1
  have hrep2 : s.Rep (TM2.Cfg.stk (initList s.tm (w.map s.inp))) r2 := by
    refine ⟨?_, hB1, fun k => ?_⟩
    · rw [hB3 0 s.scr_ne_zero.symm (s.regOf_ne_zero _).symm]
      exact hA1
    · by_cases hk : k = s.tm.k₀
      · subst hk
        rw [hB2, hA3 _ (s.regOf_ne_zero _) (s.regOf_ne_scr _), hn _ (s.regOf_ne_zero _),
          initList_stk_self]
        simp
      · rw [hB3 _ (s.regOf_ne_scr _) (fun e => hk (s.regOf_inj e)),
          hA3 _ (s.regOf_ne_zero _) (s.regOf_ne_scr _), hn _ (s.regOf_ne_zero _),
          initList_stk_ne _ _ hk]
        rfl
  obtain ⟨r3, hC, hrep3⟩ := s.sim_run t _ _ r2 hrep2 h
  have hk1 : r3 (s.regOf s.tm.k₁) = s.encStack s.tm.k₁ o := by
    rw [hrep3.2.2, haltList_stk_self]
  obtain ⟨r4, hD, hD1, hD2⟩ := s.reach_post1 o r3 hk1
  have hscr4 : r4 s.scr = (o.map s.out).reverse := by
    rw [hD1, hrep3.2.1, List.append_nil]
  obtain ⟨r5, hE, hE1, hE2, hE3⟩ := reach_move (p := s.prog) (src := s.scr) (dst := 0)
    s.scr_ne_zero (la := Label.postB) s.code_post2 s.code_postB _ r4 hscr4
  have hdone : Complexity.StackProgram.run s.prog 1 .done r5 = some (true, r5) := by
    simp [Complexity.StackProgram.run, step, code_done]
  have hABC := (hA.trans hB).trans hC
  have e1 : (s.N + 6) * w.length = (s.N + 4) * w.length + 2 * w.length := by ring
  have e2 : (s.N + 6) * o.length = (s.N + 4) * o.length + 2 * o.length := by ring
  have hlen : o.length ≤ s.preMain w.length t := by
    have h1 := s.length_le_encStack s.tm.k₁ o
    have h2 := hABC.length_le (s.regOf s.tm.k₁)
    rw [hk1, hn _ (s.regOf_ne_zero _)] at h2
    simp only [List.length_nil, List.length_reverse] at h2
    unfold preMain
    omega
  have hmul := Nat.mul_le_mul_left (s.N + 6) hlen
  obtain ⟨time, htime, hrun⟩ := ((hABC.trans hD).trans hE).run hdone
  refine ⟨time, r5, ?_, hrun, ?_⟩
  · simp only [List.length_reverse, List.length_map] at htime
    unfold total
    unfold preMain at hlen hmul ⊢
    omega
  · rw [hE2, hD2 0 s.scr_ne_zero.symm (s.regOf_ne_zero _).symm, hrep3.1]
    simp

theorem simulate (w : List Bool) (t : Nat) (o : List (s.tm.Γ s.tm.k₁))
    (h : (flip bind (TM2.step s.tm.m))^[t] (some (initList s.tm (w.map s.inp))) =
      some (haltList s.tm o)) :
    ∃ time r', time ≤ s.total w.length t ∧
      Complexity.StackProgram.run s.prog time .pre1 (fun j => if j = 0 then w else []) =
        some (true, r') ∧
      r' 0 = o.map s.out :=
  s.simulate_core w t o h _ (by simp) (fun j hj => by simp [hj])

end

end Setup

end Bridge

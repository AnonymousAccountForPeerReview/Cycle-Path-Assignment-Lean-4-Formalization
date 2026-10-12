module

public import Bridge.TM2.Reach
public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Prod

/-!
# The Boolean-stack program simulating a TM2 machine

Symbols of stack `k` are written in unary (`idx` many `true` bits followed by one
`false` bit, top first).  Register `0` holds the raw input/output word, one scratch
register is used for reversals, and every TM2 stack owns one further register.
-/

@[expose] public section

namespace Bridge

open Turing Complexity.StackProgram
open Complexity.StackMachine (Registers set branch)

attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.σFin

/-- Number of nodes of a TM2 statement. -/
def stmtSize {K : Type} {Γ : K → Type} {Λ σ : Type} : TM2.Stmt Γ Λ σ → Nat
  | .push _ _ q => stmtSize q + 1
  | .peek _ _ q => stmtSize q + 1
  | .pop _ _ q => stmtSize q + 1
  | .load _ q => stmtSize q + 1
  | .branch _ q₁ q₂ => stmtSize q₁ + stmtSize q₂ + 1
  | .goto _ => 1
  | .halt => 1

/-- Data of the simulation: a machine, the bit translations, and unary symbol indices. -/
structure Setup where
  tm : FinTM2
  inp : Bool → tm.Γ tm.k₀
  out : tm.Γ tm.k₁ → Bool
  N : Nat
  idx : ∀ k, tm.Γ k → Nat
  idx_lt : ∀ k g, idx k g < N
  idx_inj : ∀ k, Function.Injective (idx k)

namespace Setup

noncomputable section

variable (s : Setup)

/-- Statements of the machine. -/
abbrev St : Type := TM2.Stmt s.tm.Γ s.tm.Λ s.tm.σ

open scoped Classical in
/-- All sub-statements of all function bodies. -/
def allStmts : Finset s.St := Finset.univ.biUnion fun l => TM2.stmts₁ (s.tm.m l)

/-- The finite type of statement positions. -/
abbrev SIdx : Type := {q : s.St // q ∈ s.allStmts}

/-- A statement all of whose sub-statements are positions of the machine. -/
def Good (q : s.St) : Prop := TM2.stmts₁ q ⊆ s.allStmts

open scoped Classical in
theorem good_m (l : s.tm.Λ) : s.Good (s.tm.m l) := by
  intro q hq
  unfold allStmts
  exact Finset.mem_biUnion.2 ⟨l, Finset.mem_univ _, hq⟩

theorem Good.of_mem {s : Setup} {q q' : s.St} (h : s.Good q) (hm : q' ∈ TM2.stmts₁ q) :
    s.Good q' :=
  (TM2.stmts₁_trans hm).trans h

open scoped Classical in
theorem Good.push {s : Setup} {k f} {q : s.St} (h : s.Good (TM2.Stmt.push k f q)) : s.Good q :=
  h.of_mem (by rw [TM2.stmts₁]; exact Finset.mem_insert_of_mem TM2.stmts₁_self)

open scoped Classical in
theorem Good.peek {s : Setup} {k f} {q : s.St} (h : s.Good (TM2.Stmt.peek k f q)) : s.Good q :=
  h.of_mem (by rw [TM2.stmts₁]; exact Finset.mem_insert_of_mem TM2.stmts₁_self)

open scoped Classical in
theorem Good.pop {s : Setup} {k f} {q : s.St} (h : s.Good (TM2.Stmt.pop k f q)) : s.Good q :=
  h.of_mem (by rw [TM2.stmts₁]; exact Finset.mem_insert_of_mem TM2.stmts₁_self)

open scoped Classical in
theorem Good.load {s : Setup} {a} {q : s.St} (h : s.Good (TM2.Stmt.load a q)) : s.Good q :=
  h.of_mem (by rw [TM2.stmts₁]; exact Finset.mem_insert_of_mem TM2.stmts₁_self)

open scoped Classical in
theorem Good.branch_left {s : Setup} {f} {q₁ q₂ : s.St}
    (h : s.Good (TM2.Stmt.branch f q₁ q₂)) : s.Good q₁ :=
  h.of_mem (by
    rw [TM2.stmts₁]
    exact Finset.mem_insert_of_mem (Finset.mem_union_left _ TM2.stmts₁_self))

open scoped Classical in
theorem Good.branch_right {s : Setup} {f} {q₁ q₂ : s.St}
    (h : s.Good (TM2.Stmt.branch f q₁ q₂)) : s.Good q₂ :=
  h.of_mem (by
    rw [TM2.stmts₁]
    exact Finset.mem_insert_of_mem (Finset.mem_union_right _ TM2.stmts₁_self))

open scoped Classical in
/-- Retraction of all statements onto positions. -/
def ι (q : s.St) : s.SIdx :=
  if h : q ∈ s.allStmts then ⟨q, h⟩ else ⟨s.tm.m s.tm.main, s.good_m _ TM2.stmts₁_self⟩

theorem ι_val {q : s.St} (h : s.Good q) : (s.ι q).val = q := by
  unfold ι
  rw [dite_eq_left (h TM2.stmts₁_self)]

open scoped Classical in
/-- Partial inverse of the symbol index. -/
def decO (k : s.tm.K) (c : Nat) : Option (s.tm.Γ k) :=
  if h : ∃ g, s.idx k g = c then some h.choose else none

theorem decO_idx (k : s.tm.K) (g : s.tm.Γ k) : s.decO k (s.idx k g) = some g := by
  unfold decO
  have h : ∃ g', s.idx k g' = s.idx k g := ⟨g, rfl⟩
  rw [dite_eq_left h]
  exact congrArg some (s.idx_inj k h.choose_spec)

/-- Counters stored in the finite control. -/
def fin (n : Nat) : Fin (s.N + 1) := ⟨n % (s.N + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩

theorem fin_val {n : Nat} (h : n ≤ s.N) : (s.fin n).val = n :=
  Nat.mod_eq_of_lt (by omega)

/-- The Boolean code of a stack, top first. -/
def encStack (k : s.tm.K) : List (s.tm.Γ k) → List Bool
  | [] => []
  | g :: l => List.replicate (s.idx k g) true ++ false :: encStack k l

@[simp] theorem encStack_nil (k : s.tm.K) : s.encStack k [] = [] := rfl

theorem encStack_cons (k : s.tm.K) (g : s.tm.Γ k) (l : List (s.tm.Γ k)) :
    s.encStack k (g :: l) = List.replicate (s.idx k g) true ++ false :: s.encStack k l := rfl

theorem encStack_append (k : s.tm.K) (l₁ l₂ : List (s.tm.Γ k)) :
    s.encStack k (l₁ ++ l₂) = s.encStack k l₁ ++ s.encStack k l₂ := by
  induction l₁ with
  | nil => rfl
  | cons g l ih => simp [encStack_cons, ih]

theorem length_le_encStack (k : s.tm.K) (l : List (s.tm.Γ k)) :
    l.length ≤ (s.encStack k l).length := by
  induction l with
  | nil => simp
  | cons g l ih => simp [encStack_cons]; omega

/-- Number of registers minus one. -/
abbrev nreg : Nat := Fintype.card s.tm.K + 1

/-- The scratch register. -/
def scr : Fin (s.nreg + 1) := ⟨1, by show 1 < Fintype.card s.tm.K + 1 + 1; omega⟩

/-- The register of a TM2 stack. -/
def regOf (k : s.tm.K) : Fin (s.nreg + 1) :=
  ⟨(Fintype.equivFin s.tm.K k).val + 2, by
    have := (Fintype.equivFin s.tm.K k).isLt
    show _ < Fintype.card s.tm.K + 1 + 1
    omega⟩

theorem scr_ne_zero : s.scr ≠ 0 := by
  intro h
  have := congrArg Fin.val h
  simp [scr] at this

theorem regOf_ne_zero (k : s.tm.K) : s.regOf k ≠ 0 := by
  intro h
  have := congrArg Fin.val h
  simp [regOf] at this

theorem regOf_ne_scr (k : s.tm.K) : s.regOf k ≠ s.scr := by
  intro h
  have := congrArg Fin.val h
  simp [regOf, scr] at this

theorem regOf_inj {k k' : s.tm.K} (h : s.regOf k = s.regOf k') : k = k' := by
  have := congrArg Fin.val h
  simp only [regOf, Nat.add_right_cancel_iff] at this
  exact (Fintype.equivFin s.tm.K).injective (Fin.ext this)

/-- Control labels of the simulating program. -/
inductive Label (s : Setup) where
  | pre1
  | preA (b : Bool)
  | pre2
  | exec (q : s.SIdx) (v : s.tm.σ)
  | pushF (k : s.tm.K) (c : Fin (s.N + 1)) (cont : Option (s.SIdx × s.tm.σ))
  | pushT (k : s.tm.K) (c : Fin (s.N + 1)) (cont : Option (s.SIdx × s.tm.σ))
  | popT (q : s.SIdx) (v : s.tm.σ) (c : Fin (s.N + 1))
  | post1
  | postP (c : Fin (s.N + 1))
  | postA (b : Bool)
  | post2
  | postB (b : Bool)
  | done
  deriving Fintype

/-- Where to continue after pushing a symbol. -/
def contLabel : Option (s.SIdx × s.tm.σ) → Label s
  | none => .pre2
  | some (q, v) => .exec q v

/-- Output bit of a decoded symbol. -/
def outO : Option (s.tm.Γ s.tm.k₁) → Bool
  | some g => s.out g
  | none => false

/-- The register read by a pop or peek statement. -/
def readReg : s.St → Fin (s.nreg + 1)
  | .pop k _ _ => s.regOf k
  | .peek k _ _ => s.regOf k
  | _ => 0

/-- Continuation after a pop or peek statement has read the symbol with index `c`. -/
def afterRead : s.St → s.tm.σ → Nat → Label s
  | .pop k f q, v, c => .exec (s.ι q) (f v (s.decO k c))
  | .peek k f q, v, c => .pushF k (s.fin c) (some (s.ι q, f v (s.decO k c)))
  | _, _, _ => .done

/-- First instruction of a statement. -/
def execOp : s.St → s.tm.σ → Op s.nreg (Label s)
  | .push k f q, v => .goto (.pushF k (s.fin (s.idx k (f v))) (some (s.ι q, v)))
  | .peek k f q, v => .peek (s.regOf k) (.exec (s.ι q) (f v none))
      (.popT (s.ι (.peek k f q)) v (s.fin 0)) (.popT (s.ι (.peek k f q)) v (s.fin 0))
  | .pop k f q, v => .peek (s.regOf k) (.exec (s.ι q) (f v none))
      (.popT (s.ι (.pop k f q)) v (s.fin 0)) (.popT (s.ι (.pop k f q)) v (s.fin 0))
  | .load a q, v => .goto (.exec (s.ι q) (a v))
  | .branch f q₁ q₂, v => .goto (.exec (s.ι (cond (f v) q₁ q₂)) v)
  | .goto f, v => .goto (.exec (s.ι (s.tm.m (f v))) v)
  | .halt, _ => .goto .post1

/-- The simulating program. -/
def prog : Program s.nreg (Label s) where
  start := .pre1
  code
    | .pre1 => .pop 0 .pre2 (.preA false) (.preA true)
    | .preA b => .push s.scr b .pre1
    | .pre2 => .pop s.scr (.exec (s.ι (s.tm.m s.tm.main)) s.tm.initialState)
        (.pushF s.tm.k₀ (s.fin (s.idx s.tm.k₀ (s.inp false))) none)
        (.pushF s.tm.k₀ (s.fin (s.idx s.tm.k₀ (s.inp true))) none)
    | .exec q v => s.execOp q.val v
    | .pushF k c cont => .push (s.regOf k) false (.pushT k c cont)
    | .pushT k c cont =>
      if c.val = 0 then .goto (s.contLabel cont)
      else .push (s.regOf k) true (.pushT k (s.fin (c.val - 1)) cont)
    | .popT q v c => .pop (s.readReg q.val) .done (s.afterRead q.val v c.val)
        (.popT q v (s.fin (c.val + 1)))
    | .post1 => .peek (s.regOf s.tm.k₁) .post2 (.postP (s.fin 0)) (.postP (s.fin 0))
    | .postP c => .pop (s.regOf s.tm.k₁) .post2 (.postA (s.outO (s.decO s.tm.k₁ c.val)))
        (.postP (s.fin (c.val + 1)))
    | .postA b => .push s.scr b .post1
    | .post2 => .pop s.scr .done (.postB false) (.postB true)
    | .postB b => .push 0 b .post2
    | .done => .halt true

theorem code_pre1 : s.prog.code .pre1 = .pop 0 .pre2 (.preA false) (.preA true) := rfl
theorem code_preA (b : Bool) : s.prog.code (.preA b) = .push s.scr b .pre1 := rfl
theorem code_pre2 : s.prog.code .pre2 =
    .pop s.scr (.exec (s.ι (s.tm.m s.tm.main)) s.tm.initialState)
      (.pushF s.tm.k₀ (s.fin (s.idx s.tm.k₀ (s.inp false))) none)
      (.pushF s.tm.k₀ (s.fin (s.idx s.tm.k₀ (s.inp true))) none) := rfl
theorem code_exec (q : s.SIdx) (v : s.tm.σ) : s.prog.code (.exec q v) = s.execOp q.val v := rfl
theorem code_pushF (k : s.tm.K) (c : Fin (s.N + 1)) (cont : Option (s.SIdx × s.tm.σ)) :
    s.prog.code (.pushF k c cont) = .push (s.regOf k) false (.pushT k c cont) := rfl
theorem code_pushT (k : s.tm.K) (c : Fin (s.N + 1)) (cont : Option (s.SIdx × s.tm.σ)) :
    s.prog.code (.pushT k c cont) =
      if c.val = 0 then .goto (s.contLabel cont)
      else .push (s.regOf k) true (.pushT k (s.fin (c.val - 1)) cont) := rfl
theorem code_popT (q : s.SIdx) (v : s.tm.σ) (c : Fin (s.N + 1)) :
    s.prog.code (.popT q v c) = .pop (s.readReg q.val) .done (s.afterRead q.val v c.val)
      (.popT q v (s.fin (c.val + 1))) := rfl
theorem code_post1 : s.prog.code .post1 =
    .peek (s.regOf s.tm.k₁) .post2 (.postP (s.fin 0)) (.postP (s.fin 0)) := rfl
theorem code_postP (c : Fin (s.N + 1)) : s.prog.code (.postP c) =
    .pop (s.regOf s.tm.k₁) .post2 (.postA (s.outO (s.decO s.tm.k₁ c.val)))
      (.postP (s.fin (c.val + 1))) := rfl
theorem code_postA (b : Bool) : s.prog.code (.postA b) = .push s.scr b .post1 := rfl
theorem code_post2 : s.prog.code .post2 = .pop s.scr .done (.postB false) (.postB true) := rfl
theorem code_postB (b : Bool) : s.prog.code (.postB b) = .push 0 b .post2 := rfl
theorem code_done : s.prog.code .done = .halt true := rfl

end

end Setup

end Bridge

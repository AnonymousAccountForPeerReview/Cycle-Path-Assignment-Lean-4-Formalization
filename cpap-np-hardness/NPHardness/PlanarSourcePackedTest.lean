module

public import Complexity.Planar.EmitGrid

/-!
Finite guards used by the packed grid emitter.  These are ordinary syntax:
every guard compiles into the registered clause language's arithmetic and
input branches.  No guard calls an arbitrary Lean predicate at runtime.
-/

@[expose] public section
namespace STACS2027.PlanarSource.Packed
open Complexity Complexity.SAT Complexity.StackTableauEmitter

inductive Test (n : Nat) where
  | const (b : Bool)
  | le (a b : NumExpr n)
  | input (index : NumExpr n)
  | and (a b : Test n)
  | or (a b : Test n)
  | not (a : Test n)

def Test.eval {n : Nat} (w : Word) (env : Env n) : Test n → Bool
  | .const b => b
  | .le a b => decide (a.eval env ≤ b.eval env)
  | .input index => (w[index.eval env]?).getD false
  | .and a b => a.eval w env && b.eval w env
  | .or a b => a.eval w env || b.eval w env
  | .not a => !(a.eval w env)

def Test.select {n : Nat} (t : Test n) (yes no : ClauseProgram n) : ClauseProgram n :=
  match t with
  | .const b => if b then yes else no
  | .le a b => .ifLe a b yes no
  | .input index => .ifInput index no no yes
  | .and a b => a.select (b.select yes no) no
  | .or a b => a.select yes (b.select yes no)
  | .not a => a.select no yes

theorem Test.select_emit {n : Nat} (t : Test n) (yes no : ClauseProgram n)
    (w : Word) (env : Env n) :
    (t.select yes no).emit w env =
      if t.eval w env then yes.emit w env else no.emit w env := by
  induction t generalizing yes no with
  | const b => cases b <;> rfl
  | le a b => simp only [select, ClauseProgram.emit, eval, decide_eq_true_eq]
  | input i =>
      change (ClauseProgram.ifInput i no no yes).emit w env = _
      calc
        _ = (if (w[i.eval env]?).getD false then yes else no).emit w env :=
          Complexity.Planar.Emit.ifInput_bool i (fun b => if b then yes else no) w env
        _ = _ := by change _ = if (w[i.eval env]?).getD false then _ else _; split <;> rfl
  | and a b ia ib =>
      simp only [select, ia, ib, eval]
      by_cases ha : a.eval w env = true <;> by_cases hb : b.eval w env = true <;>
        simp_all
  | or a b ia ib =>
      simp only [select, ia, ib, eval]
      by_cases ha : a.eval w env = true <;> by_cases hb : b.eval w env = true <;>
        simp_all
  | not a ia =>
      simp only [select, ia, eval]
      by_cases ha : a.eval w env = true <;> simp_all

def Test.eq {n : Nat} (a b : NumExpr n) : Test n := .and (.le a b) (.le b a)
def Test.lt {n : Nat} (a b : NumExpr n) : Test n := .not (.le b a)

@[simp] theorem Test.eval_eq {n : Nat} (a b : NumExpr n) (w : Word) (env : Env n) :
    (Test.eq a b).eval w env = decide (a.eval env = b.eval env) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Test.eq, Test.eval, Bool.and_eq_true, decide_eq_true_eq,
    Nat.le_antisymm_iff]

@[simp] theorem Test.eval_lt {n : Nat} (a b : NumExpr n) (w : Word) (env : Env n) :
    (Test.lt a b).eval w env = decide (a.eval env < b.eval env) := by
  by_cases h : b.eval env ≤ a.eval env
  · simp [Test.lt, Test.eval, h, Nat.not_lt.mpr h]
  · simp [Test.lt, Test.eval, h, Nat.lt_of_not_ge h]

def Test.all {n : Nat} : List (Test n) → Test n
  | [] => .const true
  | t :: ts => .and t (Test.all ts)

@[simp] theorem Test.eval_all {n : Nat} (ts : List (Test n)) (w : Word) (env : Env n) :
    (Test.all ts).eval w env = ts.all (fun t => t.eval w env) := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp only [Test.all, Test.eval, List.all_cons, ih]

/-- One implication clause; both signs are computed by finite input tests. -/
def pairProgram {n : Nat} (a b : NumExpr n) (sa sb : Test n) : ClauseProgram n :=
  sa.select
    (sb.select (.clause [⟨a,true⟩,⟨b,false⟩]) (.clause [⟨a,true⟩,⟨b,true⟩]))
    (sb.select (.clause [⟨a,false⟩,⟨b,false⟩]) (.clause [⟨a,false⟩,⟨b,true⟩]))

theorem pairProgram_emit {n : Nat} (a b : NumExpr n) (sa sb : Test n)
    (w : Word) (env : Env n) :
    (pairProgram a b sa sb).emit w env =
      [[⟨a.eval env, sa.eval w env⟩, ⟨b.eval env, !(sb.eval w env)⟩]] := by
  simp only [pairProgram, Test.select_emit]
  cases sa.eval w env <;> cases sb.eval w env <;> rfl

end STACS2027.PlanarSource.Packed

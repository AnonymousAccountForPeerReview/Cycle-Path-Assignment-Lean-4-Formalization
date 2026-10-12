module

public import NPHardness.PlanarSourcePackedTest
public import Complexity.StackTableauMachineBounds

/-!
A compiled finite-candidate successor emitter.  Candidate descriptions are
finite arithmetic/input syntax.  The emitted clauses implement the explicit
minimum-successor/wraparound test, with every comparison compiled by the
registered clause compiler.  Coverage of a particular grid neighborhood is
a separate geometric theorem, not a runtime oracle.
-/

@[expose] public section
namespace STACS2027.PlanarSource.Packed
open Complexity Complexity.SAT Complexity.StackTableauEmitter

structure Entry where
  live : Bool
  index : Nat
  «variable» : Nat
  top : Bool
  key : Nat
  sign : Bool
  deriving DecidableEq

structure Occurrence (n : Nat) where
  live : Test n
  index : NumExpr n
  «variable» : NumExpr n
  top : Bool
  key : NumExpr n
  sign : Test n

def Occurrence.eval {n : Nat} (p : Occurrence n) (w : SAT.Word) (env : Env n) : Entry :=
  ⟨p.live.eval w env, p.index.eval env, p.variable.eval env, p.top,
    p.key.eval env, p.sign.eval w env⟩

def Before (p q : Entry) : Prop :=
  (p.top = true ∧ q.top = false) ∨ (p.top = q.top ∧ p.key < q.key)

def Active (p q : Entry) : Prop := q.live = true ∧ q.variable = p.variable

def NextIn (p q : Entry) (xs : List Entry) : Prop :=
  p.live = true ∧ Active p q ∧
    ((Before p q ∧ ∀ r ∈ xs, Active p r → ¬ (Before p r ∧ Before r q)) ∨
      ((∀ r ∈ xs, Active p r → ¬ Before p r) ∧
        (∀ r ∈ xs, Active p r → ¬ Before r q)))

def beforeTest {n : Nat} (p q : Occurrence n) : Test n :=
  if p.top then
    if q.top then Test.lt p.key q.key else .const true
  else if q.top then .const false else Test.lt p.key q.key

def activeTest {n : Nat} (p q : Occurrence n) : Test n :=
  .and q.live (Test.eq q.variable p.variable)

theorem beforeTest_eval {n : Nat} (p q : Occurrence n) (w : SAT.Word) (env : Env n) :
    (beforeTest p q).eval w env = true ↔ Before (p.eval w env) (q.eval w env) := by
  rcases p with ⟨pl, pi, pv, pt, pk, ps⟩
  rcases q with ⟨ql, qi, qv, qt, qk, qs⟩
  cases pt <;> cases qt <;>
    simp [beforeTest, Occurrence.eval, Before, Test.eval]

theorem activeTest_eval {n : Nat} (p q : Occurrence n) (w : SAT.Word) (env : Env n) :
    (activeTest p q).eval w env = true ↔ Active (p.eval w env) (q.eval w env) := by
  simp [activeTest, Test.eval, Active, Occurrence.eval]

def successorTest {n : Nat} (p q : Occurrence n) (xs : List (Occurrence n)) : Test n :=
  .and p.live (.and (activeTest p q)
    (.or
      (.and (beforeTest p q)
        (Test.all (xs.map fun r => .not (.and (activeTest p r)
          (.and (beforeTest p r) (beforeTest r q))))))
      (.and
        (Test.all (xs.map fun r => .not (.and (activeTest p r) (beforeTest p r))))
        (Test.all (xs.map fun r => .not (.and (activeTest p r) (beforeTest r q)))))))

theorem successorTest_eval {n : Nat} (p q : Occurrence n) (xs : List (Occurrence n))
    (w : SAT.Word) (env : Env n) :
    (successorTest p q xs).eval w env = true ↔
      NextIn (p.eval w env) (q.eval w env) (xs.map (fun r => r.eval w env)) := by
  have hn (b : Bool) : (!b) = true ↔ ¬ (b = true) := by cases b <;> decide
  simp only [successorTest, Test.eval, Bool.and_eq_true, Bool.or_eq_true,
    Test.eval_all, List.all_eq_true, List.mem_map, forall_exists_index,
    and_imp, forall_apply_eq_imp_iff₂, hn, activeTest_eval, beforeTest_eval, NextIn]
  simp only [Occurrence.eval, not_and]

def successorProgram {n : Nat} (p : Occurrence n) (xs : List (Occurrence n)) :
    ClauseProgram n :=
  (xs.foldr (fun q rest => .seq
      ((successorTest p q xs).select
        (pairProgram p.index q.index p.sign q.sign) .skip) rest) .skip)

/-- Exact emitted list, including the chosen endpoint indices and signs. -/
theorem successorProgram_emit {n : Nat} (p : Occurrence n) (xs : List (Occurrence n))
    (w : SAT.Word) (env : Env n) :
    (successorProgram p xs).emit w env =
      xs.flatMap (fun q => if (successorTest p q xs).eval w env then
        [[⟨p.index.eval env,p.sign.eval w env⟩,
          ⟨q.index.eval env,!(q.sign.eval w env)⟩]] else []) := by
  unfold successorProgram
  suffices h : ∀ ys : List (Occurrence n), (ys.foldr (fun q rest => ClauseProgram.seq
      ((successorTest p q xs).select (pairProgram p.index q.index p.sign q.sign) .skip)
      rest) .skip).emit w env = ys.flatMap (fun q =>
        if (successorTest p q xs).eval w env then
          [[⟨p.index.eval env,p.sign.eval w env⟩,
            ⟨q.index.eval env,!(q.sign.eval w env)⟩]] else []) by exact h xs
  intro ys
  induction ys with
  | nil => rfl
  | cons q ys ih =>
      simp only [List.foldr_cons, ClauseProgram.emit_seq, Test.select_emit,
        pairProgram_emit, ClauseProgram.emit_skip, List.flatMap_cons, ih]

end STACS2027.PlanarSource.Packed

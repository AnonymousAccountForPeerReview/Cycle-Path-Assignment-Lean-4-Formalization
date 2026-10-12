module

public import NPHardness.GlobalReduction

/-!
# The two optimization problems and L-reductions (Section 6)

MAX-SAT asks for a truth assignment satisfying as many clauses as possible; the
cycle-path assignment problem asks for an assignment of least cost. The optima are
characterized rather than computed: `IsMaxSat f S` says that `S` is attained and never
exceeded, `IsMinCost g k C` that `C` is the least budget admitting an assignment.
An L-reduction with parameters `α = αn / αd` and `β = βn / βd` from the first problem to
the second is recorded by its two inequalities (Section 6 of the manuscript):
`OPT_B(f(x)) ≤ α OPT_A(x)` and `OPT_A(x) − m_A(x, g(x, y)) ≤ β (m_B(f(x), y) − OPT_B(f(x)))`,
the second for every feasible solution `y` of the target instance.
-/

@[expose] public section
namespace STACS2027
open Complexity.SAT

/-- The number of clauses of `f` satisfied by `a`: the objective `s(A)` of MAX-SAT. -/
def satisfiedCount (a : Assignment) (f : CNF) : Nat := f.countP (evalClause a)

/-- `S` is the optimum `S*` of MAX-SAT on `f`: attained by some assignment, never exceeded. -/
def IsMaxSat (f : CNF) (S : Nat) : Prop :=
  (∃ a : Assignment, satisfiedCount a f = S) ∧ ∀ a : Assignment, satisfiedCount a f ≤ S

/-- `C` is the optimum `C*` of `CPAP(g, k)`: the least budget admitting an assignment. -/
def IsMinCost (g : Graph) (k C : Nat) : Prop :=
  HasAssignment g k C ∧ ∀ B, HasAssignment g k B → C ≤ B

/-- The L-reduction inequalities (`α = αn/αd`, `β = βn/βd`) for a map `F` to `CPAP(·, k)`: `αd C* ≤ αn S*`,
and every assignment `ps` gives some `a` with `βd (S* − s(a)) ≤ βn (c(ps) − C*)` (without subtraction). -/
def LReductionToCPAP (Source : CNF → Prop) (F : CNF → Graph) (k αn αd βn βd : Nat) : Prop :=
  ∀ f, Source f → ∀ S C, IsMaxSat f S → IsMinCost (F f) k C →
    αd * C ≤ αn * S ∧
    ∀ ps, ValidChoices ((cycles (F f) k).map selectedOptions) ps →
      ∃ a : Assignment, βd * S + βn * C ≤ βd * satisfiedCount a f + βn * cost ps

/-- The L-reduction inequalities for a MAX-SAT map `T`: `αd OPT(T f) ≤ αn OPT(f)`, and every `b` gives
some `a` with `βd (OPT(f) − s_f(a)) ≤ βn (OPT(T f) − s_{T f}(b))` (without subtraction). -/
def LReductionSat (Source : CNF → Prop) (T : CNF → CNF) (αn αd βn βd : Nat) : Prop :=
  ∀ f, Source f → ∀ S S', IsMaxSat f S → IsMaxSat (T f) S' →
    αd * S' ≤ αn * S ∧
    ∀ b : Assignment, ∃ a : Assignment, βd * S + βn * satisfiedCount b (T f) ≤ βd * satisfiedCount a f + βn * S'

end STACS2027

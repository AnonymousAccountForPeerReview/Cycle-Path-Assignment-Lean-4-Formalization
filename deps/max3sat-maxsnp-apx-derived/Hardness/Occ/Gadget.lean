module

public import Hardness.Occ.Basic

/-!
# Consistency gadgets: the generic construction

A gadget family `g : Gadget` gives, for a variable with `k` occurrences, a directed multigraph
on the nodes `0, …, g.nodes k - 1` (arcs `g.arcs k`) and the node `g.cont k j` (the *contact*)
that replaces the `j`-th occurrence. For a formula `f`, with `V = variableBound f` and
`W = width f` (a strict bound on the numbers of nodes), node `v` of the gadget of `x` is the
new variable `x * W + v`, and `red f` is

* `relabel f`: `f` with the `j`-th occurrence of `x` replaced by the contact of number `j`,
* `gadgetCNF f`: for every variable `x` that occurs, a clause `(¬ (x, u) ∨ (x, w))` for every
  arc `u → w` of its gadget.

`roundWord f y` rounds an assignment of `red f` to an assignment of `f`: every variable gets
the majority value of its contacts. `liftWord f y` copies an assignment of `f` to all nodes.
All maps are explicit list programs; `PT.red` and `PT.roundWord` state that they are
polynomial-time when the gadget family is.
-/

@[expose] public section

set_option linter.dupNamespace false

namespace Complexity.Occ

open Complexity.PT

/-- A family of consistency gadgets, indexed by the number of occurrences. -/
structure Gadget where
  nodes : Nat → Nat
  cont : Nat → Nat → Nat
  arcs : Nat → List (Nat × Nat)

namespace Gadget

variable (g : Gadget)

/-- A strict bound on the numbers of nodes of the gadgets used for `f`. -/
def width (f : SAT.CNF) : Nat :=
  ((List.range (SAT.variableBound f)).map fun x => g.nodes (occ f x)).sum + 1

/-- The new literal for the annotated literal `q`: the contact of number `q.2` of the gadget of
its variable. -/
def newLit (f : SAT.CNF) (q : SAT.Literal × Nat) : SAT.Literal :=
  ⟨q.1.var * g.width f + g.cont (occ f q.1.var) q.2, q.1.positive⟩

/-- `f` with every occurrence replaced by its contact. -/
def relabel (f : SAT.CNF) : SAT.CNF := (ann f).map fun cl => cl.map (g.newLit f)

/-- The clause `(¬ (x, e.1) ∨ (x, e.2))` of the arc `e`. -/
def arcClause (W x : Nat) (e : Nat × Nat) : SAT.Clause :=
  [⟨x * W + e.1, false⟩, ⟨x * W + e.2, true⟩]

/-- The gadget clauses of the variable `x`. -/
def block (f : SAT.CNF) (x : Nat) : SAT.CNF :=
  if occ f x = 0 then [] else (g.arcs (occ f x)).map (arcClause (g.width f) x)

/-- All gadget clauses. -/
def gadgetCNF (f : SAT.CNF) : SAT.CNF := (List.range (SAT.variableBound f)).flatMap (g.block f)

/-- The reduced formula. -/
def red (f : SAT.CNF) : SAT.CNF := g.relabel f ++ g.gadgetCNF f

/-- The number of true contacts of `x` under `σ`. -/
def trueCount (f : SAT.CNF) (σ : SAT.Assignment) (x : Nat) : Nat :=
  (List.range (occ f x)).countP fun j => σ (x * g.width f + g.cont (occ f x) j)

/-- The majority value of the contacts of `x` (true in case of a tie). -/
def majority (f : SAT.CNF) (σ : SAT.Assignment) (x : Nat) : Bool :=
  decide (occ f x ≤ 2 * g.trueCount f σ x)

/-- The rounded assignment, as a word no longer than the code of `f`. -/
def roundWord (f : SAT.CNF) (y : Word) : Word :=
  (List.range (SAT.encode f).length).map (g.majority f (SAT.assignmentOf y))

/-- An assignment of `f` copied to all nodes, as a word no longer than the code of `red f`. -/
def liftWord (f : SAT.CNF) (y : Word) : Word :=
  (List.range (SAT.encode (g.red f)).length).map fun n => SAT.assignmentOf y (n / g.width f)

/-! ### Polynomial time -/

/-- The gadget family is polynomial-time computable. -/
structure IsPT : Prop where
  nodes : PT g.nodes
  cont : PT (fun p : Nat × Nat => g.cont p.1 p.2)
  arcs : PT g.arcs

variable {g}

protected theorem PT.width (hg : g.IsPT) : PT g.width := by
  have h1 := hg.nodes
  unfold width
  fun_prop

protected theorem PT.red (hg : g.IsPT) : PT g.red := by
  have h1 := hg.nodes
  have h2 := hg.cont
  have h3 := hg.arcs
  have hw := PT.width hg
  unfold red relabel gadgetCNF block newLit arcClause
  fun_prop

protected theorem PT.roundWord (hg : g.IsPT) :
    PT (fun p : SAT.CNF × Word => g.roundWord p.1 p.2) := by
  have h1 := hg.nodes
  have h2 := hg.cont
  have hw := PT.width hg
  unfold roundWord majority trueCount
  fun_prop

end Gadget

end Complexity.Occ

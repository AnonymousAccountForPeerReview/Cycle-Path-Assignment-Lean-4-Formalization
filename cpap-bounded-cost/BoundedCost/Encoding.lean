module

public import NPHardness.OmittedVertex
public import Complexity.SAT

/-!
# The 2-CNF encodings of Section 4 (Theorem 4 and Corollary 5)

For a graph `g` and `k ≥ 4`, with the simple `k`-cycles `C_0, …, C_{t-1}` of
`cycles g k`, the Boolean variable `b_{C_i,e}` for the edge `e` at position `j` of
`C_i` is the number `i * k + j`; it means "do not use `e` in the path chosen for
`C_i`". The path constraints `Γ₁` forbid marking two vertex-disjoint edges of a
cycle; the overlap constraint of a candidate overlap `(e, {C, C'})` requires one of
the two paths to omit `e`. `Γ'` repeats `Γ₁` `Ψ + 1` times and adds every overlap
constraint, so that deleting at most `Ψ` clauses can only delete overlap
constraints; Almost 2-SAT asks whether such a deletion leaves a satisfiable
formula. For cost zero (Corollary 5), the overlap constraints of each edge `e`
are replaced by a linear-size prefix encoding with the auxiliary variables
`s_{e,1}, …, s_{e,p-1}`, `p` being the number of cycles containing `e`.

Formulas use the registered CNF type of the foundation (`Complexity.SAT`).
-/

@[expose] public section
namespace STACS2027
open Complexity.SAT

/-- `C_i`, the `i`-th enumerated simple `k`-cycle of `g` (the empty list if there is none). -/
def kCycle (g : Graph) (k i : Nat) : Cycle := (cycles g k).getD i []

/-- The variable `b_{C_i,e}` for the edge `e` at position `j` of `C_i`: the number `i * k + j`. -/
def pathVariable (k i j : Nat) : Nat := i * k + j

/-- The edge at position `j` of `C_i` (the edges of `C_i` are `cycleEdges (kCycle g k i)`). -/
def cycleEdgeAt (g : Graph) (k i j : Nat) : Edge := (cycleEdges (kCycle g k i)).getD j (0, 0)

/-- The position of `e` among the edges of `C_i`. -/
def edgePosition (g : Graph) (k i : Nat) (e : Edge) : Nat := (cycleEdges (kCycle g k i)).idxOf e

/-- The variable `b_{C_i,e}`, named by the edge `e`. -/
def edgeVariable (g : Graph) (k i : Nat) (e : Edge) : Nat :=
  pathVariable k i (edgePosition g k i e)

/-- `e` and `e'` are vertex-disjoint: they share no endpoint. -/
def disjointEdges (e e' : Edge) : Bool :=
  e.1 != e'.1 && e.1 != e'.2 && e.2 != e'.1 && e.2 != e'.2

/-- The path constraints `Γ₁`: `¬b_{C,e_a} ∨ ¬b_{C,e_b}` for every cycle `C = C_i` and every
pair of vertex-disjoint edges `e_a, e_b` of `C`, at positions `a < b`. -/
def pathConstraints (g : Graph) (k : Nat) : CNF :=
  (List.range (cycles g k).length).flatMap fun i =>
    (List.range k).flatMap fun a =>
      (List.range k).filterMap fun b =>
        if decide (a < b) && disjointEdges (cycleEdgeAt g k i a) (cycleEdgeAt g k i b) then
          some [⟨pathVariable k i a, false⟩, ⟨pathVariable k i b, false⟩]
        else none

/-- The candidate overlaps `𝒰`: `(i, i', e)` for `i < i'` and `e` an edge of both `C_i` and
`C_{i'}`; the manuscript's `(e, {C_i, C_{i'}})`. -/
def candidateOverlaps (g : Graph) (k : Nat) : List (Nat × Nat × Edge) :=
  (List.range (cycles g k).length).flatMap fun i =>
    (List.range (cycles g k).length).flatMap fun i' =>
      if i < i' then
        ((cycleEdges (kCycle g k i)).filter fun e => (cycleEdges (kCycle g k i')).contains e).map
          fun e => (i, i', e)
      else []

/-- The overlap constraint `λ_u = b_{C,e} ∨ b_{C',e}` of the candidate overlap `u`. -/
def overlapClause (g : Graph) (k : Nat) (u : Nat × Nat × Edge) : Clause :=
  [⟨edgeVariable g k u.1 u.2.2, true⟩, ⟨edgeVariable g k u.2.1 u.2.2, true⟩]

/-- `Γ_𝓘`: the path constraints and the overlap constraints of the candidate overlaps outside
the permitted list `permitted`. -/
def permittedFormula (g : Graph) (k : Nat) (permitted : List (Nat × Nat × Edge)) : CNF :=
  pathConstraints g k ++
    ((candidateOverlaps g k).filter fun u => !permitted.contains u).map (overlapClause g k)

/-- `Γ'`: `Ψ + 1` copies of the path constraints, then every overlap constraint. -/
def almostFormula (g : Graph) (k Ψ : Nat) : CNF :=
  (List.replicate (Ψ + 1) (pathConstraints g k)).flatten ++
    (candidateOverlaps g k).map (overlapClause g k)

/-- Almost 2-SAT accepts `(f, Ψ)`: deleting at most `Ψ` clause occurrences from `f` leaves a
satisfiable formula. -/
def AlmostSatisfiable (f : CNF) (Ψ : Nat) : Prop :=
  ∃ sub : CNF, sub.Sublist f ∧ f.length ≤ sub.length + Ψ ∧ Satisfiable sub

/-- The edges lying on a `k`-cycle of `g`, each once, in order of first appearance. -/
def edgesOnCycles (g : Graph) (k : Nat) : List Edge :=
  ((cycles g k).flatMap cycleEdges).eraseDups

/-- The indices of the cycles containing `e`: the `C_1, …, C_p` of Corollary 5. -/
def cyclesThrough (g : Graph) (k : Nat) (e : Edge) : List Nat :=
  (List.range (cycles g k).length).filter fun i => (cycleEdges (kCycle g k i)).contains e

/-- The number of the variable `s_{e,1}`: after the `k t` path variables and the prefix
variables of the edges listed before `e`. -/
def prefixOffset (g : Graph) (k : Nat) (e : Edge) : Nat :=
  k * (cycles g k).length +
    (((edgesOnCycles g k).takeWhile fun e' => e' != e).map fun e' =>
      (cyclesThrough g k e').length - 1).sum

/-- The variable `s_{e,x+1}` (so `x = 0, …, p − 2`). -/
def prefixVariable (g : Graph) (k : Nat) (e : Edge) (x : Nat) : Nat := prefixOffset g k e + x

/-- The prefix clauses of `e`, with cycles `C_1, …, C_p` (here `0, …, p − 1`) and variables
`s_1, …, s_{p-1}` (here `0, …, p − 2`): `b_{C_x,e} ∨ s_x` for `x < p − 1`;
`¬s_{x-1} ∨ s_x` for `1 ≤ x < p − 1`; `b_{C_x,e} ∨ ¬s_{x-1}` for `1 ≤ x ≤ p − 1`. -/
def prefixClauses (g : Graph) (k : Nat) (e : Edge) : CNF :=
  let cs := cyclesThrough g k e
  let b := fun x => edgeVariable g k (cs.getD x 0) e
  let s := fun x => prefixVariable g k e x
  ((List.range (cs.length - 1)).map fun x => [⟨b x, true⟩, ⟨s x, true⟩]) ++
  ((List.range (cs.length - 1)).filterMap fun x =>
    if 0 < x then some [⟨s (x - 1), false⟩, ⟨s x, true⟩] else none) ++
  ((List.range cs.length).filterMap fun x =>
    if 0 < x then some [⟨b x, true⟩, ⟨s (x - 1), false⟩] else none)

/-- The formula of Corollary 5: the path constraints and the prefix clauses of every edge on a
`k`-cycle. -/
def zeroCostFormula (g : Graph) (k : Nat) : CNF :=
  pathConstraints g k ++ (edgesOnCycles g k).flatMap (prefixClauses g k)

end STACS2027

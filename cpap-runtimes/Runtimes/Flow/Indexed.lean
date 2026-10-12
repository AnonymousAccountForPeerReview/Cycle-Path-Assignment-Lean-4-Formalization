module

public import Runtimes.Flow.Solver
import Mathlib.Tactic

/-!
# Indexed unit-capacity flow and its residual graph

Parallel arc occurrences are indexed separately. This is the representation used by the
ordinary polynomial solver development; it does not replace the cited almost-linear solver.
-/

@[expose] public section

namespace STACS2027.Runtimes.Flow

/-- A finite, numbered, unit-capacity network. Parallel arcs have separate indices. -/
structure IndexedNetwork (nodes arcs : ℕ) where
  tail : Fin arcs → Fin nodes
  head : Fin arcs → Fin nodes
  cost : Fin arcs → ℕ
  source : Fin nodes
  sink : Fin nodes
  source_ne_sink : source ≠ sink

/-- A Boolean choice for every arc occurrence. -/
abbrev IndexedFlow (arcs : ℕ) := Fin arcs → Bool

/-- Signed divergence of the selected arcs at a numbered node. -/
def indexedBalance {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    (flow : IndexedFlow arcs) (v : Fin nodes) : ℤ :=
  ∑ i : Fin arcs, if flow i then
    (if net.tail i = v then (1 : ℤ) else 0) - (if net.head i = v then (1 : ℤ) else 0)
    else 0

/-- Total nonnegative cost of selected arc occurrences. -/
def indexedCost {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    (flow : IndexedFlow arcs) : ℕ :=
  ∑ i : Fin arcs, if flow i then net.cost i else 0

/-- A feasible flow of value `d`, expressed as divergence at each numbered node. -/
def IsIndexedFlow {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    (d : ℕ) (flow : IndexedFlow arcs) : Prop :=
  ∀ v, indexedBalance net flow v =
    if v = net.source then (d : ℤ) else if v = net.sink then -(d : ℤ) else 0

/-- One residual arc: a free original occurrence, or a used occurrence backwards. -/
structure ResidualEdge (arcs : ℕ) where
  index : Fin arcs
  reverse : Bool
  deriving DecidableEq, BEq

/-- A residual arc is available precisely when its direction reverses its current bit. -/
def residualAvailable {arcs : ℕ} (flow : IndexedFlow arcs) (edge : ResidualEdge arcs) : Prop :=
  edge.reverse = flow edge.index

/-- Tail of a residual arc. -/
def residualTail {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    (edge : ResidualEdge arcs) : Fin nodes :=
  if edge.reverse then net.head edge.index else net.tail edge.index

/-- Head of a residual arc. -/
def residualHead {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    (edge : ResidualEdge arcs) : Fin nodes :=
  if edge.reverse then net.tail edge.index else net.head edge.index

/-- Signed residual cost; removing a selected arc refunds its cost. -/
def residualEdgeCost {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    (edge : ResidualEdge arcs) : ℤ :=
  if edge.reverse then -(net.cost edge.index : ℤ) else (net.cost edge.index : ℤ)

/-- Signed total cost of a residual-edge list. -/
def residualCost {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    (edges : List (ResidualEdge arcs)) : ℤ :=
  (edges.map (residualEdgeCost net)).sum

/-- Divergence of a residual-edge list. -/
def residualBalance {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    (edges : List (ResidualEdge arcs)) (v : Fin nodes) : ℤ :=
  (edges.map fun edge =>
    (if residualTail net edge = v then (1 : ℤ) else 0) -
      (if residualHead net edge = v then (1 : ℤ) else 0)).sum

/-- A nonempty available closed residual walk using each original occurrence at most once. -/
def IsResidualCycle {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    (flow : IndexedFlow arcs) (edges : List (ResidualEdge arcs)) : Prop :=
  edges ≠ [] ∧
    (∀ edge ∈ edges, residualAvailable flow edge) ∧
    (edges.map ResidualEdge.index).Nodup ∧
    edges.IsChain (fun a b => residualHead net a = residualTail net b) ∧
    edges.head?.map (residualTail net) = edges.getLast?.map (residualHead net)

/-- The residual changes from one bit vector to another, in original arc-index order. -/
def residualDifference {arcs : ℕ} (flow target : IndexedFlow arcs) : List (ResidualEdge arcs) :=
  (List.finRange arcs).filterMap fun i =>
    if flow i = target i then none else some ⟨i, flow i⟩

end STACS2027.Runtimes.Flow

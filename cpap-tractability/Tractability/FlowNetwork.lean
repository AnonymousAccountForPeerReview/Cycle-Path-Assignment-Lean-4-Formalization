module

public import NPHardness.CPAP

/-!
# The min-cost flow network of Theorem 2 (Appendix A)

For a graph `g`, the network has a source `s`, a sink `z`, two opposing-pair
nodes `x_{C,{e₁,e₃}}` and `x_{C,{e₂,e₄}}` for each simple four-cycle `C` with
cyclically ordered edges `e₁, e₂, e₃, e₄`, and one edge node `y_e` for each
edge `e` lying on a four-cycle. Its arcs, all of capacity one, are `s → x_{C,p}`
(cost 0), `x_{C,p} → y_e` for the two edges `e` of the pair `p` (cost 0), and
`ϖ(e)` parallel arcs `y_e → z` with costs `0, …, ϖ(e) - 1`, where `ϖ(e)` is the
number of four-cycles containing `e`.

An integral flow is a sublist of the arc list (the arcs carrying one unit) that
conserves flow at every node other than `s` and `z`. The cycles are those
enumerated by `cycles g 4`, each counted once by its edge set, as in `HasAssignment`.
-/

@[expose] public section
namespace STACS2027

/-- A node of the network of Theorem 2 or of its modification for triangles (the corollary
`K3TimeComplexity`, k = 3): the source `s`, the sink `z`, the opposing-pair node `x_{C_i,p}`
of the `i`-th enumerated four-cycle `C_i` (`p = false` is the pair `{e₁, e₃}`, `p = true` the
pair `{e₂, e₄}`), the triangle node `x_{C_i}` of the `i`-th enumerated triangle, or the edge node
`y_e`. -/
inductive FlowNode where
  | source
  | sink
  | pair (cycle : Nat) (parity : Bool)
  | triangle (cycle : Nat)
  | edgeNode (e : Edge)

/-- Equality of nodes, as a Boolean. -/
def FlowNode.beq : FlowNode → FlowNode → Bool
  | .source, .source => true
  | .sink, .sink => true
  | .pair i p, .pair j q => i == j && p == q
  | .triangle i, .triangle j => i == j
  | .edgeNode e, .edgeNode f => e == f
  | _, _ => false

/-- An arc of the network, from `tail` to `head`, with the given cost. Every arc has
capacity one. -/
structure Arc where
  tail : FlowNode
  head : FlowNode
  cost : Nat

/-- The opposing pair `p` of the four-cycle `c`: its edges at even positions, `e₁` and
`e₃`, when `p = false`, and at odd positions, `e₂` and `e₄`, when `p = true`. -/
def opposingPair (c : Cycle) (p : Bool) : List Edge :=
  ((cycleEdges c).zipIdx.filter fun x => (x.2 % 2 == 1) == p).map Prod.fst

/-- The edges lying on a four-cycle of `g`, each once, in order of first appearance. -/
def cycleEdgeList (g : Graph) : List Edge :=
  ((cycles g 4).flatMap cycleEdges).eraseDups

/-- `ϖ(e)`: the number of four-cycles of `g` containing `e`. -/
def cycleCount (g : Graph) (e : Edge) : Nat :=
  (cycles g 4).countP fun c => (cycleEdges c).contains e

/-- The arcs `s → x_{C_i,p}`, of cost `0`. -/
def sourceArcs (g : Graph) : List Arc :=
  (List.range (cycles g 4).length).flatMap fun i =>
    [⟨.source, .pair i false, 0⟩, ⟨.source, .pair i true, 0⟩]

/-- `C_i`, the `i`-th enumerated four-cycle of `g` (the empty list if there is none). -/
def fourCycle (g : Graph) (i : Nat) : Cycle := (cycles g 4).getD i []

/-- The arcs `x_{C_i,p} → y_e` for the two edges `e` of the opposing pair `p` of `C_i`,
of cost `0`. -/
def pairArcs (g : Graph) : List Arc :=
  (List.range (cycles g 4).length).flatMap fun i =>
    [false, true].flatMap fun p =>
      (opposingPair (fourCycle g i) p).map fun e => ⟨.pair i p, .edgeNode e, 0⟩

/-- The `ϖ(e)` parallel arcs `y_e → z`, with costs `0, …, ϖ(e) - 1`. -/
def sinkArcs (g : Graph) : List Arc :=
  (cycleEdgeList g).flatMap fun e =>
    (List.range (cycleCount g e)).map fun j => ⟨.edgeNode e, .sink, j⟩

/-- The network `𝓕` of Theorem 2: all arcs, in the order source arcs, pair arcs, sink arcs. -/
def fourCycleNetwork (g : Graph) : List Arc :=
  sourceArcs g ++ pairArcs g ++ sinkArcs g

/-- The nodes of the network: `s`, `z`, the pair nodes, and the edge nodes. -/
def networkNodes (g : Graph) : List FlowNode :=
  .source :: .sink ::
    ((List.range (cycles g 4).length).flatMap fun i => [.pair i false, .pair i true]) ++
    (cycleEdgeList g).map .edgeNode

/-- The number of arcs of `flow` entering `v`. -/
def inflow (flow : List Arc) (v : FlowNode) : Nat :=
  flow.countP fun a => a.head.beq v

/-- The number of arcs of `flow` leaving `v`. -/
def outflow (flow : List Arc) (v : FlowNode) : Nat :=
  flow.countP fun a => a.tail.beq v

/-- `flow` is an integral flow of the unit-capacity network `network`: a sublist of its arcs
(those carrying one unit) that conserves flow at every node other than the source and the
sink. -/
def IsFlow (network flow : List Arc) : Prop :=
  flow.Sublist network ∧
    ∀ v : FlowNode, v ≠ .source → v ≠ .sink → inflow flow v = outflow flow v

/-- The value of a flow: the number of its arcs leaving the source. -/
def flowValue (flow : List Arc) : Nat := outflow flow .source

/-- The cost of a flow: the sum of the costs of its arcs. -/
def flowCost (flow : List Arc) : Nat := (flow.map Arc.cost).sum

end STACS2027

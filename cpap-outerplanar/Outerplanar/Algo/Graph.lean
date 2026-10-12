module

public import Outerplanar.DFS
public import Outerplanar.PerfectK23

/-!
# The algorithm of Theorem 21: the graph-level phases

The functions below are the abstract specification of the linear-time random-access
machine of Theorem 21 (Lemma 35): each is what one phase of the machine computes.

* `proper`, `labels`, `idOf`, `idEdges`, `numV`: the input edges written smaller end first,
  the vertex labels in order of first appearance, and the deduplicated edges between the
  ids `0, …, numV g - 1` of the labels;
* `nbOf`: neighbour lists, in the order of the edges;
* `dfsOf`: the depth-first search of `DFS` from the roots `0, …, numV g - 1`;
* `lowOf`: ANONYMIZED and ANONYMIZED's low points, in reverse preorder;
* `headOf`: the head of every vertex (the tree edge starting its block), in preorder;
* `blocksOf`: the blocks, bucketed by head;
* `solveWith`: the output — the concatenation of the outputs of the blocks, with ids
  replaced by labels.
-/

@[expose] public section

namespace STACS2027.Algo

/-- The input entries written smaller end first (the edges of the simple graph). -/
def proper (g : Graph) : List Edge := g.filter fun e => decide (e.1 < e.2)

/-- The vertex labels, in order of first appearance. -/
def labels (g : Graph) : List ℕ := ((proper g).flatMap fun e => [e.1, e.2]).eraseDups

/-- The number of vertices. -/
def numV (g : Graph) : ℕ := (labels g).length

/-- The id of a label: its position in `labels g`. -/
def idOf (g : Graph) (x : ℕ) : ℕ := (labels g).idxOf x

/-- The label of an id. -/
def labelOf (g : Graph) (v : ℕ) : ℕ := (labels g).getD v 0

/-- The edges between ids, without repetitions, in order of first appearance. -/
def idEdges (g : Graph) : List Edge :=
  ((proper g).map fun e => edge (idOf g e.1) (idOf g e.2)).eraseDups

/-- Neighbour lists of an edge list, in the order of the edges. -/
def nbOf (E : List Edge) (v : ℕ) : List ℕ :=
  E.flatMap fun e => if e.1 = v then [e.2] else if e.2 = v then [e.1] else []

/-- The depth-first search of the id graph. -/
def dfsOf (g : Graph) : DFS.State := DFS.final (List.range (numV g)) (nbOf (idEdges g))

/-- One low point: the least preorder number reached from `v` by one edge other than the
tree edge to its parent, through the low points of its children. -/
def lowStep (s : DFS.State) (nb : ℕ → List ℕ) (lowf : ℕ → ℕ) (v : ℕ) : ℕ :=
  (nb v).foldl (fun acc w =>
    if w = s.par v ∧ s.par v ≠ v then acc
    else min acc (if s.par w = v ∧ w ≠ v then lowf w else s.pre w)) (s.pre v)

/-- The low points, computed in reverse preorder. -/
def lowOf (s : DFS.State) (nb : ℕ → List ℕ) : ℕ → ℕ :=
  s.ord.foldr (fun v lowf => Function.update lowf v (lowStep s nb lowf v)) (fun _ => 0)

/-- The heads, computed in preorder: a non-root vertex `v` is a head when no edge from its
subtree other than its tree edge reaches above its parent (`pre (par v) ≤ low v`);
otherwise its head is that of its parent. -/
def headOf (s : DFS.State) (low : ℕ → ℕ) : ℕ → ℕ :=
  s.ord.foldl (fun hf v => Function.update hf v
    (if s.par v = v then v else if s.pre (s.par v) ≤ low v then v else hf (s.par v)))
    (fun _ => 0)

/-- The lower end of an edge: the end with the larger preorder number. -/
def lowerOf (s : DFS.State) (e : Edge) : ℕ := if s.pre e.1 < s.pre e.2 then e.2 else e.1

/-- The blocks of the id graph, bucketed by head `0, …, numV g - 1` (empty buckets for
non-heads), each in the order of the edges. -/
def blocksOf (g : Graph) : List (List Edge) :=
  let s := dfsOf g
  let hd := headOf s (lowOf s (nbOf (idEdges g)))
  (List.range (numV g)).map fun h => (idEdges g).filter fun e => hd (lowerOf s e) = h

/-- The output, given the solver of a block: the cycles found in the blocks, with ids
replaced by labels, concatenated. -/
def solveWith (solveBlock : List Edge → List (List ℕ)) (g : Graph) : List ℕ :=
  ((blocksOf g).flatMap solveBlock).flatMap fun c => c.map (labelOf g)

end STACS2027.Algo

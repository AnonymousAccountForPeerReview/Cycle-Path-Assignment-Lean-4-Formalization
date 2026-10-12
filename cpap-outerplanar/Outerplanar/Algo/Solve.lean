module

public import Outerplanar.Algo.Poly
public import Outerplanar.Algo.Ear
public import Outerplanar.Algo.K4Out

/-!
# The algorithm of Theorem 21: the block solver and the whole algorithm

On a block (its edge list `E`, ids, smaller end first, each edge once):

* `blockVerts E`: its vertices in order of first appearance; `localEdges vs E`: the edges
  renamed to positions in `vs` (local ids `0, …, |vs| - 1`);
* at most two vertices: no cycle, nothing to output;
* four vertices and six edges (a `K₄`): the fixed output `k4Out`;
* otherwise (an outerplanar block, by Lemma 19): the Hamiltonian cycle `ham` of the local
  graph by ear elimination (`Ear.earHam`); the polygon `localEdges ham L` (the local ids
  renamed to their positions on `ham`); the dynamic program's output `Poly.polyOut` on
  it, with positions renamed back to local ids and local ids to ids.

`solve k g`: the output of the whole algorithm (`solveWith`: blocks, ids → labels).
-/

@[expose] public section

namespace STACS2027.Algo

/-- The vertices of a block, in order of first appearance. -/
def blockVerts (E : List Edge) : List ℕ := (E.flatMap fun e => [e.1, e.2]).eraseDups

/-- The edges renamed to their positions in `vs`, smaller end first. -/
def localEdges (vs : List ℕ) (E : List Edge) : List Edge :=
  E.map fun e => edge (vs.idxOf e.1) (vs.idxOf e.2)

/-- **The block solver.** -/
def solveBlock (k : ℕ) (E : List Edge) : List (List ℕ) :=
  let vs := blockVerts E
  if vs.length ≤ 2 then []
  else if vs.length = 4 ∧ E.length = 6 then k4Out k vs
  else
    let L := localEdges vs E
    let ham := Ear.earHam vs.length L
    (Poly.polyOut (localEdges ham L) vs.length k).map
      (List.map fun p => vs.getD (ham.getD p 0) 0)

/-- **The algorithm of Theorem 21** (Lemma 35 for outerplanar graphs): the output on
the graph `g` for cycle length `k`. -/
def solve (k : ℕ) (g : Graph) : List ℕ := solveWith (solveBlock k) g

end STACS2027.Algo

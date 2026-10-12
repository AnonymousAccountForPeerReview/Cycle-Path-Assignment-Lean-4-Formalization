module

public import Outerplanar.Algo.Graph
public import Outerplanar.Enumerate

/-!
# The algorithm of Lemma 35 on a polygon: the abstract specification

The dynamic program of Appendix F, on a polygon `pg` with non-crossing chords on the
positions `0, …, n - 1`, for `k`-cycles, written as the phases of the random-access
machine compute them:

* `nbP p`: the neighbours of position `p`, in increasing order;
* `segEnum`, `segOrder`: the segments (edges `(a, b)`, `a + 2 ≤ b`), and the same ordered by
  size (children before parents);
* `slots s`: the consecutive pairs of face vertices of `s` (sides and child segments);
* `rpF`: the region paths of an edge with `L` vertices, by folding over the face slots
  (`extendParts`);
* `pool`: the convex `k`-cycles, grouped by top segment in `segOrder`;
* `bnd s`, `topIdx s`, `rel s`: the indices in `pool` of the boundary cycles of `s` (both
  ends of `s` on the cycle, top elsewhere), of the cycles with top `s`, and both;
* `owned s`: the edges owned by `s` (itself and the sides of its face);
* `cfg`, `enc`: configurations as base-`k` numbers;
* `table`, `argTab`: the table `DP[s, α]` and a minimizing `β`, by recursion on segments;
* `backtrack`: the chosen configurations, top-down; `valOf`: the omitted index of each
  cycle; `polyOut`: the cycles of the pool, each rotated to start at its omitted vertex.
-/

@[expose] public section

namespace STACS2027.Poly

variable (pg : Graph) (n k : ℕ)

/-- The neighbours of position `p`, in increasing order. -/
def nbP (p : ℕ) : List ℕ := (List.range n).filter fun q => decide (Adj pg p q)

/-- The segments, enumerated by their smaller end and then their larger end. -/
def segEnum : List (ℕ × ℕ) :=
  (List.range n).flatMap fun a => ((nbP pg n a).filter fun b => decide (a + 2 ≤ b)).map fun b => (a, b)

/-- The segments ordered by size `b - a` (children before parents), stably. -/
def segOrder : List (ℕ × ℕ) :=
  (List.range n).flatMap fun d => (segEnum pg n).filter fun s => decide (s.2 - s.1 = d)

/-- Consecutive pairs of a list. -/
def pairs : List ℕ → List (ℕ × ℕ)
  | x :: y :: rest => (x, y) :: pairs (y :: rest)
  | _ => []

/-- The slots of the face of `s`: consecutive face vertices. -/
def slots (s : ℕ × ℕ) : List (ℕ × ℕ) := pairs (faceVerts pg n s)

/-- The child segments of `s`. -/
def childSegs (s : ℕ × ℕ) : List (ℕ × ℕ) := (slots pg n s).filter fun t => decide (t.1 + 2 ≤ t.2)

/-- Extending partial region paths (with their numbers of edges) through the slot `(x, y)`,
using the region paths `rp x y L'` of the slot with `L'` vertices, up to `k - 1` edges in
all. -/
def extendParts (rp : ℕ → ℕ → ℕ → List (List ℕ)) (parts : List (List ℕ × ℕ)) (x y : ℕ) :
    List (List ℕ × ℕ) :=
  parts.flatMap fun pe => (List.range' 2 (k - pe.2)).flatMap fun L' =>
    (rp x y L').map fun q => (pe.1 ++ q.tail, pe.2 + (L' - 1))

/-- The region paths of the edge `(a, b)` with `L` vertices, with recursion fuel: `[a, b]`
for `L = 2`, and for a segment the paths through its face, folding over the slots. -/
def rpF : ℕ → ℕ → ℕ → ℕ → List (List ℕ)
  | _, a, b, 2 => if a < b ∧ Adj pg a b then [[a, b]] else []
  | 0, _, _, _ => []
  | fuel + 1, a, b, L =>
    if (a, b) ∈ segEnum pg n then
      (((slots pg n (a, b)).foldl (fun parts t => extendParts k (rpF fuel) parts t.1 t.2)
        [([a], 0)]).filter fun pe => decide (pe.2 + 1 = L)).map Prod.fst
    else []

/-- The cycle pool: the convex `k`-cycles, grouped by top segment in `segOrder`. -/
def pool : List (List ℕ) := (segOrder pg n).flatMap fun s => rpF pg n k n s.1 s.2 k

/-- The top segment of a cycle: its first and last entries. -/
def topOf (u : List ℕ) : ℕ × ℕ := (u.headD 0, u.getLastD 0)

/-- The pool entry `i`. -/
def cyc (i : ℕ) : List ℕ := (pool pg n k).getD i []

/-- The boundary cycles of `s`: both ends of `s` on the cycle, top elsewhere. -/
def bnd (s : ℕ × ℕ) : List ℕ :=
  (List.range (pool pg n k).length).filter fun i =>
    decide (s.1 ∈ cyc pg n k i ∧ s.2 ∈ cyc pg n k i ∧ topOf (cyc pg n k i) ≠ s)

/-- The cycles with top `s`. -/
def topIdx (s : ℕ × ℕ) : List ℕ :=
  (List.range (pool pg n k).length).filter fun i => decide (topOf (cyc pg n k i) = s)

/-- The cycles relevant at `s`. -/
def rel (s : ℕ × ℕ) : List ℕ := bnd pg n k s ++ topIdx pg n k s

/-- The edges owned by `s`: itself and the sides of its face. -/
def owned (s : ℕ × ℕ) : List Edge := s :: (slots pg n s).filter fun t => decide (t.2 = t.1 + 1)

/-- The base-`k` digits of `x`, `L` of them. -/
def cfg (L x : ℕ) : List ℕ := (List.range L).map fun t => x / k ^ t % k

/-- The number with base-`k` digits `ds`. -/
def enc : List ℕ → ℕ
  | [] => 0
  | d :: ds => d + k * enc ds

/-- The load of the edge `e` when the relevant cycles take the omitted indices `vals`. -/
def loadAt (s : ℕ × ℕ) (vals : List ℕ) (e : Edge) : ℕ :=
  ((rel pg n k s).zip vals).countP fun iv =>
    decide (e ∈ selectedAt (cyc pg n k iv.1) ((cyc pg n k iv.1).getD iv.2 0))

/-- The cost of the edges owned by `s`. -/
def localCost (s : ℕ × ℕ) (vals : List ℕ) : ℕ :=
  ((owned pg n s).map fun e => pairCount (loadAt pg n k s vals e)).sum

/-- The configuration of the boundary cycles of the child `w`, read off those of `s`. -/
def childIdx (s w : ℕ × ℕ) (vals : List ℕ) : ℕ :=
  enc k ((bnd pg n k w).map fun i => vals.getD ((rel pg n k s).idxOf i) 0)

/-- The tables, with recursion fuel: the entry of `α` is the least, over `β`, of the local
cost plus the children's entries; the first minimizing `β` with it. -/
def tabArg : ℕ → ℕ × ℕ → ℕ → ℕ × ℕ
  | 0, _, _ => (0, 0)
  | fuel + 1, s, α =>
    let nb := (bnd pg n k s).length
    let nc := (topIdx pg n k s).length
    let total := fun β =>
      localCost pg n k s (cfg k nb α ++ cfg k nc β) +
        ((childSegs pg n s).map fun w =>
          (tabArg fuel w (childIdx pg n k s w (cfg k nb α ++ cfg k nc β))).2).sum
    (List.range' 1 (k ^ nc - 1)).foldl
      (fun bv β => if total β < bv.2 then (β, total β) else bv) (0, total 0)

/-- `DP[s, α]`. -/
def table (s : ℕ × ℕ) (α : ℕ) : ℕ := (tabArg pg n k n s α).2

/-- A minimizing configuration `β` of the cycles with top `s`. -/
def argTab (s : ℕ × ℕ) (α : ℕ) : ℕ := (tabArg pg n k n s α).1

/-- The chosen configurations `(α, β)` of the segments, top-down: the root's `α` is `0`;
each segment passes the restriction of its `(α, β)` to its children. -/
def backtrack : (ℕ × ℕ → ℕ) × (ℕ × ℕ → ℕ) :=
  (segOrder pg n).foldr (fun s ab =>
    let α := ab.1 s
    let β := argTab pg n k s α
    let nb := (bnd pg n k s).length
    let nc := (topIdx pg n k s).length
    ((childSegs pg n s).foldl (fun f w =>
      Function.update f w (childIdx pg n k s w (cfg k nb α ++ cfg k nc β))) ab.1,
     Function.update ab.2 s β))
    (fun _ => 0, fun _ => 0)

/-- The omitted index of the pool cycle `i`: its digit in the chosen `β` of its top. -/
def valOf (i : ℕ) : ℕ :=
  let s := topOf (cyc pg n k i)
  (backtrack pg n k).2 s / k ^ ((topIdx pg n k s).idxOf i) % k

/-- A cycle written from its `j`-th vertex. -/
def rotateTo (u : List ℕ) (j : ℕ) : List ℕ := u.drop j ++ u.take j

/-- The output on the polygon: the pool cycles, each written from its omitted vertex. -/
def polyOut : List (List ℕ) :=
  (List.range (pool pg n k).length).map fun i => rotateTo (cyc pg n k i) (valOf pg n k i)

end STACS2027.Poly

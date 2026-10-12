module

public import Outerplanar.Algo.Graph

/-!
# The Hamiltonian cycle of an outerplanar block by ear elimination: the specification

The algorithm, on a graph with the vertices `0, …, N - 1` and the edge list `L` (each edge
once, smaller end first), as the random-access machine runs it:

* **Elimination.** A stack holds vertices of degree two. Repeatedly, while more than three
  vertices are alive: pop `v`; if `v` is alive with degree two, find its two alive
  neighbours `u`, `w` (scanning its adjacency list), kill `v`, log `(v, u, w)`, and replace
  the path `u v w` by the edge `u w`: if `u w` is already an edge, the degrees of `u` and
  `w` drop by one (a vertex reaching degree two is pushed); otherwise the edge `u w` is
  added (a *virtual* edge; the degrees do not change).
* **Reconstruction.** The three surviving vertices `x < y < z` form the cycle
  `x → y → z → x` (a successor function); the logged vertices are reinserted, last
  eliminated first, each between its two logged neighbours (which are consecutive);
  the Hamiltonian cycle is read off by following the successors from `x`.

The adjacency lists grow at the front (the machine's linked lists); the adjacency matrix
`mat` records the current edges, original and virtual.
-/

@[expose] public section

namespace STACS2027.Ear

/-- The state of the elimination. -/
structure State where
  /-- Adjacency lists (original edges and virtual edges; dead entries are kept). -/
  adj : ℕ → List ℕ
  /-- The adjacency matrix of the current graph. -/
  mat : ℕ → ℕ → Bool
  /-- Current degrees. -/
  deg : ℕ → ℕ
  /-- Eliminated vertices. -/
  dead : ℕ → Bool
  /-- The stack of candidates (top first). -/
  stack : List ℕ
  /-- The eliminations `(v, u, w)`, last first. -/
  log : List (ℕ × ℕ × ℕ)
  /-- The number of alive vertices. -/
  cnt : ℕ

/-- Two-argument update. -/
def update2 (f : ℕ → ℕ → Bool) (a b : ℕ) (x : Bool) : ℕ → ℕ → Bool :=
  fun i j => if i = a ∧ j = b then x else f i j

/-- The adjacency lists of the edge list, each edge prepended at both ends in order. -/
def initAdj (L : List Edge) : ℕ → List ℕ :=
  L.foldl (fun f e =>
    let f1 := Function.update f e.1 (e.2 :: f e.1)
    Function.update f1 e.2 (e.1 :: f1 e.2)) (fun _ => [])

/-- The initial state: the vertices of degree two pushed in increasing order. -/
def init (N : ℕ) (L : List Edge) : State :=
  let adj := initAdj L
  { adj := adj
    mat := L.foldl (fun m e => update2 (update2 m e.1 e.2 true) e.2 e.1 true) (fun _ _ => false)
    deg := fun v => (adj v).length
    dead := fun _ => false
    stack := ((List.range N).filter fun v => (adj v).length = 2).reverse
    log := []
    cnt := N }

/-- Push `v` if its degree is two. -/
def pushIf2 (s : State) (v : ℕ) : State :=
  if s.deg v = 2 then { s with stack := v :: s.stack } else s

/-- Lower the degree of `v` by one, pushing it if it reaches two. -/
def decDeg (s : State) (v : ℕ) : State :=
  pushIf2 { s with deg := Function.update s.deg v (s.deg v - 1) } v

/-- Eliminate `v` (alive, degree two) with alive neighbours `u`, `w`. -/
def elim (s : State) (v u w : ℕ) : State :=
  let s1 : State := { s with
    dead := Function.update s.dead v true
    cnt := s.cnt - 1
    log := (v, u, w) :: s.log }
  if s1.mat u w then decDeg (decDeg s1 u) w
  else
    let s2 : State := { s1 with mat := update2 (update2 s1.mat u w true) w u true }
    let s3 : State := { s2 with adj := Function.update s2.adj u (w :: s2.adj u) }
    { s3 with adj := Function.update s3.adj w (u :: s3.adj w) }

/-- One iteration: pop `v`; skip it unless it is alive with degree two; else eliminate it
with the first two alive entries of its adjacency list. -/
def step (s : State) : State :=
  match s.stack with
  | [] => s
  | v :: rest =>
    let s0 : State := { s with stack := rest }
    if s0.dead v = false ∧ s0.deg v = 2 then
      let nb := (s0.adj v).filter fun x => s0.dead x = false
      elim s0 v (nb.getD 0 0) (nb.getD 1 0)
    else s0

/-- The elimination loop: while the stack is nonempty and more than three vertices are
alive. -/
def loop : ℕ → State → State
  | 0, s => s
  | fuel + 1, s => if s.stack ≠ [] ∧ 3 < s.cnt then loop fuel (step s) else s

/-- Reinsert `v` between `u` and `w` (consecutive, in one of the two directions). -/
def reinsert (succ : ℕ → ℕ) (vuw : ℕ × ℕ × ℕ) : ℕ → ℕ :=
  let v := vuw.1
  let u := vuw.2.1
  let w := vuw.2.2
  if succ u = w then Function.update (Function.update succ u v) v w
  else Function.update (Function.update succ w v) v u

/-- Following the successors `m` times from `x`. -/
def walk (succ : ℕ → ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | m + 1, x => x :: walk succ m (succ x)

/-- **The Hamiltonian cycle** found by ear elimination on `0, …, N - 1` with edges `L`. -/
def earHam (N : ℕ) (L : List Edge) : List ℕ :=
  let s := loop (4 * N + 1) (init N L)
  let tri := (List.range N).filter fun v => s.dead v = false
  let x := tri.getD 0 0
  let y := tri.getD 1 0
  let z := tri.getD 2 0
  let succ0 : ℕ → ℕ :=
    Function.update (Function.update (Function.update (fun _ => 0) x y) y z) z x
  walk (s.log.foldl reinsert succ0) N x

end STACS2027.Ear

module

public import ApproximationHardness.Embed.Forest
import Lean.Elab.Tactic.Omega

/-!
# Depth-first search

An iterative depth-first search (`DG.step`), in the form a random-access machine runs it: a scan
pointer `r` over the darts starts a new tree at every unvisited vertex; inside a tree, the current
vertex `cur` explores its next dart (`ptr cur`), descending to the far vertex if it is unvisited, and
when all its darts are explored it is finished and the search returns to its parent. Vertices have a
state `st` (`0` unvisited, `1` open, `2` finished); `post` lists the finished vertices, each root
followed by its top node `2E + r`.

The abstract state carries two ghost lists (the visited vertices and the explored darts) that bound
the number of steps.
-/

@[expose] public section

namespace STACS2027.Embed

/-- Update a function at one point. -/
def upd {α : Type} (f : Nat → α) (a : Nat) (v : α) : Nat → α := fun i => if i = a then v else f i

@[simp] theorem upd_same {α : Type} (f : Nat → α) (a : Nat) (v : α) : upd f a v a = v := by simp [upd]

theorem upd_ne {α : Type} (f : Nat → α) {a i : Nat} (v : α) (h : i ≠ a) : upd f a v i = f i := by
  simp [upd, h]

theorem upd_apply {α : Type} (f : Nat → α) (a v i) : upd (α := α) f a v i = if i = a then v else f i := rfl

/-- The graph to search: its darts `0, …, 2E - 1` and the vertex of every dart. -/
structure DG where
  E : Nat
  rep : Nat → Nat

/-- The state of the search. -/
structure DS where
  r : Nat
  cur : Nat
  inner : Bool
  par : Nat → Nat
  depth : Nat → Nat
  ptr : Nat → Nat
  st : Nat → Nat
  post : List Nat
  H : Nat
  vl : List Nat
  ex : List Nat

namespace DG

variable (G : DG)

/-- The darts at a vertex, in increasing order. -/
def darts (u : Nat) : List Nat := (List.range (2 * G.E)).filter fun d => G.rep d == u

/-- The forest of a state. -/
def fd (s : DS) : ForestData := ⟨G.E, G.rep, s.par, s.depth, s.H⟩

theorem darts_eq (s : DS) (u : Nat) : G.darts u = (G.fd s).dartsAt u := rfl

/-- The next dart of the current vertex. -/
def nd (s : DS) : Nat := (G.darts s.cur).getD (s.ptr s.cur) 0

/-- The vertex at the far end of the next dart. -/
def nw (s : DS) : Nat := G.rep (pair (G.nd s))

/-- One step of the search. -/
def step (s : DS) : DS :=
  if s.inner then
    if s.ptr s.cur < (G.darts s.cur).length then
      if s.st (G.nw s) = 0 then
        { s with
          ptr := upd s.ptr s.cur (s.ptr s.cur + 1)
          ex := s.ex ++ [G.nd s]
          st := upd s.st (G.nw s) 1
          par := upd s.par (G.nw s) (pair (G.nd s))
          depth := upd s.depth (G.nw s) (s.depth s.cur + 1)
          H := max s.H (s.depth s.cur + 2)
          cur := G.nw s
          vl := s.vl ++ [G.nw s] }
      else
        { s with
          ptr := upd s.ptr s.cur (s.ptr s.cur + 1)
          ex := s.ex ++ [G.nd s] }
    else if 2 * G.E ≤ s.par s.cur then
      { s with
        st := upd s.st s.cur 2
        post := s.post ++ [s.cur, 2 * G.E + s.cur]
        inner := false
        r := s.r + 1 }
    else
      { s with
        st := upd s.st s.cur 2
        post := s.post ++ [s.cur]
        cur := G.rep (pair (s.par s.cur)) }
  else if s.r < 2 * G.E then
    if G.rep s.r = s.r ∧ s.st s.r = 0 then
      { s with
        st := upd s.st s.r 1
        par := upd s.par s.r (2 * G.E)
        depth := upd s.depth s.r 0
        cur := s.r
        inner := true
        vl := s.vl ++ [s.r]
        H := max s.H 1 }
    else { s with r := s.r + 1 }
  else s

/-- The initial state: everything zero. -/
def init : DS := ⟨0, 0, false, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, [], 0, [], []⟩

/-- The search has halted. -/
def Halted (s : DS) : Prop := s.inner = false ∧ 2 * G.E ≤ s.r

/-- The hypotheses on the graph. -/
structure Ok : Prop where
  rep_lt : ∀ d, d < 2 * G.E → G.rep d < 2 * G.E
  rep_rep : ∀ d, d < 2 * G.E → G.rep (G.rep d) = G.rep d
  rep_le : ∀ d, d < 2 * G.E → G.rep d ≤ d
  noloop : ∀ d, d < 2 * G.E → G.rep (pair d) ≠ G.rep d
  deg : ∀ r, (G.darts r).length ≤ 3

end DG

end STACS2027.Embed

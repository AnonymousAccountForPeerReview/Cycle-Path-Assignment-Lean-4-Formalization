module

public import ApproximationHardness.Embed.SolverIds
public import ApproximationHardness.Embed.DFS
import Lean.Elab.Tactic.Omega

/-!
# The solver as a machine on arrays

The machine processes the nodes of a post-order one by one, keeping the results of the nodes in
arrays: a class of a group is a linked list of open ends (`nx`, pointers plus one, `0` for none)
with a head and a tail pointer per class (`ph`, `pt`, `mh`, `mt`), the groups of a stack are linked
by `gn`, and the result of a node is its stack head `rs` and its `low` `rl`. A merge at a fork runs
over several steps: popping the groups of `rx` reaching above `ry.low` (`mode 1`) and consuming the
groups of `ry` (`mode 2`); classes are concatenated in constant time through their tail pointers.
The merges are recorded in `gp` (merged group plus one) and `gf` (flip bit), and the information for
the bit of a node in `inf` and `ia`.

`cons` is a ghost list of the consumed groups.
-/

@[expose] public section

namespace STACS2027.Embed

/-- The arrays of the machine. -/
structure SMem where
  nx : Nat → Nat
  ph : Nat → Nat
  pt : Nat → Nat
  mh : Nat → Nat
  mt : Nat → Nat
  gn : Nat → Nat
  rs : Nat → Nat
  rl : Nat → Nat
  gp : Nat → Nat
  gf : Nat → Nat
  inf : Nat → Nat
  ia : Nat → Nat

/-- The state of the machine. -/
structure SMS where
  m : SMem
  k : Nat
  mode : Nat
  v : Nat
  G : Nat
  lh : Nat
  lx : Nat
  rxp : Nat
  ryp : Nat
  ah : Nat
  at' : Nat
  bh : Nat
  bt : Nat
  ch : Nat
  ct : Nat
  cons : List Nat

/-- Storing the result of a node. -/
def SMem.store (m : SMem) (v h l : Nat) : SMem := { m with rs := upd m.rs v h, rl := upd m.rl v l }

/-- Concatenating the lists `(h1, t1)` and `(h2, t2)`: the head, the tail and the new pointers. -/
def appL (nx : Nat → Nat) (h1 t1 h2 t2 : Nat) : Nat × Nat × (Nat → Nat) :=
  if h1 = 0 then (h2, t2, nx) else if h2 = 0 then (h1, t1, nx) else (h1, t2, upd nx (t1 - 1) h2)

namespace Sol

variable (S : Sol)

/-- The key plus one of the head of a class (`0` if empty). -/
def khM (h : Nat) : Nat := if h = 0 then 0 else S.key (h - 1) + 1

/-- The largest key plus one of a group. -/
def gtopM (m : SMem) (g : Nat) : Nat := max (S.khM (m.ph g)) (S.khM (m.mh g))

/-- The result of a part: a child's stored result, or a new group for a dart. -/
def itRes (m : SMem) : Item → SMem × Nat × Nat
  | .node c => (m, m.rs c, m.rl c)
  | .dart e => ({ m with
      ph := upd m.ph e (e + 1)
      pt := upd m.pt e (e + 1)
      mh := upd m.mh e 0
      gn := upd m.gn e 0 }, e + 1, S.key e + 1)


/-- The target data of a two-part node: its child and its dart, if it is a target. -/
def tgtOf : Item → Item → Option (Nat × Nat)
  | .node c, .dart d => if S.isIn d then some (c, d) else none
  | .dart d, .node c => if S.isIn d then some (c, d) else none
  | _, _ => none

/-- The bit code of a target: `1` for the bit `!o (α d)`, `2` for `o (α d)`. -/
def tcode : Item → Nat
  | .node _ => 1
  | .dart _ => 2

/-- Closing the deepest open end `e` of the result `(h, l)` of the child. -/
def closeM (m : SMem) (e h l : Nat) : SMem × Nat × Nat :=
  if h = 0 then (m, 0, S.INF) else
  let m1 : SMem := if m.ph (h - 1) = e + 1 then
      { m with ph := upd m.ph (h - 1) (if m.ph (h - 1) = m.pt (h - 1) then 0 else m.nx e) }
    else { m with mh := upd m.mh (h - 1) (if m.mh (h - 1) = m.mt (h - 1) then 0 else m.nx e) }
  (m1, if m1.ph (h - 1) = 0 ∧ m1.mh (h - 1) = 0 then m1.gn (h - 1) else h,
    if l = S.key e + 1 then S.INF else l)

variable (post : List Nat)

/-- Start a fork after its two represented operands have been ordered by their least keys. -/
def forkStart (s : SMS) (m : SMem) (v hx lx hy ly code : Nat) : SMS :=
  if hy = 0 then
    {s with m := {SMem.store m v hx lx with inf := upd m.inf v 0}, k := s.k + 1}
  else
    {s with
      m := {m with inf := upd m.inf v code}
      k := s.k + 1
      mode := 1
      v := v
      G := S.gid v
      lh := ly
      lx := lx
      rxp := hx
      ryp := hy
      ah := 0
      at' := 0
      bh := 0
      bt := 0
      ch := 0
      ct := 0}

/-- A node with two parts. -/
def twoStep (s : SMS) (v : Nat) (p q : Item) : SMS :=
  match S.tgtOf p q with
  | some (c, d) =>
    let r := S.closeM s.m (S.α d) (s.m.rs c) (s.m.rl c)
    { s with
      m := { SMem.store r.1 v r.2.1 r.2.2 with
             inf := upd r.1.inf v (tcode p)
             ia := upd r.1.ia v (S.α d) }
      k := s.k + 1 }
  | none =>
    let r1 := S.itRes s.m p
    let r2 := S.itRes r1.1 q
    let px := decide (r1.2.2 < r2.2.2)
    let hx := if px then r1.2.1 else r2.2.1
    let lx := if px then r1.2.2 else r2.2.2
    let hy := if px then r2.2.1 else r1.2.1
    let ly := if px then r2.2.2 else r1.2.2
    S.forkStart s r2.1 v hx lx hy ly (if px then 3 else 4)

/-- Starting a node. -/
def nodeStep (s : SMS) (v : Nat) : SMS :=
  match S.P.parts v with
  | [] =>
    { s with
      m := { SMem.store s.m v 0 S.INF with inf := upd s.m.inf v 0 }
      k := s.k + 1 }
  | [it] =>
    let r := S.itRes s.m it
    { s with
      m := { SMem.store r.1 v r.2.1 r.2.2 with inf := upd r.1.inf v 0 }
      k := s.k + 1 }
  | [p, q] => S.twoStep s v p q
  | _ => { s with k := s.k + 1 }

/-- Popping a group of `rx` reaching above `ry.low`. -/
def popStep (s : SMS) : SMS :=
  if s.rxp ≠ 0 ∧ s.lh < S.gtopM s.m (s.rxp - 1) then
    let g := s.rxp - 1
    let up := decide (s.lh < S.khM (s.m.ph g))
    let uh := if up then s.m.ph g else s.m.mh g
    let ut := if up then s.m.pt g else s.m.mt g
    let wh := if up then s.m.mh g else s.m.ph g
    let wt := if up then s.m.mt g else s.m.pt g
    let a := appL s.m.nx s.ah s.at' uh ut
    let b := appL a.2.2 s.bh s.bt wh wt
    { s with
      m := { s.m with
             nx := b.2.2
             gp := upd s.m.gp g (s.G + 1)
             gf := upd s.m.gf g (if up then 0 else 1) }
      rxp := s.m.gn g
      ah := a.1
      at' := a.2.1
      bh := b.1
      bt := b.2.1
      cons := s.cons ++ [g] }
  else { s with mode := 2 }

/-- Consuming a group of `ry`, or finishing the merge. -/
def consStep (s : SMS) : SMS :=
  if s.ryp ≠ 0 then
    let g := s.ryp - 1
    let a := appL s.m.nx s.ch s.ct (s.m.ph g) (s.m.pt g)
    let b := appL a.2.2 a.1 a.2.1 (s.m.mh g) (s.m.mt g)
    { s with
      m := { s.m with
             nx := b.2.2
             gp := upd s.m.gp g (s.G + 1)
             gf := upd s.m.gf g (if s.m.ph g ≠ 0 then 1 else 0) }
      ryp := s.m.gn g
      ch := b.1
      ct := b.2.1
      cons := s.cons ++ [g] }
  else
    let y := appL s.m.nx s.ch s.ct s.bh s.bt
    { s with
      m := { SMem.store { s.m with nx := y.2.2 } s.v (s.G + 1) s.lx with
             ph := upd s.m.ph s.G s.ah
             pt := upd s.m.pt s.G s.at'
             mh := upd s.m.mh s.G y.1
             mt := upd s.m.mt s.G y.2.1
             gn := upd s.m.gn s.G s.rxp }
      mode := 0 }

/-- **One step of the machine.** -/
def mstep (s : SMS) : SMS :=
  if s.mode = 0 then
    match post[s.k]? with
    | some v => S.nodeStep s v
    | none => s
  else if s.mode = 1 then S.popStep s
  else consStep s

end Sol

end STACS2027.Embed

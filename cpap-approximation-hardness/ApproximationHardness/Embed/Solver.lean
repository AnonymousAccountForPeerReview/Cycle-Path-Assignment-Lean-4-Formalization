module

public import ApproximationHardness.Embed.PlanWord
import Lean.Elab.Tactic.Omega

/-!
# The constraint solver

The solver works bottom-up on a plan. The result of a node (`Res`) is a stack of groups (`seg`,
top first) and the least key of its open ends plus one (`low`, `INF` if none). A group has an
identifier and two classes `P` and `M` of open ends, each by decreasing key; the ends of `P` go to
one side, the ends of `M` to the other. The groups of a stack occupy disjoint ranges of keys, the
top group the deepest one.

* A dart opening a chord is a group of its own (`dartRes`), with the dart as identifier.
* At a target, the partner of the closing dart is the deepest open end of the child: the head of a
  class of the top group, which it leaves (`closeRes`).
* At a fork `v`, the part whose ends reach higher (`rx`, the smaller `low`) is merged with the
  other (`ry`): all groups of `ry`, and the groups of `rx` reaching above `ry.low`, become one group
  with identifier `gid v` whose first class holds the classes of `rx` reaching above `ry.low` and
  whose second class holds everything else (`mergeRes`).

The groups consumed at a fork, each with a flip bit, are `consAt v`: an orientation `o` of the
groups is consistent if `o g = o (gid v) xor flip` for every group `g` consumed at `v`. The sides of
the darts are then `o` itself (a dart is the identifier of its own group), and the bit of a node is
`bit o v`.
-/

@[expose] public section

namespace STACS2027.Embed

/-- A group: its identifier and its two classes. -/
structure Grp where
  id : Nat
  P : List Nat
  M : List Nat

/-- The result of a node: its stack of groups and its least key plus one. -/
structure Res where
  seg : List Grp
  low : Nat

/-- The ends of a group. -/
def Grp.els (g : Grp) : List Nat := g.P ++ g.M

/-- The ends of a stack of groups. -/
def els (seg : List Grp) : List Nat := seg.flatMap Grp.els

/-- The data of the solver: a plan, the partner map, the keys, the test for a dart closing a chord
of its sibling part, a bound on the keys, and the identifiers of the groups created at forks. -/
structure Sol where
  P : Plan
  α : Nat → Nat
  key : Nat → Nat
  isIn : Nat → Bool
  INF : Nat
  gid : Nat → Nat

namespace Sol

variable (S : Sol)

/-- The key plus one of the head of a class (`0` if empty). -/
def kh (l : List Nat) : Nat := match l with | [] => 0 | e :: _ => S.key e + 1

/-- The largest key plus one of a group. -/
def gtop (g : Grp) : Nat := max (S.kh g.P) (S.kh g.M)

/-- The empty result. -/
def empty : Res := ⟨[], S.INF⟩

/-- The result of a dart opening a chord. -/
def dartRes (e : Nat) : Res := ⟨[⟨e, [e], []⟩], S.key e + 1⟩

/-- Closing the chord of the open end `e`, the head of a class of the top group. -/
def closeRes (e : Nat) (r : Res) : Res :=
  match r.seg with
  | [] => S.empty
  | g :: rest =>
    let g' : Grp := if g.P.head? = some e then ⟨g.id, g.P.tail, g.M⟩ else ⟨g.id, g.P, g.M.tail⟩
    ⟨if g'.P = [] ∧ g'.M = [] then rest else g' :: rest, if r.low = S.key e + 1 then S.INF else r.low⟩

/-- The class of a group reaching above `lh`, and the other one. -/
def upC (lh : Nat) (g : Grp) : List Nat := if lh < S.kh g.P then g.P else g.M
def loC (lh : Nat) (g : Grp) : List Nat := if lh < S.kh g.P then g.M else g.P

/-- The groups of `rx` reaching above `lh`, and the others. -/
def popped (lh : Nat) (rx : Res) : List Grp := rx.seg.takeWhile fun g => decide (lh < S.gtop g)
def rest (lh : Nat) (rx : Res) : List Grp := rx.seg.dropWhile fun g => decide (lh < S.gtop g)

/-- Merging at a fork `v`: `rx` reaches higher than `ry`. -/
def mergeRes (v : Nat) (rx ry : Res) : Res :=
  if ry.seg = [] then rx else
  ⟨⟨S.gid v, (S.popped ry.low rx).flatMap (S.upC ry.low),
      els ry.seg ++ (S.popped ry.low rx).flatMap (S.loC ry.low)⟩ ::
    S.rest ry.low rx, rx.low⟩

/-- The result of a fork. -/
def forkRes (v : Nat) (rp rq : Res) : Res :=
  if rp.low < rq.low then S.mergeRes v rp rq else S.mergeRes v rq rp

/-- The result of a two-part node from the results of its parts. -/
def twoRes (v : Nat) (p q : Item) (rp rq : Res) : Res :=
  match p, q with
  | .node _, .dart d => if S.isIn d then S.closeRes (S.α d) rp else S.forkRes v rp rq
  | .dart d, .node _ => if S.isIn d then S.closeRes (S.α d) rq else S.forkRes v rp rq
  | _, _ => S.forkRes v rp rq

/-- **The solver**: the result of every node. -/
def solve (v : Nat) : Res :=
  let rpart : Item → Res := fun it => match it with
    | .node c => if _h : S.P.ht c < S.P.ht v then solve c else S.empty
    | .dart e => S.dartRes e
  match S.P.parts v with
  | [] => S.empty
  | [it] => rpart it
  | [p, q] => S.twoRes v p q (rpart p) (rpart q)
  | _ => S.empty
termination_by S.P.ht v

/-- The result of a part. -/
def rpart (it : Item) : Res := match it with
  | .node c => S.solve c
  | .dart e => S.dartRes e

theorem rpart_guard {v : Nat} {it : Item} (h : it ∈ S.P.parts v) :
    (match it with
      | .node c => if _h : S.P.ht c < S.P.ht v then S.solve c else S.empty
      | .dart e => S.dartRes e) = S.rpart it := by
  cases it with
  | node c => simp only [rpart]; rw [dite_eq_left (S.P.ht_lt v c h)]
  | dart e => rfl

theorem solve_eq (v : Nat) : S.solve v =
    match S.P.parts v with
    | [] => S.empty
    | [it] => S.rpart it
    | [p, q] => S.twoRes v p q (S.rpart p) (S.rpart q)
    | _ => S.empty := by
  rw [solve]
  have g : ∀ it, it ∈ S.P.parts v → (match it with
      | .node c => if _h : S.P.ht c < S.P.ht v then S.solve c else S.empty
      | .dart e => S.dartRes e) = S.rpart it := by
    intro it h
    cases it with
    | node c => simp only [rpart]; rw [dite_eq_left (S.P.ht_lt v c h)]
    | dart e => rfl
  split
  · rfl
  · rename_i it h; exact g it (by rw [h]; simp)
  · rename_i p q h
    simp only
    rw [g p (by rw [h]; simp), g q (by rw [h]; simp)]
  · rfl

theorem solve_nil {v : Nat} (h : S.P.parts v = []) : S.solve v = S.empty := by rw [solve_eq, h]
theorem solve_one {v : Nat} {it : Item} (h : S.P.parts v = [it]) : S.solve v = S.rpart it := by rw [solve_eq, h]
theorem solve_two {v : Nat} {p q : Item} (h : S.P.parts v = [p, q]) :
    S.solve v = S.twoRes v p q (S.rpart p) (S.rpart q) := by rw [solve_eq, h]

/-! ### Consistent orientations and bits -/

/-- The groups consumed by merging `ry` into `rx`, with their flip bits. -/
def mergeCons (rx ry : Res) : List (Nat × Bool) :=
  if ry.seg = [] then [] else
    ry.seg.map (fun g => (g.id, decide (g.P ≠ []))) ++
      (S.popped ry.low rx).map (fun g => (g.id, !decide (ry.low < S.kh g.P)))

def forkCons (rp rq : Res) : List (Nat × Bool) :=
  if rp.low < rq.low then S.mergeCons rp rq else S.mergeCons rq rp

def twoCons (p q : Item) (rp rq : Res) : List (Nat × Bool) :=
  match p, q with
  | .node _, .dart d => if S.isIn d then [] else S.forkCons rp rq
  | .dart d, .node _ => if S.isIn d then [] else S.forkCons rp rq
  | _, _ => S.forkCons rp rq

/-- The groups consumed at `v`, with their flip bits. -/
def consAt (v : Nat) : List (Nat × Bool) :=
  match S.P.parts v with
  | [p, q] => S.twoCons p q (S.rpart p) (S.rpart q)
  | _ => []

/-- An orientation of the groups is consistent with every merge. -/
def Consistent (o : Nat → Bool) : Prop := ∀ v, ∀ x ∈ S.consAt v, o x.1 = (o (S.gid v) ^^ x.2)

/-- The bit of a fork: the lower part first iff the merged ends of the higher part go right. -/
def forkBit (v : Nat) (o : Nat → Bool) (rp rq : Res) : Bool :=
  if rp.low < rq.low then (if rq.seg = [] then false else o (S.gid v))
  else (if rp.seg = [] then false else !o (S.gid v))

def twoBit (v : Nat) (o : Nat → Bool) (p q : Item) (rp rq : Res) : Bool :=
  match p, q with
  | .node _, .dart d => if S.isIn d then !o (S.α d) else S.forkBit v o rp rq
  | .dart d, .node _ => if S.isIn d then o (S.α d) else S.forkBit v o rp rq
  | _, _ => S.forkBit v o rp rq

/-- The bit of a node for the orientation `o`. -/
def bit (o : Nat → Bool) (v : Nat) : Bool :=
  match S.P.parts v with
  | [p, q] => S.twoBit v o p q (S.rpart p) (S.rpart q)
  | _ => false

end Sol

end STACS2027.Embed

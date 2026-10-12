module

public import Init

/-!
Finite simple cycles, the paths selected in them, and the overlap cost.
Edges are unordered pairs, represented in increasing endpoint order.
The overlap sum counts every unordered pair of selected paths once, and counts
every shared edge separately, as required by the manuscript's CPAP objective.
-/

@[expose] public section
namespace STACS2027

/-- An undirected edge, stored with its smaller endpoint first. -/
abbrev Edge := Nat × Nat
/-- A graph on natural-number vertices, given by its list of edges. -/
abbrev Graph := List Edge
/-- A cycle, given by its vertices in traversal order. -/
abbrev Cycle := List Nat

/-- The edge between `a` and `b`, with its smaller endpoint first. -/
def edge (a b : Nat) : Edge := (min a b, max a b)

/-- The edges between consecutive vertices of a walk. -/
def pathEdges : List Nat → List Edge
  | [] => []
  | [_] => []
  | a :: b :: rest => edge a b :: pathEdges (b :: rest)

/-- The edges of a cycle, including the edge from its last vertex back to its first. -/
def cycleEdges (c : Cycle) : List Edge :=
  pathEdges (c ++ c.take 1)

/-- `c` is a simple `k`-cycle of `g`: `k ≥ 3` distinct vertices, cyclically consecutive
vertices joined by edges of `g`. -/
def IsCycle (g : Graph) (k : Nat) (c : Cycle) : Prop :=
  3 ≤ k ∧ c.length = k ∧ c.Nodup ∧ ∀ e ∈ cycleEdges c, e ∈ g

/-- Being a simple `k`-cycle is decidable. -/
instance (g : Graph) (k : Nat) (c : Cycle) : Decidable (IsCycle g k c) :=
  inferInstanceAs (Decidable (3 ≤ k ∧ c.length = k ∧ c.Nodup ∧
    ∀ e ∈ cycleEdges c, e ∈ g))

/-- `c` and `d` have the same edges. Rotations and reversals of a cycle have the same edges. -/
def SameCycle (c d : Cycle) : Prop :=
  (∀ e ∈ cycleEdges c, e ∈ cycleEdges d) ∧
  (∀ e ∈ cycleEdges d, e ∈ cycleEdges c)

/-- Having the same edges is decidable. -/
instance (c d : Cycle) : Decidable (SameCycle c d) :=
  inferInstanceAs (Decidable ((∀ e ∈ cycleEdges c, e ∈ cycleEdges d) ∧
    (∀ e ∈ cycleEdges d, e ∈ cycleEdges c)))

/-- The path left by deleting vertex `c[i]` and its two incident edges from the cycle `c`:
`k - 2` edges for a simple `k`-cycle. -/
def selected (c : Cycle) (i : Nat) : List Edge :=
  pathEdges (((c.drop (i + 1)) ++ c.take (i + 1)).take (c.length - 1))

theorem pathEdges_length (c : List Nat) : (pathEdges c).length = c.length - 1 := by
  induction c with
  | nil => rfl
  | cons a c ih =>
    cases c with
    | nil => rfl
    | cons b tail => simp only [pathEdges, List.length_cons] at ih ⊢; omega

theorem selected_length (c : Cycle) (i : Nat) :
    (selected c i).length = c.length - 2 := by
  simp only [selected, pathEdges_length, List.length_take, List.length_append,
    List.length_drop]
  omega

/-- The number of edges shared by two paths: each edge of `p`, counted as often as it occurs in `q`. -/
def overlap (p q : List Edge) : Nat :=
  (p.map fun e => q.count e).sum

theorem overlap_nil_left (q : List Edge) : overlap [] q = 0 := rfl

theorem overlap_cons_left (e : Edge) (p q : List Edge) :
    overlap (e :: p) q = q.count e + overlap p q := by simp [overlap]

theorem overlap_nil_right (p : List Edge) : overlap p [] = 0 := by
  induction p with
  | nil => rfl
  | cons e p ih => simp [overlap_cons_left, ih]

theorem overlap_cons_right (p q : List Edge) (e : Edge) :
    overlap p (e :: q) = p.count e + overlap p q := by
  induction p with
  | nil => rfl
  | cons x p ih =>
    simp only [overlap_cons_left, List.count_cons, ih]
    have h : (x == e) = (e == x) := BEq.comm
    rw [h]
    omega

theorem overlap_comm (p q : List Edge) : overlap p q = overlap q p := by
  induction p with
  | nil => simp [overlap_nil_left, overlap_nil_right]
  | cons e p ih => rw [overlap_cons_left, overlap_cons_right, ih]

/-- The cost of a family of paths: the edges shared by each unordered pair of paths. On the paths
of an assignment it is `∑_e binom(l(e), 2)`, Definition 1's objective (`hasAssignment_iff_load_cost`). -/
def cost : List (List Edge) → Nat
  | [] => 0
  | p :: ps => (ps.map (overlap p)).sum + cost ps

theorem cost_snoc (ps : List (List Edge)) (p : List Edge) :
    cost (ps ++ [p]) = (ps.map (overlap p)).sum + cost ps := by
  induction ps with
  | nil => simp [cost]
  | cons q qs ih =>
    simp only [List.cons_append, cost, List.map_append, List.map_cons,
      List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero, ih]
    rw [overlap_comm q p]
    omega

theorem cost_reverse (ps : List (List Edge)) : cost ps.reverse = cost ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    rw [List.reverse_cons, cost_snoc, ih]
    simp [cost, List.map_reverse]

end STACS2027

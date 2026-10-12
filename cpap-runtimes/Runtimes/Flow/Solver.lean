module

public import Tractability
public import Outerplanar.RAM.Model
public import Outerplanar.RAM.Bounded
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Minimum-cost flow on the RAM: the cited algorithm as an explicit hypothesis

Theorem 2 of the manuscript (`T1`) and the corollary for triangles reduce `CPAP(G, 4)` and
`CPAP(G, 3)` to a minimum-cost flow problem (Section 3 / Appendix A, formalized in the
`Tractability` library: `cpap4_iff_flow`, `cpap3_iff_flow`), and then invoke

> **[vdB+23]** J. ANONYMIZED, L. ANONYMIZED, R. ANONYMIZED, Y. P. ANONYMIZED, R. ANONYMIZED, M. ANONYMIZED,
> S. ANONYMIZED, A. ANONYMIZED, *A deterministic almost-linear time algorithm for minimum-cost flow*,
> FOCS 2023: on a directed (multi-)graph with `m` arcs, integral capacities in `[0, U]`,
> integral costs in `[-Q, Q]` and integral demands, an optimal (integral) flow is computed, or
> infeasibility is reported, deterministically in `m^{1+o(1)} · log U · log Q` time.

That algorithm is **not** formalized: it stays cited, and enters the timed theorems as the
single hypothesis `MinCostFlowSolver F T` defined here — a RAM program `F` with a running-time
bound `T` that solves exactly the min-cost flow instances the reductions produce, and whose
runs access only the memory addresses below the same bound `T` (space at most time).

## The networks (Section 3's notions)

A network is a list of Section 3 arcs `net : List Arc` (`Arc`: tail, head, cost; **every arc
has capacity one**, parallel arcs model larger capacities), with the source `.source` and the
sink `.sink`. An integral flow is Section 3's `IsFlow net flow` (a sublist of the arcs,
conserving flow at every node other than the source and the sink), its value is `flowValue`
(the arcs leaving the source) and its cost `flowCost`. `IsMinFlow net d flow`: `flow` is an
integral flow of value `d` of least cost among all integral flows of value `d`.

To be given to a machine, the nodes are numbered by `num : FlowNode → ℕ`: `netInput num n d net`
is the list `n, m, s, z, d` followed by `tail, head, cost` for every arc (`m = |net|`,
`s = num source`, `z = num sink`). The class of networks (`GoodNet num n net`): the numbering
is injective on the nodes of the network with values `< n`, `n ≤ m + 2`, no arc enters the source
or leaves the sink (so `flowValue` is the usual value), and every cost is `< m`.

The answer of the solver (`FlowAnswer net d out`): `out = [0]` if `net` has no integral flow of
value `d`; otherwise `out = 1 :: bits`, a `0/1` vector over the arcs (`bits.length = m`) whose
selected arcs `select net bits` form an integral flow of value `d` of minimum cost.

## Why [vdB+23] gives the hypothesis with `T(N) ≤ C_ε N^{1+ε}` for every `ε > 0`

Let `N = |netInput num n d net| = 3m + 5`. Reading the input takes `O(N)` steps. The instance is
a min-cost flow instance with capacities `U = 1`, costs in `[0, m)` (`Q < N`), demand `d` at `s`
and `-d` at `z` (if `d > m` there is no flow; parallel arcs may be subdivided if a simple graph
is required, at most doubling `m` and `n`; `n ≤ m + 2`), so [vdB+23] runs in
`m^{1+o(1)} · log 2 · log N = N^{1+o(1)}` operations on `O(log N)`-bit words, and returns an
integral flow vector `Φ ∈ {0,1}^m` (the integrality theorem), or infeasibility. Our RAM
(`Outerplanar/RAM/Model.lean`) has unit-cost `add`, truncated `sub`, indirect `load`/`store` and
`ifz`, but **no multiplication, division or bit operations**: each word operation on
`O(log N)`-bit numbers (multiplication, division, comparison, shifts) is simulated in
`O(log N)` steps (schoolbook with precomputed powers of two, obtained by doubling `x + x`), and
array accesses cost `O(1)`. Hence the program runs within `T(N) = N^{1+o(1)} · O(log N) =
N^{1+o(1)}` steps, i.e. for every `ε > 0` there is `C_ε` with `T(N) ≤ C_ε N^{1+ε}`
(`AlmostLinear T`).

## The space bound

A run of `steps` unit-cost steps touches at most `steps` memory cells, but they may be spread
over a much larger address range (a program may compute `2^steps` by doubling and store there),
and the space of a run is its address range (`RAM.ComputesIn`, `Outerplanar/RAM/Bounded.lean`). The
hypothesis therefore bounds both: on an input of length `N`, `F` halts within `T N` steps and
accesses only the addresses below `T N` (the input cells included). This is the meaning of
"time `T`" for an algorithm whose memory is laid out in arrays of total size at most its running
time — the usual case, and the case of [vdB+23], whose data structures have size bounded by its
running time `m^{1+o(1)}` (the simulation of word operations on this RAM, which has no
multiplication, needs `O(log N)` further cells). A program whose arrays are allocated
contiguously, each of size at most the running time, satisfies it up to a constant factor (the
cells beyond the input are zero, so allocation needs no initialization). With this hypothesis
the statements say that the whole pipeline uses memory proportional to its running time.

The hypothesis is not vacuous: for each `N` the instances of size `N` with `d ≤ m` are finitely
many (all entries are bounded), so a brute-force solver (enumerating the `0/1` vectors over the
arcs in a work array of `O(N)` cells) satisfies it for a suitable `T`.
-/

@[expose] public section

namespace STACS2027.Runtimes.Flow

open STACS2027

/-! ### Flow vectors and the encoding -/

/-- The arcs of `net` whose entry in `bits` is nonzero (a `0/1` flow vector as a sublist). -/
def select : List Arc → List ℕ → List Arc
  | a :: net, b :: bits => if b = 0 then select net bits else a :: select net bits
  | _, _ => []

/-- The arcs as numbers: `tail, head, cost` for every arc, in order. -/
def encArcs (num : FlowNode → ℕ) (net : List Arc) : List ℕ :=
  net.flatMap fun a => [num a.tail, num a.head, a.cost]

/-- **The encoding of a network** with nodes numbered by `num` in `[0, n)`, and the required
value `d`: `n, m, s, z, d`, then `tail, head, cost` for each of the `m` arcs (capacity one). -/
def netInput (num : FlowNode → ℕ) (n d : ℕ) (net : List Arc) : List ℕ :=
  n :: net.length :: num .source :: num .sink :: d :: encArcs num net

/-- `v` is a node of the network: the source, the sink, or an end of an arc. -/
def NodeOf (net : List Arc) (v : FlowNode) : Prop :=
  v = .source ∨ v = .sink ∨ ∃ a ∈ net, v = a.tail ∨ v = a.head

/-- **The networks of the solver**: `num` numbers the nodes injectively in `[0, n)`, `n ≤ m + 2`;
no arc enters the source or leaves the sink; every arc has capacity one and a cost `< m`. -/
structure GoodNet (num : FlowNode → ℕ) (n : ℕ) (net : List Arc) : Prop where
  lt : ∀ v, NodeOf net v → num v < n
  inj : ∀ v w, NodeOf net v → NodeOf net w → num v = num w → v = w
  head_ne : ∀ a ∈ net, a.head ≠ .source
  tail_ne : ∀ a ∈ net, a.tail ≠ .sink
  cost_lt : ∀ a ∈ net, a.cost < net.length
  nodes_le : n ≤ net.length + 2

/-- `flow` is an integral flow of `net` of value `d` and of minimum cost among those. -/
def IsMinFlow (net : List Arc) (d : ℕ) (flow : List Arc) : Prop :=
  IsFlow net flow ∧ flowValue flow = d ∧
    ∀ flow', IsFlow net flow' → flowValue flow' = d → flowCost flow ≤ flowCost flow'

/-- **The answer of a min-cost flow solver**: `[0]` if there is no integral flow of value `d`,
else `1` and a `0/1` vector over the arcs selecting a minimum-cost integral flow of value `d`. -/
def FlowAnswer (net : List Arc) (d : ℕ) (out : List ℕ) : Prop :=
  (out = [0] ∧ ¬ ∃ flow, IsFlow net flow ∧ flowValue flow = d) ∨
    ∃ bits : List ℕ, out = 1 :: bits ∧ bits.length = net.length ∧ (∀ b ∈ bits, b ≤ 1) ∧
      IsMinFlow net d (select net bits)

/-- **The cited min-cost flow algorithm, as a hypothesis** ([vdB+23]): on the encoding of any
network of the class `GoodNet` and any value `d`, `F` halts within `T N` steps and the addresses
below `T N` (`N` the length of the encoding) with a correct answer (`FlowAnswer`). -/
def MinCostFlowSolver (F : RAM.Stmt) (T : ℕ → ℕ) : Prop :=
  ∀ (num : FlowNode → ℕ) (n d : ℕ) (net : List Arc), GoodNet num n net →
    ∃ (out : List ℕ) (steps : ℕ),
      RAM.ComputesIn F (netInput num n d net) out steps (T (netInput num n d net).length) ∧
      steps ≤ T (netInput num n d net).length ∧ FlowAnswer net d out

/-- **Almost-linear time**: `T(N) ≤ C_ε N^{1+ε}` for every `ε > 0` and every `N ≥ 1`. -/
def AlmostLinear (T : ℕ → ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N → (T N : ℝ) ≤ C * (N : ℝ) ^ (1 + ε)

/-! ### Basic facts -/

@[simp] theorem length_encArcs (num : FlowNode → ℕ) (net : List Arc) :
    (encArcs num net).length = 3 * net.length := by
  induction net with
  | nil => rfl
  | cons a net ih => simp [encArcs, List.flatMap_cons] at ih ⊢; omega

@[simp] theorem length_netInput (num : FlowNode → ℕ) (n d : ℕ) (net : List Arc) :
    (netInput num n d net).length = 3 * net.length + 5 := by
  simp [netInput]

theorem encArcs_append (num : FlowNode → ℕ) (l l' : List Arc) :
    encArcs num (l ++ l') = encArcs num l ++ encArcs num l' := by
  simp [encArcs, List.flatMap_append]

theorem select_sublist : ∀ (net : List Arc) (bits : List ℕ), (select net bits).Sublist net
  | [], _ => by simp [select]
  | _ :: _, [] => by simp [select]
  | a :: net, b :: bits => by
    by_cases hb : b = 0
    · simp only [select, hb, ↓reduceIte]
      exact (select_sublist net bits).cons a
    · simp only [select, hb, ↓reduceIte]
      exact (select_sublist net bits).cons_cons a

/-- In a network without repeated arcs, the arc at position `j` is selected iff its bit is
nonzero. -/
theorem getD_mem_select : ∀ {net : List Arc} {bits : List ℕ} (d : Arc), net.Nodup →
    ∀ {j : ℕ}, j < net.length → j < bits.length →
      (net.getD j d ∈ select net bits ↔ bits.getD j 0 ≠ 0)
  | [], _, _, _, _, hj, _ => by simp at hj
  | _ :: _, [], _, _, _, _, hb => by simp at hb
  | a :: net, b :: bits, d, hn, j, hj, hb => by
    obtain ⟨ha, hn'⟩ := List.nodup_cons.mp hn
    cases j with
    | zero =>
      by_cases hb0 : b = 0
      · simp only [List.getD_cons_zero, select, hb0, ↓reduceIte, ne_eq, not_true_eq_false,
          iff_false]
        exact fun h => ha ((select_sublist net bits).subset h)
      · simp [select, hb0]
    | succ j =>
      have ih := getD_mem_select (bits := bits) d hn' (j := j) (by simpa using hj) (by simpa using hb)
      have hne : net.getD j d ≠ a := by
        intro h
        apply ha
        rw [← h, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hj)]
        exact List.getElem_mem _
      by_cases hb0 : b = 0
      · simp only [select, hb0, ↓reduceIte, List.getD_cons_succ]
        exact ih
      · simp only [select, hb0, ↓reduceIte, List.getD_cons_succ, List.mem_cons, hne, false_or]
        exact ih

end STACS2027.Runtimes.Flow

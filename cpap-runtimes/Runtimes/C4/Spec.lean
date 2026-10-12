module

public import Outerplanar.Algo.Graph
public import NPHardness.Enumerate
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Nat.Find
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Tactic

/-!
# Four-cycle listing: the abstract specification

The functions below are exactly what the phases of the four-cycle machine compute. The machine is the offline form of ANONYMIZED and ANONYMIZED's
listing algorithm (STOC 2023, Theorem 7.2): a degeneracy order, every edge oriented
towards the later end, every 2-path whose centre is not the latest of its three vertices
put into the bucket of its unordered endpoint pair, and paired with the 2-paths already
there. Each 4-cycle is reported exactly once (`Output.lean`).

* **The id graph.** `nb g v = nbOf (idEdges g) v`: the neighbour lists of R1's CSR arrays.
* **Peeling** (phase PEEL). A smallest-last order by a bucket queue with lazy deletion:
  `PState` (removed flags `del`, current degrees `cur`, the buckets `stk d` as stacks that
  may hold stale entries, the bucket pointer `p`, the removal order `ord`), the operations
  `push`, `relax`, `remove`, the loop step `pstep` and the initial state `pinit`. After
  `peelFuel g` steps the order `peelOrd g` is complete (`Peel.lean`); `peelPos g v` is the
  position of `v` in it.
* **Orientation and wedges** (phases ORIENT, SIZE, ENUM), for any ranking `pos`:
  `outL g pos v` (the later neighbours of `v`), `pairsOf l` (the index pairs `a < b` of `l`),
  the wedges `(x, z, y)` (centre `z`) generated at `v`: type 1 `v → j → k` (`wedges1`) and
  type 2 `j ← v → k` (`wedges2`); the entries `(key x y, z)` (`entry`) inserted in this order
  (`ins`), their number `numPaths`, and the admissibility predicate `Adm`.
* **Buckets** (phase ENUM). `bucket l k`: the centres inserted with key `k`, newest first
  (the linked list of the machine); `reports l`: on inserting `l[j] = (k, z)`, the reports
  `(k, z, z')` for every `z'` already in the bucket of `k` (`reports_snoc`).
* **Output.** `canon4 a b c d`: the canonical rotation/reflection of the 4-cycle `a b c d`
  (smallest vertex first, its smaller cycle-neighbour second; `IsCanon4`); `phi g r` maps a
  report to its cycle in labels; `enumOutP g pos` lists the cycles reported for the ranking
  `pos`, `enumOut g` for the peeling order.
* **Bounds.** `degen g`: the largest out-degree of the peeling orientation; `pow43 m`: the
  least `X` with `m ^ 4 ≤ X ^ 3` (that is, `⌈m^{4/3}⌉`).
-/

@[expose] public section

namespace STACS2027.Runtimes.C4

open STACS2027 STACS2027.Algo

/-! ### The id graph -/

/-- The neighbour lists of the id graph `idEdges g` (in the order of R1's CSR arrays). -/
abbrev nb (g : Graph) : ℕ → List ℕ := nbOf (idEdges g)

/-! ### Peeling with a lazy bucket queue -/

/-- The state of the peeling loop. -/
structure PState where
  /-- Removed? -/
  del : ℕ → Bool
  /-- Current degree (meaningful for vertices not removed). -/
  cur : ℕ → ℕ
  /-- Bucket `d`: a stack (head = top); it may contain stale entries. -/
  stk : ℕ → List ℕ
  /-- The bucket pointer (a lower bound of the current degrees of the remaining vertices). -/
  p : ℕ
  /-- The removed vertices, in removal order. -/
  ord : List ℕ

/-- Push `w` onto bucket `d`. -/
def push (s : PState) (w d : ℕ) : PState :=
  { s with stk := Function.update s.stk d (w :: s.stk d) }

/-- Relax the neighbour `w` of a removed vertex: if `w` is not removed, decrement its
current degree and push it onto the bucket of its new degree. -/
def relax (s : PState) (w : ℕ) : PState :=
  if s.del w then s
  else push { s with cur := Function.update s.cur w (s.cur w - 1) } w (s.cur w - 1)

/-- Remove `v`: mark it, append it to the order, relax its neighbours, and move the bucket
pointer one down (truncated, as the machine's `sub`). -/
def remove (nb : ℕ → List ℕ) (s : PState) (v : ℕ) : PState :=
  let s' := (nb v).foldl relax { s with del := Function.update s.del v true, ord := s.ord ++ [v] }
  { s' with p := s'.p - 1 }

/-- One round of the peeling loop (the identity once all `N` vertices are removed): advance
the pointer past an empty bucket, or pop the top of the current bucket and remove it if the
entry is valid (not removed, current degree equal to the pointer). -/
def pstep (N : ℕ) (nb : ℕ → List ℕ) (s : PState) : PState :=
  if s.ord.length < N then
    match s.stk s.p with
    | [] => { s with p := s.p + 1 }
    | v :: rest =>
      let s₁ := { s with stk := Function.update s.stk s.p rest }
      if s.del v = false ∧ s.cur v = s.p then remove nb s₁ v else s₁
  else s

/-- The state before the empty-bucket loop: nothing removed, `cur v = |nb v|`, every
`v < N` pushed onto bucket `|nb v|` (in the order `0, …, N - 1`), pointer `0`. -/
def pinit (N : ℕ) (nb : ℕ → List ℕ) : PState :=
  (List.range N).foldl (fun s v => push s v (nb v).length)
    ⟨fun _ => false, fun v => (nb v).length, fun _ => [], 0, []⟩

/-- The number of rounds after which the peeling is complete (the initial potential plus
one, `Peel.lean`). -/
def peelFuel (g : Graph) : ℕ := 9 * numV g + 8 * (idEdges g).length + 1

/-- The final state of the peeling. -/
def peelState (g : Graph) : PState :=
  (pstep (numV g) (nb g))^[peelFuel g] (pinit (numV g) (nb g))

/-- The peeling (smallest-last) order. -/
def peelOrd (g : Graph) : List ℕ := (peelState g).ord

/-- The position of a vertex in the peeling order. -/
def peelPos (g : Graph) (v : ℕ) : ℕ := (peelOrd g).idxOf v

/-! ### Orientation and wedges, for any ranking `pos` -/

/-- The later neighbours of `v`: the out-list of `v` in the orientation by `pos`. -/
def outL (g : Graph) (pos : ℕ → ℕ) (v : ℕ) : List ℕ := (nb g v).filter fun u => pos v < pos u

/-- The pairs `(l[a], l[b])` with `a < b`, as the machine's loops `for a < |l|`,
`for b ∈ [a + 1, |l|)` produce them. -/
def pairsOf (l : List ℕ) : List (ℕ × ℕ) :=
  (List.range l.length).flatMap fun a =>
    (List.range' (a + 1) (l.length - (a + 1))).map fun b => (l.getD a 0, l.getD b 0)

/-- Type-1 wedges `(v, j, k)` (centre `j`) generated at `v`: `v → j → k`. -/
def wedges1 (g : Graph) (pos : ℕ → ℕ) (v : ℕ) : List (ℕ × ℕ × ℕ) :=
  (outL g pos v).flatMap fun j => (outL g pos j).map fun k => (v, j, k)

/-- Type-2 wedges `(j, v, k)` (centre `v`) generated at `v`: `j ← v → k`. -/
def wedges2 (g : Graph) (pos : ℕ → ℕ) (v : ℕ) : List (ℕ × ℕ × ℕ) :=
  (pairsOf (outL g pos v)).map fun jk => (jk.1, v, jk.2)

/-- The wedges `(x, z, y)` (endpoints `x`, `y`, centre `z`) generated at `v`. -/
def wedges (g : Graph) (pos : ℕ → ℕ) (v : ℕ) : List (ℕ × ℕ × ℕ) :=
  wedges1 g pos v ++ wedges2 g pos v

/-- The bucket key of the endpoints `x`, `y`: the unordered pair, smaller first. -/
def key (x y : ℕ) : ℕ × ℕ := (min x y, max x y)

/-- A list of insertions `(key, centre)`. -/
abbrev Ins := List ((ℕ × ℕ) × ℕ)

/-- The insertion of a wedge `(x, z, y)`: its key and its centre. -/
def entry (w : ℕ × ℕ × ℕ) : (ℕ × ℕ) × ℕ := (key w.1 w.2.2, w.2.1)

/-- All insertions, in the machine's order: vertex by vertex, type 1 then type 2. -/
def ins (g : Graph) (pos : ℕ → ℕ) : Ins :=
  (List.range (numV g)).flatMap fun v => (wedges g pos v).map entry

/-- The number of inserted 2-paths. -/
def numPaths (g : Graph) (pos : ℕ → ℕ) : ℕ := (ins g pos).length

/-- `z` is an admissible centre for the endpoints `x ≠ y`: a path `x – z – y` whose centre is
not the latest of its three vertices. -/
def Adm (g : Graph) (pos : ℕ → ℕ) (x z y : ℕ) : Prop :=
  x < numV g ∧ y < numV g ∧ x ≠ y ∧ z ∈ nb g x ∧ y ∈ nb g z ∧ pos z < max (pos x) (pos y)

/-! ### Buckets and reports -/

/-- The centres inserted so far with key `k`, newest first (the machine's linked list). -/
def bucket (l : Ins) (k : ℕ × ℕ) : List ℕ := ((l.filter (·.1 = k)).map (·.2)).reverse

/-- On inserting `l[j] = (k, z)`: the reports `(k, z, z')` for every `z'` already in the
bucket of `k`, newest first. -/
def reports (l : Ins) : List ((ℕ × ℕ) × ℕ × ℕ) :=
  (List.range l.length).flatMap fun j =>
    (bucket (l.take j) (l.getD j ((0, 0), 0)).1).map fun z' =>
      ((l.getD j ((0, 0), 0)).1, (l.getD j ((0, 0), 0)).2, z')

/-! ### Output -/

/-- Canonical 4-cycles: smallest vertex first, its smaller cycle-neighbour second. -/
def IsCanon4 : Cycle → Prop
  | [a, b, c, d] => a < b ∧ a < c ∧ a < d ∧ b < d
  | _ => False

/-- The canonical rotation/reflection of the cycle `a – b – c – d` (for distinct entries). -/
def canon4 (a b c d : ℕ) : Cycle :=
  if a < b ∧ a < c ∧ a < d then (if b < d then [a, b, c, d] else [a, d, c, b])
  else if b < c ∧ b < d then (if a < c then [b, a, d, c] else [b, c, d, a])
  else if c < d then (if b < d then [c, b, a, d] else [c, d, a, b])
  else (if a < c then [d, a, b, c] else [d, c, b, a])

/-- The reported cycle `x – z – y – z'` of the report `((x, y), z, z')`, in labels,
canonicalized in label order. -/
def phi (g : Graph) (r : (ℕ × ℕ) × ℕ × ℕ) : Cycle :=
  canon4 (labelOf g r.1.1) (labelOf g r.2.1) (labelOf g r.1.2) (labelOf g r.2.2)

/-- The cycles reported for the ranking `pos`. -/
def enumOutP (g : Graph) (pos : ℕ → ℕ) : List Cycle := (reports (ins g pos)).map (phi g)

/-- The output of the machine: the cycles reported for the peeling order. -/
def enumOut (g : Graph) : List Cycle := enumOutP g (peelPos g)

/-! ### Quantities of the bounds -/

/-- The degeneracy of the peeling orientation: the largest out-degree. -/
def degen (g : Graph) : ℕ := (Finset.range (numV g)).sup fun v => (outL g (peelPos g) v).length

theorem exists_pow43 (m : ℕ) : ∃ X, m ^ 4 ≤ X ^ 3 :=
  ⟨m ^ 2, by
    rcases Nat.eq_zero_or_pos m with h | h
    · simp [h]
    · rw [← pow_mul]; exact Nat.pow_le_pow_right h (by norm_num)⟩

/-- `⌈m^{4/3}⌉`: the least `X` with `m ^ 4 ≤ X ^ 3`. -/
def pow43 (m : ℕ) : ℕ := Nat.find (exists_pow43 m)

/-! ### Step lemmas -/

theorem pstep_of_not_lt {N : ℕ} {nb : ℕ → List ℕ} {s : PState} (h : ¬ s.ord.length < N) :
    pstep N nb s = s := by
  simp [pstep, h]

theorem pstep_advance {N : ℕ} {nb : ℕ → List ℕ} {s : PState} (h : s.ord.length < N)
    (he : s.stk s.p = []) : pstep N nb s = { s with p := s.p + 1 } := by
  simp [pstep, h, he]

theorem pstep_valid {N : ℕ} {nb : ℕ → List ℕ} {s : PState} {v : ℕ} {rest : List ℕ}
    (h : s.ord.length < N) (he : s.stk s.p = v :: rest) (hd : s.del v = false)
    (hc : s.cur v = s.p) :
    pstep N nb s = remove nb { s with stk := Function.update s.stk s.p rest } v := by
  simp [pstep, h, he, hd, hc]

theorem pstep_stale {N : ℕ} {nb : ℕ → List ℕ} {s : PState} {v : ℕ} {rest : List ℕ}
    (h : s.ord.length < N) (he : s.stk s.p = v :: rest) (hv : ¬ (s.del v = false ∧ s.cur v = s.p)) :
    pstep N nb s = { s with stk := Function.update s.stk s.p rest } := by
  simp only [pstep, h, he, ↓reduceIte, hv]

/-- The initial state as a fold over a prefix (the machine's initialization loop). -/
def pinitPre (nb : ℕ → List ℕ) (j : ℕ) : PState :=
  (List.range j).foldl (fun s v => push s v (nb v).length)
    ⟨fun _ => false, fun v => (nb v).length, fun _ => [], 0, []⟩

theorem pinitPre_zero (nb : ℕ → List ℕ) :
    pinitPre nb 0 = ⟨fun _ => false, fun v => (nb v).length, fun _ => [], 0, []⟩ := rfl

theorem pinitPre_succ (nb : ℕ → List ℕ) (j : ℕ) :
    pinitPre nb (j + 1) = push (pinitPre nb j) j (nb j).length := by
  simp [pinitPre, List.range_succ, List.foldl_append]

theorem pinit_eq (N : ℕ) (nb : ℕ → List ℕ) : pinit N nb = pinitPre nb N := rfl

theorem remove_eq (nb : ℕ → List ℕ) (s : PState) (v : ℕ) :
    remove nb s v = { (nb v).foldl relax
      { s with del := Function.update s.del v true, ord := s.ord ++ [v] } with
        p := ((nb v).foldl relax
          { s with del := Function.update s.del v true, ord := s.ord ++ [v] }).p - 1 } := rfl

theorem ins_eq (g : Graph) (pos : ℕ → ℕ) :
    ins g pos = (List.range (numV g)).flatMap fun v =>
      (wedges1 g pos v).map entry ++ (wedges2 g pos v).map entry := by
  simp [ins, wedges, List.map_append]

@[simp] theorem bucket_nil (k : ℕ × ℕ) : bucket [] k = [] := rfl

theorem bucket_snoc (l : Ins) (k : ℕ × ℕ) (z : ℕ) (k' : ℕ × ℕ) :
    bucket (l ++ [(k, z)]) k' = if k = k' then z :: bucket l k' else bucket l k' := by
  by_cases h : k = k' <;> simp [bucket, List.filter_append, h]

@[simp] theorem reports_nil : reports [] = [] := rfl

theorem reports_snoc (l : Ins) (k : ℕ × ℕ) (z : ℕ) :
    reports (l ++ [(k, z)]) = reports l ++ (bucket l k).map fun z' => (k, z, z') := by
  unfold reports
  rw [List.length_append, List.length_singleton, List.range_succ, List.flatMap_append]
  congr 1
  · refine List.flatMap_congr fun j hj => ?_
    have hj' : j < l.length := List.mem_range.mp hj
    have h1 : (l ++ [(k, z)]).getD j ((0, 0), 0) = l.getD j ((0, 0), 0) := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hj']
    have h2 : (l ++ [(k, z)]).take j = l.take j := List.take_append_of_le_length hj'.le
    rw [h1, h2]
  · simp [List.getD_eq_getElem?_getD]

theorem length_canon4 (a b c d : ℕ) : (canon4 a b c d).length = 4 := by
  unfold canon4; split_ifs <;> rfl

theorem length_phi (g : Graph) (r : (ℕ × ℕ) × ℕ × ℕ) : (phi g r).length = 4 :=
  length_canon4 _ _ _ _

/-- The flattened output has four entries per cycle. -/
theorem length_flatten_enumOutP (g : Graph) (pos : ℕ → ℕ) :
    (enumOutP g pos).flatten.length = 4 * (enumOutP g pos).length := by
  unfold enumOutP
  induction reports (ins g pos) with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_append, length_phi,
      List.length_cons] at ih ⊢
    omega

theorem pow43_spec (m : ℕ) : m ^ 4 ≤ pow43 m ^ 3 := Nat.find_spec (exists_pow43 m)

theorem pow43_min {m X : ℕ} (h : m ^ 4 ≤ X ^ 3) : pow43 m ≤ X := Nat.find_min' _ h

end STACS2027.Runtimes.C4

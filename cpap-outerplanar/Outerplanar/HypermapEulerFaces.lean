module

public import Outerplanar.HypermapEuler
import Lean.Elab.Tactic.Omega

/-!
# Faces of graph embeddings

Facts on the face cycles of a hypermap embedding a graph given by an edge list (the embedding
conditions of `Complexity.PlanarGraph` and `OuterplanarEmbedding`, `IsGraphEmbedding`), used
with Euler's formula (`Outerplanar/HypermapEuler.lean`) to bound the number of faces.

* Counting: the cycles of a permutation partition the darts, so lists of distinct darts, one
  inside each cycle, have total length at most the number of darts
  (`sum_orbit_lists_le`); if no cycle closes before `k` steps, `k · #cycles ≤ n`
  (`cycleCount_mul_le`); `orbit_count` is the form with one longer cycle. Exactly: the
  cycle lengths `cycleLen` sum to `n` (`sum_cycleLen`), and `k ≤ cycleLen p x` iff the cycle
  of `x` does not close before `k` steps (`le_cycleLen_iff`).
* The darts of a graph embedding: `dartEnd es d` is the vertex of the half-edge `d` and
  `dartOther es d` the other end of its edge. A face step goes along an edge: the face
  successor of `y` is a dart at the other end of `y` (`dartEnd_face`); hence face cycles are
  closed walks.
* For an edge list without loops and without two entries joining the same two vertices
  (`SimpleEdgeList`), no face cycle has one dart (`face_ne_self`) and none has two darts
  unless both ends of the edge are of degree one, i.e. its component is a single edge
  (`face_face_ne_self`); so when every vertex has degree at least two every face cycle has at
  least three darts (`face_girth_three`). For a bipartite edge list every face cycle has even
  length (`face_return_even`), hence at least four darts (`face_girth_four`).
* The counts of a graph embedding: `cycleCount edge` is the number of edges
  (`edge_cycleCount`), `cycleCount node` is at most the number of vertices
  (`node_cycleCount_le`), and a nonempty hypermap has a component (`componentCount_pos`);
  Euler's formula for a planar embedding, `2 · #components + #edges = #nodes + #faces`
  (`euler_graph`); `3 · #faces ≤ #darts` (`three_mul_faces_le`), `4 · #faces ≤ #darts` in the
  bipartite case (`four_mul_faces_le`).
-/

@[expose] public section

namespace STACS2027.HypEuler

open Complexity Complexity.Planar STACS2027.PlanarGluing

/-! ## Counting darts on cycles -/

section counting

variable {n : Nat} {p : Fin n → Fin n}

/-- The first `k` darts of the orbit of `x`: `x, p x, …, p^(k-1) x`. -/
def orbitPrefix (p : Fin n → Fin n) (x : Fin n) (k : Nat) : List (Fin n) :=
  (List.range k).map fun i => iterate p i x

theorem orbitPrefix_length (x : Fin n) (k : Nat) : (orbitPrefix p x k).length = k := by
  simp [orbitPrefix]

/-- If the orbit of `x` does not close before `k` steps, its first `k` darts are distinct. -/
theorem orbitPrefix_nodup (hp : ∀ a b, p a = p b → a = b) {x : Fin n} {k : Nat}
    (h : ∀ i, 0 < i → i < k → iterate p i x ≠ x) : (orbitPrefix p x k).Nodup := by
  have key : ∀ i j, i < j → j < k → iterate p i x ≠ iterate p j x := by
    intro i j hij hj he
    have h1 : iterate p i (iterate p (j - i) x) = iterate p i x := by
      rw [← iterate_add, show j - i + i = j by omega]; exact he.symm
    exact h (j - i) (by omega) (by omega) (iterate_inj hp i h1)
  apply nodup_map_of_injOn' _ List.nodup_range
  intro i hi j hj he
  simp only [List.mem_range] at hi hj
  rcases Nat.lt_trichotomy i j with hlt | heq | hgt
  · exact absurd he (key i j hlt hj)
  · exact heq
  · exact absurd he.symm (key j i hgt hi)

theorem orbitPrefix_cmin (hp : ∀ a b, p a = p b → a = b) (x : Fin n) (k : Nat) :
    ∀ y ∈ orbitPrefix p x k, cmin p y = cmin p x := by
  intro y hy
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hy
  exact cmin_iterate hp x i

/-- Lists of distinct darts, one inside the cycle of each of distinct cycle roots, are
disjoint: their concatenation has no repetition. -/
theorem flatMap_orbit_lists_nodup (L : Fin n → List (Fin n))
    (hnd : ∀ r ∈ cycleRoots p, (L r).Nodup)
    (hmem : ∀ r ∈ cycleRoots p, ∀ y ∈ L r, cmin p y = r) :
    ∀ rs : List (Fin n), rs.Nodup → (∀ r ∈ rs, r ∈ cycleRoots p) →
      (rs.flatMap L).Nodup ∧ ∀ y ∈ rs.flatMap L, cmin p y ∈ rs := by
  intro rs
  induction rs with
  | nil => intro _ _; simp
  | cons r rs ih =>
    intro h hsub
    rw [List.nodup_cons] at h
    have hr : r ∈ cycleRoots p := hsub r List.mem_cons_self
    obtain ⟨ih1, ih2⟩ := ih h.2 (fun s hs => hsub s (List.mem_cons_of_mem r hs))
    rw [List.flatMap_cons]
    refine ⟨List.nodup_append.mpr ⟨hnd r hr, ih1, ?_⟩, ?_⟩
    · intro a ha b hb hab
      subst hab
      have := ih2 a hb
      rw [hmem r hr a ha] at this
      exact h.1 this
    · intro y hy
      rcases List.mem_append.mp hy with hy | hy
      · rw [hmem r hr y hy]; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih2 y hy)

/-- **The cycles partition the darts**: lists of distinct darts, one inside the cycle of each
cycle root, have total length at most `n`. -/
theorem sum_orbit_lists_le (L : Fin n → List (Fin n))
    (hnd : ∀ r ∈ cycleRoots p, (L r).Nodup)
    (hmem : ∀ r ∈ cycleRoots p, ∀ y ∈ L r, cmin p y = r) :
    ((cycleRoots p).map fun r => (L r).length).sum ≤ n := by
  have h := (flatMap_orbit_lists_nodup L hnd hmem _ (cycleRoots_nodup p) (fun _ h => h)).1
  have hle := h.length_le_of_subset (l₂ := List.finRange n) (fun y _ => List.mem_finRange y)
  rw [List.length_flatMap, List.length_finRange] at hle
  exact hle

theorem sum_map_ge {α : Type} (g : α → Nat) (k : Nat) :
    ∀ l : List α, (∀ a ∈ l, k ≤ g a) → k * l.length ≤ (l.map g).sum
  | [], _ => by simp
  | a :: l, h => by
    have ih := sum_map_ge g k l (fun b hb => h b (List.mem_cons_of_mem a hb))
    have ha := h a List.mem_cons_self
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.mul_succ]
    omega

theorem sum_map_ge_one {α : Type} (g : α → Nat) (k A : Nat) (r : α) :
    ∀ l : List α, l.Nodup → r ∈ l → (∀ a ∈ l, a ≠ r → k ≤ g a) → A ≤ g r →
      k * (l.length - 1) + A ≤ (l.map g).sum
  | [], _, hr, _, _ => by simp at hr
  | a :: l, hnd, hr, h, hA => by
    rw [List.nodup_cons] at hnd
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_sub_cancel]
    by_cases har : a = r
    · subst har
      have := sum_map_ge g k l (fun b hb => h b (List.mem_cons_of_mem a hb)
        (fun he => hnd.1 (he ▸ hb)))
      omega
    · have hr' : r ∈ l := by
        rcases List.mem_cons.mp hr with h' | h'
        · exact absurd h'.symm har
        · exact h'
      have ih := sum_map_ge_one g k A r l hnd.2 hr'
        (fun b hb => h b (List.mem_cons_of_mem a hb)) hA
      have ha := h a List.mem_cons_self har
      obtain ⟨m, hm⟩ : ∃ m, l.length = m + 1 := ⟨l.length - 1, by
        have := List.length_pos_of_mem hr'; omega⟩
      rw [hm] at ih ⊢
      simp only [Nat.add_sub_cancel, Nat.mul_succ] at ih ⊢
      omega

/-- If no cycle of `p` closes before `k` steps, then `k · #cycles ≤ n`. -/
theorem cycleCount_mul_le (hp : ∀ a b, p a = p b → a = b) (k : Nat)
    (h : ∀ x i, 0 < i → i < k → iterate p i x ≠ x) : k * cycleCount p ≤ n := by
  have hs := sum_orbit_lists_le (fun r => orbitPrefix p r k)
    (fun r _ => orbitPrefix_nodup hp (h r))
    (fun r hr y hy => (orbitPrefix_cmin hp r k y hy).trans ((mem_cycleRoots hp r).mp hr))
  have hg := sum_map_ge (fun r => (orbitPrefix p r k).length) k (cycleRoots p)
    (fun r _ => Nat.le_of_eq (orbitPrefix_length r k).symm)
  rw [cycleRoots_length] at hg
  omega

/-- **Counting with one long cycle**: if no cycle of `p` closes before `k` steps and the
cycle of `x` contains the distinct darts `ys`, then `k · (#cycles − 1) + |ys| ≤ n`. -/
theorem orbit_count (hp : ∀ a b, p a = p b → a = b) (k : Nat)
    (h : ∀ x i, 0 < i → i < k → iterate p i x ≠ x) (x : Fin n) (ys : List (Fin n))
    (hys : ys.Nodup) (hysx : ∀ y ∈ ys, cmin p y = cmin p x) :
    k * (cycleCount p - 1) + ys.length ≤ n := by
  let L : Fin n → List (Fin n) := fun r => if r = cmin p x then ys else orbitPrefix p r k
  have hs := sum_orbit_lists_le L
    (fun r _ => by
      by_cases hr : r = cmin p x
      · simp only [L, hr, ite_true]; exact hys
      · simp only [L, hr, ite_false]; exact orbitPrefix_nodup hp (h r))
    (fun r hr y hy => by
      by_cases hrx : r = cmin p x
      · simp only [L, hrx, ite_true] at hy; rw [hysx y hy, hrx]
      · simp only [L, hrx, ite_false] at hy
        exact (orbitPrefix_cmin hp r k y hy).trans ((mem_cycleRoots hp r).mp hr))
  have hg := sum_map_ge_one (fun r => (L r).length) k ys.length (cmin p x) (cycleRoots p)
    (cycleRoots_nodup p) (cmin_mem_cycleRoots hp x)
    (fun r _ hr => by simp only [L, hr, ite_false, orbitPrefix_length, Nat.le_refl])
    (by simp only [L, ite_true, Nat.le_refl])
  rw [cycleRoots_length] at hg
  omega

/-! ### Cycle lengths -/

/-- The length of the cycle of `x`: the least `k > 0` with `p^k x = x`. -/
noncomputable def cycleLen (p : Fin n → Fin n) (hp : ∀ a b, p a = p b → a = b) (x : Fin n) :
    Nat :=
  Classical.choose (exists_least (P := fun k => 0 < k ∧ iterate p k x = x)
    (by obtain ⟨T, hT0, -, hT⟩ := period hp x; exact ⟨T, hT0, hT⟩))

theorem cycleLen_spec (hp : ∀ a b, p a = p b → a = b) (x : Fin n) :
    (0 < cycleLen p hp x ∧ iterate p (cycleLen p hp x) x = x) ∧
      ∀ i, i < cycleLen p hp x → ¬ (0 < i ∧ iterate p i x = x) :=
  Classical.choose_spec (exists_least (P := fun k => 0 < k ∧ iterate p k x = x)
    (by obtain ⟨T, hT0, -, hT⟩ := period hp x; exact ⟨T, hT0, hT⟩))

/-- The cycle of `x` has at least `k` darts iff it does not close before `k` steps. -/
theorem le_cycleLen_iff (hp : ∀ a b, p a = p b → a = b) (x : Fin n) (k : Nat) :
    k ≤ cycleLen p hp x ↔ ∀ i, 0 < i → i < k → iterate p i x ≠ x := by
  obtain ⟨⟨h0, hL⟩, hmin⟩ := cycleLen_spec hp x
  constructor
  · intro hk i hi hik he
    exact hmin i (by omega) ⟨hi, he⟩
  · intro h
    apply Classical.byContradiction
    intro hlt
    exact h _ h0 (by omega) hL

/-- The cycle of `x` consists of its first `cycleLen` iterates. -/
theorem mem_orbitPrefix_cycleLen (hp : ∀ a b, p a = p b → a = b) (y : Fin n) :
    y ∈ orbitPrefix p (cmin p y) (cycleLen p hp (cmin p y)) := by
  obtain ⟨⟨h0, hL⟩, -⟩ := cycleLen_spec hp (cmin p y)
  obtain ⟨hy, hmin⟩ := crank_spec hp y
  apply List.mem_map.mpr
  refine ⟨crank p hp y, List.mem_range.mpr ?_, hy⟩
  apply Classical.byContradiction
  intro hge
  obtain ⟨m, hm⟩ : ∃ m, crank p hp y = cycleLen p hp (cmin p y) + m :=
    ⟨crank p hp y - cycleLen p hp (cmin p y), by omega⟩
  apply hmin m (by omega)
  calc iterate p m (cmin p y) = iterate p (cycleLen p hp (cmin p y) + m) (cmin p y) := by
        rw [iterate_add, hL]
    _ = y := by rw [← hm]; exact hy

/-- **The cycles partition the darts**: the lengths of the cycles sum to `n`. -/
theorem sum_cycleLen (hp : ∀ a b, p a = p b → a = b) :
    ((cycleRoots p).map (cycleLen p hp)).sum = n := by
  let L : Fin n → List (Fin n) := fun r => orbitPrefix p r (cycleLen p hp r)
  have hnd : ∀ r ∈ cycleRoots p, (L r).Nodup := fun r _ =>
    orbitPrefix_nodup hp ((le_cycleLen_iff hp r _).mp (Nat.le_refl _))
  have hmem : ∀ r ∈ cycleRoots p, ∀ y ∈ L r, cmin p y = r := fun r hr y hy =>
    (orbitPrefix_cmin hp r _ y hy).trans ((mem_cycleRoots hp r).mp hr)
  have hle := sum_orbit_lists_le L hnd hmem
  have hsum : ((cycleRoots p).map fun r => (L r).length) = (cycleRoots p).map (cycleLen p hp) :=
    List.map_congr_left (fun r _ => orbitPrefix_length r _)
  rw [hsum] at hle
  have hge := (List.nodup_finRange n).length_le_of_subset
    (l₂ := (cycleRoots p).flatMap L) (by
      intro y _
      exact List.mem_flatMap.mpr
        ⟨cmin p y, cmin_mem_cycleRoots hp y, mem_orbitPrefix_cycleLen hp y⟩)
  rw [List.length_flatMap, hsum, List.length_finRange] at hge
  omega

end counting

/-! ## The darts of a graph embedding -/

section graph

variable {V : Type}

/-- The vertex at the half-edge `d` of the edge list `es` (half-edges `2i`, `2i + 1` are the
two ends of entry `i`). -/
def dartEnd (es : List (V × V)) (d : Fin (2 * es.length)) : V :=
  if d.val % 2 = 0 then (es[d.val / 2]'(by have := d.isLt; omega)).1
  else (es[d.val / 2]'(by have := d.isLt; omega)).2

/-- The other end of the edge of the half-edge `d`. -/
def dartOther (es : List (V × V)) (d : Fin (2 * es.length)) : V :=
  if d.val % 2 = 0 then (es[d.val / 2]'(by have := d.isLt; omega)).2
  else (es[d.val / 2]'(by have := d.isLt; omega)).1

theorem halfEdgeEnd_eq (es : List (V × V)) (d : Fin (2 * es.length)) :
    halfEdgeEnd es d.val = some (dartEnd es d) := by
  have hlt : d.val / 2 < es.length := by have := d.isLt; omega
  unfold halfEdgeEnd dartEnd
  rw [List.getElem?_eq_getElem hlt]
  rcases Nat.mod_two_eq_zero_or_one d.val with h | h
  · simp only [Option.map_some, h, ite_true]; rfl
  · simp only [Option.map_some, h]; rfl

/-- The embedding conditions of `Complexity.PlanarGraph` and `OuterplanarEmbedding` (without
planarity): `edge` pairs the two ends of every entry, and the `node` cycles are the sets of
half-edges at a common vertex. -/
def IsGraphEmbedding (es : List (V × V)) (G : Hypermap (2 * es.length)) : Prop :=
  (∀ d, (G.edge d).val = cond (Nat.beq (d.val % 2) 0) (d.val + 1) (d.val - 1)) ∧
  (∀ d d', (∃ k, iterate G.node k d = d') ↔ halfEdgeEnd es d.val = halfEdgeEnd es d'.val)

variable {es : List (V × V)} {G : Hypermap (2 * es.length)} (hG : IsGraphEmbedding es G)
include hG

theorem edge_edge (d : Fin (2 * es.length)) : G.edge (G.edge d) = d := by
  apply Fin.ext
  rcases graphEdge_val hG.1 d with ⟨h2, he⟩ | ⟨h2, he⟩ <;>
  rcases graphEdge_val hG.1 (G.edge d) with ⟨h2', he'⟩ | ⟨h2', he'⟩ <;> omega

/-- Two half-edges of the same entry are equal or exchanged by `edge`. -/
theorem same_entry {d d' : Fin (2 * es.length)} (h : d.val / 2 = d'.val / 2) :
    d' = d ∨ d' = G.edge d := by
  rcases graphEdge_val hG.1 d with ⟨h2, he⟩ | ⟨h2, he⟩
  · by_cases h' : d'.val = d.val
    · exact Or.inl (Fin.ext h')
    · exact Or.inr (Fin.ext (by omega))
  · by_cases h' : d'.val = d.val
    · exact Or.inl (Fin.ext h')
    · exact Or.inr (Fin.ext (by omega))

theorem dartEnd_edge (d : Fin (2 * es.length)) : dartEnd es (G.edge d) = dartOther es d := by
  have hdiv := graphEdge_div hG.1 d
  rcases graphEdge_val hG.1 d with ⟨h2, he⟩ | ⟨h2, he⟩
  · have h2' : (G.edge d).val % 2 = 1 := by omega
    simp [dartEnd, dartOther, h2, h2', hdiv]
  · have h2' : (G.edge d).val % 2 = 0 := by omega
    simp [dartEnd, dartOther, h2, h2', hdiv]

theorem dartOther_edge (d : Fin (2 * es.length)) : dartOther es (G.edge d) = dartEnd es d := by
  have h := dartEnd_edge hG (G.edge d)
  rw [edge_edge hG] at h
  exact h.symm

theorem dartEnd_eq_iff (d d' : Fin (2 * es.length)) :
    (∃ k, iterate G.node k d = d') ↔ dartEnd es d = dartEnd es d' := by
  rw [hG.2, halfEdgeEnd_eq, halfEdgeEnd_eq, Option.some.injEq]

theorem dartEnd_node (d : Fin (2 * es.length)) : dartEnd es (G.node d) = dartEnd es d :=
  ((dartEnd_eq_iff hG d (G.node d)).mp ⟨1, rfl⟩).symm

theorem dartEnd_iterate_node (k : Nat) (d : Fin (2 * es.length)) :
    dartEnd es (iterate G.node k d) = dartEnd es d :=
  ((dartEnd_eq_iff hG d _).mp ⟨k, rfl⟩).symm

theorem node_face (y : Fin (2 * es.length)) : G.node (G.face y) = G.edge y := by
  have h := G.edgeK (G.edge y)
  rwa [edge_edge hG] at h

/-- **A face step follows an edge**: the face successor of `y` is a dart at the other end of
the edge of `y`. -/
theorem dartEnd_face (y : Fin (2 * es.length)) : dartEnd es (G.face y) = dartOther es y := by
  rw [← dartEnd_node hG, node_face hG, dartEnd_edge hG]

/-- A dart sharing its vertex with another dart is not a fixed point of `node`. -/
theorem node_ne_self {d d' : Fin (2 * es.length)} (hne : d' ≠ d)
    (he : dartEnd es d' = dartEnd es d) : G.node d ≠ d := by
  intro hfix
  obtain ⟨k, hk⟩ := (dartEnd_eq_iff hG d d').mpr he.symm
  have : ∀ k, iterate G.node k d = d := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [iterate_succ', ih, hfix]
  exact hne (hk ▸ this k)

theorem linkedPath_of_dartEnd {d d' : Fin (2 * es.length)} (h : dartEnd es d = dartEnd es d') :
    LinkedPath G d d' :=
  nodeOrbit_linked G ((dartEnd_eq_iff hG d d').mpr h)

omit hG in
theorem linkedPath_edge (d : Fin (2 * es.length)) : LinkedPath G d (G.edge d) :=
  LinkedPath.step G (Or.inl rfl)

/-! ## Short face cycles -/

/-- Without loops, no face cycle has a single dart. -/
theorem face_ne_self (hloop : ∀ d, dartEnd es d ≠ dartOther es d) (y : Fin (2 * es.length)) :
    G.face y ≠ y := by
  intro h
  have := dartEnd_face hG y
  rw [h] at this
  exact hloop y this

/-- Without loops and repeated edges, a face cycle with two darts is a single edge whose two
ends have degree one. -/
theorem face_face_ne_self (hloop : ∀ d, dartEnd es d ≠ dartOther es d)
    (hsimple : ∀ d d' : Fin (2 * es.length), d.val / 2 ≠ d'.val / 2 →
      dartEnd es d = dartEnd es d' → dartOther es d ≠ dartOther es d')
    (y : Fin (2 * es.length)) (hdeg : G.node y ≠ y ∨ G.node (G.edge y) ≠ G.edge y) :
    G.face (G.face y) ≠ y := by
  intro h
  have h1 : dartEnd es (G.face y) = dartOther es y := dartEnd_face hG y
  have h2 : dartEnd es y = dartOther es (G.face y) := by
    have := dartEnd_face hG (G.face y); rwa [h] at this
  by_cases hdiv : (G.face y).val / 2 = y.val / 2
  · rcases same_entry hG hdiv.symm with hz | hz
    · exact face_ne_self hG hloop y hz
    · have hn1 : G.node (G.edge y) = G.edge y := by
        have := node_face hG y; rwa [hz] at this
      have hn2 : G.node y = y := by
        have := node_face hG (G.face y)
        rwa [h, hz, edge_edge hG] at this
      rcases hdeg with hd | hd
      · exact hd hn2
      · exact hd hn1
  · apply hsimple (G.face y) (G.edge y)
    · rw [graphEdge_div hG.1 y]; exact hdiv
    · rw [h1, dartEnd_edge hG]
    · rw [← h2, dartOther_edge hG]

/-- In a bipartite edge list every face cycle has even length. -/
theorem face_return_even (col : V → Bool)
    (hcol : ∀ d, col (dartEnd es d) ≠ col (dartOther es d))
    (k : Nat) (y : Fin (2 * es.length)) (h : iterate G.face k y = y) : k % 2 = 0 := by
  have hstep : ∀ y, col (dartEnd es (G.face y)) = !col (dartEnd es y) := by
    intro y
    rw [dartEnd_face hG]
    have := hcol y
    revert this
    cases col (dartEnd es y) <;> cases col (dartOther es y) <;> simp
  have key : ∀ k y, col (dartEnd es (iterate G.face k y)) =
      if k % 2 = 0 then col (dartEnd es y) else !col (dartEnd es y) := by
    intro k
    induction k with
    | zero => intro y; simp [iterate]
    | succ k ih =>
      intro y
      rw [iterate_succ', hstep, ih]
      rcases Nat.mod_two_eq_zero_or_one k with hk | hk
      · have : (k + 1) % 2 = 1 := by omega
        simp [hk, this]
      · have : (k + 1) % 2 = 0 := by omega
        simp [hk, this]
  have := key k y
  rw [h] at this
  rcases Nat.mod_two_eq_zero_or_one k with hk | hk
  · exact hk
  · simp [hk] at this

/-! ## Edge lists without loops and repeated edges -/

/-- An edge list without loops in which no two entries join the same two vertices, in
either orientation. -/
def SimpleEdgeList (es : List (V × V)) : Prop :=
  (∀ e ∈ es, e.1 ≠ e.2) ∧ es.Pairwise fun e e' => e ≠ e' ∧ e ≠ (e'.2, e'.1)

omit hG in
theorem SimpleEdgeList.loopless (hs : SimpleEdgeList es) (d : Fin (2 * es.length)) :
    dartEnd es d ≠ dartOther es d := by
  have hlt : d.val / 2 < es.length := by have := d.isLt; omega
  have hl := hs.1 _ (List.getElem_mem hlt)
  unfold dartEnd dartOther
  split
  · exact hl
  · exact fun h => hl h.symm

omit hG in
theorem dart_pair (d : Fin (2 * es.length)) :
    (dartEnd es d, dartOther es d) = es[d.val / 2]'(by have := d.isLt; omega) ∨
      (dartOther es d, dartEnd es d) = es[d.val / 2]'(by have := d.isLt; omega) := by
  unfold dartEnd dartOther
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

omit hG in
theorem SimpleEdgeList.simple (hs : SimpleEdgeList es) (d d' : Fin (2 * es.length))
    (hdiv : d.val / 2 ≠ d'.val / 2) (he : dartEnd es d = dartEnd es d') :
    dartOther es d ≠ dartOther es d' := by
  intro ho
  have hlt : d.val / 2 < es.length := by have := d.isLt; omega
  have hlt' : d'.val / 2 < es.length := by have := d'.isLt; omega
  -- the two entries are equal or reversed
  have key : es[d.val / 2] = es[d'.val / 2] ∨
      es[d.val / 2] = ((es[d'.val / 2]).2, (es[d'.val / 2]).1) := by
    rcases dart_pair d with h1 | h1 <;> rcases dart_pair d' with h2 | h2 <;>
      rw [← h1, ← h2, he, ho] <;> simp
  have hp := List.pairwise_iff_getElem.mp hs.2
  rcases Nat.lt_or_gt_of_ne hdiv with hlt2 | hlt2
  · obtain ⟨n1, n2⟩ := hp _ _ hlt hlt' hlt2
    rcases key with k | k
    · exact n1 k
    · exact n2 k
  · obtain ⟨n1, n2⟩ := hp _ _ hlt' hlt hlt2
    rcases key with k | k
    · exact n1 k.symm
    · exact n2 (by rw [k])

/-- **Face cycles of a simple graph have at least three darts** when every vertex has degree
at least two. -/
theorem face_girth_three (hs : SimpleEdgeList es)
    (hdeg : ∀ d : Fin (2 * es.length), ∃ d', d' ≠ d ∧ dartEnd es d' = dartEnd es d) :
    ∀ y i, 0 < i → i < 3 → iterate G.face i y ≠ y := by
  intro y i h0 h3
  obtain ⟨d', hne, he⟩ := hdeg y
  have hny := node_ne_self hG hne he
  rcases (show i = 1 ∨ i = 2 by omega) with rfl | rfl
  · exact face_ne_self hG hs.loopless y
  · exact face_face_ne_self hG hs.loopless hs.simple y (Or.inl hny)

/-- **Face cycles of a simple bipartite graph have at least four darts** when every vertex
has degree at least two. -/
theorem face_girth_four (hs : SimpleEdgeList es)
    (hdeg : ∀ d : Fin (2 * es.length), ∃ d', d' ≠ d ∧ dartEnd es d' = dartEnd es d)
    (col : V → Bool) (hcol : ∀ e ∈ es, col e.1 ≠ col e.2) :
    ∀ y i, 0 < i → i < 4 → iterate G.face i y ≠ y := by
  have hcol' : ∀ d, col (dartEnd es d) ≠ col (dartOther es d) := by
    intro d
    have hlt : d.val / 2 < es.length := by have := d.isLt; omega
    have hl := hcol _ (List.getElem_mem hlt)
    unfold dartEnd dartOther
    split
    · exact hl
    · exact fun h => hl h.symm
  intro y i h0 h4 he
  rcases (show i = 3 ∨ i < 3 by omega) with rfl | h3
  · have := face_return_even hG col hcol' 3 y he
    omega
  · exact face_girth_three hG hs hdeg y i h0 h3 he

/-! ## The counts of a graph embedding -/

/-- The edge cycles are the entries of the edge list. -/
theorem edge_cycleCount : cycleCount G.edge = es.length :=
  Nat.le_antisymm (cycleCount_graphEdge_le hG.1) (cycleCount_graphEdge_ge hG.1)

/-- There are at most as many node cycles as vertices. -/
theorem node_cycleCount_le (vs : List V) (hvs : ∀ d, dartEnd es d ∈ vs) :
    cycleCount G.node ≤ vs.length := by
  rw [← cycleRoots_length]
  have hnd : ((cycleRoots G.node).map (dartEnd es)).Nodup := by
    apply nodup_map_of_injOn' _ (cycleRoots_nodup _)
    intro r hr r' hr' he
    exact cycleRoots_eq_of_reaches (hm_node_inj G) hr hr' ((dartEnd_eq_iff hG r r').mpr he)
  have := hnd.length_le_of_subset (l₂ := vs) (by
    intro v hv
    obtain ⟨d, _, rfl⟩ := List.mem_map.mp hv
    exact hvs d)
  simpa using this

/-- **Euler's formula for a planar graph embedding**:
`2 · #components + #edges = #nodes + #faces`. -/
theorem euler_graph (hP : G.Planar) :
    2 * G.componentCount + es.length = cycleCount G.node + cycleCount G.face := by
  have h := (Hypermap.planar_iff_euler_eq G).mp hP
  have hE := edge_cycleCount hG
  unfold Hypermap.eulerLhs Hypermap.eulerRhs at h
  omega

/-- In a simple graph with all degrees at least two, `3 · #faces ≤ #darts`. -/
theorem three_mul_faces_le (hs : SimpleEdgeList es)
    (hdeg : ∀ d : Fin (2 * es.length), ∃ d', d' ≠ d ∧ dartEnd es d' = dartEnd es d) :
    3 * cycleCount G.face ≤ 2 * es.length :=
  cycleCount_mul_le (hm_face_inj G) 3 (face_girth_three hG hs hdeg)

/-- In a simple bipartite graph with all degrees at least two, `4 · #faces ≤ #darts`. -/
theorem four_mul_faces_le (hs : SimpleEdgeList es)
    (hdeg : ∀ d : Fin (2 * es.length), ∃ d', d' ≠ d ∧ dartEnd es d' = dartEnd es d)
    (col : V → Bool) (hcol : ∀ e ∈ es, col e.1 ≠ col e.2) :
    4 * cycleCount G.face ≤ 2 * es.length :=
  cycleCount_mul_le (hm_face_inj G) 4 (face_girth_four hG hs hdeg col hcol)

omit hG in
/-- A hypermap with a dart has a component. -/
theorem componentCount_pos {n : Nat} (H : Hypermap n) (x : Fin n) : 1 ≤ H.componentCount := by
  unfold Hypermap.componentCount
  apply List.countP_pos_iff.mpr
  refine ⟨⟨0, by have := x.isLt; omega⟩, List.mem_finRange _, ?_⟩
  simp

end graph

end STACS2027.HypEuler

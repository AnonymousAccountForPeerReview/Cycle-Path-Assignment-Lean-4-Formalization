module

public import Outerplanar.OuterplanarDef
public import NPHardness.PlanarGluingLists
public import NPHardness.PlanarGluingSpherical

/-!
# Basic invariance of outerplanar embeddings

The definitions of `Outerplanar/OuterplanarDef.lean` do not depend on the order in which the
edges are listed, on the names of the vertices, or on the multigraph `g` beyond its simple
graph. This file proves it:

* `OuterFaceCond G`: the outer-face condition of `OuterplanarEmbedding`, for one hypermap
  (`outerplanarEmbedding_iff` restates the definition with it);
* `OuterFaceCond.dartEquiv`: it is preserved by renumbering the darts;
* `OuterplanarEmbedding.of_graphDartEquiv`, `OuterplanarEmbedding.perm`: renumbering the
  edges (a permutation of the edge list) preserves outerplanar embeddings;
* `OuterplanarEmbedding.map_injOn`, `outerplanarEmbedding_map_iff`: renaming the vertices
  by a function injective on the ends of the edges preserves them (both directions);
* `RepEdges g es`: `es` lists the simple graph of `g` (every adjacent pair once, smaller end
  first); two such lists are permutations of each other (`RepEdges.perm`), so outerplanar
  embeddings depend only on the adjacency (`RepEdges.outerplanarEmbedding_iff`).
-/

@[expose] public section

namespace STACS2027

open Complexity Complexity.Planar PlanarGluing

/-- The outer-face condition of `OuterplanarEmbedding` for one hypermap `G` on `n` darts:
for every dart `d` there is a dart `x` whose face meets the node of every dart linked to
`d`. -/
def OuterFaceCond {n : Nat} (G : Hypermap n) : Prop :=
  ∀ d, ∃ x, ∀ d', G.linked n d d' = true →
    ∃ j k, iterate G.face j x = iterate G.node k d'

/-- `OuterplanarEmbedding`, restated with `OuterFaceCond`. -/
theorem outerplanarEmbedding_iff {V : Type} (es : List (V × V)) :
    OuterplanarEmbedding es ↔ ∃ G : Hypermap (2 * es.length),
      (∀ d, (G.edge d).val = cond (Nat.beq (d.val % 2) 0) (d.val + 1) (d.val - 1)) ∧
      (∀ d d', (∃ k, iterate G.node k d = d') ↔
        halfEdgeEnd es d.val = halfEdgeEnd es d'.val) ∧
      G.Planar ∧ OuterFaceCond G := Iff.rfl

/-! ### Maps commuting with the three permutations -/

/-- A map of darts commuting with `edge`, `node` and `face` maps linked darts to linked
darts. -/
theorem linked_of_commute {n m : Nat} (G : Hypermap n) (H : Hypermap m) (f : Fin n → Fin m)
    (he : ∀ x, H.edge (f x) = f (G.edge x)) (hn : ∀ x, H.node (f x) = f (G.node x))
    (hf : ∀ x, H.face (f x) = f (G.face x)) {k : Nat} {x y : Fin n}
    (h : G.linked k x y = true) : H.linked k (f x) (f y) = true := by
  induction k generalizing y with
  | zero =>
    rw [Linked.linked_zero] at h ⊢
    exact congrArg f h
  | succ k ih =>
    rw [Linked.linked_succ] at h ⊢
    rcases h with h | ⟨z, hz, hs⟩
    · exact Or.inl (ih h)
    · refine Or.inr ⟨f z, ih hz, ?_⟩
      rcases hs with hs | hs | hs
      · exact Or.inl (by rw [he, hs])
      · exact Or.inr (Or.inl (by rw [hn, hs]))
      · exact Or.inr (Or.inr (by rw [hf, hs]))

/-- Iterates of commuting maps. -/
theorem iterate_commute {α β : Type} (p : α → α) (q : β → β) (f : α → β)
    (h : ∀ x, q (f x) = f (p x)) (k : Nat) (x : α) :
    iterate q k (f x) = f (iterate p k x) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih => simp only [iterate, h, ih]

/-- Renumbering the darts preserves the outer-face condition. -/
theorem OuterFaceCond.dartEquiv {n m : Nat} (e : DartEquiv n m) {G : Hypermap n}
    (h : OuterFaceCond G) : OuterFaceCond (e.hypermap G) := by
  intro d
  obtain ⟨x, hx⟩ := h (e.invFun d)
  refine ⟨e.toFun x, fun d' hd' => ?_⟩
  have hl := linked_of_commute (e.hypermap G) G e.invFun
    (fun y => (DartEquiv.inv_conjugate e G.edge y).symm)
    (fun y => (DartEquiv.inv_conjugate e G.node y).symm)
    (fun y => (DartEquiv.inv_conjugate e G.face y).symm) hd'
  obtain ⟨j, k, hjk⟩ := hx _ (Linked.linked_stable G hl)
  refine ⟨j, k, ?_⟩
  change iterate (e.conjugate G.face) j (e.toFun x) = iterate (e.conjugate G.node) k d'
  rw [DartEquiv.iterate_conjugate, DartEquiv.iterate_conjugate, e.left_inv, hjk]

/-! ### Renumbering the edges -/

/-- The edge and node conditions of a graph embedding are carried along a dart isomorphism
of edge lists. -/
theorem graphDartEquiv_embedding {V : Type} {es ts : List (V × V)}
    (e : GraphDartEquiv es ts) {G : Hypermap (2 * es.length)}
    (hE : ∀ d, (G.edge d).val = cond (Nat.beq (d.val % 2) 0) (d.val + 1) (d.val - 1))
    (hN : ∀ d d', (∃ k, iterate G.node k d = d') ↔
      halfEdgeEnd es d.val = halfEdgeEnd es d'.val) :
    (∀ d, ((e.darts.hypermap G).edge d).val =
      cond (Nat.beq (d.val % 2) 0) (d.val + 1) (d.val - 1)) ∧
    (∀ d d', (∃ k, iterate (e.darts.hypermap G).node k d = d') ↔
      halfEdgeEnd ts d.val = halfEdgeEnd ts d'.val) := by
  have he : ∀ d, G.edge d = graphEdge d := fun d => Fin.ext (hE d)
  refine ⟨?_, ?_⟩
  · intro y
    change (e.darts.toFun (G.edge (e.darts.invFun y))).val = _
    rw [he, e.edge, e.darts.right_inv]
    rfl
  · intro y y'
    have hn : (∃ k, iterate (e.darts.conjugate G.node) k y = y') ↔
        ∃ k, iterate G.node k (e.darts.invFun y) = e.darts.invFun y' := by
      constructor
      · rintro ⟨k, hk⟩
        rw [e.darts.iterate_conjugate] at hk
        exact ⟨k, by
          have := congrArg e.darts.invFun hk
          simpa only [e.darts.left_inv] using this⟩
      · rintro ⟨k, hk⟩
        exact ⟨k, by rw [e.darts.iterate_conjugate, hk, e.darts.right_inv]⟩
    change (∃ k, iterate (e.darts.conjugate G.node) k y = y') ↔ _
    rw [hn, hN]
    have hy := e.ends (e.darts.invFun y)
    have hy' := e.ends (e.darts.invFun y')
    rw [e.darts.right_inv] at hy hy'
    rw [← hy, ← hy']

/-- A dart isomorphism of edge lists (preserving the edge pairing and the ends) carries
outerplanar embeddings. -/
theorem OuterplanarEmbedding.of_graphDartEquiv {V : Type} {es ts : List (V × V)}
    (e : GraphDartEquiv es ts) (h : OuterplanarEmbedding es) : OuterplanarEmbedding ts := by
  obtain ⟨G, hE, hN, hP, hO⟩ := h
  obtain ⟨hE', hN'⟩ := graphDartEquiv_embedding e hE hN
  exact ⟨e.darts.hypermap G, hE', hN', e.darts.planar G hP,
    OuterFaceCond.dartEquiv e.darts hO⟩

/-- **Renumbering the edges.** An outerplanar embedding of an edge list gives one of every
permutation of it. -/
theorem OuterplanarEmbedding.perm {V : Type} {es es' : List (V × V)} (hp : es.Perm es')
    (h : OuterplanarEmbedding es) : OuterplanarEmbedding es' := by
  obtain ⟨e⟩ := IndexEquiv.of_perm hp
  exact h.of_graphDartEquiv e.graphDarts

/-- Outerplanar embeddings of two permutations of an edge list. -/
theorem outerplanarEmbedding_perm_iff {V : Type} {es es' : List (V × V)} (hp : es.Perm es') :
    OuterplanarEmbedding es ↔ OuterplanarEmbedding es' :=
  ⟨OuterplanarEmbedding.perm hp, OuterplanarEmbedding.perm hp.symm⟩

/-! ### Renaming the vertices -/

/-- Every half-edge of an edge list ends at an end of one of its edges. -/
theorem halfEdgeEnd_isEnd {V : Type} (es : List (V × V)) {d : Nat} (hd : d < 2 * es.length) :
    ∃ v, halfEdgeEnd es d = some v ∧ ∃ e ∈ es, v = e.1 ∨ v = e.2 := by
  have hi : d / 2 < es.length := by omega
  refine ⟨cond (Nat.beq (d % 2) 0) es[d / 2].1 es[d / 2].2, ?_, es[d / 2],
    List.getElem_mem hi, ?_⟩
  · simp only [halfEdgeEnd, List.getElem?_eq_getElem hi, Option.map_some]
  · cases Nat.beq (d % 2) 0 <;> simp

/-- Renaming the vertices by a map that is injective on the ends of the edges. -/
theorem outerplanarEmbedding_map_iff {V W : Type} {es : List (V × V)} (f : V → W)
    (hf : ∀ a b, (∃ e ∈ es, a = e.1 ∨ a = e.2) → (∃ e ∈ es, b = e.1 ∨ b = e.2) →
      f a = f b → a = b) :
    OuterplanarEmbedding (es.map fun e => (f e.1, f e.2)) ↔ OuterplanarEmbedding es := by
  have hi : ∀ d d' : Fin (2 * es.length),
      (halfEdgeEnd es d.val).map f = (halfEdgeEnd es d'.val).map f ↔
        halfEdgeEnd es d.val = halfEdgeEnd es d'.val := by
    intro d d'
    obtain ⟨v, hv, hve⟩ := halfEdgeEnd_isEnd es d.isLt
    obtain ⟨v', hv', hve'⟩ := halfEdgeEnd_isEnd es d'.isLt
    rw [hv, hv']
    simp only [Option.map_some, Option.some.injEq]
    exact ⟨hf v v' hve hve', congrArg f⟩
  unfold OuterplanarEmbedding
  simp only [STACS2027.halfEdgeEnd_relabel]
  rw [List.length_map]
  constructor
  · rintro ⟨G, hE, hN, hP, hO⟩
    exact ⟨G, hE, fun d d' => (hN d d').trans (hi d d'), hP, hO⟩
  · rintro ⟨G, hE, hN, hP, hO⟩
    exact ⟨G, hE, fun d d' => (hN d d').trans (hi d d').symm, hP, hO⟩

/-- **Renaming the vertices.** Relabelling the vertices by a map injective on the ends of
the edges preserves outerplanar embeddings. -/
theorem OuterplanarEmbedding.map_injOn {V W : Type} {es : List (V × V)} (f : V → W)
    (hf : ∀ a b, (∃ e ∈ es, a = e.1 ∨ a = e.2) → (∃ e ∈ es, b = e.1 ∨ b = e.2) →
      f a = f b → a = b)
    (h : OuterplanarEmbedding es) : OuterplanarEmbedding (es.map fun e => (f e.1, f e.2)) :=
  (outerplanarEmbedding_map_iff f hf).mpr h

/-! ### Edge lists of simple graphs -/

/-- `es` lists the simple graph of `g`: every pair of adjacent vertices once, smaller end
first. -/
def RepEdges (g : Graph) (es : List Edge) : Prop :=
  es.Nodup ∧ ∀ e : Edge, e ∈ es ↔ e.1 < e.2 ∧ Adj g e.1 e.2

/-- Two edge lists of graphs with the same adjacency are permutations of each other. -/
theorem RepEdges.perm {g g' : Graph} {es es' : List Edge} (h : RepEdges g es)
    (h' : RepEdges g' es') (hadj : ∀ u v, Adj g u v ↔ Adj g' u v) : es.Perm es' :=
  (List.perm_ext_iff_of_nodup h.1 h'.1).mpr fun e => by rw [h.2, h'.2, hadj]

/-- Outerplanar embeddings of edge lists of graphs with the same adjacency. -/
theorem RepEdges.outerplanarEmbedding_iff {g g' : Graph} {es es' : List Edge}
    (h : RepEdges g es) (h' : RepEdges g' es') (hadj : ∀ u v, Adj g u v ↔ Adj g' u v) :
    OuterplanarEmbedding es ↔ OuterplanarEmbedding es' :=
  outerplanarEmbedding_perm_iff (h.perm h' hadj)

theorem eraseDups_nodup_of_length {α : Type} [BEq α] [LawfulBEq α] :
    ∀ (n : Nat) (l : List α), l.length ≤ n → l.eraseDups.Nodup
  | _, [], _ => by simp
  | 0, _ :: _, h => by simp at h
  | n + 1, a :: as, h => by
    rw [List.eraseDups_cons]
    refine List.nodup_cons.mpr ⟨fun ha => ?_, eraseDups_nodup_of_length n _
      (Nat.le_trans (List.length_filter_le _ _) (by simp at h; omega))⟩
    have := List.mem_filter.mp (List.mem_eraseDups.mp ha)
    simp at this

/-- `simpleEdges g` has no repeated entry. -/
theorem nodup_simpleEdges (g : Graph) : (simpleEdges g).Nodup :=
  eraseDups_nodup_of_length _ _ (Nat.le_refl _)

/-- The entries of `simpleEdges g`: the adjacent pairs of `g`, smaller end first. -/
theorem mem_simpleEdges {g : Graph} {e : Edge} :
    e ∈ simpleEdges g ↔ e.1 < e.2 ∧ Adj g e.1 e.2 := by
  have hedge : e.1 < e.2 → edge e.1 e.2 = e := fun h => by
    unfold edge; ext <;> simp <;> omega
  simp only [simpleEdges, List.mem_eraseDups, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨he, hlt⟩
    exact ⟨hlt, Nat.ne_of_lt hlt, by rw [hedge hlt]; exact he⟩
  · rintro ⟨hlt, -, he⟩
    rw [hedge hlt] at he
    exact ⟨he, hlt⟩

/-- `simpleEdges g` lists the simple graph of `g`. -/
theorem simpleEdges_rep (g : Graph) : RepEdges g (simpleEdges g) :=
  ⟨nodup_simpleEdges g, fun _ => mem_simpleEdges⟩

/-- **Outerplanarity depends only on the adjacency.** -/
theorem OuterplanarDrawing.congr {g g' : Graph} (h : ∀ u v, Adj g u v ↔ Adj g' u v)
    (hd : OuterplanarDrawing g) : OuterplanarDrawing g' :=
  ((simpleEdges_rep g).outerplanarEmbedding_iff (simpleEdges_rep g') h).mp hd

end STACS2027

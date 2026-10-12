module

public import Outerplanar.OuterplanarMinorContract
public import Outerplanar.OuterplanarBasic
public import Batteries.Data.List.Basic
import Mathlib.Tactic

/-!
# Edge-list operations preserving outerplanar embeddings

From the hypermap surgery of `OuterplanarMinorDelete` and `OuterplanarMinorContract` and the
renumbering invariance of `OuterplanarBasic` (`OuterplanarEmbedding.perm`,
`OuterplanarEmbedding.of_graphDartEquiv`):

* `OuterplanarEmbedding.sublist`, `OuterplanarEmbedding.subperm`: deleting any edges
  (given Euler's inequality for hypermaps);
* `OuterplanarEmbedding.flipEdges`, `OuterplanarEmbedding.canonical`: reversing the stored
  orientation of edges, in particular writing every edge smaller end first (`edge`);
* `OuterplanarEmbedding.contract`: contracting an edge `(s, t)`, `s ≠ t`, anywhere in the
  list (it is removed once and `t` is renamed `s`).
-/

@[expose] public section

namespace STACS2027
open Complexity Complexity.Planar STACS2027.PlanarGluing STACS2027.OuterplanarMinor

theorem OuterplanarEmbedding.sublist_prefix (hE : HypermapEuler) {V : Type}
    {es ts : List (V × V)} (h : es.Sublist ts) :
    ∀ pre : List (V × V), OuterplanarEmbedding (pre ++ ts) →
      OuterplanarEmbedding (pre ++ es) := by
  induction h with
  | slnil => intro pre hp; exact hp
  | @cons es ts e h ih =>
    intro pre hp
    have he : (pre ++ e :: ts).Perm ((pre ++ ts) ++ [e]) := by
      simpa only [List.append_assoc, List.singleton_append] using
        (List.perm_append_comm (l₁ := [e]) (l₂ := ts)).append_left pre
    exact ih pre (OuterplanarEmbedding.dropLast hE (OuterplanarEmbedding.perm he hp))
  | @cons_cons es ts e h ih =>
    intro pre hp
    have he : OuterplanarEmbedding ((pre ++ [e]) ++ ts) := by
      simpa only [List.append_assoc, List.singleton_append] using hp
    have ht := ih (pre ++ [e]) he
    simpa only [List.append_assoc, List.singleton_append] using ht

/-- **Deleting edges.** A sublist of an outerplanar embedding has one (given Euler's
inequality for hypermaps). -/
theorem OuterplanarEmbedding.sublist (hE : HypermapEuler) {V : Type} {es ts : List (V × V)}
    (h : es.Sublist ts) (ho : OuterplanarEmbedding ts) : OuterplanarEmbedding es := by
  simpa only [List.nil_append] using OuterplanarEmbedding.sublist_prefix hE h [] ho

/-- Deleting edges and reordering the rest. -/
theorem OuterplanarEmbedding.subperm (hE : HypermapEuler) {V : Type} {es ts : List (V × V)}
    (h : es.Subperm ts) (ho : OuterplanarEmbedding ts) : OuterplanarEmbedding es := by
  obtain ⟨l, hp, hs⟩ := h
  exact OuterplanarEmbedding.perm hp (ho.sublist hE hs)

/-- Reversing the stored orientation of some edges is a dart isomorphism. -/
def flipGraphDartEquiv {V : Type} (es : List (V × V)) (flips : Nat → Bool) :
    GraphDartEquiv es (flipEdges es flips) where
  darts := (flipDartEquiv es.length flips).trans (DartEquiv.cast (by rw [flipEdges_length]))
  edge d := by
    apply Fin.ext
    change (flipDart flips (graphEdge d)).val = ed (flipDart flips d).val
    rw [flipDart_edge]
    rfl
  ends d := flipDart_ends es flips d

/-- **Reversing edges.** -/
theorem OuterplanarEmbedding.flipEdges {V : Type} {es : List (V × V)} (flips : Nat → Bool)
    (h : OuterplanarEmbedding es) : OuterplanarEmbedding (PlanarGluing.flipEdges es flips) :=
  h.of_graphDartEquiv (flipGraphDartEquiv es flips)

/-- **Writing every edge smaller end first.** -/
theorem OuterplanarEmbedding.canonical {es : List (Nat × Nat)} (h : OuterplanarEmbedding es) :
    OuterplanarEmbedding (es.map fun e => edge e.1 e.2) := by
  have he : (es.map fun e => edge e.1 e.2) = es.map canonicalEdge := rfl
  rw [he, canonicalEdges_eq_flipEdges]
  exact h.flipEdges _

/-- **Contracting an edge** `(s, t)`, `s ≠ t`, of an outerplanar embedding: one copy of it is
removed and `t` is renamed `s` (given Euler's inequality, through the reordering). -/
theorem OuterplanarEmbedding.contract {V : Type} [DecidableEq V] {es : List (V × V)} {s t : V}
    (hst : s ≠ t) (hmem : (s, t) ∈ es) (h : OuterplanarEmbedding es) :
    OuterplanarEmbedding ((es.erase (s, t)).map fun e => (renameTo s t e.1, renameTo s t e.2)) := by
  have hp : es.Perm (es.erase (s, t) ++ [(s, t)]) :=
    (List.perm_cons_erase hmem).trans (List.perm_append_singleton _ _).symm
  exact OuterplanarEmbedding.contractLast hst (OuterplanarEmbedding.perm hp h)

end STACS2027

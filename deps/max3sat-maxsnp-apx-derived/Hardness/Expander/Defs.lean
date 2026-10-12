module

/-!
# Explicit expander families in plain list form

`IsExpanderFamily D c G`: for every `k ≥ 1`, `G k` is a `D`-regular symmetric multigraph on
between `k` and `c * k` vertices, given by neighbour lists, in which every set of at most half
the vertices has at least as many outgoing arcs as elements. Self-loops and parallel arcs are
allowed. This file is core-only.
-/

@[expose] public section

namespace Complexity

/-- `G k` is a multigraph given by neighbour lists (`(G k).getD v []` lists the heads of the arcs
leaving `v`). -/
structure IsExpanderFamily (D c : Nat) (G : Nat → List (List Nat)) : Prop where
  size_ge : ∀ k, 1 ≤ k → k ≤ (G k).length
  size_le : ∀ k, 1 ≤ k → (G k).length ≤ c * k
  degree : ∀ k, ∀ row ∈ G k, row.length = D
  range : ∀ k, ∀ row ∈ G k, ∀ u ∈ row, u < (G k).length
  /-- as many arcs from `v` to `u` as from `u` to `v` -/
  symm : ∀ k v u, ((G k).getD v []).count u = ((G k).getD u []).count v
  /-- every set of at most half the vertices has at least as many arcs leaving it as elements -/
  expand : ∀ k (S : List Nat), S.Nodup → (∀ v ∈ S, v < (G k).length) → 2 * S.length ≤ (G k).length →
    S.length ≤ (S.flatMap fun v => ((G k).getD v []).filter fun u => decide (u ∉ S)).length

end Complexity

module

public import NPHardness.PlanarSourceEmbeddingGraph
public import Complexity.Planar.Incidence

/-! Extract the two incidence rotations from a registered hypermap. -/

@[expose] public section
namespace STACS2027.PlanarSource.Embedding
open Complexity Complexity.Planar STACS2027.PlanarGluing

def nodePred {n : Nat} (G : Hypermap n) (d : Fin n) : Fin n := G.face (G.edge d)

theorem node_nodePred {n : Nat} (G : Hypermap n) (d : Fin n) :
    G.node (nodePred G d) = d := G.edgeK d

theorem nodePred_node {n : Nat} (G : Hypermap n) (d : Fin n) :
    nodePred G (G.node d) = d := by
  apply hm_node_inj G
  exact node_nodePred G (G.node d)

theorem node_dart {E : Nat} (G : Hypermap (2 * E))
    (hpar : ∀ d, (G.node d).val % 2 = d.val % 2) (i : Fin E) (t : Fin 2) :
    G.node (d2 i t) = d2 (index 2 (by decide) (G.node (d2 i t))) t := by
  have he := dart_index 2 (by decide) (G.node (d2 i t))
  have ht : (⟨(G.node (d2 i t)).val % 2, Nat.mod_lt _ (by decide)⟩ : Fin 2) = t := by
    apply Fin.ext
    change (G.node (d2 i t)).val % 2 = t.val
    rw [hpar, dart_mod]
  rw [ht] at he
  exact he.symm

theorem nodePred_dart {E : Nat} (G : Hypermap (2 * E))
    (hpar : ∀ d, (G.node d).val % 2 = d.val % 2) (i : Fin E) (t : Fin 2) :
    nodePred G (d2 i t) = d2 (index 2 (by decide) (nodePred G (d2 i t))) t := by
  have he := dart_index 2 (by decide) (nodePred G (d2 i t))
  have hp := hpar (nodePred G (d2 i t))
  rw [node_nodePred, dart_mod] at hp
  have ht : (⟨(nodePred G (d2 i t)).val % 2, Nat.mod_lt _ (by decide)⟩ : Fin 2) = t :=
    Fin.ext hp.symm
  rw [ht] at he
  exact he.symm

def blockRotation {E : Nat} (G : Hypermap (2 * E))
    (hpar : ∀ d, (G.node d).val % 2 = d.val % 2) (t : Fin 2) : DartEquiv E E where
  toFun i := index 2 (by decide) (G.node (d2 i t))
  invFun i := index 2 (by decide) (nodePred G (d2 i t))
  left_inv i := by
    rw [← node_dart G hpar, nodePred_node, index_dart]
  right_inv i := by
    rw [← nodePred_dart G hpar, node_nodePred, index_dart]

def fromHypermap {E : Nat} (G : Hypermap (2 * E))
    (hpar : ∀ d, (G.node d).val % 2 = d.val % 2) : BipartiteRotation E where
  varRot := blockRotation G hpar 0
  clause := blockRotation G hpar 1

theorem blockRotation_iterate {E : Nat} (G : Hypermap (2 * E))
    (hpar : ∀ d, (G.node d).val % 2 = d.val % 2) (t : Fin 2) (k : Nat) (i : Fin E) :
    iterate G.node k (d2 i t) = d2 (iterate (blockRotation G hpar t).toFun k i) t := by
  induction k generalizing i with
  | zero => rfl
  | succ k ih =>
    simp only [iterate]
    rw [node_dart G hpar, ih]
    rfl

theorem blockRotation_orbit {E : Nat} (G : Hypermap (2 * E))
    (hpar : ∀ d, (G.node d).val % 2 = d.val % 2) (t : Fin 2) (i j : Fin E) :
    STACS2027.PlanarGluing.Reaches (blockRotation G hpar t).toFun i j ↔
      ∃ k, iterate G.node k (d2 i t) = d2 j t := by
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, by rw [blockRotation_iterate G hpar, hk]⟩
  · rintro ⟨k, hk⟩
    rw [blockRotation_iterate G hpar] at hk
    exact ⟨k, dart_injective (by decide) t hk⟩

theorem fromHypermap_node {E : Nat} (G : Hypermap (2 * E))
    (hpar : ∀ d, (G.node d).val % 2 = d.val % 2) :
    ∀ d, (fromHypermap G hpar).original.node d = G.node d := by
  apply two_cases
  intro i
  constructor <;> simp [BipartiteRotation.original, BipartiteRotation.oldNode,
    fromHypermap, blockRotation, d2] <;> exact (node_dart G hpar _ _).symm

theorem fromHypermap_edge {E : Nat} (G : Hypermap (2 * E))
    (hpar : ∀ d, (G.node d).val % 2 = d.val % 2)
    (hedge : ∀ d, (G.edge d).val = cond (Nat.beq (d.val % 2) 0) (d.val + 1) (d.val - 1)) :
    ∀ d, (fromHypermap G hpar).original.edge d = G.edge d := by
  apply two_cases
  intro i
  constructor <;> apply Fin.ext <;> rw [hedge] <;>
    simp [BipartiteRotation.original, BipartiteRotation.oldEdge, d2] <;> simp [dart]

theorem hypermap_eq_of_edge_node {n : Nat} (G H : Hypermap n)
    (he : ∀ d, G.edge d = H.edge d) (hn : ∀ d, G.node d = H.node d) : G = H := by
  have hf : ∀ d, G.face d = H.face d := by
    intro d
    obtain ⟨x, rfl⟩ := hm_edge_surj G d
    apply hm_node_inj G
    rw [G.edgeK, hn, he, H.edgeK]
  have heq := funext he
  have hnq := funext hn
  have hfq := funext hf
  cases G
  cases H
  cases heq
  cases hnq
  cases hfq
  rfl

/-- Extraction retains the actual registered embedding, including faces. -/
theorem fromHypermap_original {E : Nat} (G : Hypermap (2 * E))
    (hpar : ∀ d, (G.node d).val % 2 = d.val % 2)
    (hedge : ∀ d, (G.edge d).val = cond (Nat.beq (d.val % 2) 0) (d.val + 1) (d.val - 1)) :
    (fromHypermap G hpar).original = G :=
  hypermap_eq_of_edge_node _ G (fromHypermap_edge G hpar hedge) (fromHypermap_node G hpar)

theorem halfEdgeEnd_d2_zero {V : Type} (es : List (V × V)) (i : Fin es.length) :
    halfEdgeEnd es (d2 i 0).val = some es[i.val].1 := by
  simp [halfEdgeEnd, d2, dart]

theorem halfEdgeEnd_d2_one {V : Type} (es : List (V × V)) (i : Fin es.length) :
    halfEdgeEnd es (d2 i 1).val = some es[i.val].2 := by
  have hi : (2 * i.val + 1) / 2 = i.val := by omega
  simp [halfEdgeEnd, d2, dart, hi]

def bipartiteSide {V C : Type} : Sum V C → Nat
  | .inl _ => 0
  | .inr _ => 1

theorem halfEdgeEnd_side {V C : Type} (es : List (Sum V C × Sum V C))
    (varLabel : Fin es.length → V) (clauseLabel : Fin es.length → C)
    (hends : ∀ i : Fin es.length, es[i.val] = (.inl (varLabel i), .inr (clauseLabel i))) :
    ∀ d : Fin (2 * es.length), (halfEdgeEnd es d.val).map bipartiteSide = some (d.val % 2) := by
  apply two_cases
  intro i
  constructor
  · rw [halfEdgeEnd_d2_zero, hends]
    simp [d2, bipartiteSide]
  · rw [halfEdgeEnd_d2_one, hends]
    simp [d2, bipartiteSide]

theorem incidence_node_parity {V C : Type} (es : List (Sum V C × Sum V C))
    (varLabel : Fin es.length → V) (clauseLabel : Fin es.length → C)
    (hends : ∀ i : Fin es.length, es[i.val] = (.inl (varLabel i), .inr (clauseLabel i)))
    (G : Hypermap (2 * es.length))
    (horbit : ∀ d d', (∃ k, iterate G.node k d = d') ↔
      halfEdgeEnd es d.val = halfEdgeEnd es d'.val) :
    ∀ d, (G.node d).val % 2 = d.val % 2 := by
  intro d
  have he := (horbit d (G.node d)).mp ⟨1, rfl⟩
  have hs := congrArg (fun z => z.map bipartiteSide) he
  rw [halfEdgeEnd_side es varLabel clauseLabel hends,
    halfEdgeEnd_side es varLabel clauseLabel hends] at hs
  exact (Option.some.inj hs).symm

end STACS2027.PlanarSource.Embedding

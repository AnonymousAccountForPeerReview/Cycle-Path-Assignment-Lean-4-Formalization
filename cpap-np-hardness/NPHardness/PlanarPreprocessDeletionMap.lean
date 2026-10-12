module

public import NPHardness.PlanarPreprocessDeletionPerm
public import NPHardness.PlanarGluingTransposition

/-! Index lemmas for excising the two darts of the last edge from a hypermap. -/

@[expose] public section
namespace STACS2027.PlanarPreprocess.Deletion
open Complexity Complexity.Planar STACS2027.PlanarGluing

def penultimate (n : Nat) : Fin (n+2) := embed (last n)

theorem penultimate_ne_last (n : Nat) : penultimate n ≠ last (n+1) := embed_ne_last _

theorem embedPair_ne_penultimate {n : Nat} (x : Fin n) : embedPair x ≠ penultimate n := by
  intro h
  exact embed_ne_last x (embed_injective h)

theorem embedPair_ne_last {n : Nat} (x : Fin n) : embedPair x ≠ last (n+1) := embed_ne_last _

theorem embed_removePair_of_avoids {n : Nat} {p : Fin (n+2) → Fin (n+2)}
    (hp : ∀ x y, p x = p y → x = y) (x : Fin n)
    (ha : p (embedPair x) ≠ penultimate n) (hb : p (embedPair x) ≠ last (n+1)) :
    embedPair (removePair p hp x) = p (embedPair x) := by
  have hfirst : embed (removeLast p hp (embed x)) = p (embedPair x) := by
    rw [embed_removeLast]
    change skipLast p (embedPair x) = p (embedPair x)
    simp [skipLast,hb]
  have hne : removeLast p hp (embed x) ≠ last n := by
    intro he
    rw [he] at hfirst
    exact ha hfirst.symm
  change embed (embed (removeLast (removeLast p hp) (removeLast_injective hp) x)) = p (embedPair x)
  rw [embed_removeLast]
  simp only [skipLast,hne,↓reduceIte]
  exact hfirst

def nodeInverse {n : Nat} (G : Hypermap n) (x : Fin n) : Fin n := G.face (G.edge x)

theorem nodeInverse_injective {n : Nat} (G : Hypermap n) :
    ∀ x y, nodeInverse G x = nodeInverse G y → x = y := by
  intro x y h
  exact hm_edge_inj G x y (hm_face_inj G _ _ h)

theorem node_nodeInverse {n : Nat} (G : Hypermap n) (x : Fin n) : G.node (nodeInverse G x) = x := G.edgeK x

end STACS2027.PlanarPreprocess.Deletion

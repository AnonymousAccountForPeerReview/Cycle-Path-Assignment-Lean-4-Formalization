module

public import NPHardness.PlanarSourceEmbeddingExtract
public import Complexity.Planar.GridTarget

/-!
Executable data for the registered comb embedding. The registered `nxt` and
`prv` definitions use a classical decider for a decidable arithmetic test.
Here that test is made explicit; equality with the registered hypermap lets
all geometric certificates be reused. This is computational data, not a
polynomial-time implementation theorem.
-/

@[expose] public section
namespace STACS2027.PlanarSource.ComputableComb
open Complexity Complexity.SAT Complexity.Planar Comb

/-- A registered graph embedding with its actual map retained as data. -/
structure GraphEmbedding {V : Type} (es : List (V × V)) where
  map : Hypermap (2 * es.length)
  edge_pair : ∀ d, (map.edge d).val =
    cond (Nat.beq (d.val % 2) 0) (d.val + 1) (d.val - 1)
  node_orbit : ∀ d d', (∃ k, iterate map.node k d = d') ↔
    halfEdgeEnd es d.val = halfEdgeEnd es d'.val
  planar : map.Planar

/-- The computable branch test is definitionally the same finite predicate. -/
def next (f : CNF) (d : Nat) : Nat :=
  if d < 2 * nM f ∧ d % 2 = 1 then clNext f d else rnext (rot f (vtx f d)) d

def prev (f : CNF) (d : Nat) : Nat :=
  if d < 2 * nM f ∧ d % 2 = 1 then clPrev f d else rprev (rot f (vtx f d)) d

@[simp] theorem next_eq (f : CNF) (d : Nat) : next f d = nxt f d := by
  unfold next nxt isCl
  by_cases hc : d < 2 * nM f ∧ d % 2 = 1 <;> simp [hc]

@[simp] theorem prev_eq (f : CNF) (d : Nat) : prev f d = prv f d := by
  unfold prev prv isCl
  by_cases hc : d < 2 * nM f ∧ d % 2 = 1 <;> simp [hc]

/-- Executable copy of the registered comb hypermap. -/
def map {f : CNF} (h : CombOK f) :
    Hypermap (2 * (incidenceGraph f ++ variableCycle f).length) where
  edge d := ⟨Complexity.Planar.ed d.val, lt_darts h (Comb.ed_lt h (dart_lt h d))⟩
  node d := ⟨next f d.val, by rw [next_eq]; exact lt_darts h (nxt_spec h (dart_lt h d)).1⟩
  face d := ⟨prev f (Complexity.Planar.ed d.val), by
    rw [prev_eq]
    exact lt_darts h (nxt_spec h (Comb.ed_lt h (dart_lt h d))).2.1⟩
  edgeK d := by
    apply Fin.ext
    simp only [Comb.ed_ed, next_eq, prev_eq]
    exact (nxt_spec h (dart_lt h d)).2.2.1

@[simp] theorem map_eq {f : CNF} (h : CombOK f) : map h = hmap h := by
  apply Embedding.hypermap_eq_of_edge_node
  · intro d; rfl
  · intro d; apply Fin.ext; exact next_eq f d.val

theorem registered_node_orbit {f : CNF} (h : CombOK f)
    (d d' : Fin (2 * (incidenceGraph f ++ variableCycle f).length)) :
    (∃ k, iterate (hmap h).node k d = d') ↔
      halfEdgeEnd (incidenceGraph f ++ variableCycle f) d.val =
      halfEdgeEnd (incidenceGraph f ++ variableCycle f) d'.val := by
  rw [end_eq h (dart_lt h d), end_eq h (dart_lt h d')]
  constructor
  · rintro ⟨k, hk⟩
    have he := (iterate_end h (dart_lt h d) k).2
    rw [← iterate_val h, hk] at he
    rw [he]
  · intro he
    simp only [Option.some.injEq] at he
    obtain ⟨k, hk⟩ := reach_of_end h (dart_lt h d) (dart_lt h d') he
    exact ⟨k, Fin.ext (by rw [iterate_val h]; exact hk)⟩

theorem registered_planar {f : CNF} (h : CombOK f) : (hmap h).Planar := by
  apply planar_of_bounds _ (nM f + nK f) (nK f + f.length) (nM f - f.length + 1) 1
  · have he := cycleCount_graphEdge_ge (E := (incidenceGraph f ++ variableCycle f).length)
      (edge := (hmap h).edge) (fun d => rfl)
    have he' := es_length (f := f)
    omega
  · exact nodes_ge h
  · exact faces_ge h
  · exact components_le h
  · have hm := m_le_M h
    have he := es_length (f := f)
    omega

/-- The registered comb embedding, now available without classical choice. -/
def embedding {f : CNF} (h : CombOK f) :
    GraphEmbedding (incidenceGraph f ++ variableCycle f) where
  map := map h
  edge_pair d := rfl
  node_orbit d d' := by rw [map_eq]; exact registered_node_orbit h d d'
  planar := by rw [map_eq]; exact registered_planar h

@[simp] theorem embedding_node {f : CNF} (h : CombOK f)
    (d : Fin (2 * (incidenceGraph f ++ variableCycle f).length)) :
    ((embedding h).map.node d).val = next f d.val := rfl

/-- A concrete registered grid embedding; no existential witness is selected. -/
def gridEmbedding (W m : Nat) (bits : Nat → Nat → Bool × Bool) (hm : 1 ≤ m) :
    GraphEmbedding (incidenceGraph (Grid.gridCNF W m bits) ++
      variableCycle (Grid.gridCNF W m bits)) :=
  embedding (Grid.gridCNF_combOK hm bits)

end STACS2027.PlanarSource.ComputableComb

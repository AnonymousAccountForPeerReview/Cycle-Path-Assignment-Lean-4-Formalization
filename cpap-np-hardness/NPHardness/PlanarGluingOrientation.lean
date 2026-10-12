module

public import NPHardness.PlanarGluingLists
import Lean.Elab.Tactic.Omega

/-! Independent reversals of the stored endpoints of edges do not change
the registered undirected planarity predicate. No simplicity hypothesis
is needed, and parallel edges may be reversed independently. -/

@[expose] public section
namespace STACS2027.PlanarGluing
open Complexity Complexity.Planar

def flipEdge {V : Type} (b : Bool) (e : V × V) : V × V :=
  if b then (e.2, e.1) else e

def flipEdges {V : Type} (es : List (V × V)) (flips : Nat → Bool) : List (V × V) :=
  es.zipIdx.map fun p => flipEdge (flips p.2) p.1

@[simp] theorem flipEdges_length {V : Type} (es : List (V × V)) (flips : Nat → Bool) :
    (flipEdges es flips).length = es.length := by simp [flipEdges]

theorem flipEdges_getElem {V : Type} (es : List (V × V)) (flips : Nat → Bool)
    (i : Nat) (hi : i < es.length) :
    (flipEdges es flips)[i]'(by simpa using hi) = flipEdge (flips i) es[i] := by
  simp [flipEdges, List.getElem_zipIdx]

theorem flipEdge_twice {V : Type} (b : Bool) (e : V × V) : flipEdge b (flipEdge b e) = e := by
  cases b <;> cases e <;> rfl

theorem flipEdges_twice {V : Type} (es : List (V × V)) (flips : Nat → Bool) :
    flipEdges (flipEdges es flips) flips = es := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    rw [flipEdges_getElem _ _ i (by simpa using hi), flipEdges_getElem _ _ i hi', flipEdge_twice]

theorem graphEdge_twice {n : Nat} (d : Fin (2 * n)) : graphEdge (graphEdge d) = d := by
  apply Fin.ext
  simp only [graphEdge]
  rcases Nat.mod_two_eq_zero_or_one d.val with h | h
  · simp [ed, h, show (d.val + 1) % 2 = 1 by omega]
  · simp [ed, h, show (d.val - 1) % 2 = 0 by omega]
    omega

def flipDart {n : Nat} (flips : Nat → Bool) (d : Fin (2 * n)) : Fin (2 * n) :=
  if flips (d.val / 2) then graphEdge d else d

theorem flipDart_index {n : Nat} (flips : Nat → Bool) (d : Fin (2 * n)) :
    (flipDart flips d).val / 2 = d.val / 2 := by
  unfold flipDart
  cases h : flips (d.val / 2)
  · rfl
  · exact congrArg Fin.val (edgeIndex_graphEdge d)

theorem flipDart_twice {n : Nat} (flips : Nat → Bool) (d : Fin (2 * n)) :
    flipDart flips (flipDart flips d) = d := by
  unfold flipDart
  cases h : flips (d.val / 2)
  · simp [h]
  · have he : (graphEdge d).val / 2 = d.val / 2 := congrArg Fin.val (edgeIndex_graphEdge d)
    simp [h, he, graphEdge_twice]

theorem flipDart_edge {n : Nat} (flips : Nat → Bool) (d : Fin (2 * n)) :
    flipDart flips (graphEdge d) = graphEdge (flipDart flips d) := by
  have he : (graphEdge d).val / 2 = d.val / 2 := congrArg Fin.val (edgeIndex_graphEdge d)
  unfold flipDart
  rw [he]
  cases h : flips (d.val / 2) <;> simp

def flipDartEquiv (n : Nat) (flips : Nat → Bool) : DartEquiv (2 * n) (2 * n) :=
  ⟨flipDart flips, flipDart flips, flipDart_twice flips, flipDart_twice flips⟩

theorem flipDart_ends {V : Type} (es : List (V × V)) (flips : Nat → Bool)
    (d : Fin (2 * es.length)) :
    halfEdgeEnd (flipEdges es flips) (flipDart flips d).val = halfEdgeEnd es d.val := by
  have hi : d.val / 2 < es.length := by have := d.isLt; omega
  unfold halfEdgeEnd
  rw [flipDart_index, List.getElem?_eq_getElem (by simpa using hi),
    flipEdges_getElem _ _ _ hi, List.getElem?_eq_getElem hi]
  cases hb : flips (d.val / 2) <;> rcases Nat.mod_two_eq_zero_or_one d.val with he | he
  · simp [flipDart, flipEdge, hb, he]
  · simp [flipDart, flipEdge, hb, he]
  · simp [flipDart, flipEdge, hb, he, graphEdge, ed, show (d.val + 1) % 2 = 1 by omega]
  · simp [flipDart, flipEdge, hb, he, graphEdge, ed, show (d.val - 1) % 2 = 0 by omega]

theorem planarGraph_flipEdges_forward {V : Type} {es : List (V × V)}
    (flips : Nat → Bool) (h : PlanarGraph es) : PlanarGraph (flipEdges es flips) := by
  obtain ⟨G, hE, hN, hP⟩ := h
  unfold PlanarGraph
  rw [flipEdges_length]
  let e := flipDartEquiv es.length flips
  have he : ∀ d, G.edge d = graphEdge d := fun d => Fin.ext (hE d)
  refine ⟨e.hypermap G, ?_, ?_, e.planar G hP⟩
  · intro y
    change (flipDart flips (G.edge (flipDart flips y))).val = _
    rw [he, flipDart_edge, flipDart_twice]
    rfl
  · intro y y'
    have hn : (∃ k, iterate (e.conjugate G.node) k y = y') ↔
        ∃ k, iterate G.node k (e.invFun y) = e.invFun y' := by
      constructor
      · rintro ⟨k, hk⟩
        rw [e.iterate_conjugate] at hk
        exact ⟨k, by have := congrArg e.invFun hk; simpa only [e.left_inv] using this⟩
      · rintro ⟨k, hk⟩
        exact ⟨k, by rw [e.iterate_conjugate, hk, e.right_inv]⟩
    change (∃ k, iterate (e.conjugate G.node) k y = y') ↔ _
    rw [hn, hN]
    have hy := flipDart_ends es flips (flipDart flips y)
    have hy' := flipDart_ends es flips (flipDart flips y')
    rw [flipDart_twice] at hy hy'
    change halfEdgeEnd es (flipDart flips y).val = halfEdgeEnd es (flipDart flips y').val ↔ _
    rw [← hy, ← hy']

/-- Every edge can independently have its stored orientation reversed. -/
theorem planarGraph_flipEdges {V : Type} (es : List (V × V)) (flips : Nat → Bool) :
    PlanarGraph (flipEdges es flips) ↔ PlanarGraph es := by
  constructor
  · intro h
    have := planarGraph_flipEdges_forward flips h
    simpa only [flipEdges_twice] using this
  · exact planarGraph_flipEdges_forward flips

def canonicalEdge (e : Nat × Nat) : Nat × Nat := (min e.1 e.2, max e.1 e.2)

theorem canonicalEdges_eq_flipEdges (es : List (Nat × Nat)) :
    es.map canonicalEdge = flipEdges es (fun i =>
      match es[i]? with
      | none => false
      | some (a, b) => decide (b < a)) := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    have hie : i < es.length := by simpa using hi
    simp only [List.getElem_map, flipEdges_getElem _ _ i hie,
      List.getElem?_eq_getElem hie]
    change canonicalEdge es[i] = flipEdge (decide (es[i].2 < es[i].1)) es[i]
    by_cases h : es[i].2 < es[i].1
    · simp [canonicalEdge, flipEdge, h, Nat.min_eq_right (by omega : es[i].2 ≤ es[i].1),
        Nat.max_eq_left (by omega : es[i].2 ≤ es[i].1)]
    · simp [canonicalEdge, flipEdge, h, Nat.min_eq_left (by omega : es[i].1 ≤ es[i].2),
        Nat.max_eq_right (by omega : es[i].1 ≤ es[i].2)]

/-- Sorting the two ends of every natural-number edge preserves planarity. -/
theorem planarGraph_canonical (es : List (Nat × Nat)) :
    PlanarGraph (es.map canonicalEdge) ↔ PlanarGraph es := by
  rw [canonicalEdges_eq_flipEdges]
  exact planarGraph_flipEdges _ _

end STACS2027.PlanarGluing

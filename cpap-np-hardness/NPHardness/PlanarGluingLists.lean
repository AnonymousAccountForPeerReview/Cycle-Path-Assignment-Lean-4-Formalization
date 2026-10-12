module

public import NPHardness.PlanarGluingTransport
import Lean.Elab.Tactic.Omega

/-! Edge-list permutations preserve the registered planarity predicate,
including lists containing repeated edges and loops. -/

@[expose] public section
namespace STACS2027.PlanarGluing
open Complexity Complexity.Planar

def liftIndex {n m : Nat} (f : Fin n → Fin m) (i : Fin (n + 1)) : Fin (m + 1) :=
  if h : i.val = 0 then ⟨0, by omega⟩ else
    ⟨(f ⟨i.val - 1, by omega⟩).val + 1, by have := (f ⟨i.val - 1, by omega⟩).isLt; omega⟩

theorem liftIndex_inverse {n m : Nat} (f : Fin n → Fin m) (g : Fin m → Fin n)
    (hgf : ∀ i, g (f i) = i) (i : Fin (n + 1)) : liftIndex g (liftIndex f i) = i := by
  by_cases hi : i.val = 0
  · apply Fin.ext; simp [liftIndex, hi]
  · unfold liftIndex
    rw [dite_eq_right hi, dite_eq_right (by simp)]
    have he : (⟨(f ⟨i.val - 1, by omega⟩).val + 1 - 1, by
      have := (f ⟨i.val - 1, by omega⟩).isLt; omega⟩ : Fin m) = f ⟨i.val - 1, by omega⟩ :=
      Fin.ext (by simp)
    simp only [he, hgf]
    apply Fin.ext; simp; omega

def DartEquiv.cons {n m : Nat} (e : DartEquiv n m) : DartEquiv (n + 1) (m + 1) where
  toFun := liftIndex e.toFun
  invFun := liftIndex e.invFun
  left_inv := liftIndex_inverse e.toFun e.invFun e.left_inv
  right_inv := liftIndex_inverse e.invFun e.toFun e.right_inv

structure IndexEquiv {α : Type} (as bs : List α) where
  indices : DartEquiv as.length bs.length
  values : ∀ i : Fin as.length, bs[(indices.toFun i).val]? = as[i.val]?

namespace IndexEquiv
variable {α : Type} {as bs cs : List α}

def refl (as : List α) : IndexEquiv as as := ⟨DartEquiv.refl _, fun _ => rfl⟩

def trans (e : IndexEquiv as bs) (f : IndexEquiv bs cs) : IndexEquiv as cs where
  indices := e.indices.trans f.indices
  values i := (f.values (e.indices.toFun i)).trans (e.values i)

def cons (a : α) (e : IndexEquiv as bs) : IndexEquiv (a :: as) (a :: bs) where
  indices := e.indices.cons
  values i := by
    by_cases hi : i.val = 0
    · simp [DartEquiv.cons, liftIndex, hi]
    · have hij : i.val = (i.val - 1) + 1 := by omega
      change (a :: bs)[(liftIndex e.indices.toFun i).val]? = (a :: as)[i.val]?
      simp only [liftIndex, dite_eq_right hi]
      rw [List.getElem?_cons_succ]
      conv => rhs; rw [hij, List.getElem?_cons_succ]
      exact e.values ⟨i.val - 1, by have hil : i.val < as.length + 1 := i.isLt; omega⟩

def swapHead (a b : α) (as : List α) : IndexEquiv (a :: b :: as) (b :: a :: as) where
  indices := {
    toFun := swap ⟨0, by simp⟩ ⟨1, by simp⟩
    invFun := swap ⟨0, by simp⟩ ⟨1, by simp⟩
    left_inv := fun i => swap_swap _ _ i
    right_inv := fun i => swap_swap _ _ i }
  values i := by
    by_cases h0 : i.val = 0
    · have he : i = ⟨0, by simp⟩ := Fin.ext h0
      simp [swap, he]
    · by_cases h1 : i.val = 1
      · have he : i = ⟨1, by simp⟩ := Fin.ext h1
        simp [swap, he]
      · have he0 : i ≠ ⟨0, by simp⟩ := fun h => h0 (congrArg Fin.val h)
        have he1 : i ≠ ⟨1, by simp⟩ := fun h => h1 (congrArg Fin.val h)
        simp only [swap, ite_eq_right he0, ite_eq_right he1]
        have hi : i.val = (i.val - 2) + 1 + 1 := by omega
        rw [hi, List.getElem?_cons_succ, List.getElem?_cons_succ,
          List.getElem?_cons_succ, List.getElem?_cons_succ]

theorem of_perm (h : as.Perm bs) : Nonempty (IndexEquiv as bs) := by
  induction h with
  | nil => exact ⟨refl []⟩
  | cons a _ ih => obtain ⟨e⟩ := ih; exact ⟨e.cons a⟩
  | swap a b as => exact ⟨swapHead b a as⟩
  | trans _ _ ih₁ ih₂ => obtain ⟨e⟩ := ih₁; obtain ⟨f⟩ := ih₂; exact ⟨e.trans f⟩

end IndexEquiv

def edgeIndex {n : Nat} (d : Fin (2 * n)) : Fin n := ⟨d.val / 2, by have := d.isLt; omega⟩

def liftDart {n m : Nat} (f : Fin n → Fin m) (d : Fin (2 * n)) : Fin (2 * m) :=
  ⟨2 * (f (edgeIndex d)).val + d.val % 2, by
    have := (f (edgeIndex d)).isLt
    have := Nat.mod_lt d.val (by decide : 0 < 2)
    omega⟩

@[simp] theorem edgeIndex_liftDart {n m : Nat} (f : Fin n → Fin m) (d : Fin (2 * n)) :
    edgeIndex (liftDart f d) = f (edgeIndex d) := by
  apply Fin.ext
  simp only [edgeIndex, liftDart]
  omega

theorem liftDart_mod {n m : Nat} (f : Fin n → Fin m) (d : Fin (2 * n)) :
    (liftDart f d).val % 2 = d.val % 2 := by simp [liftDart, Nat.add_mod]

theorem liftDart_inverse {n m : Nat} (f : Fin n → Fin m) (g : Fin m → Fin n)
    (hgf : ∀ i, g (f i) = i) (d : Fin (2 * n)) : liftDart g (liftDart f d) = d := by
  apply Fin.ext
  change 2 * (g (edgeIndex (liftDart f d))).val + (liftDart f d).val % 2 = d.val
  rw [edgeIndex_liftDart, hgf, liftDart_mod]
  simp only [edgeIndex]
  omega

def DartEquiv.darts {n m : Nat} (e : DartEquiv n m) : DartEquiv (2 * n) (2 * m) where
  toFun := liftDart e.toFun
  invFun := liftDart e.invFun
  left_inv := liftDart_inverse e.toFun e.invFun e.left_inv
  right_inv := liftDart_inverse e.invFun e.toFun e.right_inv

theorem edgeIndex_graphEdge {n : Nat} (d : Fin (2 * n)) :
    edgeIndex (graphEdge d) = edgeIndex d := by
  apply Fin.ext
  simp only [edgeIndex, graphEdge]
  rcases Nat.mod_two_eq_zero_or_one d.val with h | h <;> simp [ed, h] <;> omega

theorem liftDart_graphEdge {n m : Nat} (f : Fin n → Fin m) (d : Fin (2 * n)) :
    liftDart f (graphEdge d) = graphEdge (liftDart f d) := by
  apply Fin.ext
  change 2 * (f (edgeIndex (graphEdge d))).val + (graphEdge d).val % 2 = ed (liftDart f d).val
  rw [edgeIndex_graphEdge]
  simp only [graphEdge]
  rcases Nat.mod_two_eq_zero_or_one d.val with h | h
  · simp [ed, h, liftDart]
    omega
  · simp [ed, h, liftDart]
    omega

def IndexEquiv.graphDarts {V : Type} {es ts : List (V × V)} (e : IndexEquiv es ts) :
    GraphDartEquiv es ts where
  darts := e.indices.darts
  edge := liftDart_graphEdge e.indices.toFun
  ends d := by
    change halfEdgeEnd ts (liftDart e.indices.toFun d).val = halfEdgeEnd es d.val
    unfold halfEdgeEnd
    have hd : d.val / 2 < es.length := (edgeIndex d).isLt
    have he : (liftDart e.indices.toFun d).val / 2 = (e.indices.toFun (edgeIndex d)).val :=
      congrArg Fin.val (edgeIndex_liftDart _ _)
    rw [he, e.values (edgeIndex d), liftDart_mod]
    rfl

/-- Reordering the edge list preserves planarity; multiplicities are retained. -/
theorem planarGraph_perm {V : Type} {es ts : List (V × V)} (h : es.Perm ts) :
    PlanarGraph es ↔ PlanarGraph ts := by
  obtain ⟨e⟩ := IndexEquiv.of_perm h
  obtain ⟨f⟩ := IndexEquiv.of_perm h.symm
  exact ⟨e.graphDarts.planar, f.graphDarts.planar⟩

end STACS2027.PlanarGluing

module

public import NPHardness.PlanarGluingTransport
public import NPHardness.PlanarSourceCycles
public import NPHardness.BoundedSAT
public import Complexity.Restricted.Occurrence
public import Complexity.Planar.Perm

/-!
Explicit dart permutations for replacing the variable vertices of a
bipartite incidence embedding by implication cycles. An old incidence edge
has two darts; its replacement has six, for the original incidence and the
two incidences of the implication clause. The node and face tables are
defined here rather than assuming a planar replacement operation.
-/

@[expose] public section
namespace STACS2027.PlanarSource.Embedding
open Complexity Complexity.Planar STACS2027.PlanarGluing

structure BipartiteRotation (E : Nat) where
  varRot : DartEquiv E E
  clause : DartEquiv E E

def dart {E : Nat} (k : Nat) (_hk : 0 < k) (i : Fin E) (t : Fin k) : Fin (k * E) :=
  ⟨k * i.val + t.val, by
    have h := Nat.mul_le_mul_left k i.isLt
    rw [Nat.mul_succ] at h
    have := t.isLt
    omega⟩

def index {E : Nat} (k : Nat) (hk : 0 < k) (d : Fin (k * E)) : Fin E :=
  ⟨d.val / k, by have := d.isLt; exact (Nat.div_lt_iff_lt_mul hk).mpr (by simpa only [Nat.mul_comm] using d.isLt)⟩

@[simp] theorem index_dart {E : Nat} (k : Nat) (hk : 0 < k) (i : Fin E) (t : Fin k) :
    index k hk (dart k hk i t) = i := by
  apply Fin.ext
  simp only [index, dart]
  rw [Nat.mul_add_div hk, Nat.div_eq_of_lt t.isLt, Nat.add_zero]

@[simp] theorem dart_mod {E : Nat} (k : Nat) (hk : 0 < k) (i : Fin E) (t : Fin k) :
    (dart k hk i t).val % k = t.val := by
  simp only [dart, Nat.mul_add_mod, Nat.mod_eq_of_lt t.isLt]

theorem dart_index {E : Nat} (k : Nat) (hk : 0 < k) (d : Fin (k * E)) :
    dart k hk (index k hk d) ⟨d.val % k, Nat.mod_lt _ hk⟩ = d := by
  apply Fin.ext
  exact Nat.div_add_mod d.val k

abbrev d2 {E : Nat} (i : Fin E) (t : Fin 2) := dart 2 (by decide) i t
abbrev d6 {E : Nat} (i : Fin E) (t : Fin 6) := dart 6 (by decide) i t

theorem two_cases {E : Nat} (P : Fin (2 * E) → Prop)
    (h : ∀ i, P (d2 i 0) ∧ P (d2 i 1)) : ∀ d, P d := by
  intro d
  have ht := Nat.mod_lt d.val (by decide : 0 < 2)
  have he := dart_index 2 (by decide) d
  rcases (show d.val % 2 = 0 ∨ d.val % 2 = 1 by omega) with ht | ht
  · have hx : d2 (index 2 (by decide) d) 0 = d := by simpa [ht] using he
    rw [← hx]; exact (h _).1
  · have hx : d2 (index 2 (by decide) d) 1 = d := by simpa [ht] using he
    rw [← hx]; exact (h _).2

theorem six_cases {E : Nat} (P : Fin (6 * E) → Prop)
    (h : ∀ i, P (d6 i 0) ∧ P (d6 i 1) ∧ P (d6 i 2) ∧
      P (d6 i 3) ∧ P (d6 i 4) ∧ P (d6 i 5)) : ∀ d, P d := by
  intro d
  have ht := Nat.mod_lt d.val (by decide : 0 < 6)
  have he := dart_index 6 (by decide) d
  have hcases : d.val % 6 = 0 ∨ d.val % 6 = 1 ∨ d.val % 6 = 2 ∨
      d.val % 6 = 3 ∨ d.val % 6 = 4 ∨ d.val % 6 = 5 := by omega
  rcases hcases with ht | ht | ht | ht | ht | ht
  · have hx : d6 (index 6 (by decide) d) 0 = d := by simpa [ht] using he
    rw [← hx]; exact (h _).1
  · have hx : d6 (index 6 (by decide) d) 1 = d := by simpa [ht] using he
    rw [← hx]; exact (h _).2.1
  · have hx : d6 (index 6 (by decide) d) 2 = d := by simpa [ht] using he
    rw [← hx]; exact (h _).2.2.1
  · have hx : d6 (index 6 (by decide) d) 3 = d := by simpa [ht] using he
    rw [← hx]; exact (h _).2.2.2.1
  · have hx : d6 (index 6 (by decide) d) 4 = d := by simpa [ht] using he
    rw [← hx]; exact (h _).2.2.2.2.1
  · have hx : d6 (index 6 (by decide) d) 5 = d := by simpa [ht] using he
    rw [← hx]; exact (h _).2.2.2.2.2

namespace BipartiteRotation
variable {E : Nat} (B : BipartiteRotation E)

def oldEdge (d : Fin (2 * E)) : Fin (2 * E) :=
  if d.val % 2 = 0 then d2 (index 2 (by decide) d) 1 else d2 (index 2 (by decide) d) 0

def oldNode (d : Fin (2 * E)) : Fin (2 * E) :=
  if d.val % 2 = 0 then d2 (B.varRot.toFun (index 2 (by decide) d)) 0
  else d2 (B.clause.toFun (index 2 (by decide) d)) 1

def oldFace (d : Fin (2 * E)) : Fin (2 * E) :=
  if d.val % 2 = 0 then d2 (B.clause.invFun (index 2 (by decide) d)) 1
  else d2 (B.varRot.invFun (index 2 (by decide) d)) 0

def original : Hypermap (2 * E) where
  edge := oldEdge
  node := B.oldNode
  face := B.oldFace
  edgeK := two_cases _ (by
    intro i
    constructor <;> simp [oldEdge, oldNode, oldFace, d2, B.varRot.right_inv, B.clause.right_inv])

def newEdge (d : Fin (6 * E)) : Fin (6 * E) :=
  let i := index 6 (by decide) d
  match d.val % 6 with
  | 0 => d6 i 1
  | 1 => d6 i 0
  | 2 => d6 i 3
  | 3 => d6 i 2
  | 4 => d6 i 5
  | _ => d6 i 4

/-- Darts 0,2,5 are the copy-node incidences; 3,4 belong to the new
implication clause; dart 1 keeps the original clause rotation. -/
def newNode (d : Fin (6 * E)) : Fin (6 * E) :=
  let i := index 6 (by decide) d
  match d.val % 6 with
  | 0 => d6 i 2
  | 1 => d6 (B.clause.toFun i) 1
  | 2 => d6 (B.varRot.invFun i) 5
  | 3 => d6 i 4
  | 4 => d6 i 3
  | _ => d6 (B.varRot.toFun i) 0

/-- Darts 2,4 form the new interior faces around the old variable vertices.
The remaining dart types traverse the old faces with inserted incidences. -/
def newFace (d : Fin (6 * E)) : Fin (6 * E) :=
  let i := index 6 (by decide) d
  match d.val % 6 with
  | 0 => d6 (B.clause.invFun i) 1
  | 1 => d6 (B.varRot.invFun i) 5
  | 2 => d6 i 4
  | 3 => d6 i 0
  | 4 => d6 (B.varRot.toFun i) 2
  | _ => d6 i 3

def expanded : Hypermap (6 * E) where
  edge := newEdge
  node := B.newNode
  face := B.newFace
  edgeK := six_cases _ (by
    intro i
    simp [newEdge, newNode, newFace, d6, B.varRot.right_inv, B.varRot.left_inv, B.clause.right_inv,
      show (3 : Fin 6).val = 3 from rfl, show (4 : Fin 6).val = 4 from rfl,
      show (5 : Fin 6).val = 5 from rfl])

end BipartiteRotation
end STACS2027.PlanarSource.Embedding

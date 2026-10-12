module

public import NPHardness.SourceOccurrences
public import NPHardness.PlanarRelabel
public import Complexity.Planar.Incidence
public import Complexity.Planar.GridTarget
public import NPHardness.PlanarSourceEmbeddingGraph

/-!
The actual CNF incidence list for occurrence copies and implication rings.
The occurrence indexing reuses `tagSource` and `sourceCopies` from the existing
checked reduction. This module concerns concrete lists and their endpoints;
it does not infer source hardness from a planar hypermap alone.
-/

@[expose] public section
namespace STACS2027.PlanarSource.Formula
open Complexity Complexity.SAT

abbrev IncidenceEdge := Sum Nat Nat × Sum Nat Nat

def incidenceAt (start : Nat) (f : CNF) : List IncidenceEdge :=
  (f.zipIdx start).flatMap fun p => p.1.map fun l => (Sum.inl l.var, Sum.inr p.2)

@[simp] theorem incidenceAt_zero (f : CNF) : incidenceAt 0 f = incidenceGraph f := rfl

@[simp] theorem incidenceAt_cons (start : Nat) (c : Clause) (f : CNF) :
    incidenceAt start (c :: f) =
      (c.map fun l => (Sum.inl l.var, Sum.inr start)) ++ incidenceAt (start+1) f := by
  simp [incidenceAt, List.zipIdx_cons]

theorem incidenceAt_length (start : Nat) (f : CNF) :
    (incidenceAt start f).length = f.flatten.length := by
  induction f generalizing start with
  | nil => rfl
  | cons c f ih => simp [incidenceAt_cons, ih]

def copyFormula (f : CNF) : CNF := (tagSource 0 f).map sourceCopies

theorem tagCopies_length (next : Nat) (f : CNF) :
    ((tagSource next f).map sourceCopies).length = f.length := by
  induction f generalizing next with
  | nil => rfl
  | cons c f ih => simp [tagSource, ih]

theorem tagCopies_incidenceAt (next start : Nat) (f : CNF) :
    incidenceAt start ((tagSource next f).map sourceCopies) =
      (incidenceAt start f).mapIdx (fun i e => (Sum.inl (next+i), e.2)) := by
  induction f generalizing next start with
  | nil => rfl
  | cons c f ih =>
    simp only [tagSource,List.map_cons,incidenceAt_cons,ih,List.mapIdx_append,List.length_map]
    congr 1
    · apply List.ext_getElem
      · simp [sourceCopies]
      · intro i hi hj
        simp [sourceCopies,List.getElem_zipIdx]
    · congr 1
      funext i e
      simp [Nat.add_comm,Nat.add_left_comm]

theorem copyFormula_incidence (f : CNF) :
    incidenceGraph (copyFormula f) =
      (incidenceGraph f).mapIdx (fun i e => (Sum.inl i,e.2)) := by
  simpa [copyFormula] using tagCopies_incidenceAt 0 0 f

def ringClauses (E : Nat) (next : Nat → Nat) (signs : Nat → Bool) : CNF :=
  (List.range E).map fun i => [⟨i,signs i⟩,⟨next i,!(signs (next i))⟩]

def ringFormula (f : CNF) (next : Nat → Nat) (signs : Nat → Bool) : CNF :=
  copyFormula f ++ ringClauses f.flatten.length next signs

def implicationEdges (start E : Nat) (next : Nat → Nat) : List IncidenceEdge :=
  (List.range E).flatMap fun i =>
    [(Sum.inl i,Sum.inr (start+i)),(Sum.inl (next i),Sum.inr (start+i))]

theorem ringClauses_incidenceAt (start E : Nat) (next : Nat → Nat) (signs : Nat → Bool) :
    incidenceAt start (ringClauses E next signs) = implicationEdges start E next := by
  simp only [incidenceAt,ringClauses,Complexity.Planar.Grid.zipIdx_map_range,
    List.flatMap_map,implicationEdges,List.map_cons,List.map_nil]

theorem ringFormula_incidence (f : CNF) (next : Nat → Nat) (signs : Nat → Bool) :
    incidenceGraph (ringFormula f next signs) =
      (incidenceGraph f).mapIdx (fun i e => (Sum.inl i,e.2)) ++
        implicationEdges f.length f.flatten.length next := by
  rw [ringFormula,Complexity.Planar.Grid.incidenceGraph_append,copyFormula_incidence]
  change _ ++ incidenceAt (copyFormula f).length (ringClauses _ next signs) = _
  rw [show (copyFormula f).length = f.length from tagCopies_length 0 f,
    ringClauses_incidenceAt]

theorem map_range_triples {α : Type} (E : Nat) (h : Nat → α) :
    (List.range (3*E)).map h =
      (List.range E).flatMap (fun i => [h (3*i),h (3*i+1),h (3*i+2)]) := by
  induction E with
  | zero => rfl
  | succ E ih =>
    rw [Nat.mul_succ, List.range_add, List.map_append, ih]
    rw [show List.range (E+1) = List.range E ++ [E] from List.range_succ,
      List.flatMap_append]
    simp [List.range_succ]

theorem map_flatMap_interleave {α β : Type} (ls : List α) (a : α → β) (b : α → List β) :
    (ls.map a ++ ls.flatMap b).Perm (ls.flatMap fun x => a x :: b x) := by
  induction ls with
  | nil => exact List.Perm.refl _
  | cons x xs ih =>
    simp only [List.map_cons,List.flatMap_cons,List.cons_append]
    apply List.Perm.cons
    have hs : (xs.map a ++ (b x ++ xs.flatMap b)).Perm
        (b x ++ (xs.map a ++ xs.flatMap b)) := by
      simpa only [List.append_assoc] using
        (List.Perm.append_right (xs.flatMap b) (List.perm_append_comm (l₁ := xs.map a) (l₂ := b x)))
    exact hs.trans (List.Perm.append_left (b x) ih)

end STACS2027.PlanarSource.Formula

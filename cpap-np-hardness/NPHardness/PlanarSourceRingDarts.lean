module

public import NPHardness.PlanarSourceDimensions
public import NPHardness.PlanarSourceComputableDelete

/-!
Explicit arithmetic dart reindexing from the six-dart occurrence expansion to
the actual CNF incidence list: copied incidences first, then the two incidences
of each implication. The last edge of each expansion block is reversed.
-/

@[expose] public section
namespace STACS2027.PlanarSource.Formula
open Complexity Complexity.SAT Complexity.Planar STACS2027.PlanarGluing
open STACS2027.PlanarSource.Embedding
open STACS2027.PlanarSource.Embedding.BipartiteRotation
open STACS2027.PlanarSource.ComputableComb

def ringDartValue (E d : Nat) : Nat :=
  match d%6 with
  | 0 => 2*(d/6)
  | 1 => 2*(d/6)+1
  | 2 => 2*E+4*(d/6)
  | 3 => 2*E+4*(d/6)+1
  | 4 => 2*E+4*(d/6)+3
  | _ => 2*E+4*(d/6)+2

def expandedDartValue (E d : Nat) : Nat :=
  if d<2*E then 6*(d/2)+d%2
  else
    match (d-2*E)%4 with
    | 0 => 6*((d-2*E)/4)+2
    | 1 => 6*((d-2*E)/4)+3
    | 2 => 6*((d-2*E)/4)+5
    | _ => 6*((d-2*E)/4)+4

theorem ringDartValue_lt {E d : Nat} (hd : d<6*E) : ringDartValue E d<6*E := by
  unfold ringDartValue
  split <;> omega

theorem expandedDartValue_lt {E d : Nat} (hd : d<6*E) : expandedDartValue E d<6*E := by
  unfold expandedDartValue
  split
  · omega
  · split <;> omega

theorem expanded_ringDartValue {E d : Nat} (hd : d<6*E) :
    expandedDartValue E (ringDartValue E d)=d := by
  have hi : d/6<E := by omega
  have hm : d%6=0 ∨ d%6=1 ∨ d%6=2 ∨ d%6=3 ∨ d%6=4 ∨ d%6=5 := by omega
  rcases hm with hm | hm | hm | hm | hm | hm
  all_goals simp only [ringDartValue,hm]
  all_goals simp [expandedDartValue,Nat.mul_add_div,Nat.add_assoc,Nat.add_sub_cancel_left,
    show 2*(d/6)<2*E by omega,show 2*(d/6)+1<2*E by omega]
  all_goals try omega
  all_goals split <;> omega

theorem ring_expandedDartValue {E d : Nat} (_hd : d<6*E) :
    ringDartValue E (expandedDartValue E d)=d := by
  by_cases hc : d<2*E
  · have hm : d%2=0 ∨ d%2=1 := by omega
    rcases hm with hm | hm <;>
      simp [expandedDartValue,hc,hm,ringDartValue,Nat.mul_add_div] <;> omega
  · have hm : (d-2*E)%4=0 ∨ (d-2*E)%4=1 ∨ (d-2*E)%4=2 ∨ (d-2*E)%4=3 := by omega
    rcases hm with hm | hm | hm | hm <;>
      simp [expandedDartValue,hc,hm,ringDartValue,Nat.mul_add_div] <;> omega

/-- This bijection is executable arithmetic; no list-permutation witness is
selected by classical choice. -/
def ringDarts (E : Nat) : DartEquiv (6*E) (6*E) where
  toFun d := ⟨ringDartValue E d.val,ringDartValue_lt d.isLt⟩
  invFun d := ⟨expandedDartValue E d.val,expandedDartValue_lt d.isLt⟩
  left_inv d := Fin.ext (expanded_ringDartValue d.isLt)
  right_inv d := Fin.ext (ring_expandedDartValue d.isLt)

@[simp] theorem ringDarts_zero {E : Nat} (i : Fin E) :
    ((ringDarts E).toFun (d6 i 0)).val=2*i.val := by simp [ringDarts,ringDartValue,d6,dart]
@[simp] theorem ringDarts_one {E : Nat} (i : Fin E) :
    ((ringDarts E).toFun (d6 i 1)).val=2*i.val+1 := by simp [ringDarts,ringDartValue,d6,dart,Nat.mul_add_div]
@[simp] theorem ringDarts_two {E : Nat} (i : Fin E) :
    ((ringDarts E).toFun (d6 i 2)).val=2*E+4*i.val := by simp [ringDarts,ringDartValue,d6,dart,Nat.mul_add_div]
@[simp] theorem ringDarts_three {E : Nat} (i : Fin E) :
    ((ringDarts E).toFun (d6 i 3)).val=2*E+4*i.val+1 := by simp [ringDarts,ringDartValue,d6,dart,Nat.mul_add_div]
@[simp] theorem ringDarts_four {E : Nat} (i : Fin E) :
    ((ringDarts E).toFun (d6 i 4)).val=2*E+4*i.val+3 := by simp [ringDarts,ringDartValue,d6,dart,Nat.mul_add_div]
@[simp] theorem ringDarts_five {E : Nat} (i : Fin E) :
    ((ringDarts E).toFun (d6 i 5)).val=2*E+4*i.val+2 := by simp [ringDarts,ringDartValue,d6,dart,Nat.mul_add_div]

theorem ringDarts_edge {E : Nat} (B : BipartiteRotation E) (d : Fin (6*E)) :
    ((ringDarts E).toFun (B.expanded.edge d)).val=ed ((ringDarts E).toFun d).val := by
  apply six_cases (fun d => _) ?_ d
  intro i
  simp [expanded,newEdge,ringDarts,ringDartValue,d6,dart,index,ed,Nat.mul_add_div]
  omega

end STACS2027.PlanarSource.Formula

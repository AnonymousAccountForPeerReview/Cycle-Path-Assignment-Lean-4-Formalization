module

public import Outerplanar.PlanarConeObstructions
public import Outerplanar.GeneralDegenerate
import Mathlib.Tactic

@[expose] public section
namespace STACS2027.PlanarTriangleGeometry

/-- The graph induced by the neighbours of a fixed apex. -/
def neighbourGraph (g : Graph) (apex : Nat) : Graph :=
  g.filter fun e => decide (Adj g apex e.1 ∧ Adj g apex e.2)

theorem adj_neighbourGraph {g : Graph} {apex a b : Nat} :
    Adj (neighbourGraph g apex) a b ↔ Adj g a b ∧ Adj g apex a ∧ Adj g apex b := by
  classical
  rw [neighbourGraph,adj_filter]
  constructor
  · rintro ⟨hab,hcond⟩
    have hc := of_decide_eq_true hcond
    rcases Nat.le_total a b with h | h
    · simpa [edge,min_eq_left h,max_eq_right h] using And.intro hab hc
    · simpa [edge,min_eq_right h,max_eq_left h,and_comm,and_left_comm] using And.intro hab hc
  · rintro ⟨hab,ha,hb⟩
    refine ⟨hab,decide_eq_true_eq.mpr ?_⟩
    rcases Nat.le_total a b with h | h
    · simpa [edge,min_eq_left h,max_eq_right h] using And.intro ha hb
    · simpa [edge,min_eq_right h,max_eq_left h] using And.intro hb ha

/-- Appending a new apex to every old vertex. -/
def cone (h : Graph) (size : Nat) : Graph :=
  h ++ (List.range size).map fun i => edge i size

theorem neighbour_walk_head {g : Graph} {apex x y : Nat} {S : Nat→Prop} {w : List Nat}
    (hw : WalkWithin (neighbourGraph g apex) S w) (hh : w.head?=some x)
    (ht : w.getLast?=some y) (hy : Adj g apex y) : Adj g apex x := by
  cases w with
  | nil => simp at hh
  | cons p rest =>
    simp only [List.head?_cons,Option.some.injEq] at hh
    subst p
    cases rest with
    | nil =>
      simp only [List.getLast?_singleton,Option.some.injEq] at ht
      subst y
      exact hy
    | cons q rest => exact (adj_neighbourGraph.mp hw.2.1).2.1

/-- A minor of the neighbour graph extends to the same minor with an added apex. -/
theorem neighbour_minor_cone {g h : Graph} {apex size : Nat}
    (hm : HasMinor (neighbourGraph g apex) size h)
    (hbound : ∀ e∈h,e.1<size ∧ e.2<size)
    (hvertex : ∀ i,i<size → ∃ j,Adj h i j) : HasMinor g (size+1) (cone h size) := by
  classical
  obtain ⟨branch,hne,hdisj,hconn,hedges⟩ := hm
  have hbranch : ∀ i,i<size → ∀ x∈branch i,Adj g apex x := by
    intro i hi x hx
    obtain ⟨j,hij⟩ := hvertex i hi
    obtain ⟨a,b,ha,hb,hab⟩ := hedges (edge i j) hij.2
    have hanchor : ∃ y∈branch i,Adj g apex y := by
      rcases Nat.le_total i j with hl | hl
      · have he : edge i j=(i,j) := by simp [edge,min_eq_left hl,max_eq_right hl]
        rw [he] at ha
        exact ⟨a,ha,(adj_neighbourGraph.mp hab).2.1⟩
      · have he : edge i j=(j,i) := by simp [edge,min_eq_right hl,max_eq_left hl]
        rw [he] at hb
        exact ⟨b,hb,(adj_neighbourGraph.mp hab).2.2⟩
    obtain ⟨y,hy,hapy⟩ := hanchor
    obtain ⟨w,hh,ht,hw⟩ := hconn i hi x y hx hy
    exact neighbour_walk_head hw hh ht hapy
  let B : Nat→List Nat := fun i => if i<size then branch i else [apex]
  refine ⟨B,?_,?_,?_,?_⟩
  · intro i hi
    by_cases hil : i<size
    · simpa [B,hil] using hne i hil
    · simp [B,hil]
  · intro i j hi hj hij x hxi hxj
    by_cases hil : i<size <;> by_cases hjl : j<size
    · exact hdisj i j hil hjl hij x (by simpa [B,hil] using hxi) (by simpa [B,hjl] using hxj)
    · have hx : x∈branch i := by simpa [B,hil] using hxi
      have hxa : x=apex := by simpa [B,hjl] using hxj
      exact (hbranch i hil x hx).1 hxa.symm
    · have hx : x∈branch j := by simpa [B,hjl] using hxj
      have hxa : x=apex := by simpa [B,hil] using hxi
      exact (hbranch j hjl x hx).1 hxa.symm
    · omega
  · intro i hi
    by_cases hil : i<size
    · have hc := (hconn i hil).mono (fun _ _ ha => (adj_neighbourGraph.mp ha).1)
      simpa [B,hil] using hc
    · simpa [B,hil] using connectedWithin_singleton g apex
  · intro e he
    rcases List.mem_append.mp he with he | he
    · obtain ⟨a,b,ha,hb,hab⟩ := hedges e he
      exact ⟨a,b,by simpa [B,(hbound e he).1] using ha,
        by simpa [B,(hbound e he).2] using hb,(adj_neighbourGraph.mp hab).1⟩
    · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp he
      have hil := List.mem_range.mp hi
      have hei : edge i size=(i,size) := by simp [edge,min_eq_left (by omega : i≤size),max_eq_right (by omega : i≤size)]
      obtain ⟨x,hx⟩ := List.exists_mem_of_ne_nil _ (hne i hil)
      rw [hei]
      exact ⟨x,apex,by simpa [B,hil] using hx,by simp [B],(hbranch i hil x hx).symm⟩

end STACS2027.PlanarTriangleGeometry

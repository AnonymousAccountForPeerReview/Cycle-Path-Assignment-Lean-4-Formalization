module

public import NPHardness.PlanarSourcePackedSound
public import NPHardness.PlanarSourcePackedProgram
public import NPHardness.PlanarSourceRotationTableGeometry

/-! Exact local position of every descriptor in the source emitter's zipped
position tables. These are list-order identities, retaining multiplicity. -/

@[expose] public section
namespace STACS2027.PlanarSource.Packed
open Complexity Complexity.SAT Complexity.StackTableauEmitter Complexity.Planar Grid
open Complexity.Planar.Emit

theorem blockOccurrences_variables {n : Nat} (live : Test n) (N K cb lb : NumExpr n)
    (ts : List (Template n)) (w : SAT.Word) (env : Env n) :
    (blockOccurrences live N K cb lb ts).map (fun p => p.variable.eval env) =
      (ts.map (fun t => t.eval w env)).flatten.map Literal.var := by
  have h := congrArg (List.map (fun p : SourceOccurrence => p.1.var))
    (RotationTable.blockOccurrences_enumerate live N K cb lb ts w env)
  have he : (fun p : SourceOccurrence => p.1.var)=Literal.var∘Prod.fst := rfl
  rw [he] at h
  simp only [← List.map_map,List.zipIdx_map_fst] at h
  simpa only [List.map_map,Function.comp_def,RotationTable.entryOccurrence,Occurrence.eval] using h

theorem map_eq_of_mem_zip {α β γ : Type} (xs : List α) (ys : List β) (F : α → γ) (G : β → γ)
    (h : xs.map F=ys.map G) {a : α} {b : β} (hab : (a,b)∈xs.zip ys) : F a=G b := by
  induction xs generalizing ys with
  | nil => simp at hab
  | cons x xs ih =>
    cases ys with
    | nil => simp at hab
    | cons y ys =>
      obtain ⟨hh,ht⟩ := List.cons.inj h
      rcases List.mem_cons.mp hab with he | hm
      · cases he; exact hh
      · exact ih ys ht hm

theorem cellPositions_eq (odd : Bool) : cellPositions odd=RotationTable.cellPositions odd := by
  cases odd <;> decide

theorem Layout.cellOccurrences_variables {n : Nat} (d : Layout n) (k idx : NumExpr n)
    (odd : Bool) (w : SAT.Word) (env : Env n) :
    (d.cellOccurrences k idx odd).map (fun p => p.variable.eval env) =
      (cellPositions odd).map (cellOff (d.W.eval env) (2*k.eval env+(if odd then 1 else 0)) (idx.eval env)+·) := by
  rw [Layout.cellOccurrences,blockOccurrences_variables (w := w),Layout.cellTemplates,cellTemplates_eval]
  simpa only [twoE,NumExpr.eval,cellPositions_eq] using
    RotationTable.cell_variables (d.W.eval env) (2*k.eval env+(if odd then 1 else 0))
      (idx.eval env) odd _ _

theorem Layout.cell_zip_position {n : Nat} (d : Layout n) (k idx : NumExpr n)
    (odd : Bool) (w : SAT.Word) (env : Env n) {p : Occurrence n} {s : Nat}
    (hp : (p,s)∈(d.cellOccurrences k idx odd).zip (cellPositions odd)) :
    s<10 ∧ p.variable.eval env=cellOff (d.W.eval env) (2*k.eval env+(if odd then 1 else 0)) (idx.eval env)+s ∧
      p.live=d.cellLive k idx odd := by
  have hm := List.of_mem_zip hp
  refine ⟨RotationTable.cellPositions_lt odd s (by rw [cellPositions_eq] at hm; exact hm.2),
    map_eq_of_mem_zip _ _ _ _ (d.cellOccurrences_variables k idx odd w env) hp,?_⟩
  exact blockOccurrences_live _ _ _ _ _ _ hm.1

theorem Layout.startOccurrences_variables {n : Nat} (d : Layout n) (k : NumExpr n)
    (odd : Bool) (w : SAT.Word) (env : Env n) :
    (d.startOccurrences k odd).map (fun p => p.variable.eval env) =
      [0,1,1,0].map (colBase (d.W.eval env) (2*k.eval env+(if odd then 1 else 0))+·) := by
  rw [Layout.startOccurrences,blockOccurrences_variables (w := w),startTemplates_eval]
  simp only [startG,twoE,NumExpr.eval,List.flatten_cons,List.flatten_nil,List.append_nil,
    List.cons_append,List.nil_append,List.map_cons,List.map_nil,Nat.add_zero]

theorem Layout.start_zip_position {n : Nat} (d : Layout n) (k : NumExpr n)
    (odd : Bool) (w : SAT.Word) (env : Env n) {p : Occurrence n} {s : Nat}
    (hp : (p,s)∈(d.startOccurrences k odd).zip [0,1,1,0]) :
    s<2 ∧ p.variable.eval env=colBase (d.W.eval env) (2*k.eval env+(if odd then 1 else 0))+s ∧
      p.live=d.columnLive k odd := by
  have hm := List.of_mem_zip hp
  refine ⟨by have := hm.2; simp only [List.mem_cons,List.not_mem_nil,or_false] at this; omega,
    map_eq_of_mem_zip _ _ _ _ (d.startOccurrences_variables k odd w env) hp,?_⟩
  exact blockOccurrences_live _ _ _ _ _ _ hm.1

theorem Layout.endOccurrences_variables {n : Nat} (d : Layout n) (k : NumExpr n)
    (odd : Bool) (w : SAT.Word) (env : Env n) :
    (d.endOccurrences k odd).map (fun p => p.variable.eval env) =
      [0,1,1,0].map (cellOff (d.W.eval env) (2*k.eval env+(if odd then 1 else 0)) (d.W.eval env)+·) := by
  rw [Layout.endOccurrences,blockOccurrences_variables (w := w),endTemplates_eval]
  simp only [endG,twoE,NumExpr.eval,List.flatten_cons,List.flatten_nil,List.append_nil,
    List.cons_append,List.nil_append,List.map_cons,List.map_nil,Nat.add_zero]

theorem Layout.end_zip_position {n : Nat} (d : Layout n) (k : NumExpr n)
    (odd : Bool) (w : SAT.Word) (env : Env n) {p : Occurrence n} {s : Nat}
    (hp : (p,s)∈(d.endOccurrences k odd).zip [0,1,1,0]) :
    s<2 ∧ p.variable.eval env=cellOff (d.W.eval env) (2*k.eval env+(if odd then 1 else 0)) (d.W.eval env)+s ∧
      p.live=d.columnLive k odd := by
  have hm := List.of_mem_zip hp
  refine ⟨by have := hm.2; simp only [List.mem_cons,List.not_mem_nil,or_false] at this; omega,
    map_eq_of_mem_zip _ _ _ _ (d.endOccurrences_variables k odd w env) hp,?_⟩
  exact blockOccurrences_live _ _ _ _ _ _ hm.1

def rainbowEndpoint (W k v : Nat) (odd : Bool) (s : Nat) : Nat :=
  if odd then
    if s=0 then cellOff W (2*k+2) v+1 else cellOff W (2*k+1) (W-1-v)+8
  else if s=0 then cellOff W (2*k) v+8 else cellOff W (2*k+1) (W-1-v)+1

theorem Layout.rainbowOccurrences_variables {n : Nat} (d : Layout n) (k v : NumExpr n)
    (odd : Bool) (w : SAT.Word) (env : Env n) :
    (d.rainbowOccurrences k v odd).map (fun p => p.variable.eval env) =
      [0,1,0,1].map (rainbowEndpoint (d.W.eval env) (k.eval env) (v.eval env) odd) := by
  rw [Layout.rainbowOccurrences,blockOccurrences_variables (w := w),rainbowTemplates_eval]
  cases odd <;> simp [rainbowEndpoint,rbOdd,rbEven,twoE,NumExpr.eval,Nat.add_assoc]

theorem Layout.rainbow_zip_position {n : Nat} (d : Layout n) (k v : NumExpr n)
    (odd : Bool) (w : SAT.Word) (env : Env n) {p : Occurrence n} {s : Nat}
    (hp : (p,s)∈(d.rainbowOccurrences k v odd).zip [0,1,0,1]) :
    s<2 ∧ p.variable.eval env=rainbowEndpoint (d.W.eval env) (k.eval env) (v.eval env) odd s ∧
      p.live=d.rainbowLive k v odd := by
  have hm := List.of_mem_zip hp
  refine ⟨by have := hm.2; simp only [List.mem_cons,List.not_mem_nil,or_false] at this; omega,
    map_eq_of_mem_zip _ _ _ _ (d.rainbowOccurrences_variables k v odd w env) hp,?_⟩
  exact blockOccurrences_live _ _ _ _ _ _ hm.1

end STACS2027.PlanarSource.Packed

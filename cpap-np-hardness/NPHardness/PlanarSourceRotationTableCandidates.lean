module

public import NPHardness.PlanarSourceRotationTableBlockAt
public import NPHardness.PlanarSourceRotationTableNeighborhood
public import NPHardness.PlanarSourcePackedAddresses

/-! Exact source-occurrence projections of the active finite candidate
blocks. Gate tests affect liveness, never occurrence identity or polarity. -/

@[expose] public section
namespace STACS2027.PlanarSource.RotationTable
open Complexity Complexity.SAT Complexity.Planar Comb Grid
open Complexity.StackTableauEmitter
open STACS2027.PlanarSource.Packed

def liveProjection {n : Nat} (xs : List (Occurrence n)) (w : SAT.Word) (env : Env n) :
    List SourceOccurrence :=
  (xs.filter (fun p => p.live.eval w env)).map (fun p => entryOccurrence (p.eval w env))

@[simp] theorem liveProjection_append {n : Nat} (xs ys : List (Occurrence n))
    (w : SAT.Word) (env : Env n) :
    liveProjection (xs++ys) w env = liveProjection xs w env ++ liveProjection ys w env := by
  simp [liveProjection]

theorem templateOccurrences_live {n : Nat}
    (live : Test n) (N K cb lb : NumExpr n) (t : Template n)
    {p : Occurrence n} (hp : p ∈ templateOccurrences live N K cb lb t) : p.live = live := by
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
  rfl

theorem blockOccurrences_live {n : Nat}
    (live : Test n) (N K cb lb : NumExpr n) (ts : List (Template n)) :
    ∀ p ∈ blockOccurrences live N K cb lb ts, p.live = live := by
  induction ts generalizing cb lb with
  | nil => simp [blockOccurrences]
  | cons t ts ih =>
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact templateOccurrences_live live N K cb lb t hp
    · exact ih _ _ p hp

theorem blockOccurrences_liveProjection {n : Nat}
    (live : Test n) (N K cb lb : NumExpr n) (ts : List (Template n))
    (w : SAT.Word) (env : Env n) :
    liveProjection (blockOccurrences live N K cb lb ts) w env =
      if live.eval w env then (ts.map (fun t => t.eval w env)).flatten.zipIdx (lb.eval env) else [] := by
  by_cases hl : live.eval w env = true
  · have hf : (blockOccurrences live N K cb lb ts).filter (fun p => p.live.eval w env) =
        blockOccurrences live N K cb lb ts := by
      apply List.filter_eq_self.mpr
      intro p hp
      rw [blockOccurrences_live live N K cb lb ts p hp]
      exact hl
    simp only [liveProjection,hf,hl,ite_true,blockOccurrences_enumerate]
  · have hf : (blockOccurrences live N K cb lb ts).filter (fun p => p.live.eval w env) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro p hp
      rw [blockOccurrences_live live N K cb lb ts p hp]
      exact hl
    simp [liveProjection,hf,hl]

@[simp] theorem liveProjection_gate {n : Nat} (t : Test n) (xs : List (Occurrence n))
    (w : SAT.Word) (env : Env n) :
    liveProjection (gate t xs) w env = if t.eval w env then liveProjection xs w env else [] := by
  unfold liveProjection gate
  rw [List.filter_map,List.map_map]
  by_cases ht : t.eval w env = true
  · simp only [Test.eval,ht,Bool.true_and,ite_true,Function.comp_def]
    rfl
  · have ht' := Bool.eq_false_iff.mpr ht
    simp [Test.eval,ht',Function.comp_def]

def layoutBits {n : Nat} (d : Layout n) (w : SAT.Word) (env : Env n) : Nat → Nat → Bool×Bool :=
  Complexity.Planar.Emit.bitsW w (d.A.eval env) (d.M.eval env) (d.R.eval env) (d.W.eval env)

theorem layoutCellTemplates_eval {n : Nat} (d : Layout n) (k idx : NumExpr n)
    (odd : Bool) (w : SAT.Word) (env : Env n) :
    (d.cellTemplates k idx odd).map (fun t => t.eval w env) =
      GridBlock.formula (d.W.eval env) (layoutBits d w env) (.cell (k.eval env) (idx.eval env) odd) := by
  rw [Layout.cellTemplates,Packed.cellTemplates_eval]
  simp only [GridBlock.formula,columnIndex,layoutBits,Test.eval,Complexity.Planar.Emit.posE_eval,
    Complexity.Planar.Emit.rowE_eval,Complexity.Planar.Emit.twoE,NumExpr.eval,Complexity.Planar.Emit.bitsW]

theorem cell_liveProjection {n : Nat} (d : Layout n) (k idx : NumExpr n)
    (odd : Bool) (w : SAT.Word) (env : Env n) :
    liveProjection (d.cellOccurrences k idx odd) w env =
      if (GridBlock.cell (k.eval env) (idx.eval env) odd).Valid (d.W.eval env) (d.M.eval env) then
        (GridBlock.formula (d.W.eval env) (layoutBits d w env) (.cell (k.eval env) (idx.eval env) odd)).flatten.zipIdx
          ((d.cellBase k idx odd true).eval env) else [] := by
  rw [Layout.cellOccurrences,blockOccurrences_liveProjection,layoutCellTemplates_eval]
  have he : ((d.cellLive k idx odd).eval w env = true) ↔
      (GridBlock.cell (k.eval env) (idx.eval env) odd).Valid (d.W.eval env) (d.M.eval env) := by
    rw [Layout.cellLive_eval]
    cases odd <;> simp [GridBlock.Valid,columnIndex] <;> omega
  simp only [he]

theorem start_liveProjection {n : Nat} (d : Layout n) (k : NumExpr n)
    (odd : Bool) (w : SAT.Word) (env : Env n) :
    liveProjection (d.startOccurrences k odd) w env =
      if (GridBlock.start (k.eval env) odd).Valid (d.W.eval env) (d.M.eval env) then
        (GridBlock.formula (d.W.eval env) (layoutBits d w env) (.start (k.eval env) odd)).flatten.zipIdx
          ((d.columnBase k odd true).eval env) else [] := by
  rw [Layout.startOccurrences,blockOccurrences_liveProjection,startTemplates_eval]
  have he : ((d.columnLive k odd).eval w env = true) ↔
      (GridBlock.start (k.eval env) odd).Valid (d.W.eval env) (d.M.eval env) := by
    rw [Layout.columnLive_eval]
    cases odd <;> simp [GridBlock.Valid,columnIndex] <;> omega
  simp only [he]
  rfl

theorem end_liveProjection {n : Nat} (d : Layout n) (k : NumExpr n)
    (odd : Bool) (w : SAT.Word) (env : Env n) :
    liveProjection (d.endOccurrences k odd) w env =
      if (GridBlock.finish (k.eval env) odd).Valid (d.W.eval env) (d.M.eval env) then
        (GridBlock.formula (d.W.eval env) (layoutBits d w env) (.finish (k.eval env) odd)).flatten.zipIdx
          ((d.endBase k odd true).eval env) else [] := by
  rw [Layout.endOccurrences,blockOccurrences_liveProjection,endTemplates_eval]
  have he : ((d.columnLive k odd).eval w env = true) ↔
      (GridBlock.finish (k.eval env) odd).Valid (d.W.eval env) (d.M.eval env) := by
    rw [Layout.columnLive_eval]
    cases odd <;> simp [GridBlock.Valid,columnIndex] <;> omega
  simp only [he]
  rfl

theorem rainbow_liveProjection {n : Nat} (d : Layout n) (k v : NumExpr n)
    (odd : Bool) (w : SAT.Word) (env : Env n) :
    liveProjection (d.rainbowOccurrences k v odd) w env =
      if (GridBlock.rainbow (k.eval env) (v.eval env) odd).Valid (d.W.eval env) (d.M.eval env) then
        (GridBlock.formula (d.W.eval env) (layoutBits d w env) (.rainbow (k.eval env) (v.eval env) odd)).flatten.zipIdx
          ((d.rainbowBase k v odd true).eval env) else [] := by
  rw [Layout.rainbowOccurrences,blockOccurrences_liveProjection,rainbowTemplates_eval]
  have he : ((d.rainbowLive k v odd).eval w env = true) ↔
      (GridBlock.rainbow (k.eval env) (v.eval env) odd).Valid (d.W.eval env) (d.M.eval env) := by
    rw [Layout.rainbowLive_eval]
    cases odd <;> simp [GridBlock.Valid,columnIndex] <;> omega
  simp only [he]
  rfl

end STACS2027.PlanarSource.RotationTable

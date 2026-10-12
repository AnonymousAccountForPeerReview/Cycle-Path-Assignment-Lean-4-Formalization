module

public import NPHardness.PlanarSourcePackedCopyPhase
public import NPHardness.PlanarSourceRotationTableEnumeration

/-! Composition of local ring-block semantics through the complete counted
grid program.  The local obligations are confined to blocks that are actually
emitted; all loop guards and offsets remain in the concrete program. -/

@[expose] public section
namespace STACS2027.PlanarSource.Packed
open Complexity Complexity.SAT Complexity.StackTableauEmitter Complexity.Planar.Grid
open Complexity.Planar.Emit

def expandCopies (edge : Nat → Clause) (copies : CNF) : CNF :=
  copies.flatten.map fun l => edge l.var

@[simp] theorem expandCopies_append (edge : Nat → Clause) (f g : CNF) :
    expandCopies edge (f++g) = expandCopies edge f ++ expandCopies edge g := by
  simp [expandCopies]

theorem expandCopies_flatMap {α : Type} (edge : Nat → Clause) (xs : List α) (F : α → CNF) :
    expandCopies edge (xs.flatMap F) = xs.flatMap (fun x => expandCopies edge (F x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons, expandCopies_append, ih]

theorem expandCopies_copiesAt (edge : Nat → Clause) (base : Nat) (f : CNF) :
    expandCopies edge (copiesAt base f) = (List.range' base f.flatten.length).map edge := by
  rw [copiesAt_tagSource]
  have he (ps : List (List SourceOccurrence)) :
      expandCopies edge (ps.map sourceCopies) = (ps.flatten.map Prod.snd).map edge := by
    have hf : (ps.map sourceCopies).flatten =
        ps.flatten.map (fun p => (⟨p.2,false⟩ : Literal)) := by
      induction ps with
      | nil => rfl
      | cons p ps ih => simp [sourceCopies,ih]
    simp only [expandCopies, hf, List.map_map, Function.comp_def]
  rw [he, tagSource_flatten]
  have hi : (f.flatten.zipIdx base).map Prod.snd = List.range' base f.flatten.length := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp
  rw [hi]

theorem ringBlock_exact {n : Nat} (ps : List (Occurrence n)) (positions : List Nat)
    (candidates : Nat → List (Occurrence n)) (edge : Nat → Clause)
    (w : SAT.Word) (env : Env n) (hlen : positions.length = ps.length)
    (hlocal : ∀ p s, (p,s) ∈ ps.zip positions →
      (successorProgram p (candidates s)).emit w env = [edge (p.index.eval env)]) :
    (ringBlock ps positions candidates).emit w env = ps.map (fun p => edge (p.index.eval env)) := by
  simp only [ringBlock, sequence_emit, List.flatMap_map]
  have hflat : (ps.zip positions).flatMap (fun p =>
      (successorProgram p.1 (candidates p.2)).emit w env) =
      (ps.zip positions).map (fun p => edge (p.1.index.eval env)) := by
    rw [List.map_eq_flatMap]
    apply congrArg List.flatten
    apply List.map_congr_left
    intro p hp
    exact hlocal p.1 p.2 hp
  rw [hflat]
  have hf : (ps.zip positions).map Prod.fst = ps := by
    apply List.ext_getElem
    · simp [hlen]
    · intro i hi hj
      simp
  have he := congrArg (List.map (fun p : Occurrence n => edge (p.index.eval env))) hf
  simpa only [List.map_map, Function.comp_def] using he

theorem ringBlock_copies {n : Nat} (live : Test n) (N K cb lb : NumExpr n)
    (ts : List (Template n)) (positions : List Nat)
    (candidates : Nat → List (Occurrence n)) (edge : Nat → Clause)
    (w : SAT.Word) (env : Env n)
    (hlen : positions.length = (blockOccurrences live N K cb lb ts).length)
    (hlocal : ∀ p s, (p,s) ∈ (blockOccurrences live N K cb lb ts).zip positions →
      (successorProgram p (candidates s)).emit w env = [edge (p.index.eval env)]) :
    (ringBlock (blockOccurrences live N K cb lb ts) positions candidates).emit w env =
      expandCopies edge ((copyBlock lb ts).emit w env) := by
  rw [ringBlock_exact _ _ _ edge w env hlen hlocal, copyBlock_emit, expandCopies_copiesAt]
  have h := congrArg (List.map edge)
    (RotationTable.blockOccurrences_indices live N K cb lb ts w env)
  simpa only [List.map_map, Function.comp_def] using h

theorem cellPositions_length (odd : Bool) : (cellPositions odd).length = 48 := by
  cases odd <;> decide

theorem cellOccurrences_length {n : Nat} (d : Layout n) (k idx : NumExpr n) (odd : Bool) :
    (d.cellOccurrences k idx odd).length = 48 := by
  cases odd <;> rfl

theorem startOccurrences_length {n : Nat} (d : Layout n) (k : NumExpr n) (odd : Bool) :
    (d.startOccurrences k odd).length = 4 := rfl

theorem endOccurrences_length {n : Nat} (d : Layout n) (k : NumExpr n) (odd : Bool) :
    (d.endOccurrences k odd).length = 4 := rfl

theorem rainbowOccurrences_length {n : Nat} (d : Layout n) (k v : NumExpr n) (odd : Bool) :
    (d.rainbowOccurrences k v odd).length = 4 := by cases odd <;> rfl

/-- Exact local emitter refinements, only at guarded grid blocks. -/
structure RingBlocks {n : Nat} (d : Layout n) (w : SAT.Word) (env : Env n)
    (edge : Nat → Clause) : Prop where
  start : ∀ k odd, 2*k+(if odd then 2 else 1) ≤ d.M.eval env →
    (d.lift.startProgram (.var 0) odd true).emit w (extend k env) =
      expandCopies edge ((d.lift.startProgram (.var 0) odd false).emit w (extend k env))
  cell : ∀ k idx odd, 2*k+(if odd then 2 else 1) ≤ d.M.eval env → idx < d.W.eval env →
    (d.lift.lift.cellProgram (.var 1) (.var 0) odd true).emit w (extend idx (extend k env)) =
      expandCopies edge ((d.lift.lift.cellProgram (.var 1) (.var 0) odd false).emit w
        (extend idx (extend k env)))
  finish : ∀ k odd, 2*k+(if odd then 2 else 1) ≤ d.M.eval env →
    (d.lift.endProgram (.var 0) odd true).emit w (extend k env) =
      expandCopies edge ((d.lift.endProgram (.var 0) odd false).emit w (extend k env))
  rainbow : ∀ k v odd, 2*k+(if odd then 3 else 2) ≤ d.M.eval env → v < d.W.eval env →
    (d.lift.lift.rainbowProgram (.var 1) (.var 0) odd true).emit w (extend v (extend k env)) =
      expandCopies edge ((d.lift.lift.rainbowProgram (.var 1) (.var 0) odd false).emit w
        (extend v (extend k env)))

theorem RingBlocks.column {n : Nat} {d : Layout n} {w : SAT.Word} {env : Env n}
    {edge : Nat → Clause} (h : RingBlocks d w env edge) (k : Nat) (odd : Bool)
    (hk : 2*k+(if odd then 2 else 1) ≤ d.M.eval env) :
    (d.lift.columnProgram (.var 0) odd true).emit w (extend k env) =
      expandCopies edge ((d.lift.columnProgram (.var 0) odd false).emit w (extend k env)) := by
  simp only [Layout.columnProgram, ClauseProgram.emit_seq, ClauseProgram.emit_forDown,
    expandCopies_append, expandCopies_flatMap, h.start k odd hk, h.finish k odd hk]
  congr 2
  apply flatMap_congr_range
  intro idx hidx
  have hi : idx < d.W.eval env := by simpa only [Layout.lift, NumExpr.eval_lift] using hidx
  exact h.cell k idx odd hk hi

theorem RingBlocks.row {n : Nat} {d : Layout n} {w : SAT.Word} {env : Env n}
    {edge : Nat → Clause} (h : RingBlocks d w env edge) (k : Nat) (odd : Bool)
    (hk : 2*k+(if odd then 3 else 2) ≤ d.M.eval env) :
    (ClauseProgram.forDown d.W.lift
      (d.lift.lift.rainbowProgram (.var 1) (.var 0) odd true)).emit w (extend k env) =
      expandCopies edge ((ClauseProgram.forDown d.W.lift
        (d.lift.lift.rainbowProgram (.var 1) (.var 0) odd false)).emit w (extend k env)) := by
  simp only [ClauseProgram.emit_forDown, expandCopies_flatMap]
  apply flatMap_congr_range
  intro v hv
  have hv' : v < d.W.eval env := by simpa only [NumExpr.eval_lift] using hv
  exact h.rainbow k v odd hk hv'

theorem gridPhase_rings {n : Nat} (d : Layout n) (w : SAT.Word) (env : Env n)
    (edge : Nat → Clause) (h : RingBlocks d w env edge) :
    (d.gridPhase true).emit w env = expandCopies edge ((d.gridPhase false).emit w env) := by
  simp only [Layout.gridPhase, ClauseProgram.emit_seq, expandCopies_append,
    forDown_guard_emit, expandCopies_flatMap]
  have happend {a b c d : CNF} (ha : a=c) (hb : b=d) : a++b=c++d := by rw [ha,hb]
  refine happend (happend (happend ?_ ?_) ?_) ?_
  all_goals
    apply flatMap_congr_range
    intro k hk
    simp only [twoE, NumExpr.eval, NumExpr.eval_lift, extend_zero]
    split
    · next hl =>
        first
        | exact h.column k false hl
        | exact h.column k true hl
        | exact h.row k false hl
        | exact h.row k true hl
    · rfl

/-- Full program equality, with all global copying, ordering, and loop
composition discharged.  Remaining obligations are precisely local table
semantics in `RingBlocks`. -/
theorem program_eq_ringFormula {n : Nat} (d : Layout n) (w : SAT.Word) (env : Env n)
    (next : Nat → Nat) (signs : Nat → Bool)
    (hq : 2*(d.Q.eval env)=d.M.eval env ∨ 2*(d.Q.eval env)=d.M.eval env+1)
    (h : RingBlocks d w env (fun i => [⟨i,signs i⟩,⟨next i,!(signs (next i))⟩])) :
    (d.program).emit w env =
      Formula.ringFormula (gridCNF (d.W.eval env) (d.M.eval env)
        (bitsW w (d.A.eval env) (d.M.eval env) (d.R.eval env) (d.W.eval env))) next signs := by
  rw [Layout.program, ClauseProgram.emit_seq, gridPhase_rings d w env _ h,
    gridPhase_copies d w env hq, expandCopies_copiesAt, copiesAt_zero]
  simp only [Formula.ringFormula, Formula.ringClauses]
  congr 2
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

end STACS2027.PlanarSource.Packed

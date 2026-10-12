module
public import NPHardness.PlanarSourceRotationTableComplete
public import NPHardness.PlanarSourcePackedPositions
public import NPHardness.PlanarSourcePackedLocalCorrect
import Lean.Elab.Tactic.Omega
@[expose] public section
namespace STACS2027.PlanarSource.Packed
open Complexity Complexity.SAT Complexity.StackTableauEmitter Complexity.Planar Comb Grid
open RotationTable

/-- The actual incidence rotation used by the registered comb drawing. -/
def incidenceNext (f : CNF) (i : Nat) : Nat :=
  rnext (incidenceOrder f (vr f (oj f i) (ot f i))) i

def ringEdge (f : CNF) (i : Nat) : Clause :=
  [⟨i,Formula.sourceSigns f i⟩,
   ⟨incidenceNext f i, !(Formula.sourceSigns f (incidenceNext f i))⟩]

theorem successorProgram_source {n : Nat} {f : CNF} (hf : CombOK f)
    (p : Occurrence n) (xs : List (Occurrence n)) (w : SAT.Word) (env : Env n)
    (hp : DescriptorSound f (p.eval w env)) (hx : SoundList f w env xs)
    (hl : (p.eval w env).live=true) (hc : CompleteCandidates f p xs w env) :
    (successorProgram p xs).emit w env = [ringEdge f (p.index.eval env)] := by
  have h := successorProgram_registered hf p xs w env (Formula.sourceSigns f)
    hp.correct (fun q hq => (hx q hq).correct) hl hc.coverage hc.distinct
    (fun q hq hqLive => (hx q hq).sign hqLive)
  dsimp only at h
  have hv := (hp.correct hl).2.1
  change p.variable.eval env = vr f (oj f (p.index.eval env)) (ot f (p.index.eval env)) at hv
  have hs := hp.sign hl
  change p.sign.eval w env=Formula.sourceSigns f (p.index.eval env) at hs
  simpa only [ringEdge,incidenceNext,Occurrence.eval,hv,hs] using h

@[simp] theorem Layout.source_lift {n : Nat} (d : Layout n) (w : SAT.Word) (env : Env n) (i : Nat) :
    d.lift.source w (extend i env) = d.source w env := by
  simp only [Layout.source,Layout.bits,Layout.lift,NumExpr.eval_lift]

theorem Layout.startProgram_correct {n : Nat} (d : Layout n) (k : NumExpr n) (odd : Bool)
    (w : SAT.Word) (env : Env n)
    (hq : 2*d.Q.eval env=d.M.eval env ∨ 2*d.Q.eval env=d.M.eval env+1)
    (hk : 2*k.eval env+(if odd then 2 else 1)≤d.M.eval env) :
    (d.startProgram k odd true).emit w env =
      expandCopies (ringEdge (d.source w env)) ((d.startProgram k odd false).emit w env) := by
  simp only [Layout.startProgram, ↓reduceIte]
  apply ringBlock_copies
  · exact (startOccurrences_length d k odd).symm
  · intro p s hp
    obtain ⟨hs,hv,hl⟩ := d.start_zip_position k odd w env hp
    apply successorProgram_source
    · exact gridCNF_combOK (by cases odd <;> simp only [Bool.false_eq_true,↓reduceIte] at hk <;> omega) _
    · exact d.startOccurrences_sound k odd w env hq p (List.of_mem_zip hp).1
    · exact d.startCandidates_sound k odd s w env hq
    · change p.live.eval w env=true
      rw [hl]
      exact (d.columnLive_eval k odd w env).mpr hk
    · exact startCandidates_complete d k odd s p w env hq hs hv

theorem Layout.cellProgram_correct {n : Nat} (d : Layout n) (k idx : NumExpr n) (odd : Bool)
    (w : SAT.Word) (env : Env n)
    (hq : 2*d.Q.eval env=d.M.eval env ∨ 2*d.Q.eval env=d.M.eval env+1)
    (hk : 2*k.eval env+(if odd then 2 else 1)≤d.M.eval env) (hi : idx.eval env<d.W.eval env) :
    (d.cellProgram k idx odd true).emit w env =
      expandCopies (ringEdge (d.source w env)) ((d.cellProgram k idx odd false).emit w env) := by
  simp only [Layout.cellProgram, ↓reduceIte]
  apply ringBlock_copies
  · rw [cellPositions_length]
    exact (cellOccurrences_length d k idx odd).symm
  · intro p s hp
    obtain ⟨hs,hv,hl⟩ := d.cell_zip_position k idx odd w env hp
    apply successorProgram_source
    · exact gridCNF_combOK (by cases odd <;> simp only [Bool.false_eq_true,↓reduceIte] at hk <;> omega) _
    · exact d.cellOccurrences_sound k idx odd w env hq p (List.of_mem_zip hp).1
    · exact d.cellCandidates_sound k idx odd s w env hq
    · change p.live.eval w env=true
      rw [hl]
      exact (d.cellLive_eval k idx odd w env).mpr ⟨hk,hi⟩
    · exact cellCandidates_complete d k idx odd s p w env hq hi hs hv

theorem Layout.endProgram_correct {n : Nat} (d : Layout n) (k : NumExpr n) (odd : Bool)
    (w : SAT.Word) (env : Env n)
    (hq : 2*d.Q.eval env=d.M.eval env ∨ 2*d.Q.eval env=d.M.eval env+1)
    (hk : 2*k.eval env+(if odd then 2 else 1)≤d.M.eval env) :
    (d.endProgram k odd true).emit w env =
      expandCopies (ringEdge (d.source w env)) ((d.endProgram k odd false).emit w env) := by
  simp only [Layout.endProgram, ↓reduceIte]
  apply ringBlock_copies
  · exact (endOccurrences_length d k odd).symm
  · intro p s hp
    obtain ⟨hs,hv,hl⟩ := d.end_zip_position k odd w env hp
    apply successorProgram_source
    · exact gridCNF_combOK (by cases odd <;> simp only [Bool.false_eq_true,↓reduceIte] at hk <;> omega) _
    · exact d.endOccurrences_sound k odd w env hq p (List.of_mem_zip hp).1
    · exact d.endCandidates_sound k odd s w env hq
    · change p.live.eval w env=true
      rw [hl]
      exact (d.columnLive_eval k odd w env).mpr hk
    · exact endCandidates_complete d k odd s p w env hq hs hv

theorem rainbowEndpoint_eq (W k v : Nat) (odd : Bool) (s : Nat) :
    rainbowEndpoint W k v odd s = rainbowVariable W k v odd s := by
  cases odd <;> simp [rainbowEndpoint,rainbowVariable,columnIndex,Nat.mul_add]

theorem Layout.rainbowProgram_correct {n : Nat} (d : Layout n) (k v : NumExpr n) (odd : Bool)
    (w : SAT.Word) (env : Env n)
    (hq : 2*d.Q.eval env=d.M.eval env ∨ 2*d.Q.eval env=d.M.eval env+1)
    (hk : 2*k.eval env+(if odd then 3 else 2)≤d.M.eval env) (hi : v.eval env<d.W.eval env) :
    (d.rainbowProgram k v odd true).emit w env =
      expandCopies (ringEdge (d.source w env)) ((d.rainbowProgram k v odd false).emit w env) := by
  simp only [Layout.rainbowProgram, ↓reduceIte]
  apply ringBlock_copies
  · exact (rainbowOccurrences_length d k v odd).symm
  · intro p s hp
    obtain ⟨hs,hv,hl⟩ := d.rainbow_zip_position k v odd w env hp
    rw [rainbowEndpoint_eq] at hv
    apply successorProgram_source
    · exact gridCNF_combOK (by cases odd <;> simp only [Bool.false_eq_true,↓reduceIte] at hk <;> omega) _
    · exact d.rainbowOccurrences_sound k v odd w env hq p (List.of_mem_zip hp).1
    · exact d.rainbowCandidates_sound k v odd s w env hq
    · change p.live.eval w env=true
      rw [hl]
      exact (d.rainbowLive_eval k v odd w env).mpr ⟨hk,hi⟩
    · exact rainbowCandidates_complete d k v odd s p w env hq hi hs hv

theorem Layout.ringBlocks {n : Nat} (d : Layout n) (w : SAT.Word) (env : Env n)
    (hq : 2*d.Q.eval env=d.M.eval env ∨ 2*d.Q.eval env=d.M.eval env+1) :
    RingBlocks d w env (ringEdge (d.source w env)) := by
  constructor
  · intro k odd hk
    simpa only [Layout.source_lift] using d.lift.startProgram_correct (.var 0) odd w (extend k env)
      (by simpa only [Layout.lift,NumExpr.eval_lift] using hq) (by simpa only [Layout.lift,NumExpr.eval_lift,NumExpr.eval,extend_zero] using hk)
  · intro k idx odd hk hi
    simpa only [Layout.source_lift] using d.lift.lift.cellProgram_correct (.var 1) (.var 0) odd w (extend idx (extend k env))
      (by simpa only [Layout.lift,NumExpr.eval_lift] using hq)
      (by change 2*k+(if odd then 2 else 1) ≤ d.M.lift.lift.eval (extend idx (extend k env)); simpa only [NumExpr.eval_lift] using hk)
      (by simpa only [Layout.lift,NumExpr.eval_lift,NumExpr.eval,extend_zero] using hi)
  · intro k odd hk
    simpa only [Layout.source_lift] using d.lift.endProgram_correct (.var 0) odd w (extend k env)
      (by simpa only [Layout.lift,NumExpr.eval_lift] using hq) (by simpa only [Layout.lift,NumExpr.eval_lift,NumExpr.eval,extend_zero] using hk)
  · intro k v odd hk hi
    simpa only [Layout.source_lift] using d.lift.lift.rainbowProgram_correct (.var 1) (.var 0) odd w (extend v (extend k env))
      (by simpa only [Layout.lift,NumExpr.eval_lift] using hq)
      (by change 2*k+(if odd then 3 else 2) ≤ d.M.lift.lift.eval (extend v (extend k env)); simpa only [NumExpr.eval_lift] using hk)
      (by simpa only [Layout.lift,NumExpr.eval_lift,NumExpr.eval,extend_zero] using hi)

/-- Complete equality between the compiled emitter and the source ring formula.
No geometric neighborhood or successor hypothesis remains. -/
theorem Layout.program_ringFormula {n : Nat} (d : Layout n) (w : SAT.Word) (env : Env n)
    (hq : 2*d.Q.eval env=d.M.eval env ∨ 2*d.Q.eval env=d.M.eval env+1) :
    d.program.emit w env = Formula.ringFormula (d.source w env)
      (incidenceNext (d.source w env)) (Formula.sourceSigns (d.source w env)) :=
  program_eq_ringFormula d w env _ _ hq (d.ringBlocks w env hq)

end STACS2027.PlanarSource.Packed

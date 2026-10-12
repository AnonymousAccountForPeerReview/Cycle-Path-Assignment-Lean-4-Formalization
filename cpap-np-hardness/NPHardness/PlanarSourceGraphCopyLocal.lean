module

public import NPHardness.PlanarSourceGraphProgram
public import NPHardness.PlanarSourcePackedGraphComposition

/-! The emitted copied-clause graphs compute each endpoint bit from the
actual registered source descriptor's literal sign. -/

@[expose] public section
namespace STACS2027.PlanarSource.Packed
open Complexity Complexity.SAT Complexity.StackTableauEmitter Complexity.Planar Grid
open Complexity.Planar.Emit

theorem Layout.startGraphProgram_copies {n : Nat} (d : Layout n) (length : Nat)
    (k : NumExpr n) (odd : Bool) (w : SAT.Word) (env : Env n)
    (hq : 2*d.Q.eval env=d.M.eval env ∨ 2*d.Q.eval env=d.M.eval env+1)
    (hk : 2*k.eval env+(if odd then 2 else 1)≤d.M.eval env) :
    (d.startGraphProgram length k odd false).emit w env =
      copyGraphAt (sourceEndpointChoices (Formula.sourceSigns (d.source w env))) length
        (d.occurrenceCount.eval env) ((d.columnBase k odd false).eval env)
        ((d.columnBase k odd true).eval env)
        (startG (d.W.eval env) (2*k.eval env+(if odd then 1 else 0))) := by
  simp only [Layout.startGraphProgram, Bool.false_eq_true, ↓reduceIte]
  rw [copyGraphBlock_emit (Formula.sourceSigns (d.source w env))
    (d.columnLive k odd) d.formulaLength d.variableCount]
  · simp only [copyGraphAt,copiedAt,startTemplates_eval,twoE,NumExpr.eval]
  · intro p hp
    apply (d.startOccurrences_sound k odd w env hq p hp).sign
    change p.live.eval w env=true
    rw [blockOccurrences_live _ _ _ _ _ _ hp]
    exact (d.columnLive_eval k odd w env).mpr hk

theorem Layout.endGraphProgram_copies {n : Nat} (d : Layout n) (length : Nat)
    (k : NumExpr n) (odd : Bool) (w : SAT.Word) (env : Env n)
    (hq : 2*d.Q.eval env=d.M.eval env ∨ 2*d.Q.eval env=d.M.eval env+1)
    (hk : 2*k.eval env+(if odd then 2 else 1)≤d.M.eval env) :
    (d.endGraphProgram length k odd false).emit w env =
      copyGraphAt (sourceEndpointChoices (Formula.sourceSigns (d.source w env))) length
        (d.occurrenceCount.eval env) ((d.endBase k odd false).eval env)
        ((d.endBase k odd true).eval env)
        (endG (d.W.eval env) (2*k.eval env+(if odd then 1 else 0))) := by
  simp only [Layout.endGraphProgram, Bool.false_eq_true, ↓reduceIte]
  rw [copyGraphBlock_emit (Formula.sourceSigns (d.source w env))
    (d.columnLive k odd) d.formulaLength d.variableCount]
  · simp only [copyGraphAt,copiedAt,endTemplates_eval,twoE,NumExpr.eval]
  · intro p hp
    apply (d.endOccurrences_sound k odd w env hq p hp).sign
    change p.live.eval w env=true
    rw [blockOccurrences_live _ _ _ _ _ _ hp]
    exact (d.columnLive_eval k odd w env).mpr hk

theorem Layout.cellGraphProgram_copies {n : Nat} (d : Layout n) (length : Nat)
    (k idx : NumExpr n) (odd : Bool) (w : SAT.Word) (env : Env n)
    (hq : 2*d.Q.eval env=d.M.eval env ∨ 2*d.Q.eval env=d.M.eval env+1)
    (hk : 2*k.eval env+(if odd then 2 else 1)≤d.M.eval env) (hi : idx.eval env<d.W.eval env) :
    (d.cellGraphProgram length k idx odd false).emit w env =
      copyGraphAt (sourceEndpointChoices (Formula.sourceSigns (d.source w env))) length
        (d.occurrenceCount.eval env) ((d.cellBase k idx odd false).eval env)
        ((d.cellBase k idx odd true).eval env)
        (cellCNF (d.W.eval env) (2*k.eval env+(if odd then 1 else 0)) (idx.eval env) odd
          (d.bits w env (2*k.eval env+(if odd then 1 else 0)) (row (d.W.eval env) odd (idx.eval env)))) := by
  simp only [Layout.cellGraphProgram, Bool.false_eq_true, ↓reduceIte]
  rw [copyGraphBlock_emit (Formula.sourceSigns (d.source w env))
    (d.cellLive k idx odd) d.formulaLength d.variableCount]
  · simp only [copyGraphAt,copiedAt,Layout.cellTemplates_source]
  · intro p hp
    apply (d.cellOccurrences_sound k idx odd w env hq p hp).sign
    change p.live.eval w env=true
    rw [blockOccurrences_live _ _ _ _ _ _ hp]
    exact (d.cellLive_eval k idx odd w env).mpr ⟨hk,hi⟩

theorem Layout.rainbowGraphProgram_copies {n : Nat} (d : Layout n) (length : Nat)
    (k v : NumExpr n) (odd : Bool) (w : SAT.Word) (env : Env n)
    (hq : 2*d.Q.eval env=d.M.eval env ∨ 2*d.Q.eval env=d.M.eval env+1)
    (hk : 2*k.eval env+(if odd then 3 else 2)≤d.M.eval env) (hi : v.eval env<d.W.eval env) :
    (d.rainbowGraphProgram length k v odd false).emit w env =
      copyGraphAt (sourceEndpointChoices (Formula.sourceSigns (d.source w env))) length
        (d.occurrenceCount.eval env) ((d.rainbowBase k v odd false).eval env)
        ((d.rainbowBase k v odd true).eval env)
        (if odd then rbOdd (d.W.eval env) (2*k.eval env+1) (v.eval env)
         else rbEven (d.W.eval env) (2*k.eval env) (v.eval env)) := by
  simp only [Layout.rainbowGraphProgram, Bool.false_eq_true, ↓reduceIte]
  rw [copyGraphBlock_emit (Formula.sourceSigns (d.source w env))
    (d.rainbowLive k v odd) d.formulaLength d.variableCount]
  · cases odd <;> simp only [copyGraphAt,copiedAt,rainbowTemplates_eval,twoE,NumExpr.eval,Bool.false_eq_true,↓reduceIte,Nat.add_zero]
  · intro p hp
    apply (d.rainbowOccurrences_sound k v odd w env hq p hp).sign
    change p.live.eval w env=true
    rw [blockOccurrences_live _ _ _ _ _ _ hp]
    exact (d.rainbowLive_eval k v odd w env).mpr ⟨hk,hi⟩

end STACS2027.PlanarSource.Packed

module

public import NPHardness.PlanarSourceGraphBlockCorrect
public import NPHardness.PlanarSourceGraphProgram

/-! The four emitted graph implication blocks are exact refinements of the
checked finite source successor tables. -/

@[expose] public section
namespace STACS2027.PlanarSource.Packed
open Complexity Complexity.SAT Complexity.StackTableauEmitter Complexity.Planar Comb Grid
open RotationTable

def Layout.sourceRingRecords {n : Nat} (d : Layout n) (length : Nat)
    (w : SAT.Word) (env : Env n) (i : Nat) : CNF :=
  ringRecords (Formula.sourceSigns (d.source w env)) length (d.occurrenceCount.eval env)
    (d.formulaLength.eval env+i) (ringEdge (d.source w env) i)

theorem Layout.startGraphProgram_rings {n : Nat} (d : Layout n) (length : Nat) (k : NumExpr n) (odd : Bool)
    (w : SAT.Word) (env : Env n)
    (hq : 2*d.Q.eval env=d.M.eval env ∨ 2*d.Q.eval env=d.M.eval env+1)
    (hk : 2*k.eval env+(if odd then 2 else 1)≤d.M.eval env) :
    (d.startGraphProgram length k odd true).emit w env =
      expandCopyRecords (d.sourceRingRecords length w env) ((d.startProgram k odd false).emit w env) := by
  simp only [Layout.startGraphProgram, ↓reduceIte]
  apply ringGraphBlock_copies
  · exact (startOccurrences_length d k odd).symm
  · intro p s hp
    obtain ⟨hs,hv,hl⟩ := d.start_zip_position k odd w env hp
    apply successorGraphProgram_source
    · exact gridCNF_combOK (by cases odd <;> simp only [Bool.false_eq_true,↓reduceIte] at hk <;> omega) _
    · exact d.startOccurrences_sound k odd w env hq p (List.of_mem_zip hp).1
    · exact d.startCandidates_sound k odd s w env hq
    · change p.live.eval w env=true
      rw [hl]
      exact (d.columnLive_eval k odd w env).mpr hk
    · exact startCandidates_complete d k odd s p w env hq hs hv

theorem Layout.cellGraphProgram_rings {n : Nat} (d : Layout n) (length : Nat) (k idx : NumExpr n) (odd : Bool)
    (w : SAT.Word) (env : Env n)
    (hq : 2*d.Q.eval env=d.M.eval env ∨ 2*d.Q.eval env=d.M.eval env+1)
    (hk : 2*k.eval env+(if odd then 2 else 1)≤d.M.eval env) (hi : idx.eval env<d.W.eval env) :
    (d.cellGraphProgram length k idx odd true).emit w env =
      expandCopyRecords (d.sourceRingRecords length w env) ((d.cellProgram k idx odd false).emit w env) := by
  simp only [Layout.cellGraphProgram, ↓reduceIte]
  apply ringGraphBlock_copies
  · rw [cellPositions_length]
    exact (cellOccurrences_length d k idx odd).symm
  · intro p s hp
    obtain ⟨hs,hv,hl⟩ := d.cell_zip_position k idx odd w env hp
    apply successorGraphProgram_source
    · exact gridCNF_combOK (by cases odd <;> simp only [Bool.false_eq_true,↓reduceIte] at hk <;> omega) _
    · exact d.cellOccurrences_sound k idx odd w env hq p (List.of_mem_zip hp).1
    · exact d.cellCandidates_sound k idx odd s w env hq
    · change p.live.eval w env=true
      rw [hl]
      exact (d.cellLive_eval k idx odd w env).mpr ⟨hk,hi⟩
    · exact cellCandidates_complete d k idx odd s p w env hq hi hs hv

theorem Layout.endGraphProgram_rings {n : Nat} (d : Layout n) (length : Nat) (k : NumExpr n) (odd : Bool)
    (w : SAT.Word) (env : Env n)
    (hq : 2*d.Q.eval env=d.M.eval env ∨ 2*d.Q.eval env=d.M.eval env+1)
    (hk : 2*k.eval env+(if odd then 2 else 1)≤d.M.eval env) :
    (d.endGraphProgram length k odd true).emit w env =
      expandCopyRecords (d.sourceRingRecords length w env) ((d.endProgram k odd false).emit w env) := by
  simp only [Layout.endGraphProgram, ↓reduceIte]
  apply ringGraphBlock_copies
  · exact (endOccurrences_length d k odd).symm
  · intro p s hp
    obtain ⟨hs,hv,hl⟩ := d.end_zip_position k odd w env hp
    apply successorGraphProgram_source
    · exact gridCNF_combOK (by cases odd <;> simp only [Bool.false_eq_true,↓reduceIte] at hk <;> omega) _
    · exact d.endOccurrences_sound k odd w env hq p (List.of_mem_zip hp).1
    · exact d.endCandidates_sound k odd s w env hq
    · change p.live.eval w env=true
      rw [hl]
      exact (d.columnLive_eval k odd w env).mpr hk
    · exact endCandidates_complete d k odd s p w env hq hs hv

theorem Layout.rainbowGraphProgram_rings {n : Nat} (d : Layout n) (length : Nat) (k v : NumExpr n) (odd : Bool)
    (w : SAT.Word) (env : Env n)
    (hq : 2*d.Q.eval env=d.M.eval env ∨ 2*d.Q.eval env=d.M.eval env+1)
    (hk : 2*k.eval env+(if odd then 3 else 2)≤d.M.eval env) (hi : v.eval env<d.W.eval env) :
    (d.rainbowGraphProgram length k v odd true).emit w env =
      expandCopyRecords (d.sourceRingRecords length w env) ((d.rainbowProgram k v odd false).emit w env) := by
  simp only [Layout.rainbowGraphProgram, ↓reduceIte]
  apply ringGraphBlock_copies
  · exact (rainbowOccurrences_length d k v odd).symm
  · intro p s hp
    obtain ⟨hs,hv,hl⟩ := d.rainbow_zip_position k v odd w env hp
    rw [rainbowEndpoint_eq] at hv
    apply successorGraphProgram_source
    · exact gridCNF_combOK (by cases odd <;> simp only [Bool.false_eq_true,↓reduceIte] at hk <;> omega) _
    · exact d.rainbowOccurrences_sound k v odd w env hq p (List.of_mem_zip hp).1
    · exact d.rainbowCandidates_sound k v odd s w env hq
    · change p.live.eval w env=true
      rw [hl]
      exact (d.rainbowLive_eval k v odd w env).mpr ⟨hk,hi⟩
    · exact rainbowCandidates_complete d k v odd s p w env hq hi hs hv

end STACS2027.PlanarSource.Packed

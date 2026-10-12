module

public import ApproximationHardness.Embed.PlanVertexHeaderBounds
import Lean.Elab.Tactic.Omega

/-! Exact group and empty-parts table values before representative dispatch. -/

@[expose] public section
namespace STACS2027.Embed.PlanRAM
open RAM

attribute [local simp] zBase vertex degree vertexParent dart opposite child childParent
  itemType itemValue distinguished vertexBound partCount topVertex remaining slot
  address test otherTest exclusion representative constant

theorem vertexHeaderValues_run_skip (c : Config) : run .skip c=c := rfl

/-- The header's exact memory effect consists of two identifiers and ten empty defaults. -/
theorem vertexHeader_mem {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) :
    let v:=c.reg vertex
    let w:=2*G.E+v
    let b:=c.reg vertexBound
    (run vertexHeader c).mem=
      upd (upd (upd (upd (upd
      (upd (upd (upd (upd (upd
      (upd (upd c.mem ((solverLayout L).cell 15 v) (b+v))
        ((solverLayout L).cell 15 w) (b+w))
        ((solverLayout L).cell 16 v) 0) ((solverLayout L).cell 17 v) 0)
        ((solverLayout L).cell 18 v) 0) ((solverLayout L).cell 19 v) 0)
        ((solverLayout L).cell 20 v) 0)
        ((solverLayout L).cell 16 w) 0) ((solverLayout L).cell 17 w) 0)
        ((solverLayout L).cell 18 w) 0) ((solverLayout L).cell 19 w) 0)
        ((solverLayout L).cell 20 w) 0 := by
  generalize he₁ : run storeVertexGroups c=c₁
  have hc₁ : Context L G s c₁ := he₁ ▸ hc.storeVertexGroups
  have hv₁ : c₁.reg vertex=c.reg vertex := by rw [←he₁]; exact storeVertexGroups_reg c vertex (by decide)
  generalize he₂ : run (clearParts vertex) c₁=c₂
  have hc₂ : Context L G s c₂ := he₂ ▸ clearParts_context hc₁ vertex (by decide)
  have ht₂ : c₂.reg topVertex=2*G.E+c.reg vertex := by rw [←he₂,clearParts_reg _ _ _ (by decide),←he₁]; exact storeVertexGroups_top hc
  generalize he₃ : run (clearParts topVertex) c₂=c₃
  have hm₃ := clearParts_mem hc₂ topVertex (by decide)
  rw [he₃,ht₂] at hm₃
  have hm₂ := clearParts_mem hc₁ vertex (by decide)
  rw [he₂,hv₁] at hm₂
  have hm₁ := storeVertexGroups_mem hc
  rw [he₁] at hm₁
  simp only [vertexHeader,seqs,run_seq,vertexHeaderValues_run_skip,he₁,he₂,he₃]
  rw [run_mem_frame vertexLookup c₃ (by decide),hm₃,hm₂,hm₁]

/-- The ordinary and synthetic nodes have their exact reserved group identifiers. -/
theorem vertexHeader_groups {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) {r : Nat} (hr : r<2*G.E) (hv : c.reg vertex=r)
    (hbound : c.reg vertexBound=4*G.E) (hw : 4*G.E≤L.width) :
    (run vertexHeader c).mem ((solverLayout L).cell 15 r)=4*G.E+r ∧
    (run vertexHeader c).mem ((solverLayout L).cell 15 (2*G.E+r))=4*G.E+(2*G.E+r) := by
  have hvr : r<(solverLayout L).width := hr.trans_le hc.dartCapacity
  have hwt : 2*G.E+r<(solverLayout L).width := by dsimp [solverLayout]; omega
  have hne : r≠2*G.E+r := by omega
  rw [vertexHeader_mem hc]
  simp only [hv,hbound]
  simp only [RAMSolver.update_cell (solverLayout L) _ _ _ _ _ _ hvr hwt,
    RAMSolver.update_cell (solverLayout L) _ _ _ _ _ _ hvr hvr,
    RAMSolver.update_cell (solverLayout L) _ _ _ _ _ _ hwt hwt,
    RAMSolver.update_cell (solverLayout L) _ _ _ _ _ _ hwt hvr]
  simp [hne]

/-- Both node entries start with exactly the empty-list table encoding. -/
theorem vertexHeader_empty {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) {r : Nat} (hr : r<2*G.E) (hv : c.reg vertex=r)
    (hw : 4*G.E≤L.width) :
    PartSlots (solverLayout L) (run vertexHeader c).mem r [] ∧
    (run vertexHeader c).mem ((solverLayout L).cell 16 r)=0 ∧
    PartSlots (solverLayout L) (run vertexHeader c).mem (2*G.E+r) [] ∧
    (run vertexHeader c).mem ((solverLayout L).cell 16 (2*G.E+r))=0 := by
  have hvr : r<(solverLayout L).width := hr.trans_le hc.dartCapacity
  have hwt : 2*G.E+r<(solverLayout L).width := by dsimp [solverLayout]; omega
  have hne : r≠2*G.E+r := by omega
  rw [vertexHeader_mem hc]
  simp only [PartSlots,hv]
  simp only [RAMSolver.update_cell (solverLayout L) _ _ _ _ _ _ hvr hwt,
    RAMSolver.update_cell (solverLayout L) _ _ _ _ _ _ hvr hvr,
    RAMSolver.update_cell (solverLayout L) _ _ _ _ _ _ hwt hwt,
    RAMSolver.update_cell (solverLayout L) _ _ _ _ _ _ hwt hvr]
  simp [hne,RAMSolver.itemType,RAMSolver.itemValue]

end STACS2027.Embed.PlanRAM

module

public import ApproximationHardness.Embed.PlanVertexHeader
import Lean.Elab.Tactic.Omega

/-! Actual address-safe execution of the two-node vertex-table header. -/

@[expose] public section

namespace STACS2027.Embed.PlanRAM
open RAM

attribute [local simp] zBase vertex degree vertexParent dart opposite child childParent
  itemType itemValue distinguished vertexBound partCount topVertex remaining slot
  address test otherTest exclusion representative constant

theorem vertexHeaderBounds_run_skip (c : Config) : run .skip c = c := rfl

/-- Clearing the five parts cells is a bounded instruction block. -/
theorem clearParts_plan_addrOK {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) (index : Nat) (hi : index≠address)
    (hv : c.reg index<L.width) : AddrOK (zLimit L) (clearParts index) c := by
  have hlim : (solverLayout L).limit≤zLimit L := by dsimp [zLimit]; omega
  have hb (j : Nat) (hj : j<22) := hc.solver.2.2.2.2 j hj
  have ha (j : Nat) (hj : j<22) : (solverLayout L).cell j (c.reg index)<zLimit L :=
    ((solverLayout L).cell_lt hj hv).trans_le hlim
  simp only [RAMSolver.Layout.cell] at ha
  simp [clearParts,planStore,seqs,AddrOK,run,hi,hb 16 (by decide),
    hb 17 (by decide),hb 18 (by decide),hb 19 (by decide),hb 20 (by decide),
    ha 16 (by decide),ha 17 (by decide),ha 18 (by decide),ha 19 (by decide),ha 20 (by decide)]

/-- The two group stores use the ordinary and synthetic node indices within the layout. -/
theorem storeVertexGroups_addrOK {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) (hv : c.reg vertex<L.width)
    (htop : 2*G.E+c.reg vertex<L.width) : AddrOK (zLimit L) storeVertexGroups c := by
  have hlim : (solverLayout L).limit≤zLimit L := by dsimp [zLimit]; omega
  have h₁ := ((solverLayout L).cell_lt (j:=15) (by decide) hv).trans_le hlim
  have h₂ := ((solverLayout L).cell_lt (j:=15) (by decide) htop).trans_le hlim
  simp only [RAMSolver.Layout.cell] at h₁ h₂
  simp [storeVertexGroups,planStore,seqs,AddrOK,run,hc.forest.bases.2.2.1,
    hc.solver.2.2.2.2 15 (by decide),h₁,h₂]

/-- Reading the representative has exactly one bounded forest-cell access. -/
theorem vertexLookup_addrOK {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) (hv : c.reg vertex<2*G.E) :
    AddrOK (zLimit L) vertexLookup c := by
  simp only [vertexLookup,addrOK_seqs_cons]
  refine ⟨readForest_addrOK hc _ _ _ (by decide) hv,?_⟩
  simp [seqs,AddrOK]

/-- The full vertex header is an actual bounded RAM block. -/
theorem vertexHeader_addrOK {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) (hv : c.reg vertex<2*G.E)
    (htop : 2*G.E+c.reg vertex<L.width) : AddrOK (zLimit L) vertexHeader c := by
  have hwidth : c.reg vertex<L.width := hv.trans_le hc.dartCapacity
  generalize he₁ : run storeVertexGroups c=c₁
  have hc₁ : Context L G s c₁ := he₁ ▸ hc.storeVertexGroups
  have hv₁ : c₁.reg vertex=c.reg vertex := by rw [←he₁]; exact storeVertexGroups_reg c vertex (by decide)
  have ht₁ : c₁.reg topVertex=2*G.E+c.reg vertex := by rw [←he₁]; exact storeVertexGroups_top hc
  generalize he₂ : run (clearParts vertex) c₁=c₂
  have hc₂ : Context L G s c₂ := he₂ ▸ clearParts_context hc₁ vertex (by decide)
  have hv₂ : c₂.reg vertex=c.reg vertex := by rw [←he₂,clearParts_reg _ _ _ (by decide),hv₁]
  have ht₂ : c₂.reg topVertex=2*G.E+c.reg vertex := by rw [←he₂,clearParts_reg _ _ _ (by decide),ht₁]
  generalize he₃ : run (clearParts topVertex) c₂=c₃
  have hc₃ : Context L G s c₃ := he₃ ▸ clearParts_context hc₂ topVertex (by decide)
  have hv₃ : c₃.reg vertex=c.reg vertex := by rw [←he₃,clearParts_reg _ _ _ (by decide),hv₂]
  simp only [vertexHeader,addrOK_seqs_cons,addrOK_seqs_nil,and_true,he₁,he₂,he₃]
  exact ⟨storeVertexGroups_addrOK hc hwidth htop,
    clearParts_plan_addrOK hc₁ vertex (by decide) (by rw [hv₁]; exact hwidth),
    clearParts_plan_addrOK hc₂ topVertex (by decide) (by rw [ht₂]; exact htop),
    vertexLookup_addrOK hc₃ (by rw [hv₃]; exact hv)⟩

/-- A fixed constant bounds the actual header execution. -/
theorem vertexHeader_exec {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) (hv : c.reg vertex<2*G.E)
    (htop : 2*G.E+c.reg vertex<L.width) :
    ∃t,ExecB (zLimit L) vertexHeader c t (run vertexHeader c) ∧ t≤100 := by
  have hlp : LoopFree vertexHeader := by simp [vertexHeader,storeVertexGroups,vertexLookup,clearParts,planStore,readForest,seqs,LoopFree]
  have hs : size vertexHeader≤100 := by decide
  exact ⟨_,execB_run _ hlp c (vertexHeader_addrOK hc hv htop),(cost_le_size _ _).trans hs⟩

end STACS2027.Embed.PlanRAM

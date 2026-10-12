module

public import ApproximationHardness.Embed.PlanDistinguishedBounds
public import ApproximationHardness.Embed.PlanPartsRAM
import Lean.Elab.Tactic.Omega

/-! Group identifiers, empty defaults, and representative dispatch for one plan vertex. -/

@[expose] public section

namespace STACS2027.Embed.PlanRAM
open RAM

attribute [local simp] zBase vertex degree vertexParent dart opposite child childParent
  itemType itemValue distinguished vertexBound partCount topVertex remaining slot
  address test otherTest exclusion representative constant

/-- Write the two group identifiers for a dart-indexed vertex position. -/
def storeVertexGroups : Stmt := seqs [
  .add topVertex DFSRAM.dartCount vertex,
  .add itemValue vertexBound vertex, planStore 15 vertex itemValue,
  .add itemValue vertexBound topVertex, planStore 15 topVertex itemValue]

/-- Test whether the current dart index is its own vertex representative. -/
def vertexLookup : Stmt := seqs [readForest representative 0 vertex,
  .sub test representative vertex, .sub otherTest vertex representative, .add test test otherTest]

/-- Read-only dispatcher header after empty table defaults have been installed. -/
def vertexHeader : Stmt := seqs [storeVertexGroups, clearParts vertex,
  clearParts topVertex, vertexLookup]

theorem vertexHeader_run_skip (c : Config) : run .skip c = c := rfl

/-- Exact two-cell memory effect of group-id installation. -/
theorem storeVertexGroups_mem {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) :
    (run storeVertexGroups c).mem =
      upd (upd c.mem ((solverLayout L).cell 15 (c.reg vertex))
        (c.reg vertexBound+c.reg vertex))
        ((solverLayout L).cell 15 (2*G.E+c.reg vertex))
        (c.reg vertexBound+(2*G.E+c.reg vertex)) := by
  have hb := hc.solver.2.2.2.2 15 (by decide)
  have hD := hc.forest.bases.2.2.1
  funext a
  simp [storeVertexGroups, planStore, seqs, run, Config.setMem, upd, hb, hD,
    RAMSolver.Layout.cell, hc.solver.1]
  rfl

/-- The group store has the expected top index and protects all other fixed metadata. -/
theorem storeVertexGroups_reg (c : Config) (r : Nat)
    (hr : r∉[289,293,300]) : (run storeVertexGroups c).reg r=c.reg r := by
  apply run_reg_frame
  intro hn
  have hw : (regsW storeVertexGroups).all (fun q => decide (q∈[289,293,300]))=true := by decide
  exact hr (of_decide_eq_true ((List.all_eq_true.mp hw) r hn))

theorem storeVertexGroups_top {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) :
    (run storeVertexGroups c).reg topVertex=2*G.E+c.reg vertex := by
  simp [storeVertexGroups, planStore, seqs, run, hc.forest.bases.2.2.1]

/-- The group stores protect the complete installed forest and layout context. -/
theorem Context.storeVertexGroups {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) : Context L G s (run storeVertexGroups c) := by
  apply hc.memory (fun r hr => storeVertexGroups_reg c r (by simp; omega))
  intro a ha
  rw [storeVertexGroups_mem hc]
  have hlo (i : Nat) : L.limit≤(solverLayout L).cell 15 i := by
    dsimp [solverLayout, RAMSolver.Layout.cell, RAMSolver.Layout.block]; omega
  simp [upd, show a≠(solverLayout L).cell 15 (c.reg vertex) by have := hlo (c.reg vertex); omega,
    show a≠(solverLayout L).cell 15 (2*G.E+c.reg vertex) by have := hlo (2*G.E+c.reg vertex); omega]

/-- Group-id cells are disjoint from all initially zero mutable solver arrays. -/
theorem MutableZero.storeVertexGroups {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hz : MutableZero L c) (hc : Context L G s c)
    (hv : c.reg vertex<L.width) (htop : 2*G.E+c.reg vertex<L.width) :
    MutableZero L (run storeVertexGroups c) := by
  intro j hj i hi
  rw [storeVertexGroups_mem hc,
    RAMSolver.update_cell (solverLayout L) _ j 15 i (2*G.E+c.reg vertex) _ hi htop,
    RAMSolver.update_cell (solverLayout L) _ j 15 i (c.reg vertex) _ hi hv]
  simp only [show ¬(j=15∧i=2*G.E+c.reg vertex) by omega,
    show ¬(j=15∧i=c.reg vertex) by omega, ↓reduceIte]
  exact hz j hj i hi

/-- The representative lookup protects the complete compilation context. -/
theorem Context.vertexLookup {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) : Context L G s (run vertexLookup c) := by
  apply hc.readOnly (p := PlanRAM.vertexLookup) (by decide)
  have hw : (regsW PlanRAM.vertexLookup).all (fun q => decide (281≤q))=true := by decide
  intro q hq
  exact of_decide_eq_true ((List.all_eq_true.mp hw) q hq)

theorem vertexLookup_reg (c : Config) (r : Nat) (hr : r∉[300,301,302,304]) :
    (run vertexLookup c).reg r=c.reg r := by
  apply run_reg_frame
  have hw : (regsW vertexLookup).all (fun q => decide (q∈[300,301,302,304]))=true := by decide
  intro hn; exact hr (of_decide_eq_true ((List.all_eq_true.mp hw) r hn))

/-- The representative test is precisely symmetric equality, without truncated-subtraction ambiguity. -/
theorem vertexLookup_test {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) {r : Nat} (hr : r<2*G.E) (hv : c.reg vertex=r) :
    (run vertexLookup c).reg test=0 ↔ G.rep r=r := by
  have hh := hc.tables.representatives r hr
  simp only [DFSRAM.Layout.cell] at hh
  have he : G.rep r-r=0∧r-G.rep r=0 ↔ G.rep r=r := by omega
  simp [vertexLookup, readForest, seqs, run, hv, hc.forest.bases.2.2.2.2.2 0 (by decide), hh, he]

/-- The vertex header preserves the exact forest context. -/
theorem Context.vertexHeader {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) : Context L G s (run vertexHeader c) := by
  have h₁ := hc.storeVertexGroups
  have h₂ := clearParts_context h₁ vertex (by decide)
  have h₃ := clearParts_context h₂ topVertex (by decide)
  exact h₃.vertexLookup

/-- Every scalar outside the header scratch destinations is protected. -/
theorem vertexHeader_reg (c : Config) (r : Nat) (hr : r∉[289,293,300,301,302,304]) :
    (run vertexHeader c).reg r=c.reg r := by
  apply run_reg_frame
  have hw : (regsW vertexHeader).all (fun q => decide (q∈[289,293,300,301,302,304]))=true := by decide
  intro hn; exact hr (of_decide_eq_true ((List.all_eq_true.mp hw) r hn))

/-- Header initialization supplies the synthetic top's exact index. -/
theorem vertexHeader_top {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) : (run vertexHeader c).reg topVertex=2*G.E+c.reg vertex := by
  simp only [vertexHeader, seqs, run_seq, vertexHeader_run_skip]
  rw [vertexLookup_reg _ topVertex (by decide),
    clearParts_reg _ topVertex topVertex (by decide),
    clearParts_reg _ vertex topVertex (by decide)]
  exact storeVertexGroups_top hc

/-- Clear-parts writes protect every address outside that node's five cells. -/
theorem clearParts_mem_frame {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) (index : Nat) (hi : index≠address) (a : Nat)
    (hn : ∀ j, j∈[16,17,18,19,20] → a≠(solverLayout L).cell j (c.reg index)) :
    (run (clearParts index) c).mem a=c.mem a := by
  rw [clearParts_mem hc index hi]
  simp [upd, hn 16 (by decide), hn 17 (by decide), hn 18 (by decide),
    hn 19 (by decide), hn 20 (by decide)]

/-- Header initialization changes only the two nodes' six plan-table cells. -/
theorem vertexHeader_mem_frame {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) (a : Nat)
    (hn : ∀ j, j∈[15,16,17,18,19,20] →
      a≠(solverLayout L).cell j (c.reg vertex) ∧
      a≠(solverLayout L).cell j (2*G.E+c.reg vertex)) :
    (run vertexHeader c).mem a=c.mem a := by
  generalize he₁ : run storeVertexGroups c=c₁
  have hc₁ : Context L G s c₁ := he₁ ▸ hc.storeVertexGroups
  have hv₁ : c₁.reg vertex=c.reg vertex := by rw [←he₁]; exact storeVertexGroups_reg c vertex (by decide)
  have ht₁ : c₁.reg topVertex=2*G.E+c.reg vertex := by rw [←he₁]; exact storeVertexGroups_top hc
  generalize he₂ : run (clearParts vertex) c₁=c₂
  have hc₂ : Context L G s c₂ := he₂ ▸ clearParts_context hc₁ vertex (by decide)
  have ht₂ : c₂.reg topVertex=2*G.E+c.reg vertex := by rw [←he₂,clearParts_reg _ _ _ (by decide),ht₁]
  generalize he₃ : run (clearParts topVertex) c₂=c₃
  simp only [vertexHeader,seqs,run_seq,vertexHeader_run_skip,he₁,he₂,he₃]
  rw [run_mem_frame vertexLookup c₃ (by decide),←he₃]
  rw [clearParts_mem_frame hc₂ topVertex (by decide) a (by
    intro j hj; rw [ht₂]; exact (hn j (by simp at hj ⊢; omega)).2)]
  rw [←he₂,clearParts_mem_frame hc₁ vertex (by decide) a (by
    intro j hj; rw [hv₁]; exact (hn j (by simp at hj ⊢; omega)).1)]
  rw [←he₁,storeVertexGroups_mem hc]
  simp [upd,(hn 15 (by decide)).1,(hn 15 (by decide)).2]

/-- Empty defaults and group identifiers preserve all zero mutable arrays. -/
theorem MutableZero.vertexHeader {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hz : MutableZero L c) (hc : Context L G s c)
    (hv : c.reg vertex<L.width) (htop : 2*G.E+c.reg vertex<L.width) :
    MutableZero L (run vertexHeader c) := by
  generalize he₁ : run PlanRAM.storeVertexGroups c=c₁
  have hc₁ : Context L G s c₁ := he₁ ▸ hc.storeVertexGroups
  have hz₁ : MutableZero L c₁ := he₁ ▸ hz.storeVertexGroups hc hv htop
  have hv₁ : c₁.reg vertex<L.width := by rw [←he₁,storeVertexGroups_reg c vertex (by decide)]; exact hv
  have ht₁ : c₁.reg topVertex<L.width := by rw [←he₁,storeVertexGroups_top hc]; exact htop
  generalize he₂ : run (clearParts vertex) c₁=c₂
  have hc₂ : Context L G s c₂ := he₂ ▸ clearParts_context hc₁ vertex (by decide)
  have hz₂ : MutableZero L c₂ := he₂ ▸ clearParts_mutable hc₁ hz₁ vertex (by decide) hv₁
  have ht₂ : c₂.reg topVertex<L.width := by rw [←he₂,clearParts_reg _ _ _ (by decide)]; exact ht₁
  generalize he₃ : run (clearParts topVertex) c₂=c₃
  have hz₃ : MutableZero L c₃ := he₃ ▸ clearParts_mutable hc₂ hz₂ topVertex (by decide) ht₂
  simp only [PlanRAM.vertexHeader,seqs,run_seq,vertexHeader_run_skip,he₁,he₂,he₃]
  intro j hj i hi
  rw [run_mem_frame vertexLookup c₃ (by decide)]
  exact hz₃ j hj i hi

end STACS2027.Embed.PlanRAM

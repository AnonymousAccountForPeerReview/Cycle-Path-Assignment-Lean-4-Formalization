module

public import ApproximationHardness.Embed.PlanVertexRAM
import Lean.Elab.Tactic.Omega

/-! Address bounds for finite plan-table instructions and adjacency scans. -/

@[expose] public section

namespace STACS2027.Embed.PlanRAM
open RAM

attribute [local simp] zBase vertex degree vertexParent dart opposite child childParent
  itemType itemValue distinguished vertexBound partCount topVertex remaining slot
  address test otherTest exclusion representative constant

/-- Every cached forest-cell read stays inside the original DFS memory layout. -/
theorem readForest_addrOK {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) (dst block index : Nat) (hj : block < 11)
    (hi : c.reg index < 2 * G.E) : AddrOK (zLimit L) (readForest dst block index) c := by
  have hb := hc.forest.bases.2.2.2.2.2 block hj
  have hlt := DFSRAM.Layout.cell_lt (L := L) hj (hi.trans_le hc.dartCapacity)
  have hlim : L.limit ≤ zLimit L := by dsimp [zLimit, solverLayout, RAMSolver.Layout.limit]; omega
  simp only [DFSRAM.Layout.cell] at hlt
  simp [readForest, seqs, AddrOK, run, hb, hlt.trans_le hlim]

/-- Actual plan-table stores are safe at every installed solver-plan block. -/
theorem planStore_addrOK {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) (j index src : Nat) (hj : j < 22)
    (hi : c.reg index < L.width) : AddrOK (zLimit L) (planStore j index src) c := by
  obtain ⟨t, he, _⟩ := planStore_exec hc j index src hj hi
  exact (RAMSolver.boundedRun_addr he (by simp [planStore, seqs, LoopFree])).2

/-- Distinguished-cache stores use their separate width-sized bounded memory block. -/
theorem zStore_addrOK {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) (index src : Nat) (hi : c.reg index < L.width) :
    AddrOK (zLimit L) (zStore index src) c := by
  obtain ⟨t, he, _⟩ := zStore_exec hc index src hi
  exact (RAMSolver.boundedRun_addr he (by simp [zStore, seqs, LoopFree])).2

/-- Cached item decoding also stays within the combined plan-compilation layout. -/
theorem cachedItem_plan_addrOK {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) (hG : G.Ok) {d : Nat}
    (hd : d < 2 * G.E) (hv : c.reg dart = d) : AddrOK (zLimit L) cachedItem c := by
  apply AddrOK.mono (show L.limit ≤ zLimit L by dsimp [zLimit, solverLayout, RAMSolver.Layout.limit]; omega)
  exact cachedItem_addrOK hc.forest hc.tables hG hd hv hc.dartCapacity

/-- One valid distinguished adjacency slot is an address-safe RAM instruction block. -/
theorem distinguishedSlot_addrOK {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) (hG : G.Ok) {r k : Nat} (hr : r < 2 * G.E)
    (hk : k < 3) (hvalid : k < (G.darts r).length) (hv : c.reg vertex = r) :
    AddrOK (zLimit L) (distinguishedSlot k) c := by
  let c₁ := run (readForest dart (3+k) vertex) c
  have hc₁ := hc.readForest dart (3+k) vertex (by decide)
  have hd : c₁.reg dart = (G.darts r).getD k 0 := by
    have hx := hc.tables.adjacent k hk r hr
    simpa [c₁, readForest, run, seqs, hv, hc.forest.bases.2.2.2.2.2 (3+k) (by omega), DFSRAM.Layout.cell] using hx
  have hb : (G.darts r).getD k 0 < 2 * G.E := (DG.mem_darts.mp (DG.getD_mem hvalid)).1
  simp only [distinguishedSlot, addrOK_seqs_cons]
  refine ⟨readForest_addrOK hc _ _ _ (by omega) (by simpa [hv] using hr), ?_⟩
  refine ⟨cachedItem_plan_addrOK hc₁ hG hb hd, ?_⟩
  simp [seqs, AddrOK]

end STACS2027.Embed.PlanRAM

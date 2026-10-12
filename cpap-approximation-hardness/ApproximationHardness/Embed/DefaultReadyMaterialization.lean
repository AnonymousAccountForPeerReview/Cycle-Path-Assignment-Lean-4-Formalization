module

public import ApproximationHardness.Embed.PlanStoreRAM
public import ApproximationHardness.Embed.BufferHeaders
public import ApproximationHardness.Embed.SolverPhaseFrames
public import ApproximationHardness.Embed.DefaultRotationLoop
public import ApproximationHardness.Embed.DefaultReadyHelpers
import Lean.Elab.Tactic.Omega

/-! The compiled forest and plan caches supply every finite read of the
actual default-rotation pass after its output-buffer header. -/

@[expose] public section

namespace STACS2027.Embed.RAMSolver

open RAM

theorem bufferHeaders_context {D : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : PlanRAM.Context D G s c) : PlanRAM.Context D G s (run bufferHeaders c) := by
  have hm := (bufferHeaders_frame c).1
  have hf := (bufferHeaders_frame c).2.2
  have hfb : DFSRAM.Bases D G (run bufferHeaders c) := by
    apply hc.forest.bases.frame
    intro r hr
    simp only [DFSRAM.dartCount, DFSRAM.baseRegister, DFSRAM.widthRegister] at hr
    apply hf <;> rcases hr with hr | hr | hr | hr | hr | hr <;> omega
  have hfr : DFSRAM.Rep D G (run bufferHeaders c) s := by
    refine hc.forest.memory.of_regs hm hfb ?_ ?_ ?_ ?_ ?_
    · exact (hf _ (by decide) (by decide) (by decide) (by decide)).trans hc.forest.scan
    · exact (hf _ (by decide) (by decide) (by decide) (by decide)).trans hc.forest.current
    · exact (hf _ (by decide) (by decide) (by decide) (by decide)).trans hc.forest.inner
    · exact (hf _ (by decide) (by decide) (by decide) (by decide)).trans hc.forest.height
    · exact (hf _ (by decide) (by decide) (by decide) (by decide)).trans hc.forest.postLength
  exact ⟨hfr, hc.tables.mem_congr hm,
    hc.solver.finiteFrame (fun r hr => hf r (by omega) (by omega) (by omega) (by omega)),
    (hf _ (by decide) (by decide) (by decide) (by decide)).trans hc.zbase,
    hc.postCapacity, hc.dartCapacity,
    (hf _ (by decide) (by decide) (by decide) (by decide)).trans hc.postLength,
    (hf _ (by decide) (by decide) (by decide) (by decide)).trans hc.infinity⟩

theorem bufferHeaders_solverRep {L : Layout} {c : Config} {state : SMS}
    (h : Rep L c state) : Rep L (run bufferHeaders c) state := by
  apply h.finiteFrame
  · intro r hr
    exact (bufferHeaders_frame c).2.2 r (by omega) (by omega) (by omega) (by omega)
  · intro a ha
    exact congrFun (bufferHeaders_frame c).1 a

theorem bufferHeaders_solverTables {L : Layout} {c : Config} {sol : Sol} {post : List Nat}
    {vertices darts : Nat} (h : Tables L c sol post vertices darts) :
    Tables L (run bufferHeaders c) sol post vertices darts := by
  apply h.prefixFrame
  · intro r hr
    exact (bufferHeaders_frame c).2.2 r (by omega) (by omega) (by omega) (by omega)
  · intro a ha
    exact congrFun (bufferHeaders_frame c).1 a

theorem defaultReadyMaterialization {D : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : PlanRAM.Context D G s c)
    (_hG : G.Ok) (hF : (G.fd s).Valid)
    (ht : Tables (PlanRAM.solverLayout D) c ((G.fd s).sol hF) s.post (4 * G.E) (2 * G.E))
    (hw : 8 * G.E ≤ D.width)
    (hz : ∀ v, v < 2 * G.E → c.mem (c.reg 280 + v) = (G.fd s).zOf v) :
    DefaultReady (G.fd s) (bufferLimit (PlanRAM.solverLayout D)) (run bufferHeaders c) := by
  let L := PlanRAM.solverLayout D
  let e := run bufferHeaders c
  have hE : (G.fd s).E = G.E := rfl
  have hwidth : 2 * G.E ≤ D.width := by omega
  have hmem : e.mem = c.mem := (bufferHeaders_frame c).1
  have hreg (r : Nat) (h₁ : r ≠ 100) (h₂ : r ≠ 113) (h₃ : r ≠ 261) (h₄ : r ≠ 262) :
      e.reg r = c.reg r := (bufferHeaders_frame c).2.2 r h₁ h₂ h₃ h₄
  have hh := bufferHeaders_values L c hc.zbase hc.solver.2.2.2.1
  have hsolverBase (j : Nat) (hj : j < 22) : e.reg (50 + j) = L.block j :=
    (hreg _ (by omega) (by omega) (by omega) (by omega)).trans (hc.solver.2.2.2.2 j hj)
  have hforestBase (j : Nat) (hj : j < 11) : e.reg (160 + j) = D.block j :=
    (hreg _ (by omega) (by omega) (by omega) (by omega)).trans (hc.forest.bases.2.2.2.2.2 j hj)
  have hnext : e.reg 261 = nextBase L := hh.2.2.1
  have hpred : e.reg 262 = predBase L := hh.2.2.2
  have hsolverBelow : L.limit ≤ nextBase L := by
    dsimp [nextBase, keyBase, orientationBase]; omega
  have hforestBelow : D.limit ≤ nextBase L := by
    have hlimits : D.limit ≤ L.limit := by dsimp [L, PlanRAM.solverLayout, Layout.limit]; omega
    exact hlimits.trans hsolverBelow
  have hsolverSource (j i : Nat) (hj : j < 22) (hi : i < 2 * G.E) :
      e.reg (50 + j) + i < e.reg 261 := by
    rw [hsolverBase j hj, hnext]
    exact (Layout.cell_lt (L := L) hj (hi.trans_le hwidth)).trans_le hsolverBelow
  have hforestSource (j i : Nat) (hj : j < 11) (hi : i < 2 * G.E) :
      e.reg (160 + j) + i < e.reg 261 := by
    rw [hforestBase j hj, hnext]
    exact (DFSRAM.Layout.cell_lt (L := D) hj (hi.trans_le hwidth)).trans_le hforestBelow
  refine ⟨(hreg 0 (by decide) (by decide) (by decide) (by decide)).trans hc.solver.1,
    (hreg 1 (by decide) (by decide) (by decide) (by decide)).trans hc.solver.2.1,
    (hreg 140 (by decide) (by decide) (by decide) (by decide)).trans hc.forest.bases.2.2.1,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun v hv => ForestData.real_parts_bound hF hv,
    fun v hv w hw => ForestData.real_child_bound hF hv hw⟩
  · rw [hnext, hpred]; dsimp [predBase, L, PlanRAM.solverLayout]; omega
  · rw [hpred]; dsimp [bufferLimit, L, PlanRAM.solverLayout]; omega
  · intro r hr i hi
    simp only [defaultSourceRegisters, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hsolverSource 16 i (by decide) hi
    · exact hsolverSource 17 i (by decide) hi
    · exact hsolverSource 18 i (by decide) hi
    · exact hsolverSource 19 i (by decide) hi
    · exact hsolverSource 20 i (by decide) hi
    · exact hforestSource 0 i (by decide) hi
    · exact hforestSource 1 i (by decide) hi
    · exact hforestSource 2 i (by decide) hi
    · exact hforestSource 6 i (by decide) hi
    · rw [hreg 280 (by decide) (by decide) (by decide) (by decide), hc.zbase, hnext]
      dsimp [nextBase, keyBase, orientationBase, L, PlanRAM.solverLayout]
      omega
  · intro d hd; rw [hmem, hforestBase 0 (by decide)]
    exact hc.tables.representatives d hd
  · intro v hv; rw [hmem, hforestBase 6 (by decide)]
    exact hc.forest.parents v hv
  · intro d hd; rw [hmem, hforestBase 1 (by decide)]
    exact hc.tables.partners d hd
  · intro v hv; rw [hmem, hforestBase 2 (by decide)]
    exact hc.tables.degrees v hv
  · intro v hv; rw [hmem, hsolverBase 16 (by decide)]
    exact ht.counts v (by omega)
  · intro v hv; rw [hmem, hsolverBase 17 (by decide)]
    exact ht.leftType v (by omega)
  · intro v hv; rw [hmem, hsolverBase 18 (by decide)]
    exact ht.leftValue v (by omega)
  · intro v hv; rw [hmem, hsolverBase 19 (by decide)]
    exact ht.rightType v (by omega)
  · intro v hv; rw [hmem, hsolverBase 20 (by decide)]
    exact ht.rightValue v (by omega)
  · intro v hv
    rw [hmem, hreg 280 (by decide) (by decide) (by decide) (by decide)]
    exact hz v hv

end STACS2027.Embed.RAMSolver

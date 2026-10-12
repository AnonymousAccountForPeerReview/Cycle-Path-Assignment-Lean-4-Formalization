module

public import ApproximationHardness.Embed.SolverPhaseFrames
public import ApproximationHardness.Embed.BufferHeaders
public import ApproximationHardness.Embed.SolverInit

/-! # The finite runtime contract shared by the completed solver and output passes -/

@[expose] public section

namespace STACS2027.Embed.RAMSolver

open RAM

def completedSolver (G : DG) (s : DS) (hF : (G.fd s).Valid) : SMS :=
  ((G.fd s).sol hF).runPrefix s.post initialState s.post.length

structure EmbeddingRuntime (D : DFSRAM.Layout) (G : DG) (s : DS)
    (hF : (G.fd s).Valid) (c : Config) : Prop where
  forestBases : DFSRAM.Bases D G c
  forestTables : DFSRAM.Tables D G c
  solver : Rep (PlanRAM.solverLayout D) c (completedSolver G s hF)
  tables : Tables (PlanRAM.solverLayout D) c ((G.fd s).sol hF) s.post (4*G.E) (2*G.E)
  orientation : c.reg 100=orientationBase (PlanRAM.solverLayout D)
  keys : c.reg 113=keyBase (PlanRAM.solverLayout D)
  nextBase : c.reg 261=RAMSolver.nextBase (PlanRAM.solverLayout D)
  previousBase : c.reg 262=predBase (PlanRAM.solverLayout D)
  next : ∀ d,d<2*G.E → c.mem (RAMSolver.nextBase (PlanRAM.solverLayout D)+d)=
    ForestData.rotN hF (fun _=>false) d
  previous : ∀ d,d<2*G.E → c.mem (predBase (PlanRAM.solverLayout D)+d)=
    ForestData.rotInvN hF (fun _=>false) d
  output : c.out=[]

theorem EmbeddingRuntime.frame {D : DFSRAM.Layout} {G : DG} {s : DS}
    {hF : (G.fd s).Valid} {c d : Config} (h : EmbeddingRuntime D G s hF c)
    (hw : 2*G.E≤D.width)
    (hlow : ∀ r,r<72 → d.reg r=c.reg r)
    (hhigh : ∀ r,(140≤r ∧ r≤170) ∨ r=100 ∨ r=113 ∨ r=261 ∨ r=262 → d.reg r=c.reg r)
    (hmem : ∀ a,a<(PlanRAM.solverLayout D).limit → d.mem a=c.mem a)
    (hnext : ∀ i,i<2*G.E → d.mem (RAMSolver.nextBase (PlanRAM.solverLayout D)+i)=
      c.mem (RAMSolver.nextBase (PlanRAM.solverLayout D)+i))
    (hprev : ∀ i,i<2*G.E → d.mem (predBase (PlanRAM.solverLayout D)+i)=
      c.mem (predBase (PlanRAM.solverLayout D)+i))
    (hout : d.out=c.out) : EmbeddingRuntime D G s hF d := by
  have hforestBound : D.limit≤(PlanRAM.solverLayout D).limit := by
    dsimp [PlanRAM.solverLayout,Layout.limit];omega
  refine ⟨h.forestBases.phaseFrame ?_,h.forestTables.prefixFrame hw
    (fun a ha=>hmem a (ha.trans_le hforestBound)),h.solver.finiteFrame hlow hmem,
    h.tables.prefixFrame hlow hmem,?_,?_,?_,?_,?_,?_,hout.trans h.output⟩
  · intro r hr
    rcases hr with rfl | rfl | hr
    · exact hlow 0 (by decide)
    · exact hlow 1 (by decide)
    · exact hhigh r (Or.inl hr)
  · exact (hhigh 100 (by simp)).trans h.orientation
  · exact (hhigh 113 (by simp)).trans h.keys
  · exact (hhigh 261 (by simp)).trans h.nextBase
  · exact (hhigh 262 (by simp)).trans h.previousBase
  · intro i hi;exact (hnext i hi).trans (h.next i hi)
  · intro i hi;exact (hprev i hi).trans (h.previous i hi)

end STACS2027.Embed.RAMSolver

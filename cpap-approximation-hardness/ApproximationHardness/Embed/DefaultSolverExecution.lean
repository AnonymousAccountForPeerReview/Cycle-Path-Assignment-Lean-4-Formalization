module

public import ApproximationHardness.Embed.EmbeddingRuntime
public import ApproximationHardness.Embed.SolverMemoryFloor
public import ApproximationHardness.Embed.PlanStoreRAM

/-! # Cache the two local rotations and execute the complete linked solver -/

@[expose] public section

namespace STACS2027.Embed.RAMSolver

open RAM

def defaultSolverProgram : Stmt := .seq defaultRotationProgram solverProgram

theorem defaultSolverProgram_spec {D : DFSRAM.Layout} {G : DG} {s : DS}
    (_hG : G.Ok) (hF : (G.fd s).Valid) {c : Config}
    (hc : PlanRAM.Context D G s c)
    (hi : Rep (PlanRAM.solverLayout D) c initialState)
    (ht : Tables (PlanRAM.solverLayout D) c ((G.fd s).sol hF) s.post (4*G.E) (2*G.E))
    (hw : 8*G.E≤D.width) (hpositive : 0<D.width)
    {sides : Nat→Bool}
    (hfork : ∀ v p q,((G.fd s).sol hF).P.IsFork ((G.fd s).sol hF).α ((G.fd s).sol hF).key v p q →
      ((G.fd s).sol hF).P.ForkOK ((G.fd s).sol hF).α ((G.fd s).sol hF).key sides p q)
    (hpost : ForestData.PostOrder (G.fd s) hF s.post)
    (horient : c.reg 100=orientationBase (PlanRAM.solverLayout D))
    (hkeys : c.reg 113=keyBase (PlanRAM.solverLayout D))
    (hnext : c.reg 261=nextBase (PlanRAM.solverLayout D))
    (hprev : c.reg 262=predBase (PlanRAM.solverLayout D))
    (hready : DefaultReady (G.fd s) (bufferLimit (PlanRAM.solverLayout D)) c)
    (hfree : ∀ a,PlanRAM.zLimit D≤a → c.mem a=0) (hout : c.out=[]) :
    ∃ t d,ExecB (bufferLimit (PlanRAM.solverLayout D)) defaultSolverProgram c t d ∧
      t≤45000*(G.E+1) ∧ EmbeddingRuntime D G s hF d ∧
      (∀ i,i<D.width → d.mem (orientationBase (PlanRAM.solverLayout D)+i)=0) := by
  let L := PlanRAM.solverLayout D
  obtain ⟨td,d,Ed,Td,Hframe,Hout,Hnext,Hprev⟩ := defaultRotationProgram_spec hF c hready
  have Hregs (r : Nat) (hr : r<240 ∨ r=261 ∨ r=262 ∨ 265<r) : d.reg r=c.reg r :=
    defaultRotationProgram_regs Ed r hr
  have Hlow (r : Nat) (hr : r<72) : d.reg r=c.reg r := Hregs r (Or.inl (by omega))
  have Hmemory (a : Nat) (ha : a<L.limit) : d.mem a=c.mem a := by
    apply Hframe.mem
    left
    rw [hnext]
    dsimp [nextBase,keyBase,orientationBase,L] at ha ⊢
    omega
  have Hid : Rep L d initialState := hi.finiteFrame Hlow Hmemory
  have Htd : Tables L d ((G.fd s).sol hF) s.post (4*G.E) (2*G.E) := ht.prefixFrame Hlow Hmemory
  have Hbd : DFSRAM.Bases D G d := hc.forest.bases.phaseFrame (by
    intro r hr;apply Hregs r;rcases hr with rfl|rfl|hr <;> left <;> omega)
  have Hfd : DFSRAM.Tables D G d := hc.tables.prefixFrame (by omega)
    (fun a ha=>Hmemory a (by dsimp [L,PlanRAM.solverLayout,Layout.limit];omega))
  obtain ⟨ts,e,Es,Ts,Hie,Hte,Hrecords,Hbits,Houts,HregS,HmemS⟩ :=
    solverProgram_refines hF hfork hpost initialState d Hid Htd
      (initialState_bounds hpositive (by change 2*G.E≤D.width; omega)) rfl rfl (fun _=>rfl) Hbd.2.2.1
  have Hfloor := solverProgram_memBelow Hid.bases Es
  have Hbe : DFSRAM.Bases D G e := Hbd.solverFrame Hie.bases HregS
  have Hfe : DFSRAM.Tables D G e := Hfd.prefixFrame (by omega) Hfloor
  have Horientd : d.reg 100=orientationBase L := (Hregs 100 (by decide)).trans horient
  have Hkeysd : d.reg 113=keyBase L := (Hregs 113 (by decide)).trans hkeys
  have Hnextd : d.reg 261=nextBase L := (Hregs 261 (by decide)).trans hnext
  have Hprevd : d.reg 262=predBase L := (Hregs 262 (by decide)).trans hprev
  have Hruntime : EmbeddingRuntime D G s hF e := by
    refine ⟨Hbe,Hfe,Hie,Hte,(HregS 100 (by decide)).trans Horientd,
      (HregS 113 (by decide)).trans Hkeysd,(HregS 261 (by decide)).trans Hnextd,
      (HregS 262 (by decide)).trans Hprevd,?_,?_,Houts.trans (Hout.trans hout)⟩
    · intro i hi
      rw [HmemS _ (by dsimp [nextBase,keyBase,orientationBase,L];omega)]
      simpa only [hnext] using Hnext i hi
    · intro i hi
      rw [HmemS _ (by dsimp [predBase,nextBase,keyBase,orientationBase,L];omega)]
      simpa only [hprev] using Hprev i hi
  have Hbound : L.limit≤bufferLimit L := by
    dsimp [bufferLimit,predBase,nextBase,keyBase,orientationBase];omega
  refine ⟨td+ts,e,.seq Ed (Es.mono Hbound),by dsimp only [DG.fd] at Td Ts;omega,Hruntime,?_⟩
  intro i hi
  rw [HmemS _ (by dsimp [orientationBase,L];omega),Hframe.mem _ (Or.inl (by
    rw [hnext];dsimp [nextBase,keyBase,orientationBase,L,PlanRAM.solverLayout] at hi ⊢;omega))]
  apply hfree
  dsimp [PlanRAM.zLimit,orientationBase,L,PlanRAM.solverLayout]
  omega

end STACS2027.Embed.RAMSolver

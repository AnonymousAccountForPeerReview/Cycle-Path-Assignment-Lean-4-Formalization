module

public import ApproximationHardness.Embed.PlanVertexHeaderValues
import Lean.Elab.Tactic.Omega

/-! Counted bounded compilation of both halves of the vertex-plan tables. -/

@[expose] public section
namespace STACS2027.Embed.PlanRAM
open RAM

theorem vertexLoop_run_skip (c : Config) : run .skip c=c := rfl

attribute [local simp] zBase vertex degree vertexParent dart opposite child childParent
  itemType itemValue distinguished vertexBound partCount topVertex remaining slot
  address test otherTest exclusion representative constant

/-- Exact cache, identifier, count, and item cells belonging to one vertex position. -/
structure VertexEntry (L : DFSRAM.Layout) (F : ForestData) (c : Config) (r : Nat) : Prop where
  cache : c.mem ((solverLayout L).limit+r)=F.zOf r
  ordinaryGroup : c.mem ((solverLayout L).cell 15 r)=F.gid r
  ordinaryCount : c.mem ((solverLayout L).cell 16 r)=(F.parts r).length
  ordinarySlots : PartSlots (solverLayout L) c.mem r (F.parts r)
  topGroup : c.mem ((solverLayout L).cell 15 (2*F.E+r))=F.gid (2*F.E+r)
  topCount : c.mem ((solverLayout L).cell 16 (2*F.E+r))=(F.parts (2*F.E+r)).length
  topSlots : PartSlots (solverLayout L) c.mem (2*F.E+r) (F.parts (2*F.E+r))

theorem VertexEntry.mem_congr {L : DFSRAM.Layout} {F : ForestData} {c d : Config} {r : Nat}
    (h : VertexEntry L F c r) (hm : d.mem=c.mem) : VertexEntry L F d r := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · rw [hm]; exact h.cache
  · rw [hm]; exact h.ordinaryGroup
  · rw [hm]; exact h.ordinaryCount
  · rw [hm]; exact h.ordinarySlots
  · rw [hm]; exact h.topGroup
  · rw [hm]; exact h.topCount
  · rw [hm]; exact h.topSlots

/-- The already compiled vertex positions and the caches protected during compilation. -/
structure VertexPrefix (L : DFSRAM.Layout) (G : DG) (s : DS) (k : Nat) (c : Config) : Prop where
  context : Context L G s c
  mutable : MutableZero L c
  groupBound : c.reg vertexBound=4*G.E
  entries : ∀ r,r<k → VertexEntry L (G.fd s) c r

/-- Counter changes affect only scratch registers, so they preserve every table entry. -/
theorem VertexPrefix.temp {L : DFSRAM.Layout} {G : DG} {s : DS} {k : Nat} {c : Config}
    (h : VertexPrefix L G s k c) (r value : Nat) (hr : 281≤r) (hn : r≠vertexBound) :
    VertexPrefix L G s k (c.setReg r value) := by
  refine ⟨h.context.temp r value hr,h.mutable,?_,?_⟩
  · simpa [Config.setReg,Ne.symm hn] using h.groupBound
  · intro v hv; exact (h.entries v hv).mem_congr rfl

/-- The one-vertex instruction protects both loop-control registers. -/
theorem vertexTableStep_counters (c : Config) :
    (run vertexTableStep c).reg vertex=c.reg vertex ∧
    (run vertexTableStep c).reg remaining=c.reg remaining := by
  constructor <;> apply run_reg_frame <;> decide

/-- The actual counted loop turns the verified one-vertex instruction into all vertex entries. -/
theorem vertexTablesProgram_spec {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) (hz : MutableZero L c) (hg : c.reg vertexBound=4*G.E)
    (hstep : ∀ j d,j<2*G.E → VertexPrefix L G s j d → d.reg vertex=j →
      AddrOK (zLimit L) vertexTableStep d ∧ VertexPrefix L G s (j+1) (run vertexTableStep d)) :
    ∃t d,ExecB (zLimit L) vertexTablesProgram c t d ∧ t≤1004*(2*G.E)+4 ∧
      VertexPrefix L G s (2*G.E) d ∧ d.reg vertex=2*G.E ∧ d.out=c.out ∧
      (∀r,r<281 → d.reg r=c.reg r) := by
  let I : Nat → Config → Prop := fun j d => VertexPrefix L G s j d ∧ d.reg vertex=j ∧
    d.out=c.out ∧ (∀r,r<281 → d.reg r=c.reg r)
  have hbody : ∀j d,j<2*G.E → I j d → d.reg remaining=2*G.E-j →
      ∃t d',ExecB (zLimit L) vertexTableBody d t d' ∧ t≤1003 ∧ I (j+1) d' ∧
        d'.reg remaining+1=d.reg remaining := by
    intro j d hj hd hcount
    obtain ⟨hp,hv,hout,hregs⟩ := hd
    obtain ⟨ha,hp'⟩ := hstep j d hj hp hv
    have hcounter := vertexTableStep_counters d
    generalize heStep : run vertexTableStep d=e
    rw [heStep] at hp' hcounter
    have hone : e.reg 1=1 := hp'.context.solver.2.1
    have heOut : e.out=d.out := by rw [←heStep]; exact vertexTableStep_out d
    let d' := (e.setReg vertex (j+1)).setReg remaining (2*G.E-j-1)
    have heq : run vertexTableBody d=d' := by
      simp only [vertexTableBody,seqs,run_seq,vertexLoop_run_skip,heStep]
      simp [run,d',hcounter.1,hcounter.2,hv,hcount,hone]
    have hp'' : VertexPrefix L G s (j+1) d' :=
      (hp'.temp vertex (j+1) (by decide) (by decide)).temp remaining (2*G.E-j-1) (by decide) (by decide)
    have hlp : LoopFree vertexTableBody := by simp [vertexTableBody,vertexTableStep_loopFree,seqs,LoopFree]
    have hab : AddrOK (zLimit L) vertexTableBody d := by
      simp only [vertexTableBody,addrOK_seqs_cons,addrOK_add,addrOK_sub,addrOK_seqs_nil,and_true,true_and]
      exact ha
    have hsize : size vertexTableBody≤1003 := by
      have hs := vertexTableStep_size
      simp only [vertexTableBody,seqs,size] at ⊢
      omega
    refine ⟨_,d',heq ▸ execB_run _ hlp d hab,(cost_le_size _ _).trans hsize,?_,?_⟩
    · refine ⟨hp'',?_,?_,?_⟩
      · simp [d',Config.setReg]
      · exact heOut.trans hout
      · intro r hr
        simp only [d',Config.setReg,show r≠remaining by simp;omega,show r≠vertex by simp;omega,↓reduceIte]
        have hsreg : e.reg r=d.reg r := by rw [←heStep]; exact vertexTableStep_reg_frame d r (Or.inl hr)
        exact hsreg.trans (hregs r hr)
    · simp [d',Config.setReg,hcount]
      omega
  let c₀ := c.setReg vertex 0
  let c₁ := c₀.setReg remaining (2*G.E)
  have hi : I 0 c₁ := by
    refine ⟨?_,?_,rfl,?_⟩
    · exact (VertexPrefix.mk hc hz hg (fun r hr => by omega)).temp vertex 0 (by decide) (by decide)
        |>.temp remaining (2*G.E) (by decide) (by decide)
    · simp [c₁,c₀,Config.setReg]
    · intro r hr; simp [c₁,c₀,Config.setReg,show r≠remaining by simp;omega,show r≠vertex by simp;omega]
  have hm : c₁.reg remaining=2*G.E := by simp [c₁,Config.setReg]
  obtain ⟨t,d,he,ht,hI⟩ := exec_countLoop (a:=remaining) (body:=vertexTableBody) (2*G.E) I 1003 hbody c₁ hi hm
  have hinit : ExecB (zLimit L) (.add remaining DFSRAM.dartCount 0) c₀ 1 c₁ := by
    have hD : c₀.reg DFSRAM.dartCount=2*G.E := by simp [c₀,Config.setReg,hc.forest.bases.2.2.1,DFSRAM.dartCount]
    have hzero : c₀.reg 0=0 := by simp [c₀,Config.setReg,hc.solver.1]
    simpa [c₁,hD,hzero] using ExecB.add (S:=zLimit L) remaining DFSRAM.dartCount 0 c₀
  refine ⟨1+(1+(t+1)),d,.seq (.const vertex 0 c) (.seq hinit (.seq he (.skip d))),by omega,hI.1,hI.2.1,hI.2.2.1,hI.2.2.2⟩

end STACS2027.Embed.PlanRAM

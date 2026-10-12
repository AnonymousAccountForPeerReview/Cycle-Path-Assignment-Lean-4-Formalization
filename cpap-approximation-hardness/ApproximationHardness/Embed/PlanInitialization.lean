module

public import ApproximationHardness.Embed.PlanStoreRAM
public import ApproximationHardness.Embed.SolverInit
public import ApproximationHardness.Embed.DFSExecution
import Lean.Elab.Tactic.Omega

/-! # Actual initialization of the cached plan compiler -/

@[expose] public section

namespace STACS2027.Embed.PlanRAM

open RAM

def solverSetup : Stmt := .seq solverHeader RAMSolver.solverInit

theorem solverSetup_loopFree : LoopFree solverSetup :=
  ⟨solverHeader_loopFree,RAMSolver.solverInit_loopFree⟩
theorem solverSetup_size : size solverSetup ≤ 91 := by decide

theorem solverSetup_frame (c : Config) (r : Nat)
    (hr : r=0 ∨ r=1 ∨ (140≤r ∧ r≤170)) :
    (run solverSetup c).reg r=c.reg r := by
  apply run_reg_frame
  simp [solverSetup,solverHeader,RAMSolver.solverInit,seqs,regsW]
  omega

theorem solverSetup_forest {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hr : DFSRAM.Rep L G c s) : DFSRAM.Rep L G (run solverSetup c) s := by
  have hb : DFSRAM.Bases L G (run solverSetup c) := hr.bases.frame (by
    intro r hr
    apply solverSetup_frame
    simp only [DFSRAM.dartCount,DFSRAM.baseRegister,DFSRAM.widthRegister] at hr
    rcases hr with hr | hr | hr | hr | hr | hr <;> omega)
  apply hr.memory.of_regs (run_mem_frame solverSetup c (by decide)) hb
  · exact (solverSetup_frame c _ (by decide)).trans hr.scan
  · exact (solverSetup_frame c _ (by decide)).trans hr.current
  · exact (solverSetup_frame c _ (by decide)).trans hr.inner
  · exact (solverSetup_frame c _ (by decide)).trans hr.height
  · exact (solverSetup_frame c _ (by decide)).trans hr.postLength

theorem solverSetup_context {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hr : DFSRAM.Rep L G c s) (ht : DFSRAM.Tables L G c)
    (hp : s.post.length≤L.width) (hd : 2*G.E≤L.width) :
    Context L G s (run solverSetup c) := by
  have hh := solverHeader_metadata hr.bases
  have hframes := RAMSolver.solverInit_frame
  refine ⟨solverSetup_forest hr,
    ht.mem_congr (run_mem_frame solverSetup c (by decide)),
    RAMSolver.solverInit_bases (solverHeader_bases hr.bases),?_,hp,hd,?_,?_⟩
  · exact (hframes (run solverHeader c) 280 (by omega)).trans hh.1
  · exact ((hframes (run solverHeader c) 4 (by decide)).trans hh.2.1).trans hr.postLength
  · exact ((hframes (run solverHeader c) 5 (by decide)).trans hh.2.2.1).trans (congrArg (·+2) hr.height)

theorem solverSetup_rep {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hr : DFSRAM.Rep L G c s)
    (hz : ∀ a,L.limit≤a → c.mem a=0) :
    RAMSolver.Rep (solverLayout L) (run solverSetup c) RAMSolver.initialState := by
  apply RAMSolver.solverInit_rep (solverHeader_bases hr.bases)
  intro j hj i hi
  rw [run_mem_frame solverHeader c (by decide)]
  apply hz
  dsimp [solverLayout,RAMSolver.Layout.cell,RAMSolver.Layout.block]
  omega

theorem solverSetup_spec {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (S : Nat) (hr : DFSRAM.Rep L G c s) (ht : DFSRAM.Tables L G c)
    (hp : s.post.length≤L.width) (hd : 2*G.E≤L.width)
    (hz : ∀ a,L.limit≤a → c.mem a=0) :
    ∃ t,ExecB S solverSetup c t (run solverSetup c) ∧ t≤91 ∧
      Context L G s (run solverSetup c) ∧
      RAMSolver.Rep (solverLayout L) (run solverSetup c) RAMSolver.initialState ∧
      (run solverSetup c).mem=c.mem ∧ (run solverSetup c).out=c.out := by
  exact ⟨_,execB_run _ solverSetup_loopFree c (AddrOK.of_memFree (by decide)),
    (cost_le_size solverSetup c).trans solverSetup_size,solverSetup_context hr ht hp hd,
    solverSetup_rep hr hz,run_mem_frame _ _ (by decide),run_out_frame _ _ (by decide)⟩

end STACS2027.Embed.PlanRAM

namespace STACS2027.Embed.IncidenceRAM

open RAM Complexity.SAT

def preparePlanContext : Stmt := .seq prepareForest PlanRAM.solverSetup

theorem preparePlanContext_spec (f : CNF) (hf : BoundedOccurrence f) :
    ∃ t c,ExecB (PlanRAM.zLimit (cacheLayout f)) preparePlanContext
      (initial (ramInput f)) t c ∧
      t≤4100*((ramInput f).length+variableBound f+1) ∧
      PlanRAM.Context (cacheLayout f) (incDG f) (incDG f).final c ∧
      RAMSolver.Rep (PlanRAM.solverLayout (cacheLayout f)) c RAMSolver.initialState ∧
      c.out=[] ∧ (∀ a,(cacheLayout f).limit≤a → c.mem a=0) ∧
      c.reg 291=4*(incDG f).E := by
  obtain ⟨t,c,e,ht,hr,hb,hout,hfree,_⟩ := prepareForest_spec f hf
  have hpost := (DG.bounds (DG.inv_final (incOk hf))).2.2
  have hp : (incDG f).final.post.length≤(cacheLayout f).width := by
    dsimp [incDG,cacheLayout] at hpost ⊢
    omega
  have hd : 2*(incDG f).E≤(cacheLayout f).width := by dsimp [incDG,cacheLayout];omega
  obtain ⟨u,eu,hu,hc,hs,hm,ho⟩ := PlanRAM.solverSetup_spec
    (PlanRAM.zLimit (cacheLayout f)) hr hb hp hd hfree
  refine ⟨t+u,_,.seq (e.mono (by
    dsimp [PlanRAM.zLimit,PlanRAM.solverLayout,RAMSolver.Layout.limit]
    omega)) eu,?_,hc,hs,ho.trans hout,?_,?_⟩
  · omega
  · intro a ha;rw [hm,hfree a ha]
  · exact (RAMSolver.solverInit_frame (run PlanRAM.solverHeader c) 291 (by decide)).trans
      (PlanRAM.solverHeader_metadata hr.bases).2.2.2

end STACS2027.Embed.IncidenceRAM

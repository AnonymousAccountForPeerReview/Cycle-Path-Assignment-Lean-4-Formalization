module

public import ApproximationHardness.Embed.Computed
public import ApproximationHardness.Embed.DefaultReadyMaterialization
public import ApproximationHardness.Embed.DefaultSolverExecution
public import ApproximationHardness.Embed.OrientationExecution
public import ApproximationHardness.Embed.EmbeddingReadout
import Lean.Elab.Tactic.Omega

/-! A uniform formula-only RAM program constructs a planar rotation in linear time and space. -/

@[expose] public section
namespace STACS2027.Embed
open Complexity Complexity.SAT Complexity.Planar STACS2027.PlanarAssembly RAM RAMSolver

/-- Formula parsing, adjacency and DFS, cached plan compilation, linked solver,
orientation, and final rotation emission. Every phase is an actual RAM program. -/
def planarEmbeddingProgram : Stmt :=
  .seq IncidenceRAM.prepareForestPlan
    (.seq bufferHeaders (.seq defaultSolverProgram (.seq orientationProgram readoutProgram)))

/-- From the formula input alone, the fixed program emits a planar rotation with
linear time and allocated-address bounds. -/
theorem planarEmbeddingProgram_spec (f : CNF) (hf : BoundedOccurrence f)
    (hp : PlanarGraph (incidenceGraph f)) :
    ∃ t c,ExecB (bufferLimit (PlanRAM.solverLayout (IncidenceRAM.cacheLayout f)))
      planarEmbeddingProgram (initial (ramInput f)) t c ∧
      t≤100000*((ramInput f).length+variableBound f+1) ∧ IsPlanarRotation f c.out := by
  obtain ⟨tp,p,ep,btp,hc,hi,ht,op,hz,hfree⟩ := IncidenceRAM.prepareForestPlan_spec f hf
  let D := IncidenceRAM.cacheLayout f
  let L := PlanRAM.solverLayout D
  have hG := incOk hf
  have hF := incF_valid hf
  have hw : 8*(incDG f).E≤D.width := by dsimp [D,IncidenceRAM.cacheLayout,incDG];omega
  have hpositive : 0<D.width := by dsimp [D,IncidenceRAM.cacheLayout];omega
  have hpost := DG.postOrder_final hG
  obtain ⟨sides,hfork⟩ := incidence_forkWitness hf hp
  have hready := defaultReadyMaterialization hc hG hF ht hw (by
    intro d hd
    rw [hc.zbase]
    exact hz d hd)
  have hheaders := bufferHeaders_values L p hc.zbase hc.solver.2.2.2.1
  have hfreeb : ∀a,PlanRAM.zLimit D≤a → (run bufferHeaders p).mem a=0 := by
    intro a ha
    rw [(bufferHeaders_frame p).1]
    exact hfree a ha
  have hob : (run bufferHeaders p).out=[] := (bufferHeaders_frame p).2.1.trans op
  obtain ⟨th,eh,bth⟩ := bufferHeaders_spec (bufferLimit L) p
  obtain ⟨ts,s,es,bts,hruntime,hzero⟩ := defaultSolverProgram_spec hG hF
    (bufferHeaders_context hc) (bufferHeaders_solverRep hi) (bufferHeaders_solverTables ht)
    hw hpositive hfork hpost hheaders.1 hheaders.2.1 hheaders.2.2.1 hheaders.2.2.2
    hready hfreeb hob
  obtain ⟨orientTime,r,o,eo,bto,hr,hO,hconsistent,_⟩ := orientationProgram_spec hruntime
    hfork hpost hw hzero
  obtain ⟨tr,c,er,btr,_,hpl⟩ := readoutProgram_spec hf hp hr hO hconsistent
  have hspace : PlanRAM.zLimit D≤bufferLimit L := by
    dsimp [PlanRAM.zLimit,bufferLimit,predBase,nextBase,keyBase,orientationBase,L,PlanRAM.solverLayout];omega
  have ep' := ep.mono hspace
  have e : ExecB (bufferLimit L) planarEmbeddingProgram (initial (ramInput f))
      (tp+(th+(ts+(orientTime+tr)))) c := .seq ep' (.seq eh (.seq es (.seq eo er)))
  have hlen := ramInput_length_eq f
  have hpostLength := (DG.bounds (DG.inv_final hG)).2.2
  dsimp only [incDG] at bts bto hpostLength
  exact ⟨_,c,e,by omega,hpl⟩

/-- The uniform construction also accesses at most linearly many memory cells. -/
theorem planarEmbeddingProgram_space (f : CNF) :
    bufferLimit (PlanRAM.solverLayout (IncidenceRAM.cacheLayout f))≤
      100000*((ramInput f).length+variableBound f+1) := by
  have hlen := ramInput_length_eq f
  dsimp [bufferLimit,predBase,nextBase,keyBase,orientationBase,PlanRAM.solverLayout,
    Layout.limit,IncidenceRAM.cacheLayout,DFSRAM.Layout.limit]
  omega

/-- The manuscript's formula-only linear-time planar embedding claim is fully formalized. -/
theorem planarEmbedding_linear_ram : PlanarEmbeddingLinearRAM := by
  refine ⟨planarEmbeddingProgram,100000,?_⟩
  intro f hf hp
  obtain ⟨t,c,he,ht,hpl⟩ := planarEmbeddingProgram_spec f hf hp
  exact ⟨c.out,t,⟨c,he.mono (planarEmbeddingProgram_space f),rfl⟩,ht,hpl⟩

end STACS2027.Embed

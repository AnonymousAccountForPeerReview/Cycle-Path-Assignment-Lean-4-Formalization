module

public import ApproximationHardness.Embed.PlanTablesRAM
import Lean.Elab.Tactic.Omega

/-! The complete actual forest-plan preprocessing program starts from the formula input. -/

@[expose] public section
namespace STACS2027.Embed.IncidenceRAM
open RAM Complexity.SAT

/-- Cache the formula, run DFS, initialize the solver, and compile its whole plan. -/
def prepareForestPlan : Stmt := .seq preparePlanContext PlanRAM.planTablesProgram

/-- Uniform bounded preprocessing supplies the precise forest plan and initialized linked state. -/
theorem prepareForestPlan_spec (f : CNF) (hf : BoundedOccurrence f) :
    ∃t c,ExecB (PlanRAM.zLimit (cacheLayout f)) prepareForestPlan
      (initial (ramInput f)) t c ∧
      t≤20000*((ramInput f).length+variableBound f+1) ∧
      PlanRAM.Context (cacheLayout f) (incDG f) (incDG f).final c ∧
      RAMSolver.Rep (PlanRAM.solverLayout (cacheLayout f)) c RAMSolver.initialState ∧
      RAMSolver.Tables (PlanRAM.solverLayout (cacheLayout f)) c
        (((incDG f).fd (incDG f).final).sol (DG.valid_final (incOk hf)))
        (incDG f).final.post (4*(incDG f).E) (2*(incDG f).E) ∧
      c.out=[] ∧
      (∀r,r<2*(incDG f).E →c.mem ((PlanRAM.solverLayout (cacheLayout f)).limit+r)=
        ((incDG f).fd (incDG f).final).zOf r) ∧
      (∀a,PlanRAM.zLimit (cacheLayout f)≤a →c.mem a=0) := by
  obtain ⟨tp,p,ep,btp,hc,hi,op,_,hg⟩ := preparePlanContext_spec f hf
  have hw : 8*(incDG f).E≤(cacheLayout f).width := by dsimp [incDG,cacheLayout];omega
  obtain ⟨tc,c,ec,btc,hc',hi',ht,oc,_,hz⟩ := PlanRAM.planTablesProgram_spec hc hi hg
    (incOk hf) (DG.valid_final (incOk hf)) (DG.inv_final (incOk hf)) hw
  have e : ExecB (PlanRAM.zLimit (cacheLayout f)) prepareForestPlan
      (initial (ramInput f)) (tp+tc) c := .seq ep ec
  refine ⟨tp+tc,c,e,?_,hc',hi',ht,oc.trans op,hz,?_⟩
  · have hpost := (DG.bounds (DG.inv_final (incOk hf))).2.2
    have hlen := ramInput_length_eq f
    dsimp only [incDG] at btc hpost
    omega
  · intro a ha
    rw [DFSRAM.boundedRun_memAbove e a ha]
    exact zero_input_memory f a (by
      dsimp [PlanRAM.zLimit,PlanRAM.solverLayout,RAMSolver.Layout.limit,
        cacheLayout,DFSRAM.Layout.limit] at ha
      omega)

end STACS2027.Embed.IncidenceRAM

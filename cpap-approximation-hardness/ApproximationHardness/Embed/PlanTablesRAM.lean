module

public import ApproximationHardness.Embed.PlanTableContent
public import ApproximationHardness.Embed.PlanPostCopyRAM
import Lean.Elab.Tactic.Omega

/-! The complete actual linear RAM compiler from DFS caches to forest-plan tables. -/

@[expose] public section
namespace STACS2027.Embed.PlanRAM
open RAM

/-- The node-table scan precedes the dart-table scan and the postorder copy. -/
def planTablesProgram : Stmt := .seq vertexTablesProgram (.seq dartTablesProgram postCopyProgram)

/-- The actual compiler supplies all solver tables and preserves the initialized linked solver. -/
theorem planTablesProgram_spec {L : DFSRAM.Layout} {G : DG} {s : DS} {start : Config}
    (hc : Context L G s start)
    (hi : RAMSolver.Rep (solverLayout L) start RAMSolver.initialState)
    (hg : start.reg vertexBound=4*G.E) (hG : G.Ok) (hF : (G.fd s).Valid)
    (hI : G.Inv s) (hw : 8*G.E≤L.width) :
    ∃t c,ExecB (zLimit L) planTablesProgram start t c ∧
      t≤3000*(G.E+s.post.length+1) ∧ Context L G s c ∧
      RAMSolver.Rep (solverLayout L) c RAMSolver.initialState ∧
      RAMSolver.Tables (solverLayout L) c ((G.fd s).sol hF) s.post (4*G.E) (2*G.E) ∧
      c.out=start.out ∧ (∀r,r<281 →c.reg r=start.reg r) ∧
      (∀r,r<2*G.E →c.mem ((solverLayout L).limit+r)=(G.fd s).zOf r) := by
  obtain ⟨tv,v,ev,btv,hv,_,ov,rv⟩ := vertexTablesProgram_complete hc (initial_mutable hi) hg
    hG hF (by omega)
  have hzcache : ∀r,r<2*G.E →v.mem (v.reg zBase+r)=(G.fd s).zOf r := by
    intro r hr;rw [hv.context.zbase];exact (hv.entries r hr).cache
  obtain ⟨td,d,ed,btd,hd,hprefix,hframe,od,rd⟩ := dartTablesProgram_spec hv.context hG hzcache
  have hz : MutableZero L d := by
    intro j hj i hi
    rw [hframe.cell j i hi (by omega)]
    exact hv.mutable j hj i hi
  obtain ⟨tp,c,ep,btp,hcfinal,hzfinal,hpost,op,hpostframe,rp⟩ := postCopy_compiled hd hz
  obtain ⟨hpostcell,hpostabove⟩ := postCopy_prefix_frame hpostframe
  have hnodecell (j i : Nat) (hj : 15≤j ∧ j<21) (hi : i<L.width) :
      c.mem ((solverLayout L).cell j i)=v.mem ((solverLayout L).cell j i) := by
    exact (hpostcell j hj.2 i hi).trans (hframe.cell j i hi (by omega))
  have hnodes : ∀w,w<4*G.E →
      c.mem ((solverLayout L).cell 15 w)=(G.fd s).gid w ∧
      c.mem ((solverLayout L).cell 16 w)=((G.fd s).parts w).length ∧
      PartSlots (solverLayout L) c.mem w ((G.fd s).parts w) := by
    intro w hw'
    have hwidth : w<L.width := by omega
    obtain ⟨hgroup,hcount,hslots⟩ := hv.nodeValues hw'
    refine ⟨(hnodecell 15 w (by decide) hwidth).trans hgroup,
      (hnodecell 16 w (by decide) hwidth).trans hcount,?_⟩
    unfold PartSlots at hslots ⊢
    rw [hnodecell 17 w (by decide) hwidth,hnodecell 18 w (by decide) hwidth,
      hnodecell 19 w (by decide) hwidth,hnodecell 20 w (by decide) hwidth]
    exact hslots
  have hdarts : DartPrefix L (G.fd s) c (2*G.E) := by
    refine ⟨?_,?_,?_⟩
    · intro e he
      exact (hpostcell 12 (by decide) e (he.trans_le hc.dartCapacity)).trans (hprefix.keys e he)
    · intro e he
      exact (hpostcell 13 (by decide) e (he.trans_le hc.dartCapacity)).trans (hprefix.partners e he)
    · intro e he
      exact (hpostcell 14 (by decide) e (he.trans_le hc.dartCapacity)).trans (hprefix.targets e he)
  have hregs : ∀r,r<281 →c.reg r=start.reg r := by
    intro r hr
    exact (rp r (Or.inl (by omega))).trans
      ((rd r (Or.inl (by omega)) (by simp only [address];omega)).trans (rv r hr))
  have hinit := initial_rep_frame hi hcfinal.solver hzfinal (fun r hr=>hregs r (by omega))
  have ht := compiled_tables hcfinal hF hI hw hdarts hnodes hpost
  refine ⟨tv+(td+tp),c,.seq ev (.seq ed ep),by omega,hcfinal,hinit,ht,
    op.trans (od.trans ov),hregs,?_⟩
  intro r hr
  rw [hpostabove _ (by omega),hframe.above _ (by omega)]
  exact (hv.entries r hr).cache

end STACS2027.Embed.PlanRAM

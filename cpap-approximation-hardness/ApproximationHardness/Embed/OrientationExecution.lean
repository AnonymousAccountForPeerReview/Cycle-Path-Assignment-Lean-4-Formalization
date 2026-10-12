module

public import ApproximationHardness.Embed.EmbeddingRuntime
public import ApproximationHardness.Embed.OrientationReady
public import ApproximationHardness.Embed.SolverRecords
import Lean.Elab.Tactic.Omega

/-! The actual visit-stream compiler and orientation loop preserve the full embedding runtime. -/

@[expose] public section
namespace STACS2027.Embed.RAMSolver
open RAM

/-- Materialize every group visit, then execute the actual orientation fold. -/
def orientationProgram : Stmt := .seq keyProgram orientationLoop

/-- The completed solver's records suffice for the actual bounded and consistent orientation pass. -/
theorem orientationProgram_spec {D : DFSRAM.Layout} {G : DG} {s : DS}
    {hF : (G.fd s).Valid} {start : Config} {sides : Nat→Bool}
    (h : EmbeddingRuntime D G s hF start)
    (hfork : ∀v p q,((G.fd s).sol hF).P.IsFork ((G.fd s).sol hF).α
      ((G.fd s).sol hF).key v p q →
      ((G.fd s).sol hF).P.ForkOK ((G.fd s).sol hF).α ((G.fd s).sol hF).key sides p q)
    (hpost : ForestData.PostOrder (G.fd s) hF s.post) (hw : 8*G.E≤D.width)
    (hzero : ∀i,i<D.width →start.mem (orientationBase (PlanRAM.solverLayout D)+i)=0) :
    ∃t c o,ExecB (bufferLimit (PlanRAM.solverLayout D)) orientationProgram start t c ∧
      t≤200*G.E+9*s.post.length+13 ∧ EmbeddingRuntime D G s hF c ∧
      (∀i,i<D.width →c.mem (orientationBase (PlanRAM.solverLayout D)+i)=boolWord (o i)) ∧
      ((G.fd s).sol hF).Consistent o ∧ c.out=start.out := by
  let L := PlanRAM.solverLayout D
  have hcap : (orientationKeys (G.fd s) s.post).length≤D.width :=
    (orientationKeys_length hpost).trans (show 6*G.E≤D.width by omega)
  have hlen : s.post.length+2*G.E≤D.width := by
    simpa [orientationKeys_explicit,DG.fd] using hcap
  have hsource : start.reg 71+s.post.length≤(orientationLayout L).keys := by
    rw [h.solver.bases.2.2.2.2 21 (by decide)]
    have hp := h.tables.orderBound
    dsimp [orientationLayout,keyBase,orientationBase,Layout.block,Layout.limit,L,PlanRAM.solverLayout]
    omega
  have hdarts : start.reg 140=2*(G.fd s).E := h.forestBases.2.2.1
  have hcells (i : Nat) (hi : i<s.post.length) : start.mem (start.reg 71+i)=s.post.getD i 0 := by
    rw [h.solver.bases.2.2.2.2 21 (by decide)]
    exact (h.tables.order i hi).trans (DG.getD_of_lt hi).symm
  have hparents (g : Nat) (hg : g<(orientationLayout L).width) :
      start.mem ((orientationLayout L).parents+g)=(completedSolver G s hF).m.gp g := by
    simpa only [orientationLayout,Layout.cell,memField] using h.solver.arrays 8 (by decide) g hg
  have hflips (g : Nat) (hg : g<(orientationLayout L).width) :
      start.mem ((orientationLayout L).flips+g)=(completedSolver G s hF).m.gf g := by
    simpa only [orientationLayout,Layout.cell,memField] using h.solver.arrays 9 (by decide) g hg
  obtain ⟨tk,k,ek,btk,hstate,ok⟩ := keyProgram_orientationState (D:=orientationLayout L)
    h.solver.bases.1 h.solver.bases.2.1 h.tables.length hdarts hsource hcells
    (h.solver.bases.2.2.2.2 8 (by decide)) (h.solver.bases.2.2.2.2 9 (by decide))
    h.orientation h.keys hcap hparents hflips hzero
  have hspace : start.reg 113+s.post.length+2*(G.fd s).E≤bufferLimit L := by
    rw [h.keys]
    dsimp [bufferLimit,predBase,nextBase,keyBase,L,PlanRAM.solverLayout,DG.fd]
    omega
  obtain ⟨_,k',ek',_,_,_,_,_,hkeyframe⟩ := keyProgram_spec (S:=bufferLimit L) (G.fd s) s.post start
    h.solver.bases.1 h.solver.bases.2.1 h.tables.length hdarts
    (by rw [h.keys];exact hsource) hspace hcells
  have heq : k=k' := (ek.det ek').2
  rw [←heq] at hkeyframe
  have rkey (r : Nat) (hr : r<270) (ha : r≠109) (hb : r≠110) : k.reg r=start.reg r :=
    keyProgram_regs ek r hr ha hb
  have hkeybelow (a : Nat) (ha : a<L.limit) : k.mem a=start.mem a := by
    apply hkeyframe a (Or.inl ?_)
    rw [h.keys]
    dsimp [keyBase,orientationBase,L] at ha ⊢
    omega
  have hkeynext (i : Nat) (hi : i<2*G.E) :
      k.mem (nextBase L+i)=start.mem (nextBase L+i) := by
    apply hkeyframe _ (Or.inr ?_)
    rw [h.keys]
    dsimp [nextBase,keyBase,L,PlanRAM.solverLayout,DG.fd]
    omega
  have hkeyprev (i : Nat) (hi : i<2*G.E) :
      k.mem (predBase L+i)=start.mem (predBase L+i) := by
    apply hkeyframe _ (Or.inr ?_)
    rw [h.keys]
    dsimp [predBase,nextBase,keyBase,L,PlanRAM.solverLayout,DG.fd]
    omega
  have hk : EmbeddingRuntime D G s hF k := h.frame (by omega)
    (fun r hr=>rkey r (by omega) (by omega) (by omega))
    (by intro r hr;rcases hr with hr|rfl|rfl|rfl|rfl
        · exact rkey r (by omega) (by omega) (by omega)
        all_goals exact rkey _ (by decide) (by decide) (by decide))
    hkeybelow hkeynext hkeyprev ok
  have hrecords : ForestData.Records (G.fd s) hF (completedSolver G s hF).m.gp
      (completedSolver G s hF).m.gf :=
    ForestData.solver_records hF hfork hpost initialState rfl rfl (fun _=>rfl)
  obtain ⟨orientTime,c,o,eo,bto,hfinal,hconsistent,oo⟩ := orientationLoop_consistent (D:=orientationLayout L) hrecords hpost (by change 8*G.E≤D.width;exact hw) hstate
  have hp g hg : (completedSolver G s hF).m.gp g-1<(orientationLayout L).width :=
    (records_parentBound hrecords hpost g hg).trans_le hw
  have hgroup g hg : g<(orientationLayout L).width := (orientationKeys_bound hpost g hg).trans_le hw
  have hloopframe := orientationLoop_mem_frame eo hp hstate hgroup
  have rloop (r : Nat) (hr : r<101 ∨ 111<r) : c.reg r=k.reg r := by
    apply eo.reg_frame
    have H : (regsW orientationLoop).all (fun r=>decide (101≤r ∧ r≤111))=true := by decide
    intro hm;have := of_decide_eq_true ((List.all_eq_true.mp H) r hm);omega
  have hloopbelow (a : Nat) (ha : a<L.limit) : c.mem a=k.mem a := by
    apply hloopframe a (Or.inl ?_)
    change a<orientationBase L
    dsimp [orientationBase];omega
  have hloopnext (i : Nat) (hi : i<2*G.E) : c.mem (nextBase L+i)=k.mem (nextBase L+i) := by
    apply hloopframe _ (Or.inr ?_)
    change orientationBase L+L.width≤nextBase L+i
    dsimp [nextBase,keyBase];omega
  have hloopprev (i : Nat) (hi : i<2*G.E) : c.mem (predBase L+i)=k.mem (predBase L+i) := by
    apply hloopframe _ (Or.inr ?_)
    change orientationBase L+L.width≤predBase L+i
    dsimp [predBase,nextBase,keyBase];omega
  have hc : EmbeddingRuntime D G s hF c := hk.frame (by omega)
    (fun r hr=>rloop r (Or.inl (by omega)))
    (by intro r hr;rcases hr with hr|rfl|rfl|rfl|rfl
        · exact rloop r (Or.inr (by omega))
        · exact rloop 100 (by decide)
        all_goals exact rloop _ (Or.inr (by decide)))
    hloopbelow hloopnext hloopprev oo
  exact ⟨tk+orientTime,c,o,.seq ek eo,by dsimp [DG.fd] at btk bto;omega,hc,
    hfinal.orientation,hconsistent,oo.trans ok⟩

end STACS2027.Embed.RAMSolver

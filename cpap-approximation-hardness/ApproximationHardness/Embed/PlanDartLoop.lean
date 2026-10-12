module

public import ApproximationHardness.Embed.PlanDartRAM

/-! # Linear bounded execution of the complete dart-table compiler -/

@[expose] public section

set_option maxHeartbeats 1500000
set_option maxRecDepth 10000

namespace STACS2027.Embed.PlanRAM

open RAM

attribute [local simp] scanDart dartRemaining address zBase

theorem DartFrame.refl (L : DFSRAM.Layout) (c : Config) : DartFrame L c c := by
  intro a ha; rfl

theorem DartFrame.trans {L : DFSRAM.Layout} {c d e : Config}
    (h : DartFrame L c d) (h' : DartFrame L d e) : DartFrame L c e := by
  intro a ha; exact (h' a ha).trans (h a ha)

theorem DartFrame.above {L : DFSRAM.Layout} {c d : Config}
    (h : DartFrame L c d) (a : Nat) (ha : (solverLayout L).limit ≤ a) : d.mem a=c.mem a := by
  apply h a
  intro i hi
  have h₁ := (solverLayout L).cell_lt (by decide : 12<22) hi
  have h₂ := (solverLayout L).cell_lt (by decide : 13<22) hi
  have h₃ := (solverLayout L).cell_lt (by decide : 14<22) hi
  exact ⟨by omega,by omega,by omega⟩

theorem DartFrame.cell {L : DFSRAM.Layout} {c d : Config}
    (h : DartFrame L c d) (j i : Nat) (hi : i<L.width)
    (hj : j≠12 ∧ j≠13 ∧ j≠14) :
    d.mem ((solverLayout L).cell j i)=c.mem ((solverLayout L).cell j i) := by
  apply h
  intro a ha
  refine ⟨?_,?_,?_⟩
  all_goals intro he; have H := (solverLayout L).cell_injective hi ha he; omega

theorem dartBody_context {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) : Context L G s (run dartTableBody c) := by
  have H := dartTableStep_context hc
  exact H.readOnly (p:=seqs [.add scanDart scanDart 1,.sub dartRemaining dartRemaining 1])
    (by decide) (by intro r hr; simp [seqs,regsW] at hr;omega)

theorem dartBody_mem (c : Config) : (run dartTableBody c).mem=(run dartTableStep c).mem := by
  rfl

theorem dartBody_out (c : Config) : (run dartTableBody c).out=c.out := by
  exact run_out_frame _ _ (by decide)

theorem dartBody_reg (c : Config) (r : Nat) (hr : r<306 ∨ 319<r) (ha : r≠address) :
    (run dartTableBody c).reg r=c.reg r := by
  apply run_reg_frame
  have h : (regsW dartTableBody).all (fun r => decide (r=300 ∨ 306≤r ∧ r≤319))=true := by decide
  intro hm; have := of_decide_eq_true ((List.all_eq_true.mp h) r hm)
  simp only [address] at ha;omega

theorem dartBody_advance {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) :
    (run dartTableBody c).reg scanDart=c.reg scanDart+1 ∧
      (run dartTableBody c).reg dartRemaining=c.reg dartRemaining-1 := by
  have Hscan : (run dartTableStep c).reg scanDart=c.reg scanDart := by
    apply run_reg_frame; decide
  have Hcount : (run dartTableStep c).reg dartRemaining=c.reg dartRemaining := by
    apply run_reg_frame; decide
  have Hone := (dartTableStep_context hc).solver.2.1
  simp [dartTableBody,run,seqs,Hscan,Hcount,Hone]

theorem dartTablesProgram_spec {L : DFSRAM.Layout} {G : DG} {s : DS} {start : Config}
    (hc : Context L G s start) (hG : G.Ok)
    (hz : ∀ r,r<2*G.E → start.mem (start.reg zBase+r)=(G.fd s).zOf r) :
    ∃ t c,ExecB (zLimit L) dartTablesProgram start t c ∧ t≤300*(G.E+1) ∧
      Context L G s c ∧ DartPrefix L (G.fd s) c (2*G.E) ∧ DartFrame L start c ∧
      c.out=start.out ∧
      (∀ r,(r<306 ∨ 319<r) → r≠address → c.reg r=start.reg r) := by
  let pre : Stmt := seqs [.const scanDart 0,.add dartRemaining DFSRAM.dartCount 0]
  let d := run pre start
  have Hdcontext : Context L G s d := hc.readOnly (p:=pre) (by decide)
    (by intro r hr; simp [pre,seqs,regsW] at hr;omega)
  have Hmem : d.mem=start.mem := run_mem_frame _ _ (by decide)
  have Hout : d.out=start.out := run_out_frame _ _ (by decide)
  have Hreg (r : Nat) (hr : r<306 ∨ 319<r) : d.reg r=start.reg r := by
    apply run_reg_frame; simp [pre,seqs,regsW];omega
  have Hdscan : d.reg scanDart=0 := by simp [d,pre,seqs,run]
  have Hdcount : d.reg dartRemaining=2*G.E := by
    have hD := hc.forest.bases.2.2.1
    have hzero := hc.solver.1
    simp [d,pre,seqs,run,DFSRAM.dartCount,hD,hzero]
  let I : Nat → Config → Prop := fun j c => Context L G s c ∧
    c.reg scanDart=j ∧ DartPrefix L (G.fd s) c j ∧ DartFrame L start c ∧
    c.out=start.out ∧ (∀ r,(r<306 ∨ 319<r) → r≠address → c.reg r=start.reg r)
  have HI : I 0 d := by
    refine ⟨Hdcontext,Hdscan,⟨by intros;omega,by intros;omega,by intros;omega⟩,?_,Hout,?_⟩
    · intro a ha; exact congrFun Hmem a
    · intro r hr ha; exact Hreg r hr
  have Hstep : ∀ j c,j<2*G.E → I j c → c.reg dartRemaining=2*G.E-j →
      ∃ t c',ExecB (zLimit L) dartTableBody c t c' ∧ t≤103 ∧ I (j+1) c' ∧
        c'.reg dartRemaining+1=c.reg dartRemaining := by
    intro j c hj H Hcount
    obtain ⟨Hc,Hscan,Hprefix,Hframe,Hout,Hreg⟩ := H
    have Hcz : ∀ r,r<2*G.E → c.mem (c.reg zBase+r)=(G.fd s).zOf r := by
      intro r hr
      rw [Hreg zBase (by decide) (by decide)]
      rw [Hframe.above _ (by rw [hc.zbase];omega)]
      exact hz r hr
    obtain ⟨t,He,Ht⟩ := dartTableStep_exec Hc hG hj Hscan
    let advance : Stmt := seqs [.add scanDart scanDart 1,.sub dartRemaining dartRemaining 1]
    have Ha : ExecB (zLimit L) advance (run dartTableStep c) 3 (run dartTableBody c) := by
      simpa [advance,dartTableBody,RAM.cost,seqs] using
        execB_run advance (by simp [advance,seqs,LoopFree]) (run dartTableStep c)
          (AddrOK.of_memFree (by decide))
    have Hpos := dartBody_advance Hc
    have Hprefix' := dartTableStep_prefix Hc hG hj Hscan Hcz Hprefix
    have Hframe' := dartTableStep_frame Hc hG hj Hscan Hcz
    refine ⟨t+3,run dartTableBody c,.seq He Ha,by omega,?_,by have:=Hpos.2;omega⟩
    refine ⟨dartBody_context Hc,by rw [Hpos.1,Hscan],?_,?_,?_,?_⟩
    · refine ⟨?_,?_,?_⟩
      all_goals intro i hi; rw [dartBody_mem]
      all_goals first | exact Hprefix'.keys i hi | exact Hprefix'.partners i hi | exact Hprefix'.targets i hi
    · intro a ha; rw [dartBody_mem]; exact (Hframe' a ha).trans (Hframe a ha)
    · exact (dartBody_out c).trans Hout
    · intro r hr ha; exact (dartBody_reg c r hr ha).trans (Hreg r hr ha)
  obtain ⟨t,c,He,Ht,Hfinal⟩ := exec_countLoop (2*G.E) I 103 Hstep d HI Hdcount
  have Hepre : ExecB (zLimit L) pre start 3 d := by
    have Hcost : RAM.cost pre start=3 := by rfl
    rw [← Hcost]
    exact execB_run pre (by simp [pre,seqs,LoopFree]) start (AddrOK.of_memFree (by decide))
  exact ⟨3+t,c,.seq Hepre He,by omega,Hfinal.1,Hfinal.2.2⟩

end STACS2027.Embed.PlanRAM

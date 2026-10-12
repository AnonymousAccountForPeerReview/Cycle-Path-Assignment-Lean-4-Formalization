module

public import ApproximationHardness.Embed.DefaultRotationReady
import Lean.Elab.Tactic.Omega

/-! # Bounded linear construction of both default rotation arrays -/

@[expose] public section

namespace STACS2027.Embed.RAMSolver

open RAM

theorem DefaultFrame.step {F : ForestData} (hF : F.Valid) {S : Nat} {start c : Config}
    (h : DefaultReady F S start) (hf : DefaultFrame F start c)
    (hd : c.reg 240<2*F.E) : DefaultFrame F start (run defaultRotationStep c) := by
  have hc := h.frame hf
  have hm := (defaultRotationStep_correct hF hc hd).2
  have hn := hf.reg 261 (by simp [defaultFixedRegisters])
  have hp := hf.reg 262 (by simp [defaultFixedRegisters])
  refine ⟨?_,?_⟩
  · intro r hr
    rw [defaultRotationStep_reg _ r (by
      simp only [defaultFixedRegisters,defaultSourceRegisters,List.mem_append,List.mem_cons,
        List.mem_nil_iff,or_false] at hr
      omega)]
    exact hf.reg r hr
  · intro a ha
    rw [hm,hn,hp]
    have hnep : a≠start.reg 262+c.reg 240 := by
      have := h.separated;omega
    have hnen : a≠start.reg 261+c.reg 240 := by
      have := h.separated;omega
    rw [ite_eq_right hnep,ite_eq_right hnen]
    exact hf.mem a ha

structure DefaultCacheState (F : ForestData) (hF : F.Valid) (start c : Config)
    (n : Nat) : Prop where
  frame : DefaultFrame F start c
  index : c.reg 240=n
  remaining : c.reg 241=2*F.E-n
  bound : n≤2*F.E
  next : ∀ i,i<n → c.mem (start.reg 261+i)=ForestData.rotN hF (fun _=>false) i
  pred : ∀ i,i<n → c.mem (start.reg 262+i)=ForestData.rotInvN hF (fun _=>false) i

theorem DefaultCacheState.step {F : ForestData} (hF : F.Valid) {S : Nat} {start c : Config}
    {n : Nat} (h : DefaultReady F S start) (hc : DefaultCacheState F hF start c n)
    (hn : n<2*F.E) : DefaultCacheState F hF start (run defaultRotationStep c) (n+1) := by
  have hr := h.frame hc.frame
  have hd : c.reg 240<2*F.E := by rw [hc.index];exact hn
  have hm := (defaultRotationStep_correct hF hr hd).2
  have ha := defaultRotationStep_advance c hr.one
  have hnext := hc.frame.reg 261 (by simp [defaultFixedRegisters])
  have hpred := hc.frame.reg 262 (by simp [defaultFixedRegisters])
  refine ⟨hc.frame.step hF h hd,?_,?_,by omega,?_,?_⟩
  · rw [ha.1,hc.index]
  · rw [ha.2,hc.remaining];omega
  · intro i hi
    rw [hm,hnext,hpred,hc.index]
    have hnp : start.reg 261+i≠start.reg 262+n := by have := h.separated;omega
    rw [ite_eq_right hnp]
    by_cases he : i=n
    · subst i;simp
    · have hne : start.reg 261+i≠start.reg 261+n := by omega
      rw [ite_eq_right hne];exact hc.next i (by omega)
  · intro i hi
    rw [hm,hnext,hpred,hc.index]
    by_cases he : i=n
    · subst i;simp
    · have hpne : start.reg 262+i≠start.reg 262+n := by omega
      have hnne : start.reg 262+i≠start.reg 261+n := by have := h.separated;omega
      rw [ite_eq_right hpne,ite_eq_right hnne];exact hc.pred i (by omega)

theorem defaultRotationLoop_spec {F : ForestData} (hF : F.Valid) {S : Nat}
    (start : Config) (h : DefaultReady F S start) :
    ∀ (r n : Nat) (c : Config),n+r=2*F.E → DefaultCacheState F hF start c n →
      ∃ t c',ExecB S defaultRotationLoop c t c' ∧ t≤1201*r+1 ∧
        DefaultCacheState F hF start c' (2*F.E) ∧ c'.out=c.out := by
  intro r
  induction r with
  | zero =>
    intro n c hn hc
    have he : n=2*F.E := by omega
    subst n
    exact ⟨1,c,.loopDone (by rw [hc.remaining];omega),by simp,hc,rfl⟩
  | succ r ih =>
    intro n c hn hc
    have hn' : n<2*F.E := by omega
    have hr := h.frame hc.frame
    have hd : c.reg 240<2*F.E := by rw [hc.index];exact hn'
    have haddr := (defaultRotationStep_correct hF hr hd).1
    have he := execB_run defaultRotationStep defaultRotationStep_loopFree c haddr
    have ht := (cost_le_size defaultRotationStep c).trans defaultRotationStep_size
    obtain ⟨t,c',he',ht',hfinal,hout⟩ := ih (n+1) (run defaultRotationStep c) (by omega)
      (hc.step hF h hn')
    exact ⟨RAM.cost defaultRotationStep c+t+1,c',.loopNext (by rw [hc.remaining];omega) he he',
      by omega,hfinal,hout.trans (defaultRotationStep_out c)⟩

def defaultRotationPre : Stmt := seqs [.const 240 0,.add 241 140 0]
def defaultRotationProgram : Stmt := .seq defaultRotationPre defaultRotationLoop

theorem defaultRotationProgram_spec {F : ForestData} (hF : F.Valid) {S : Nat}
    (start : Config) (h : DefaultReady F S start) :
    ∃ t c',ExecB S defaultRotationProgram start t c' ∧ t≤1201*(2*F.E)+4 ∧
      DefaultFrame F start c' ∧ c'.out=start.out ∧
      (∀ d,d<2*F.E → c'.mem (start.reg 261+d)=ForestData.rotN hF (fun _=>false) d) ∧
      (∀ d,d<2*F.E → c'.mem (start.reg 262+d)=ForestData.rotInvN hF (fun _=>false) d) := by
  let c := run defaultRotationPre start
  have hframe : DefaultFrame F start c := by
    refine ⟨?_,?_⟩
    · intro r hr
      have hne : r≠240 ∧ r≠241 := by
        simp only [defaultFixedRegisters,defaultSourceRegisters,List.mem_append,List.mem_cons,
          List.mem_nil_iff,or_false] at hr
        omega
      simp [c,defaultRotationPre,seqs,run,hne.1,hne.2]
    · intro a _;simp [c,defaultRotationPre,seqs,run]
  have hc : DefaultCacheState F hF start c 0 := by
    refine ⟨hframe,?_,?_,by omega,by simp,by simp⟩
    · simp [c,defaultRotationPre,seqs,run]
    · simp [c,defaultRotationPre,seqs,run,h.zero,h.darts]
  obtain ⟨t,c',he,ht,hfinal,hout⟩ := defaultRotationLoop_spec hF start h (2*F.E) 0 c (by omega) hc
  have hpre := execB_run (S:=S) defaultRotationPre (by simp [defaultRotationPre,seqs,LoopFree])
    start (AddrOK.of_memFree (by rfl))
  have hp : RAM.cost defaultRotationPre start≤3 := cost_le_size _ _
  refine ⟨RAM.cost defaultRotationPre start+t,c',.seq hpre he,by omega,hfinal.frame,?_,hfinal.next,hfinal.pred⟩
  rw [hout];simp [c,defaultRotationPre,seqs,run]

end STACS2027.Embed.RAMSolver

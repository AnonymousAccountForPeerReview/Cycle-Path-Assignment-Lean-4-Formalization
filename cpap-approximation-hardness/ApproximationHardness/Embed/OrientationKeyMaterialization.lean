module

public import ApproximationHardness.Embed.OrientationKeysRAM
public import ApproximationHardness.RAM.FrameB
import Lean.Elab.Tactic.Omega

/-! # Complete RAM visit-stream construction for the orientation fold -/

@[expose] public section

namespace STACS2027.Embed.RAMSolver

open RAM

def keyPre : Stmt := seqs [.add 270 4 0,.const 273 0,.add 274 140 140]
def keyMid : Stmt := seqs [.add 270 140 0,.const 277 0]
def keyFinish : Stmt := seqs [.add 109 4 140,.const 110 0]
def keyProgram : Stmt := .seq keyPre (.seq reverseKeyLoop (.seq keyMid (.seq forwardKeyLoop keyFinish)))

theorem orientationKeys_explicit (F : ForestData) (post : List Nat) :
    orientationKeys F post=post.reverse.map (fun v=>4*F.E+v)++List.range (2*F.E) := by
  simp [orientationKeys,ForestData.oitems,List.map_append,List.map_map,ForestData.okey,Function.comp_def,ForestData.gid]

theorem keyPre_loopFree : LoopFree keyPre := by simp [keyPre,seqs,LoopFree]
theorem keyMid_loopFree : LoopFree keyMid := by simp [keyMid,seqs,LoopFree]
theorem keyFinish_loopFree : LoopFree keyFinish := by simp [keyFinish,seqs,LoopFree]
theorem keyPre_size : size keyPre≤4 := by decide
theorem keyMid_size : size keyMid≤3 := by decide
theorem keyFinish_size : size keyFinish≤3 := by decide

theorem keyPre_mem (c : Config) : (run keyPre c).mem=c.mem := by simp [keyPre,seqs,run]
theorem keyMid_mem (c : Config) : (run keyMid c).mem=c.mem := by simp [keyMid,seqs,run]
theorem keyFinish_mem (c : Config) : (run keyFinish c).mem=c.mem := by simp [keyFinish,seqs,run]
theorem keyPre_out (c : Config) : (run keyPre c).out=c.out := by simp [keyPre,seqs,run]
theorem keyMid_out (c : Config) : (run keyMid c).out=c.out := by simp [keyMid,seqs,run]
theorem keyFinish_out (c : Config) : (run keyFinish c).out=c.out := by simp [keyFinish,seqs,run]

theorem keyProgram_regs {S : Nat} {c c' : Config} {t : Nat} (h : ExecB S keyProgram c t c')
    (r : Nat) (hr : r<270) (hleft : r≠109) (hright : r≠110) : c'.reg r=c.reg r := by
  apply h.reg_frame
  simp only [keyProgram,keyPre,keyMid,keyFinish,reverseKeyLoop,reverseKeyStep,
    forwardKeyLoop,forwardKeyStep,seqs,regsW,List.mem_append,List.mem_cons,
    not_or,List.mem_nil_iff,or_false,not_false_eq_true]
  repeat' constructor
  all_goals omega

theorem getD_map_add (xs : List Nat) (offset i : Nat) (hi : i<xs.length) :
    (xs.map (fun x=>offset+x)).getD i 0=offset+xs.getD i 0 := by
  rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (by simpa using hi),
    List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi]
  simp

/-- Both actual loops produce exactly the abstract orientation visit stream. -/
theorem keyProgram_spec {S : Nat} (F : ForestData) (post : List Nat) (c : Config)
    (hzero : c.reg 0=0) (hone : c.reg 1=1) (hpost : c.reg 4=post.length)
    (hdarts : c.reg 140=2*F.E) (hsource : c.reg 71+post.length≤c.reg 113)
    (hspace : c.reg 113+post.length+2*F.E≤S)
    (hcells : ∀ i,i<post.length → c.mem (c.reg 71+i)=post.getD i 0) :
    ∃ t c',ExecB S keyProgram c t c' ∧ t≤9*post.length+14*F.E+12 ∧
      c'.out=c.out ∧ c'.reg 109=(orientationKeys F post).length ∧ c'.reg 110=0 ∧
      (∀ i,i<(orientationKeys F post).length →
        c'.mem (c.reg 113+i)=(orientationKeys F post).getD i 0) ∧
      (∀ a,a<c.reg 113 ∨ c.reg 113+post.length+2*F.E≤a → c'.mem a=c.mem a) := by
  have ePre := execB_run (S:=S) keyPre keyPre_loopFree c
    (AddrOK.of_memFree (by simp [keyPre,seqs,memFree]))
  have tPre := Nat.le_trans (cost_le_size keyPre c) keyPre_size
  have init : KeyCopyState post (4*F.E) (c.reg 71) (c.reg 113) c (run keyPre c) 0 := by
    refine ⟨?_,?_,?_,?_,?_,?_,by omega,hsource,?_,?_,?_⟩
    · simp [keyPre,seqs,run,hone]
    · simp [keyPre,seqs,run]
    · simp [keyPre,seqs,run]
    · simp [keyPre,seqs,run,hdarts];omega
    · simp [keyPre,seqs,run]
    · simp [keyPre,seqs,run,hpost,hzero]
    · simpa only [keyPre_mem] using hcells
    · intro i hi;omega
    · intro a _;rw [keyPre_mem]
  obtain ⟨tRev,cRev,eRev,htRev,hRev,hoRev⟩ := reverseKeyLoop_spec (S:=S)
    (by omega) post.length 0 c (run keyPre c) (by omega) init
  have regRev r (hr : r≠270 ∧ r≠273 ∧ r≠275 ∧ r≠276) : cRev.reg r=(run keyPre c).reg r := by
    apply eRev.reg_frame
    rcases hr with ⟨h₁,h₂,h₃,h₄⟩
    simp [reverseKeyLoop,reverseKeyStep,seqs,regsW,h₁,h₂,h₃,h₄]
  have rD : cRev.reg 140=2*F.E := by rw [regRev _ (by decide)];simp [keyPre,seqs,run,hdarts]
  have rz : cRev.reg 0=0 := by rw [regRev _ (by decide)];simp [keyPre,seqs,run,hzero]
  have rp : cRev.reg 4=post.length := by rw [regRev _ (by decide)];simp [keyPre,seqs,run,hpost]
  have eMid := execB_run (S:=S) keyMid keyMid_loopFree cRev
    (AddrOK.of_memFree (by simp [keyMid,seqs,memFree]))
  have tMid := Nat.le_trans (cost_le_size keyMid cRev) keyMid_size
  have fInit : ForwardKeyState (2*F.E) (c.reg 113) post.length cRev (run keyMid cRev) 0 := by
    refine ⟨?_,?_,?_,?_,?_,by omega,?_,?_⟩
    · simp [keyMid,seqs,run,hRev.one]
    · simp [keyMid,seqs,run,hRev.keyBase]
    · simp [keyMid,seqs,run,hRev.index]
    · simp [keyMid,seqs,run]
    · simp [keyMid,seqs,run,rD,rz]
    · intro i hi;omega
    · intro a _;rw [keyMid_mem]
  obtain ⟨tFwd,cFwd,eFwd,htFwd,hFwd,hoFwd⟩ := forwardKeyLoop_spec (S:=S)
    hspace (2*F.E) 0 cRev (run keyMid cRev) (by omega) fInit
  have regFwd r (hr : r≠270 ∧ r≠273 ∧ r≠275 ∧ r≠277) : cFwd.reg r=(run keyMid cRev).reg r := by
    apply eFwd.reg_frame
    rcases hr with ⟨h₁,h₂,h₃,h₄⟩
    simp [forwardKeyLoop,forwardKeyStep,seqs,regsW,h₁,h₂,h₃,h₄]
  have rD' : cFwd.reg 140=2*F.E := by rw [regFwd _ (by decide)];simp [keyMid,seqs,run,rD]
  have rp' : cFwd.reg 4=post.length := by rw [regFwd _ (by decide)];simp [keyMid,seqs,run,rp]
  have eFin := execB_run (S:=S) keyFinish keyFinish_loopFree cFwd
    (AddrOK.of_memFree (by simp [keyFinish,seqs,memFree]))
  have tFin := Nat.le_trans (cost_le_size keyFinish cFwd) keyFinish_size
  refine ⟨RAM.cost keyPre c+(tRev+(RAM.cost keyMid cRev+(tFwd+RAM.cost keyFinish cFwd))),
    run keyFinish cFwd,.seq ePre (.seq eRev (.seq eMid (.seq eFwd eFin))),by omega,?_,?_,?_,?_,?_⟩
  · rw [keyFinish_out,hoFwd,keyMid_out,hoRev,keyPre_out]
  · simp [keyFinish,seqs,run,rp',rD',orientationKeys_explicit]
  · simp [keyFinish,seqs,run]
  · intro i hi
    rw [keyFinish_mem,orientationKeys_explicit]
    simp only [orientationKeys_explicit,List.length_append,List.length_map,List.length_reverse,
      List.length_range] at hi
    by_cases hl : i<post.length
    · rw [hFwd.frame _ (Or.inl (by omega)),hRev.keyCells i hl]
      conv_rhs => rw [List.getD_eq_getElem?_getD,List.getElem?_append_left (by simpa using hl)]
      conv_rhs => rw [←List.getD_eq_getElem?_getD,getD_map_add _ _ _ (by simpa using hl)]
    · have hd : i-post.length<2*F.E := by omega
      have he : c.reg 113+i=c.reg 113+post.length+(i-post.length) := by omega
      rw [he,hFwd.cells _ hd]
      rw [List.getD_eq_getElem?_getD,List.getElem?_append_right (by simpa using Nat.le_of_not_gt hl)]
      simp [hd]
  · intro a ha
    rw [keyFinish_mem,hFwd.frame a (by omega),hRev.frame a (by omega)]

end STACS2027.Embed.RAMSolver

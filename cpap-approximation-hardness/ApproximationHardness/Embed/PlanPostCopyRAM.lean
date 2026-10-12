module

public import ApproximationHardness.Embed.PlanStoreRAM
public import ApproximationHardness.RAM.FrameB
import Lean.Elab.Tactic.Omega

/-! # Uniform bounded copying of the actual DFS postorder -/

@[expose] public section

namespace STACS2027.Embed.PlanRAM

open RAM

def postCopyPre : Stmt := seqs [.const 307 0,.add 306 4 0]
def postCopyBody : Stmt := seqs [.add 308 170 307,.load 309 308,
  .add 308 71 307,.store 308 309,.add 307 307 1,.sub 306 306 1]
def postCopyLoop : Stmt := .loop 306 postCopyBody
def postCopyProgram : Stmt := .seq postCopyPre postCopyLoop

theorem postCopyBody_loopFree : LoopFree postCopyBody := by simp [postCopyBody,seqs,LoopFree]
theorem postCopyBody_size : size postCopyBody≤7 := by decide

theorem postCopyBody_reg (c : Config) (r : Nat)
    (hr : r≠306 ∧ r≠307 ∧ r≠308 ∧ r≠309) :
    (run postCopyBody c).reg r=c.reg r := by
  rcases hr with ⟨h₁,h₂,h₃,h₄⟩
  simp [postCopyBody,seqs,run,h₁,h₂,h₃,h₄]

theorem postCopyBody_mem (c : Config) (a : Nat) :
    (run postCopyBody c).mem a=
      if a=c.reg 71+c.reg 307 then c.mem (c.reg 170+c.reg 307) else c.mem a := by
  simp [postCopyBody,seqs,run]

theorem postCopyBody_advance (c : Config) (hone : c.reg 1=1) :
    (run postCopyBody c).reg 306=c.reg 306-1 ∧
      (run postCopyBody c).reg 307=c.reg 307+1 := by
  simp [postCopyBody,seqs,run,hone]

theorem postCopyBody_out (c : Config) : (run postCopyBody c).out=c.out := by
  simp [postCopyBody,seqs,run]

theorem postCopyBody_addrOK {S : Nat} (c : Config)
    (hsource : c.reg 170+c.reg 307<S) (hdest : c.reg 71+c.reg 307<S) :
    AddrOK S postCopyBody c := by
  simp [postCopyBody,seqs,run,AddrOK,hsource,hdest]

structure PostCopyState (post : List Nat) (source target : Nat)
    (start c : Config) (n : Nat) : Prop where
  one : c.reg 1=1
  sourceBase : c.reg 170=source
  targetBase : c.reg 71=target
  index : c.reg 307=n
  count : c.reg 306=post.length-n
  bound : n≤post.length
  disjoint : source+post.length≤target
  sourceCells : ∀ i,i<post.length → c.mem (source+i)=post.getD i 0
  targetCells : ∀ i,i<n → c.mem (target+i)=post.getD i 0
  frame : ∀ a,a<target ∨ target+post.length≤a → c.mem a=start.mem a

theorem PostCopyState.step {post : List Nat} {source target : Nat}
    {start c : Config} {n : Nat} (h : PostCopyState post source target start c n)
    (hn : n<post.length) :
    PostCopyState post source target start (run postCopyBody c) (n+1) := by
  have hraw a := postCopyBody_mem c a
  have hread : c.mem (c.reg 170+c.reg 307)=post.getD n 0 := by
    rw [h.sourceBase,h.index,h.sourceCells n hn]
  have hadvance := postCopyBody_advance c h.one
  refine ⟨?_,?_,?_,?_,?_,by omega,h.disjoint,?_,?_,?_⟩
  · rw [postCopyBody_reg _ _ (by decide)];exact h.one
  · rw [postCopyBody_reg _ _ (by decide)];exact h.sourceBase
  · rw [postCopyBody_reg _ _ (by decide)];exact h.targetBase
  · rw [hadvance.2,h.index]
  · rw [hadvance.1,h.count];omega
  · intro i hi
    rw [hraw,h.targetBase,h.index]
    have hne : source+i≠target+n := by have := h.disjoint;omega
    rw [ite_eq_right hne];exact h.sourceCells i hi
  · intro i hi
    rw [hraw,hread,h.targetBase,h.index]
    by_cases he : i=n
    · subst i;simp
    · rw [ite_eq_right (by omega : target+i≠target+n)]
      exact h.targetCells i (by omega)
  · intro a ha
    rw [hraw,h.targetBase,h.index,ite_eq_right (by omega : a≠target+n)]
    exact h.frame a ha

theorem postCopyLoop_spec {S : Nat} {post : List Nat} {source target : Nat}
    (hspace : target+post.length≤S) :
    ∀ (r n : Nat) (start c : Config),n+r=post.length →
      PostCopyState post source target start c n →
      ∃ t c',ExecB S postCopyLoop c t c' ∧ t≤8*r+1 ∧
        PostCopyState post source target start c' post.length ∧ c'.out=c.out := by
  intro r
  induction r with
  | zero =>
    intro n start c hn hc
    have he : n=post.length := by omega
    subst n
    exact ⟨1,c,.loopDone (by rw [hc.count];omega),by simp,hc,rfl⟩
  | succ r ih =>
    intro n start c hn hc
    have hn' : n<post.length := by omega
    have ha : AddrOK S postCopyBody c := by
      apply postCopyBody_addrOK
      · rw [hc.sourceBase,hc.index];have := hc.disjoint;omega
      · rw [hc.targetBase,hc.index];omega
    have e := execB_run postCopyBody postCopyBody_loopFree c ha
    have ht := Nat.le_trans (cost_le_size postCopyBody c) postCopyBody_size
    obtain ⟨t,c',he,ht',hfinal,hout⟩ := ih (n+1) start (run postCopyBody c)
      (by omega) (hc.step hn')
    exact ⟨RAM.cost postCopyBody c+t+1,c',
      .loopNext (by rw [hc.count];omega) e he,by omega,hfinal,
      hout.trans (postCopyBody_out c)⟩

theorem postCopyProgram_reg {S : Nat} {c c' : Config} {t : Nat}
    (he : ExecB S postCopyProgram c t c') (r : Nat) (hr : r<306 ∨ 309<r) :
    c'.reg r=c.reg r := by
  apply he.reg_frame
  simp only [postCopyProgram,postCopyPre,postCopyLoop,postCopyBody,seqs,regsW,
    List.mem_append,List.mem_cons,List.mem_nil_iff,or_false,not_or,not_false_eq_true]
  repeat' constructor
  all_goals omega

theorem postCopyProgram_spec {S : Nat} (post : List Nat) (c : Config)
    (hzero : c.reg 0=0) (hone : c.reg 1=1) (hpost : c.reg 4=post.length)
    (hsource : c.reg 170+post.length≤c.reg 71)
    (hspace : c.reg 71+post.length≤S)
    (hcells : ∀ i,i<post.length → c.mem (c.reg 170+i)=post.getD i 0) :
    ∃ t c',ExecB S postCopyProgram c t c' ∧ t≤8*post.length+4 ∧
      c'.out=c.out ∧
      (∀ i,i<post.length → c'.mem (c.reg 71+i)=post.getD i 0) ∧
      (∀ a,a<c.reg 71 ∨ c.reg 71+post.length≤a → c'.mem a=c.mem a) := by
  have ePre := execB_run (S:=S) postCopyPre (by simp [postCopyPre,seqs,LoopFree]) c
    (AddrOK.of_memFree (by decide))
  have tPre : RAM.cost postCopyPre c≤3 := cost_le_size _ _
  have hm : (run postCopyPre c).mem=c.mem := by simp [postCopyPre,seqs,run]
  have init : PostCopyState post (c.reg 170) (c.reg 71) c (run postCopyPre c) 0 := by
    refine ⟨?_,?_,?_,?_,?_,by omega,hsource,?_,?_,?_⟩
    · simp [postCopyPre,seqs,run,hone]
    · simp [postCopyPre,seqs,run]
    · simp [postCopyPre,seqs,run]
    · simp [postCopyPre,seqs,run]
    · simp [postCopyPre,seqs,run,hpost,hzero]
    · simpa only [hm] using hcells
    · intro i hi;omega
    · intro a _;rw [hm]
  obtain ⟨t,c',he,ht,hfinal,hout⟩ := postCopyLoop_spec hspace post.length 0 c
    (run postCopyPre c) (by omega) init
  exact ⟨RAM.cost postCopyPre c+t,c',.seq ePre he,by omega,
    hout.trans (by simp [postCopyPre,seqs,run]),hfinal.targetCells,hfinal.frame⟩

/-- The real DFS postorder is copied into its final solver table while all
other plan blocks, the complete forest cache, and mutable zero arrays survive. -/
theorem postCopy_context_spec {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) :
    ∃ t c',ExecB (zLimit L) postCopyProgram c t c' ∧ t≤8*s.post.length+4 ∧
      Context L G s c' ∧
      (∀ i,i<s.post.length → c'.mem ((solverLayout L).cell 21 i)=s.post.getD i 0) ∧
      c'.out=c.out ∧
      (∀ a,a<(solverLayout L).block 21 ∨ (solverLayout L).block 21+L.width≤a →
        c'.mem a=c.mem a) ∧
      (∀ r,r<306 ∨ 309<r → c'.reg r=c.reg r) := by
  have hsource : c.reg 170=L.block 10 := hc.forest.bases.2.2.2.2.2 10 (by decide)
  have htarget : c.reg 71=(solverLayout L).block 21 := hc.solver.2.2.2.2 21 (by decide)
  have hseparated : c.reg 170+s.post.length≤c.reg 71 := by
    rw [hsource,htarget]
    have hcap := hc.postCapacity
    dsimp [DFSRAM.Layout.block,DFSRAM.Layout.limit,solverLayout,RAMSolver.Layout.block]
    omega
  have hspace : c.reg 71+s.post.length≤zLimit L := by
    rw [htarget]
    have hcap := hc.postCapacity
    dsimp [zLimit,RAMSolver.Layout.block,RAMSolver.Layout.limit,solverLayout]
    omega
  have hcells (i : Nat) (hi : i<s.post.length) : c.mem (c.reg 170+i)=s.post.getD i 0 := by
    rw [hsource]
    exact hc.forest.post i hi
  obtain ⟨t,c',he,ht,hout,hcopied,hframe⟩ := postCopyProgram_spec s.post c
    hc.solver.1 hc.solver.2.1 hc.postLength hseparated hspace hcells
  have hreg (r : Nat) (hr : r<306 ∨ 309<r) := postCopyProgram_reg he r hr
  have hblock : ∀ a,a<(solverLayout L).block 21 ∨ (solverLayout L).block 21+L.width≤a →
      c'.mem a=c.mem a := by
    intro a ha
    apply hframe
    rw [htarget]
    have hcap := hc.postCapacity
    omega
  have hforest : ∀ a,a<L.limit → c'.mem a=c.mem a := by
    intro a ha
    apply hblock a (Or.inl ?_)
    dsimp [solverLayout,RAMSolver.Layout.block]
    omega
  have hcontext : Context L G s c' := hc.memory (fun r hr=>hreg r (Or.inl (by omega))) hforest
  refine ⟨t,c',he,ht,hcontext,?_,hout,hblock,hreg⟩
  intro i hi
  simpa only [htarget,RAMSolver.Layout.cell] using hcopied i hi

theorem postCopy_compiled {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) (hz : MutableZero L c) :
    ∃ t c',ExecB (zLimit L) postCopyProgram c t c' ∧ t≤8*s.post.length+4 ∧
      Context L G s c' ∧ MutableZero L c' ∧
      (∀ i,i<s.post.length → c'.mem ((solverLayout L).cell 21 i)=s.post.getD i 0) ∧
      c'.out=c.out ∧
      (∀ a,a<(solverLayout L).block 21 ∨ (solverLayout L).block 21+L.width≤a →
        c'.mem a=c.mem a) ∧
      (∀ r,r<306 ∨ 309<r → c'.reg r=c.reg r) := by
  obtain ⟨t,c',he,ht,hcontext,hcopied,hout,hframe,hreg⟩ := postCopy_context_spec hc
  refine ⟨t,c',he,ht,hcontext,?_,hcopied,hout,hframe,hreg⟩
  intro j hj i hi
  rw [hframe]
  · exact hz j hj i hi
  · left
    have hm := Nat.mul_le_mul_right L.width (show j+1≤21 by omega)
    rw [Nat.add_mul] at hm
    dsimp [RAMSolver.Layout.cell,RAMSolver.Layout.block,solverLayout]
    omega

/-- The interval frame in the copy specification protects every earlier plan
cell and all memory beyond the solver layout. -/
theorem postCopy_prefix_frame {L : DFSRAM.Layout} {c d : Config}
    (hframe : ∀ a,a<(solverLayout L).block 21 ∨ (solverLayout L).block 21+L.width≤a →
      d.mem a=c.mem a) :
    (∀ j,j<21 → ∀ i,i<L.width → d.mem ((solverLayout L).cell j i)=c.mem ((solverLayout L).cell j i)) ∧
      (∀ a,(solverLayout L).limit≤a → d.mem a=c.mem a) := by
  constructor
  · intro j hj i hi
    apply hframe _ (Or.inl ?_)
    have hm := Nat.mul_le_mul_right L.width (show j+1≤21 by omega)
    rw [Nat.add_mul] at hm
    dsimp [RAMSolver.Layout.cell,RAMSolver.Layout.block,solverLayout]
    omega
  · intro a ha
    apply hframe a (Or.inr ?_)
    dsimp [RAMSolver.Layout.block,RAMSolver.Layout.limit,solverLayout] at ha ⊢
    omega

end STACS2027.Embed.PlanRAM

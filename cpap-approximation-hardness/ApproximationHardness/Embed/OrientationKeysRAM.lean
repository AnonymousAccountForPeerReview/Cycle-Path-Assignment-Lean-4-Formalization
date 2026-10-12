module

public import ApproximationHardness.Embed.OrientationSequence
public import ApproximationHardness.RAM.Pass
import Lean.Elab.Tactic.Omega

/-! # Linear materialization of the orientation visit stream -/

@[expose] public section

namespace STACS2027.Embed.RAMSolver

open RAM

/-- Source postorder71, destination113, offset274, remaining270, destination index273. -/
def reverseKeyStep : Stmt := seqs [
  .sub 270 270 1,.add 275 71 270,.load 276 275,
  .add 276 276 274,.add 275 113 273,.store 275 276,.add 273 273 1]

def reverseKeyLoop : Stmt := .loop 270 reverseKeyStep

theorem reverseKeyStep_loopFree : LoopFree reverseKeyStep := by
  simp [reverseKeyStep,seqs,LoopFree]

theorem reverseKeyStep_size : size reverseKeyStep≤8 := by decide

theorem reverseKeyStep_reg (c : Config) (r : Nat)
    (hr : r≠270 ∧ r≠273 ∧ r≠275 ∧ r≠276) :
    (run reverseKeyStep c).reg r=c.reg r := by
  rcases hr with ⟨h₁,h₂,h₃,h₄⟩
  simp [reverseKeyStep,seqs,run,h₁,h₂,h₃,h₄]

theorem reverseKeyStep_mem (c : Config) (hone : c.reg 1=1) (a : Nat) :
    (run reverseKeyStep c).mem a=
      if a=c.reg 113+c.reg 273 then c.mem (c.reg 71+(c.reg 270-1))+c.reg 274
      else c.mem a := by
  simp [reverseKeyStep,seqs,run,hone]

theorem reverseKeyStep_advance (c : Config) (hone : c.reg 1=1) :
    (run reverseKeyStep c).reg 270=c.reg 270-1 ∧
      (run reverseKeyStep c).reg 273=c.reg 273+1 := by
  simp [reverseKeyStep,seqs,run,hone]

theorem reverseKeyStep_out (c : Config) : (run reverseKeyStep c).out=c.out := by
  simp [reverseKeyStep,seqs,run]

theorem reverseKeyStep_addrOK {S : Nat} (c : Config) (hone : c.reg 1=1)
    (hsource : c.reg 71+(c.reg 270-1)<S) (hdest : c.reg 113+c.reg 273<S) :
    AddrOK S reverseKeyStep c := by
  simp [reverseKeyStep,seqs,run,AddrOK,hone,hsource,hdest]

theorem getD_reverse_nat (post : List Nat) (n : Nat) (hn : n<post.length) :
    post.reverse.getD n 0=post.getD (post.length-1-n) 0 := by
  rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (by simpa using hn),
    List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (by omega)]
  simp only [Option.getD_some,List.getElem_reverse]

structure KeyCopyState (post : List Nat) (offset source keys : Nat)
    (start c : Config) (n : Nat) : Prop where
  one : c.reg 1=1
  sourceBase : c.reg 71=source
  keyBase : c.reg 113=keys
  offsetValue : c.reg 274=offset
  index : c.reg 273=n
  count : c.reg 270=post.length-n
  bound : n≤post.length
  disjoint : source+post.length≤keys
  sourceCells : ∀ i,i<post.length → c.mem (source+i)=post.getD i 0
  keyCells : ∀ i,i<n → c.mem (keys+i)=offset+post.reverse.getD i 0
  frame : ∀ a,a<keys ∨ keys+post.length≤a → c.mem a=start.mem a

theorem KeyCopyState.step {post : List Nat} {offset source keys : Nat}
    {start c : Config} {n : Nat} (h : KeyCopyState post offset source keys start c n)
    (hn : n<post.length) :
    KeyCopyState post offset source keys start (run reverseKeyStep c) (n+1) := by
  have hraw a := reverseKeyStep_mem c h.one a
  have hread : c.mem (c.reg 71+(c.reg 270-1))+c.reg 274=
      offset+post.reverse.getD n 0 := by
    rw [h.sourceBase,h.count,h.offsetValue,h.sourceCells _ (by omega),getD_reverse_nat post n hn]
    have he : post.length-n-1=post.length-1-n := by omega
    rw [he];omega
  have hadvance := reverseKeyStep_advance c h.one
  refine ⟨?_,?_,?_,?_,?_,?_,by omega,h.disjoint,?_,?_,?_⟩
  · rw [reverseKeyStep_reg _ _ (by decide)];exact h.one
  · rw [reverseKeyStep_reg _ _ (by decide)];exact h.sourceBase
  · rw [reverseKeyStep_reg _ _ (by decide)];exact h.keyBase
  · rw [reverseKeyStep_reg _ _ (by decide)];exact h.offsetValue
  · rw [hadvance.2,h.index]
  · rw [hadvance.1,h.count];omega
  · intro i hi
    rw [hraw,h.keyBase,h.index]
    have hne : source+i≠keys+n := by have := h.disjoint;omega
    rw [ite_eq_right hne];exact h.sourceCells i hi
  · intro i hi
    rw [hraw,h.keyBase,h.index,hread]
    by_cases he : i=n
    · subst i;simp
    · have hne : keys+i≠keys+n := by omega
      rw [ite_eq_right hne];exact h.keyCells i (by omega)
  · intro a ha
    rw [hraw,h.keyBase,h.index]
    have hne : a≠keys+n := by omega
    rw [ite_eq_right hne];exact h.frame a ha

/-- The reverse-copy loop really materializes all node-group keys. -/
theorem reverseKeyLoop_spec {S : Nat} {post : List Nat} {offset source keys : Nat}
    (hspace : keys+post.length≤S) :
    ∀ (r n : Nat) (start c : Config),n+r=post.length →
      KeyCopyState post offset source keys start c n →
      ∃ t c',ExecB S reverseKeyLoop c t c' ∧ t≤9*r+1 ∧
        KeyCopyState post offset source keys start c' post.length ∧ c'.out=c.out := by
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
    have hnz : c.reg 270≠0 := by rw [hc.count];omega
    have ha : AddrOK S reverseKeyStep c := by
      apply reverseKeyStep_addrOK c hc.one
      · rw [hc.sourceBase,hc.count];have := hc.disjoint;omega
      · rw [hc.keyBase,hc.index];omega
    have e := execB_run reverseKeyStep reverseKeyStep_loopFree c ha
    have ht := Nat.le_trans (cost_le_size reverseKeyStep c) reverseKeyStep_size
    obtain ⟨t,c',he,ht',hfinal,hout⟩ := ih (n+1) start (run reverseKeyStep c)
      (by omega) (hc.step hn')
    exact ⟨RAM.cost reverseKeyStep c+t+1,c',.loopNext hnz e he,by omega,hfinal,
      hout.trans (reverseKeyStep_out c)⟩


/-- Append dart identifiers in their increasing order. -/
def forwardKeyStep : Stmt := seqs [
  .add 275 113 273,.store 275 277,.add 277 277 1,.add 273 273 1,.sub 270 270 1]

def forwardKeyLoop : Stmt := .loop 270 forwardKeyStep

theorem forwardKeyStep_loopFree : LoopFree forwardKeyStep := by
  simp [forwardKeyStep,seqs,LoopFree]

theorem forwardKeyStep_size : size forwardKeyStep≤6 := by decide

theorem forwardKeyStep_reg (c : Config) (r : Nat)
    (hr : r≠270 ∧ r≠273 ∧ r≠275 ∧ r≠277) :
    (run forwardKeyStep c).reg r=c.reg r := by
  rcases hr with ⟨h₁,h₂,h₃,h₄⟩
  simp [forwardKeyStep,seqs,run,h₁,h₂,h₃,h₄]

theorem forwardKeyStep_mem (c : Config) (a : Nat) :
    (run forwardKeyStep c).mem a=if a=c.reg 113+c.reg 273 then c.reg 277 else c.mem a := by
  simp [forwardKeyStep,seqs,run]

theorem forwardKeyStep_advance (c : Config) (hone : c.reg 1=1) :
    (run forwardKeyStep c).reg 270=c.reg 270-1 ∧
    (run forwardKeyStep c).reg 273=c.reg 273+1 ∧
    (run forwardKeyStep c).reg 277=c.reg 277+1 := by
  simp [forwardKeyStep,seqs,run,hone]

theorem forwardKeyStep_out (c : Config) : (run forwardKeyStep c).out=c.out := by
  simp [forwardKeyStep,seqs,run]

structure ForwardKeyState (total keys begin : Nat) (start c : Config) (n : Nat) : Prop where
  one : c.reg 1=1
  keyBase : c.reg 113=keys
  index : c.reg 273=begin+n
  value : c.reg 277=n
  count : c.reg 270=total-n
  bound : n≤total
  cells : ∀ i,i<n → c.mem (keys+begin+i)=i
  frame : ∀ a,a<keys+begin ∨ keys+begin+total≤a → c.mem a=start.mem a

theorem ForwardKeyState.step {total keys begin : Nat} {start c : Config} {n : Nat}
    (h : ForwardKeyState total keys begin start c n) (hn : n<total) :
    ForwardKeyState total keys begin start (run forwardKeyStep c) (n+1) := by
  have hm a := forwardKeyStep_mem c a
  have ha := forwardKeyStep_advance c h.one
  refine ⟨?_,?_,?_,?_,?_,by omega,?_,?_⟩
  · rw [forwardKeyStep_reg _ _ (by decide)];exact h.one
  · rw [forwardKeyStep_reg _ _ (by decide)];exact h.keyBase
  · rw [ha.2.1,h.index];omega
  · rw [ha.2.2,h.value]
  · rw [ha.1,h.count];omega
  · intro i hi
    rw [hm,h.keyBase,h.index,h.value]
    by_cases he : i=n
    · subst i;simp [Nat.add_assoc]
    · have hne : keys+begin+i≠keys+(begin+n) := by omega
      rw [ite_eq_right hne];exact h.cells i (by omega)
  · intro a hab
    rw [hm,h.keyBase,h.index]
    have hne : a≠keys+(begin+n) := by omega
    rw [ite_eq_right hne];exact h.frame a hab

/-- Actual increasing append loop, preserving every preceding visit key. -/
theorem forwardKeyLoop_spec {S total keys begin : Nat} (hspace : keys+begin+total≤S) :
    ∀ (r n : Nat) (start c : Config),n+r=total →
      ForwardKeyState total keys begin start c n →
      ∃ t c',ExecB S forwardKeyLoop c t c' ∧ t≤7*r+1 ∧
        ForwardKeyState total keys begin start c' total ∧ c'.out=c.out := by
  intro r
  induction r with
  | zero =>
    intro n start c hn hc
    have he : n=total := by omega
    subst n
    exact ⟨1,c,.loopDone (by rw [hc.count];omega),by simp,hc,rfl⟩
  | succ r ih =>
    intro n start c hn hc
    have hn' : n<total := by omega
    have hnz : c.reg 270≠0 := by rw [hc.count];omega
    have ha : AddrOK S forwardKeyStep c := by
      simp only [forwardKeyStep,seqs,AddrOK,run,setReg_reg]
      simp [hc.keyBase,hc.index];omega
    have e := execB_run forwardKeyStep forwardKeyStep_loopFree c ha
    have ht := Nat.le_trans (cost_le_size forwardKeyStep c) forwardKeyStep_size
    obtain ⟨t,c',he,ht',hfinal,hout⟩ := ih (n+1) start (run forwardKeyStep c)
      (by omega) (hc.step hn')
    exact ⟨RAM.cost forwardKeyStep c+t+1,c',.loopNext hnz e he,by omega,hfinal,
      hout.trans (forwardKeyStep_out c)⟩

end STACS2027.Embed.RAMSolver

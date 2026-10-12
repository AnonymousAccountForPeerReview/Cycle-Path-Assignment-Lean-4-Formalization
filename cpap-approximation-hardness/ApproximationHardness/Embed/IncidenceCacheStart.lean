module

public import ApproximationHardness.Embed.IncidenceCachePass
public import ApproximationHardness.RAM.Orient.Clause
import Lean.Elab.Tactic.Omega

/-! # Incidence-cache allocation after the read-only formula scan -/

@[expose] public section

namespace STACS2027.Embed.IncidenceRAM

open RAM Complexity.SAT

attribute [local simp] DFSRAM.dartCount DFSRAM.baseRegister DFSRAM.widthRegister

/-- The cache follows the input and one first-occurrence cell per variable. -/
def cacheLayout (f : CNF) : DFSRAM.Layout :=
  ⟨(ramInput f).length+variableBound f,8*f.flatten.length+2⟩

/-- Compute dense dart count and block width using additions and subtraction. -/
def cachePre : Stmt := seqs [
  .const 0 0,.const 1 1,.const 220 1,.load 221 0,
  .sub 140 8 221,.sub 140 140 1,
  .add 148 140 140,.add 148 148 148,.add 148 148 1,.add 148 148 1,
  .add 147 8 5,.add 205 8 0,.add 209 0 0,
  .add 160 147 0,.add 161 160 148,.add 162 161 148,
  .add 163 162 148,.add 164 163 148,.add 165 164 148,
  .add 166 165 148,.add 167 166 148,.add 168 167 148,
  .add 169 168 148,.add 170 169 148]

theorem cachePre_loopFree : LoopFree cachePre := by simp [cachePre,seqs,LoopFree]
theorem cachePre_size : size cachePre≤25 := by decide

theorem cachePre_mem (c : Config) : (run cachePre c).mem=c.mem := by
  simp [cachePre,seqs,run]

theorem cachePre_out (c : Config) : (run cachePre c).out=c.out := by
  simp [cachePre,seqs,run]

theorem cachePre_addrOK {S : Nat} (c : Config) (hS : 0<S) : AddrOK S cachePre c := by
  simp [cachePre,seqs,AddrOK,run,hS]

theorem cachePre_bases (f : CNF) (c : Config) (hN : c.reg 8=(ramInput f).length)
    (hn : c.reg 5=variableBound f) (hm : c.mem 0=f.length) :
    DFSRAM.Bases (cacheLayout f) (incDG f) (run cachePre c) := by
  have hD : ((ramInput f).length-f.length)-1=2*f.flatten.length := by
    have := ramInput_length_eq f;omega
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · simp [cachePre,seqs,run]
  · simp [cachePre,seqs,run]
  · simp [cachePre,seqs,run,hN,hm,hD,incDG]
  · simp [cachePre,seqs,run,hN,hn,cacheLayout]
  · simp [cachePre,seqs,run,hN,hm,hD,cacheLayout];omega
  · intro j hj
    have casesj : j=0∨j=1∨j=2∨j=3∨j=4∨j=5∨j=6∨j=7∨j=8∨j=9∨j=10 := by omega
    rcases casesj with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp [cachePre,seqs,run,hN,hn,hm,hD,cacheLayout,DFSRAM.Layout.block] <;> omega

/-- Zero unallocated input memory supplies the initial dictionary and cache. -/
theorem cachePre_start (f : CNF) (c : Config)
    (hN : c.reg 8=(ramInput f).length) (hn : c.reg 5=variableBound f)
    (hm : c.mem=(initial (ramInput f)).mem) :
    ClauseState f (cacheLayout f) c (run cachePre c) [] ∧
      (run cachePre c).reg 221=f.length ∧
      CacheAt (run cachePre c) (f.flatMap clauseCode) := by
  have hzero : c.mem 0=f.length := by simp [hm,initial,ramInput]
  have hs := cachePre_bases f c hN hn hzero
  have hD : ((ramInput f).length-f.length)-1=2*f.flatten.length := by
    have := ramInput_length_eq f;omega
  refine ⟨⟨⟨hs,?_,rfl,by dsimp [cacheLayout];omega,by simp,?_,?_,?_,?_,?_⟩,?_,?_⟩,?_,?_⟩
  · simp [cachePre,seqs,run,hN]
  · simp [cachePre,seqs,run]
  · intro v hv
    rw [cachePre_mem,hm]
    change (ramInput f).getD ((ramInput f).length+v) 0 = firstCode [] v
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_none (show (ramInput f).length≤(ramInput f).length+v by omega)]
    simp [firstCode]
  · intro d hd;simp at hd
  · intro d hd;simp at hd
  · intro a _;rw [cachePre_mem]
  · simp [cachePre,seqs,run]
  · exact cachePre_out c
  · simp [cachePre,seqs,run,hzero]
  · intro i hi
    simp [cachePre,seqs,run,hm,initial,ramInput,Nat.add_comm 1 i]

end STACS2027.Embed.IncidenceRAM

module

public import ApproximationHardness.Embed.IncidenceCacheStart
import Lean.Elab.Tactic.Omega

/-! # Initialize the cached forest search without touching its arrays -/

@[expose] public section

namespace STACS2027.Embed.IncidenceRAM

open RAM Complexity.SAT

attribute [local simp] DFSRAM.scan DFSRAM.current DFSRAM.inner DFSRAM.height
  DFSRAM.postLength DFSRAM.remaining

/-- Five zero scalars and the fixed 10E+1 search budget. -/
def dfsPre : Stmt := seqs [
  .const 141 0,.const 142 0,.const 143 0,.const 144 0,.const 145 0,
  .add 146 140 140,.add 146 146 146,.add 146 146 140,.add 146 146 1]

theorem dfsPre_loopFree : LoopFree dfsPre := by simp [dfsPre,seqs,LoopFree]
theorem dfsPre_size : size dfsPre≤10 := by decide

theorem dfsPre_mem (c : Config) : (run dfsPre c).mem=c.mem := by
  simp [dfsPre,seqs,run]

theorem dfsPre_out (c : Config) : (run dfsPre c).out=c.out := by
  simp [dfsPre,seqs,run]

theorem dfsPre_reg (c : Config) (r : Nat)
    (hr : r≠141 ∧ r≠142 ∧ r≠143 ∧ r≠144 ∧ r≠145 ∧ r≠146) :
    (run dfsPre c).reg r=c.reg r := by
  rcases hr with ⟨h₁,h₂,h₃,h₄,h₅,h₆⟩
  simp [dfsPre,seqs,run,h₁,h₂,h₃,h₄,h₅,h₆]

theorem dfsPre_bases {L : DFSRAM.Layout} {G : DG} {c : Config}
    (h : DFSRAM.Bases L G c) : DFSRAM.Bases L G (run dfsPre c) := by
  rcases h with ⟨h₀,h₁,hD,hB,hW,hbase⟩
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · rw [dfsPre_reg _ _ (by decide)];exact h₀
  · rw [dfsPre_reg _ _ (by decide)];exact h₁
  · rw [dfsPre_reg _ _ (by decide)];exact hD
  · rw [dfsPre_reg _ _ (by decide)];exact hB
  · rw [dfsPre_reg _ _ (by decide)];exact hW
  · intro j hj;rw [dfsPre_reg _ _ (by omega)];exact hbase j hj

theorem dfsPre_tables {L : DFSRAM.Layout} {G : DG} {c : Config}
    (h : DFSRAM.Tables L G c) : DFSRAM.Tables L G (run dfsPre c) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro d hd;rw [dfsPre_mem];exact h.representatives d hd
  · intro d hd;rw [dfsPre_mem];exact h.partners d hd
  · intro v hv;rw [dfsPre_mem];exact h.degrees v hv
  · intro k hk v hv;rw [dfsPre_mem];exact h.adjacent k hk v hv

theorem dfsPre_rep {L : DFSRAM.Layout} {G : DG} {c : Config}
    (h : DFSRAM.Bases L G c) (hz : ∀ j,6≤j → j<10 → ∀ v,v<2*G.E → c.mem (L.cell j v)=0) :
    DFSRAM.Rep L G (run dfsPre c) DG.init ∧ (run dfsPre c).reg 146=10*G.E+1 := by
  refine ⟨⟨dfsPre_bases h,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩,?_⟩
  · simp [dfsPre,seqs,run,DG.init]
  · simp [dfsPre,seqs,run,DG.init]
  · simp [dfsPre,seqs,run,DG.init]
  · simp [dfsPre,seqs,run,DG.init]
  · simp [dfsPre,seqs,run,DG.init]
  · intro v hv;rw [dfsPre_mem,hz 6 (by decide) (by decide) v hv];rfl
  · intro v hv;rw [dfsPre_mem,hz 7 (by decide) (by decide) v hv];rfl
  · intro v hv;rw [dfsPre_mem,hz 8 (by decide) (by decide) v hv];rfl
  · intro v hv;rw [dfsPre_mem,hz 9 (by decide) (by decide) v hv];rfl
  · intro i hi;simp [DG.init] at hi
  · simp [dfsPre,seqs,run,h.2.1,h.2.2.1];omega

end STACS2027.Embed.IncidenceRAM

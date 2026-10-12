module

public import ApproximationHardness.Embed.IncidenceCacheStart
import Lean.Elab.Tactic.Omega

/-! # Linear RAM construction of the complete incidence adjacency cache -/

@[expose] public section

namespace STACS2027.Embed.IncidenceRAM

open RAM Complexity.SAT

def adjacencyPre : Stmt := seqs [.const 200 0,.add 201 140 0]
def incidenceCache : Stmt := .seq cachePre (.seq cacheFormula (.seq adjacencyPre DFSRAM.adjacencyLoop))

theorem adjacencyPre_loopFree : LoopFree adjacencyPre := by simp [adjacencyPre,seqs,LoopFree]
theorem adjacencyPre_size : size adjacencyPre≤3 := by decide

theorem adjacencyPre_mem (c : Config) : (run adjacencyPre c).mem=c.mem := by
  simp [adjacencyPre,seqs,run]

theorem adjacencyPre_out (c : Config) : (run adjacencyPre c).out=c.out := by
  simp [adjacencyPre,seqs,run]

theorem adjacencyPre_reg (c : Config) (r : Nat) (hr : r≠200 ∧ r≠201) :
    (run adjacencyPre c).reg r=c.reg r := by
  simp [adjacencyPre,seqs,run,hr.1,hr.2]

theorem zero_input_memory (f : CNF) (a : Nat) (ha : (ramInput f).length≤a) :
    (initial (ramInput f)).mem a=0 := by
  change (ramInput f).getD a 0=0
  rw [List.getD_eq_getElem?_getD,List.getElem?_eq_none ha]
  rfl

theorem adjacencyPre_start (f : CNF) (start c : Config)
    (hI : ClauseState f (cacheLayout f) start c f)
    (hm : start.mem=(initial (ramInput f)).mem) :
    DFSRAM.AdjacencyState (cacheLayout f) (incDG f) c (run adjacencyPre c) 0 := by
  have hc := hI.cache
  have hb : DFSRAM.Bases (cacheLayout f) (incDG f) (run adjacencyPre c) := by
    rcases hc.bases with ⟨h₀,h₁,hD,hB,hW,hbase⟩
    refine ⟨?_,?_,?_,?_,?_,?_⟩
    · rw [adjacencyPre_reg _ _ (by decide)];exact h₀
    · rw [adjacencyPre_reg _ _ (by decide)];exact h₁
    · rw [adjacencyPre_reg _ _ (by decide)];exact hD
    · rw [adjacencyPre_reg _ _ (by decide)];exact hB
    · rw [adjacencyPre_reg _ _ (by decide)];exact hW
    · intro j hj;rw [adjacencyPre_reg _ _ (by omega)];exact hbase j hj
  have hzero j i (hj : 2≤j) : c.mem ((cacheLayout f).cell j i)=0 := by
    rw [hc.preserved _ (Or.inr (by
      dsimp [DFSRAM.Layout.cell,DFSRAM.Layout.block]
      have := Nat.mul_le_mul_right (cacheLayout f).width hj;omega)),hm]
    apply zero_input_memory
    dsimp [cacheLayout,DFSRAM.Layout.cell,DFSRAM.Layout.block];omega
  refine ⟨hb,hc.width,by omega,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [adjacencyPre,seqs,run]
  · simp [adjacencyPre,seqs,run,hc.bases.1,hc.bases.2.2.1]
  · intro d hd;rw [adjacencyPre_mem];exact hc.representatives d hd
  · intro d hd;rw [adjacencyPre_mem];exact hc.partners d hd
  · intro v _;rw [adjacencyPre_mem,hzero 2 v (by decide)];rfl
  · intro k hk v _;rw [adjacencyPre_mem,hzero (3+k) v (by omega)];rfl
  · intro a _;rw [adjacencyPre_mem]

/-- From a read-only first scan, the actual parser and adjacency loop install all
cache tables, preserving input and the untouched DFS arrays. -/
theorem incidenceCache_spec {S : Nat} (f : CNF) (c : Config) (hG : (incDG f).Ok)
    (hS : (cacheLayout f).limit≤S)
    (hN : c.reg 8=(ramInput f).length) (hn : c.reg 5=variableBound f)
    (hm : c.mem=(initial (ramInput f)).mem) :
    ∃ t c',ExecB S incidenceCache c t c' ∧
      t≤93*f.flatten.length+9*f.length+31 ∧
      DFSRAM.Bases (cacheLayout f) (incDG f) c' ∧
      DFSRAM.Tables (cacheLayout f) (incDG f) c' ∧ c'.out=c.out ∧
      (∀ a,(cacheLayout f).block 6≤a → c'.mem a=(initial (ramInput f)).mem a) ∧
      (∀ a,a<(ramInput f).length → c'.mem a=c.mem a) := by
  obtain ⟨hi,hcnt,ha⟩ := cachePre_start f c hN hn hm
  have hpos : 0<S := by
    have : 0<(cacheLayout f).limit := by
      have hinput : 0<(ramInput f).length := by simp [ramInput]
      dsimp [cacheLayout,DFSRAM.Layout.limit];omega
    omega
  have e₁ := execB_run cachePre cachePre_loopFree c (cachePre_addrOK c hpos)
  have ht₁ := Nat.le_trans (cost_le_size cachePre c) cachePre_size
  obtain ⟨t₂,c₂,e₂,ht₂,h₂⟩ := cacheFormula_spec f (cacheLayout f) c (run cachePre c)
    hS hi hcnt ha
  have ha₃ := adjacencyPre_start f c c₂ h₂ hm
  have e₃ := execB_run (S:=S) adjacencyPre adjacencyPre_loopFree c₂
    (AddrOK.of_memFree (by simp [adjacencyPre,seqs,memFree]))
  have ht₃ := Nat.le_trans (cost_le_size adjacencyPre c₂) adjacencyPre_size
  obtain ⟨t₄,c₄,e₄,ht₄,h₄,hout₄⟩ := DFSRAM.adjacencyLoop_spec hG hS
    (2*(incDG f).E) 0 c₂ (run adjacencyPre c₂) (by omega) ha₃
  refine ⟨RAM.cost cachePre c+(t₂+(RAM.cost adjacencyPre c₂+t₄)),c₄,
    .seq e₁ (.seq e₂ (.seq e₃ e₄)),?_,h₄.bases,h₄.tables,?_,?_,?_⟩
  · dsimp [incDG] at ht₄;omega
  · exact hout₄.trans ((adjacencyPre_out c₂).trans h₂.output)
  · intro a ha
    rw [h₄.preserved a (Or.inr ha),h₂.cache.preserved a (Or.inr (by
      dsimp [DFSRAM.Layout.block] at ha ⊢;omega)),hm]
  · intro a ha
    rw [h₄.preserved a (Or.inl (by
      dsimp [cacheLayout,DFSRAM.Layout.block];omega)),h₂.cache.preserved a (Or.inl ha)]

end STACS2027.Embed.IncidenceRAM

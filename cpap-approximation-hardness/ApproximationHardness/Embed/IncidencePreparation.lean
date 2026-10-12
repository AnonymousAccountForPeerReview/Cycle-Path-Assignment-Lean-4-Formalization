module

public import ApproximationHardness.Embed.IncidenceCache
public import ApproximationHardness.Embed.DFSStartRAM
public import ApproximationHardness.RAM.Decode.Scan
import Lean.Elab.Tactic.Omega

/-! # Uniform RAM preprocessing from the formula input to a ready forest search -/

@[expose] public section

namespace STACS2027.Embed.IncidenceRAM

open RAM Complexity.SAT

def prepareDFS : Stmt := .seq passAq (.seq incidenceCache dfsPre)

/-- Full preprocessing starts at the machine's actual initial input state. -/
theorem prepareDFS_spec {S : Nat} (f : CNF) (hf : BoundedOccurrence f)
    (hS : (cacheLayout f).limit≤S) :
    ∃ t c,ExecB S prepareDFS (initial (ramInput f)) t c ∧
      t≤passACost f+93*f.flatten.length+9*f.length+41 ∧
      DFSRAM.Bases (cacheLayout f) (incDG f) c ∧
      DFSRAM.Tables (cacheLayout f) (incDG f) c ∧
      DFSRAM.Rep (cacheLayout f) (incDG f) c DG.init ∧
      c.reg 146=10*f.flatten.length+1 ∧ c.out=[] ∧
      (∀ a,(cacheLayout f).limit≤a → c.mem a=0) ∧
      (∀ a,a<(ramInput f).length → c.mem a=(ramInput f).getD a 0) := by
  have hInput : (ramInput f).length≤S := by
    have : (ramInput f).length≤(cacheLayout f).limit := by
      dsimp [cacheLayout,DFSRAM.Layout.limit];omega
    omega
  have hThree : ∀ cl∈f,cl.length≤3 := by
    intro cl hcl;rcases hf.1 cl hcl with h|h <;> omega
  have hHolds : HoldsInput f (initial (ramInput f)) := by intro i _;rfl
  have hzero : (initial (ramInput f)).reg Reg.zero=0 := rfl
  have hnzero : (initial (ramInput f)).reg Reg.n=0 := rfl
  obtain ⟨tA,eA,htA⟩ := sat_passAq f hThree hInput (initial (ramInput f))
    ⟨hHolds,rfl,hzero,hnzero⟩
  have ha := passAqModel_spec f (initial (ramInput f)) hHolds rfl hzero hnzero
  let cA := passAqModel (initial (ramInput f))
  obtain ⟨tB,cB,eB,htB,hbases,htables,hout,hfree,hinput⟩ :=
    incidenceCache_spec f cA (incOk hf) hS ha.2.2.2.2.2.1 ha.2.2.2.2.1 ha.1
  have hz j (hj : 6≤j) (_hj' : j<10) v (_hv : v<2*(incDG f).E) :
      cB.mem ((cacheLayout f).cell j v)=0 := by
    rw [hfree _ (by
      dsimp [DFSRAM.Layout.cell,DFSRAM.Layout.block]
      have := Nat.mul_le_mul_right (cacheLayout f).width hj;omega)]
    apply zero_input_memory
    dsimp [cacheLayout,DFSRAM.Layout.cell,DFSRAM.Layout.block];omega
  have hinit := dfsPre_rep hbases hz
  have eC := execB_run (S:=S) dfsPre dfsPre_loopFree cB
    (AddrOK.of_memFree (by simp [dfsPre,seqs,memFree]))
  have htC := Nat.le_trans (cost_le_size dfsPre cB) dfsPre_size
  refine ⟨tA+(tB+RAM.cost dfsPre cB),run dfsPre cB,.seq eA (.seq eB eC),
    by omega,dfsPre_bases hbases,dfsPre_tables htables,hinit.1,?_,?_,?_,?_⟩
  · simpa only [incDG] using hinit.2
  · rw [dfsPre_out,hout];exact ha.2.1
  · intro a haLimit
    rw [dfsPre_mem,hfree _ (by
      dsimp [DFSRAM.Layout.limit,DFSRAM.Layout.block] at haLimit ⊢;omega)]
    apply zero_input_memory
    dsimp [cacheLayout,DFSRAM.Layout.limit] at haLimit;omega
  · intro a haInput
    rw [dfsPre_mem,hinput a haInput,ha.1]
    rfl

/-- The preprocessing allocation and operation count are both linear. -/
theorem prepareDFS_linear (f : CNF) :
    (cacheLayout f).limit≤128*((ramInput f).length+variableBound f+1) ∧
    passACost f+93*f.flatten.length+9*f.length+41≤
      256*((ramInput f).length+variableBound f+1) := by
  have hlen := ramInput_length_eq f
  have hpre : size passApre≤10 := by decide
  have hpost : size passApost≤10 := by decide
  have hcl : clauseACost+1≤100 := by decide
  have hmul := Nat.mul_le_mul_left f.length hcl
  unfold passACost
  dsimp [cacheLayout,DFSRAM.Layout.limit]
  omega

end STACS2027.Embed.IncidenceRAM

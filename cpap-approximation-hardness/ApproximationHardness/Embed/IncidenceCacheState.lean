module

public import ApproximationHardness.Embed.IncidenceCacheRAM
public import ApproximationHardness.Embed.IncPrefix
import Lean.Elab.Tactic.Omega

/-! # Prefix invariant of the incidence-cache pass -/

@[expose] public section

namespace STACS2027.Embed.IncidenceRAM

open RAM Complexity.SAT DFSRAM

structure CacheState (f : CNF) (L : DFSRAM.Layout) (start c : Config) (past : List Literal) : Prop where
  bases : DFSRAM.Bases L (incDG f) c
  dictionaryBase : c.reg 205 = (ramInput f).length
  tableBase : (ramInput f).length+variableBound f = L.base
  width : 2*f.flatten.length ≤ L.width
  bound : past.length ≤ f.flatten.length
  even : c.reg 209 = 2*past.length
  dictionary : ∀ v, v < variableBound f →
    c.mem ((ramInput f).length+v) = firstCode past v
  representatives : ∀ d, d < 2*past.length → c.mem (L.cell 0 d) = incRep f d
  partners : ∀ d, d < 2*past.length → c.mem (L.cell 1 d) = STACS2027.Embed.pair d
  preserved : ∀ a, a < (ramInput f).length ∨ L.block 2 ≤ a → c.mem a = start.mem a

theorem CacheState.literal_bases {f : CNF} {L : DFSRAM.Layout} {start c : Config}
    {past : List Literal} (h : CacheState f L start c past) :
    DFSRAM.Bases L (incDG f) (run cacheLiteral c) := by
  have hf (r : Nat) (hr : r < 200) : (run cacheLiteral c).reg r = c.reg r := by
    apply cacheLiteral_reg;omega
  rcases h.bases with ⟨h₀,h₁,hD,hB,hW,hbase⟩
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · rw [hf 0 (by decide)];exact h₀
  · rw [hf 1 (by decide)];exact h₁
  · rw [hf 140 (by decide)];exact hD
  · rw [hf 147 (by decide)];exact hB
  · rw [hf 148 (by decide)];exact hW
  · intro j hj;rw [hf (160+j) (by omega)];exact hbase j hj

theorem CacheState.literal_mem {f : CNF} {L : DFSRAM.Layout} {start c : Config}
    {past : List Literal} (h : CacheState f L start c past) (l : Literal)
    (hl : l.var < variableBound f) (hv : c.mem (c.reg 220) = l.var) (a : Nat) :
    (run cacheLiteral c).mem a =
      if a = L.cell 1 (2*past.length+1) then 2*past.length else
      if a = L.cell 1 (2*past.length) then 2*past.length+1 else
      if a = L.cell 0 (2*past.length+1) then c.reg 210 else
      if a = L.cell 0 (2*past.length) then firstCode (past++[l]) l.var-1 else
      if a = (ramInput f).length+l.var ∧ firstCode past l.var = 0
        then 2*past.length+1 else c.mem a := by
  have hb := h.bases.2.2.2.2.2
  rw [cacheLiteral_mem c h.bases.2.1 a,hb 0 (by decide),hb 1 (by decide),
    h.even,h.dictionaryBase,hv,h.dictionary _ hl,firstCode_snoc]
  change (if a=L.cell 1 (2*past.length+1) then 2*past.length else
    if a=L.cell 1 (2*past.length) then 2*past.length+1 else
    if a=L.cell 0 (2*past.length+1) then c.reg 210 else
    if a=L.cell 0 (2*past.length) then
      (if firstCode past l.var=0 then 2*past.length else firstCode past l.var-1) else
    if a=(ramInput f).length+l.var ∧ firstCode past l.var=0 then 2*past.length+1 else c.mem a)=_
  by_cases hz : firstCode past l.var=0 <;> simp [hz]

/-- A literal extends all representative and partner arrays by its two darts. -/
theorem CacheState.literal {f : CNF} {L : DFSRAM.Layout} {start c : Config}
    {past : List Literal} (h : CacheState f L start c past) (l : Literal)
    (hl : l.var < variableBound f) (hv : c.mem (c.reg 220) = l.var)
    (hp : past.length < f.flatten.length)
    (he : firstCode (past++[l]) l.var-1 = incRep f (2*past.length))
    (ho : c.reg 210 = incRep f (2*past.length+1)) :
    CacheState f L start (run cacheLiteral c) (past++[l]) := by
  have hpl : 2*past.length+1 < L.width := by have := h.width;omega
  have hdict : (ramInput f).length+l.var < L.base := by have := h.tableBase;omega
  have hcell (j i : Nat) : L.base ≤ L.cell j i := by
    dsimp [DFSRAM.Layout.cell,DFSRAM.Layout.block];omega
  have hblock : L.block 1+L.width ≤ L.block 2 := by
    dsimp [DFSRAM.Layout.block];omega
  refine ⟨h.literal_bases,?_,h.tableBase,h.width,by simp only [List.length_append,List.length_singleton];omega,?_,?_,?_,?_,?_⟩
  · rw [cacheLiteral_reg _ _ (by decide)];exact h.dictionaryBase
  · rw [(cacheLiteral_advance c h.bases.2.1).1,h.even];simp;omega
  · intro v hvn
    rw [h.literal_mem l hl hv]
    have hdv : (ramInput f).length+v < L.base := by have := h.tableBase;omega
    have hn j i : (ramInput f).length+v ≠ L.cell j i := by have := hcell j i;omega
    simp only [hn,ite_false,h.dictionary v hvn,firstCode_snoc]
    by_cases heq : v=l.var
    · subst v;simp
    · have heq' : l.var≠v := Ne.symm heq
      simp [heq,heq']
  · intro d hd
    rw [h.literal_mem l hl hv]
    have hdw : d < L.width := by simp only [List.length_append,List.length_singleton] at hd;omega
    simp only [DFSRAM.adjacency_cell_eq_iff L (j:=0) (k:=1) (i:=d) (a:=2*past.length+1) hdw hpl,
      DFSRAM.adjacency_cell_eq_iff L (j:=0) (k:=1) (i:=d) (a:=2*past.length) hdw (by omega),
      DFSRAM.adjacency_cell_eq_iff L (j:=0) (k:=0) (i:=d) (a:=2*past.length+1) hdw hpl,
      DFSRAM.adjacency_cell_eq_iff L (j:=0) (k:=0) (i:=d) (a:=2*past.length) hdw (by omega)]
    have hnd : L.cell 0 d ≠ (ramInput f).length+l.var := by have := hcell 0 d;omega
    simp only [Nat.zero_ne_one,false_and,ite_false,true_and,hnd]
    by_cases hdodd : d=2*past.length+1
    · subst d;simp [ho]
    · by_cases hdeven : d=2*past.length
      · subst d;simp [he]
      · simp only [hdodd,hdeven,ite_false]
        exact h.representatives d (by simp only [List.length_append,List.length_singleton] at hd;omega)
  · intro d hd
    rw [h.literal_mem l hl hv]
    have hdw : d < L.width := by simp only [List.length_append,List.length_singleton] at hd;omega
    simp only [DFSRAM.adjacency_cell_eq_iff L (j:=1) (k:=1) (i:=d) (a:=2*past.length+1) hdw hpl,
      DFSRAM.adjacency_cell_eq_iff L (j:=1) (k:=1) (i:=d) (a:=2*past.length) hdw (by omega),
      DFSRAM.adjacency_cell_eq_iff L (j:=1) (k:=0) (i:=d) (a:=2*past.length+1) hdw hpl,
      DFSRAM.adjacency_cell_eq_iff L (j:=1) (k:=0) (i:=d) (a:=2*past.length) hdw (by omega)]
    have hnd : L.cell 1 d ≠ (ramInput f).length+l.var := by have := hcell 1 d;omega
    simp only [true_and,reduceCtorEq,false_and,ite_false,hnd]
    by_cases hdodd : d=2*past.length+1
    · subst d;simp [STACS2027.Embed.pair]
    · by_cases hdeven : d=2*past.length
      · subst d;simp [STACS2027.Embed.pair]
      · simp only [hdodd,hdeven,ite_false]
        exact h.partners d (by simp only [List.length_append,List.length_singleton] at hd;omega)
  · intro a ha
    rw [h.literal_mem l hl hv]
    have hne (j i : Nat) (hj : j<2) (hi : i<L.width) : a≠L.cell j i := by
      dsimp [DFSRAM.Layout.cell,DFSRAM.Layout.block] at ha ⊢
      have hlower : L.base ≤ L.base+j*L.width+i := by omega
      have hupper : L.base+j*L.width+i < L.base+2*L.width := by
        have := Nat.mul_le_mul_right L.width (show j+1≤2 by omega)
        rw [Nat.add_mul] at this;omega
      have := h.tableBase;omega
    have hnDict : a≠(ramInput f).length+l.var := by
      have := h.tableBase
      dsimp [DFSRAM.Layout.block] at ha
      omega
    simp only [hne 1 (2*past.length+1) (by decide) hpl,
      hne 1 (2*past.length) (by decide) (by omega),
      hne 0 (2*past.length+1) (by decide) hpl,
      hne 0 (2*past.length) (by decide) (by omega),hnDict,false_and,ite_false]
    exact h.preserved a ha


theorem CacheState.literal_addrOK {S : Nat} {f : CNF} {L : DFSRAM.Layout}
    {start c : Config} {past : List Literal} (h : CacheState f L start c past)
    (l : Literal) (hl : l.var < variableBound f) (hv : c.mem (c.reg 220) = l.var)
    (hp : past.length < f.flatten.length) (hcursor : c.reg 220 < (ramInput f).length)
    (hS : L.limit ≤ S) : AddrOK S cacheLiteral c := by
  have hb := h.bases.2.2.2.2.2
  have hpl : 2*past.length+1 < L.width := by have := h.width;omega
  apply cacheLiteral_addrOK c h.bases.2.1
  · have hbase : L.base ≤ L.limit := by dsimp [DFSRAM.Layout.limit];omega
    have := h.tableBase;omega
  · rw [h.dictionaryBase,hv]
    have hbase : L.base ≤ L.limit := by dsimp [DFSRAM.Layout.limit];omega
    have := h.tableBase;omega
  · rw [hb 0 (by decide),h.even]
    exact Nat.lt_of_lt_of_le (DFSRAM.Layout.cell_lt (by decide) hpl) hS
  · rw [hb 1 (by decide),h.even]
    exact Nat.lt_of_lt_of_le (DFSRAM.Layout.cell_lt (by decide) hpl) hS

theorem cache_listPass {S : Nat} {α : Type} (code : α → List Nat) (xs : List α)
    {cnt : Nat} {body : Stmt} (I : List α → Config → Prop) (b : α → Nat)
    (hstep : ∀ pre x suf c, pre++x::suf=xs → I pre c → c.reg cnt=suf.length+1 →
      CacheAt c (code x++suf.flatMap code) →
      ∃ t c', ExecB S body c t c' ∧ t≤b x ∧ I (pre++[x]) c' ∧
        c'.reg cnt=suf.length ∧ CacheAt c' (suf.flatMap code)) :
    ∀ c, I [] c → c.reg cnt=xs.length → CacheAt c (xs.flatMap code) →
      ∃ t c', ExecB S (.loop cnt body) c t c' ∧
        t≤(xs.map (fun x=>b x+1)).sum+1 ∧ I xs c' := by
  have key : ∀ suf pre c, pre++suf=xs → I pre c → c.reg cnt=suf.length →
      CacheAt c (suf.flatMap code) →
      ∃ t c', ExecB S (.loop cnt body) c t c' ∧
        t≤(suf.map (fun x=>b x+1)).sum+1 ∧ I xs c' := by
    intro suf
    induction suf with
    | nil =>
      intro pre c hp hi hc _
      simp only [List.append_nil] at hp
      subst hp
      exact ⟨1,c,.loopDone (by simpa using hc),by simp,hi⟩
    | cons x suf ih =>
      intro pre c hp hi hc ha
      simp only [List.flatMap_cons] at ha
      obtain ⟨t,c',he,ht,hi',hc',ha'⟩ := hstep pre x suf c hp hi (by simpa using hc) ha
      obtain ⟨t',c'',he',ht',hi''⟩ := ih (pre++[x]) c' (by simp [←hp]) hi' hc' ha'
      refine ⟨t+t'+1,c'',.loopNext (by simp at hc;omega) he he',?_,hi''⟩
      simp only [List.map_cons,List.sum_cons];omega
  intro c hi hc ha
  exact key xs [] c rfl hi hc ha

end STACS2027.Embed.IncidenceRAM

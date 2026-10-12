module

public import ApproximationHardness.Embed.IncidenceCacheState
public import ApproximationHardness.RAM.Orient.Lit
import Lean.Elab.Tactic.Omega

/-! # Actual linear clause and literal passes for the incidence cache -/

@[expose] public section

namespace STACS2027.Embed.IncidenceRAM

open RAM Complexity.SAT

structure ClauseState (f : CNF) (L : DFSRAM.Layout) (start c : Config) (pre : CNF) : Prop where
  cache : CacheState f L start c pre.flatten
  cursor : c.reg 220 = 1+(pre.flatMap clauseCode).length
  output : c.out = start.out

theorem CacheState.clausePre {f : CNF} {L : DFSRAM.Layout} {start c : Config}
    {past : List Literal} (h : CacheState f L start c past) :
    CacheState f L start (run cacheClausePre c) past := by
  have hf (r : Nat) (hr : r<200) : (run cacheClausePre c).reg r=c.reg r := by
    apply cacheClausePre_reg;omega
  have hb : DFSRAM.Bases L (incDG f) (run cacheClausePre c) := by
    rcases h.bases with ⟨h₀,h₁,hD,hB,hW,hbase⟩
    refine ⟨?_,?_,?_,?_,?_,?_⟩
    · rw [hf 0 (by decide)];exact h₀
    · rw [hf 1 (by decide)];exact h₁
    · rw [hf 140 (by decide)];exact hD
    · rw [hf 147 (by decide)];exact hB
    · rw [hf 148 (by decide)];exact hW
    · intro j hj;rw [hf (160+j) (by omega)];exact hbase j hj
  refine ⟨hb,?_,h.tableBase,h.width,h.bound,?_,?_,?_,?_,?_⟩
  · rw [cacheClausePre_reg _ _ (by decide)];exact h.dictionaryBase
  · rw [cacheClausePre_reg _ _ (by decide)];exact h.even
  · simpa only [cacheClausePre_mem] using h.dictionary
  · simpa only [cacheClausePre_mem] using h.representatives
  · simpa only [cacheClausePre_mem] using h.partners
  · simpa only [cacheClausePre_mem] using h.preserved

theorem cacheClause_step {S : Nat} {f pre suf : CNF} {cl : Clause}
    {L : DFSRAM.Layout} {start c : Config} (hxs : pre++cl::suf=f)
    (hI : ClauseState f L start c pre) (hcount : c.reg 221=suf.length+1)
    (hAt : CacheAt c (clauseCode cl++suf.flatMap clauseCode)) (hS : L.limit≤S) :
    ∃ t c', ExecB S cacheClause c t c' ∧ t≤31*cl.length+8 ∧
      ClauseState f L start c' (pre++[cl]) ∧ c'.reg 221=suf.length ∧
      CacheAt c' (suf.flatMap clauseCode) := by
  have hc := hI.cache
  have hlen : (ramInput f).length = 1+(pre.flatMap clauseCode).length+
      (1+2*cl.length)+(suf.flatMap clauseCode).length := by
    rw [←hxs]
    simp only [ramInput,List.length_cons,List.flatMap_append,List.flatMap_cons,
      List.length_append,clauseCode_length]
    omega
  have hN : (ramInput f).length≤S := by
    have hbase : L.base≤L.limit := by dsimp [DFSRAM.Layout.limit];omega
    have := hc.tableBase;omega
  have hpreAddr : AddrOK S cacheClausePre c :=
    cacheClausePre_addrOK c (by rw [hI.cursor];omega)
  have e₁ := execB_run cacheClausePre cacheClausePre_loopFree c hpreAddr
  have t₁ := Nat.le_trans (cost_le_size cacheClausePre c) cacheClausePre_size
  let c₁ := run cacheClausePre c
  have r₁ := cacheClausePre_read c hc.bases.2.1
  have cnt₁ : c₁.reg 208=cl.length := by
    rw [r₁.1]
    exact hAt.head
  have at₁ : CacheAt c₁ (cl.flatMap litCode++suf.flatMap clauseCode) := by
    apply CacheAt.drop (w:=[cl.length]) (by simpa only [clauseCode,List.cons_append,List.nil_append] using hAt)
      r₁.2.1
    intro i hi;rw [cacheClausePre_mem]
  let I : List Literal → Config → Prop := fun lpre d =>
    CacheState f L start d (pre.flatten++lpre) ∧
    d.reg 210=2*pre.flatten.length+1 ∧
    d.reg 220=c₁.reg 220+2*lpre.length ∧ d.reg 221=suf.length ∧ d.out=start.out
  have hstep : ∀ lpre l lsuf d, lpre++l::lsuf=cl → I lpre d →
      d.reg 208=lsuf.length+1 → CacheAt d (litCode l++lsuf.flatMap litCode) →
      ∃ t d',ExecB S cacheLiteral d t d' ∧ t≤30 ∧ I (lpre++[l]) d' ∧
        d'.reg 208=lsuf.length ∧ CacheAt d' (lsuf.flatMap litCode) := by
    intro lpre l lsuf d hcl ⟨hd,ho,dp,dm,dout⟩ dcnt da
    have hf := RAM.flatten_prefix hxs lpre hcl
    have hl : l.var<variableBound f := RAM.literal_var_lt (by rw [←hf];simp)
    have hv : d.mem (d.reg 220)=l.var := da.head
    have hpl : (pre.flatten++lpre).length<f.flatten.length := by rw [←hf];simp
    have he : firstCode ((pre.flatten++lpre)++[l]) l.var-1 =
        incRep f (2*(pre.flatten++lpre).length) := by
      simpa only [List.length_append] using incRep_even_prefix hxs hcl
    have ho' : d.reg 210=incRep f (2*(pre.flatten++lpre).length+1) := by
      rw [List.length_append,incRep_odd_prefix hxs hcl,ho]
    have hs := hd.literal l hl hv hpl he ho'
    have hcllen : cl.length=lpre.length+1+lsuf.length := by rw [←hcl];simp;omega
    have hcursor : d.reg 220<(ramInput f).length := by
      rw [dp,r₁.2.1,hI.cursor];omega
    have haddr := hd.literal_addrOK l hl hv hpl hcursor hS
    have ex := execB_run cacheLiteral cacheLiteral_loopFree d haddr
    have ht := Nat.le_trans (cost_le_size cacheLiteral d) cacheLiteral_size
    have adv := cacheLiteral_advance d hd.bases.2.1
    refine ⟨_,run cacheLiteral d,ex,ht,⟨?_,?_,?_,?_,?_⟩,?_,?_⟩
    · simpa only [List.append_assoc] using hs
    · rw [cacheLiteral_reg _ _ (by decide),ho]
    · rw [adv.2.1,dp];simp only [List.length_append,List.length_singleton];omega
    · rw [cacheLiteral_reg _ _ (by decide),dm]
    · rw [cacheLiteral_out,dout]
    · rw [adv.2.2,dcnt];omega
    · apply CacheAt.drop da (by simpa [litCode] using adv.2.1)
      intro i hi
      have hlslen := litCodes_length lsuf
      have hinput : d.reg 220+(litCode l).length+i<(ramInput f).length := by
        rw [dp,r₁.2.1,hI.cursor];simp only [litCode,List.length_cons,List.length_nil] at *;omega
      exact (hs.preserved _ (Or.inl hinput)).trans (hd.preserved _ (Or.inl hinput)).symm
  have init : I [] c₁ := by
    refine ⟨?_,?_,by simp,?_,?_⟩
    · simpa only [List.append_nil] using hc.clausePre
    · rw [r₁.2.2.1,hc.even]
    · rw [r₁.2.2.2,hcount];omega
    · rw [cacheClausePre_out,hI.output]
  have atlit : CacheAt c₁ (cl.flatMap litCode) := by
    intro i hi
    have he := at₁ i (by simp only [List.length_append];omega)
    rw [he,List.getD_eq_getElem?_getD,List.getElem?_append_left hi]
    rfl
  obtain ⟨t₂,c₂,e₂,ht₂,h₂⟩ := cache_listPass litCode cl (cnt:=208) (body:=cacheLiteral)
    I (fun _=>30) hstep c₁ init cnt₁ atlit
  obtain ⟨hc₂,ho₂,hp₂,hm₂,hout₂⟩ := h₂
  have hsum : ∀ xs : List Literal,(xs.map (fun _=>31)).sum=31*xs.length := by
    intro xs
    induction xs with
    | nil => rfl
    | cons a xs ih => simp only [List.map_cons,List.sum_cons,List.length_cons];omega
  have htime₂ : t₂≤31*cl.length+1 := by simpa only [hsum cl] using ht₂
  refine ⟨RAM.cost cacheClausePre c+t₂,c₂,.seq e₁ e₂,by omega,⟨?_,?_,hout₂⟩,hm₂,?_⟩
  · simpa only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil] using hc₂
  · rw [hp₂,r₁.2.1,hI.cursor]
    simp only [List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,
      List.length_append,clauseCode_length]
    omega
  · apply CacheAt.drop hAt (by rw [hp₂,r₁.2.1];rw [clauseCode_length];omega)
    intro i hi
    have hinput : c.reg 220+(clauseCode cl).length+i<(ramInput f).length := by
      rw [hI.cursor,clauseCode_length];omega
    exact (hc₂.preserved _ (Or.inl hinput)).trans (hc.preserved _ (Or.inl hinput)).symm


/-- The full input pass installs exact representative and partner arrays. -/
theorem cacheFormula_spec {S : Nat} (f : CNF) (L : DFSRAM.Layout) (start c : Config)
    (hS : L.limit≤S) (hI : ClauseState f L start c []) (hm : c.reg 221=f.length)
    (hAt : CacheAt c (f.flatMap clauseCode)) :
    ∃ t c',ExecB S cacheFormula c t c' ∧ t≤31*f.flatten.length+9*f.length+1 ∧
      ClauseState f L start c' f := by
  obtain ⟨t,c',he,ht,hi⟩ := cache_listPass clauseCode f (cnt:=221) (body:=cacheClause)
    (fun pre d=>ClauseState f L start d pre) (fun cl=>31*cl.length+8)
    (fun pre cl suf d hf hd hm ha => cacheClause_step hf hd hm ha hS) c hI hm hAt
  have hsum : ∀ xs : CNF,(xs.map (fun cl=>31*cl.length+8+1)).sum =
      31*xs.flatten.length+9*xs.length := by
    intro xs
    induction xs with
    | nil => rfl
    | cons cl xs ih =>
      simp only [List.map_cons,List.sum_cons,List.flatten_cons,List.length_append,List.length_cons]
      omega
  exact ⟨t,c',he,by rw [hsum f] at ht;exact ht,hi⟩

end STACS2027.Embed.IncidenceRAM

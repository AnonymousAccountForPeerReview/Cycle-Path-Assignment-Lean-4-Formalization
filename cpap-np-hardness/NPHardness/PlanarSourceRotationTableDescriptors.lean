module

public import NPHardness.PlanarSourceRotationTablePacked
public import NPHardness.PlanarSourcePackedBlocks

/-! Arithmetic template descriptors agree with the registered occurrence
numbering and angular key. These lemmas connect packed source offsets to
`EntryCorrect`, retaining actual clause and literal order. -/

@[expose] public section
namespace STACS2027.PlanarSource.RotationTable
open Complexity Complexity.SAT Complexity.Planar Comb
open Complexity.StackTableauEmitter
open STACS2027.PlanarSource.Packed

theorem orientExpr_eval {n : Nat} (K v : NumExpr n) (top : Bool) (env : Env n) :
    (orientExpr K v top).eval env = if top then v.eval env else K.eval env - 1 - v.eval env := by
  cases top <;> rfl

theorem template_clause_length {n : Nat} {f : CNF} (t : Template n)
    (w : SAT.Word) (env : Env n) {j : Nat} (hj : j < f.length)
    (hc : f[j] = t.eval w env) : kl f j = t.literals.length := by
  rw [kl_of_lt f j hj,hc]
  simp only [Template.eval,List.length_map]

theorem template_variable {n : Nat} {f : CNF} (t : Template n)
    (w : SAT.Word) (env : Env n) {j : Nat} (hj : j < f.length)
    (hc : f[j] = t.eval w env) (s : Nat) (hs : s < t.literals.length) :
    vr f j s = (t.literals[s]).1.eval env := by
  rw [vr_of_lt f j s hj (by rw [template_clause_length t w env hj hc]; exact hs)]
  simp only [hc,Template.eval,List.getElem_map]

theorem template_lo {n : Nat} {f : CNF} (t : Template n)
    (w : SAT.Word) (env : Env n) {j : Nat} (hj : j < f.length)
    (hc : f[j] = t.eval w env) (ht : t.top = isTop f j) (hlen : 0 < t.literals.length)
    (K : NumExpr n) (hK : K.eval env = nK f) :
    (orientExpr K (t.literals.headD (.const 0,.const false)).1 t.top).eval env = lo f j := by
  rw [List.headD_eq_head?_getD,List.head?_eq_getElem?,List.getElem?_eq_getElem hlen]
  simp only [Option.getD_some,orientExpr_eval,hK,ht]
  unfold lo ov opos
  rw [template_variable t w env hj hc 0 hlen]

theorem template_hi {n : Nat} {f : CNF} (t : Template n)
    (w : SAT.Word) (env : Env n) {j : Nat} (hj : j < f.length)
    (hc : f[j] = t.eval w env) (ht : t.top = isTop f j) (hlen : 0 < t.literals.length)
    (K : NumExpr n) (hK : K.eval env = nK f) :
    (orientExpr K (t.literals.getLastD (.const 0,.const false)).1 t.top).eval env = hi f j := by
  rw [List.getLastD_eq_getLast?,List.getLast?_eq_getElem?,
    List.getElem?_eq_getElem (by omega)]
  simp only [Option.getD_some,orientExpr_eval,hK,ht]
  unfold hi ov opos
  rw [template_clause_length t w env hj hc,
    template_variable t w env hj hc _ (by omega)]

theorem keyExpr_correct {n : Nat} {f : CNF} (t : Template n)
    (w : SAT.Word) (env : Env n) (N K cb : NumExpr n) {j : Nat}
    (hN : N.eval env = f.length) (hK : K.eval env = nK f) (hcb : cb.eval env = j)
    (hj : j < f.length) (hc : f[j] = t.eval w env) (ht : t.top = isTop f j)
    (s : Nat) (hs : s < t.literals.length) :
    (keyExpr N K cb t s).eval env = key f (off f j+s) := by
  have hlen : 0 < t.literals.length := by omega
  have hk := template_clause_length t w env hj hc
  have ho := occ_eq f j s hj (by rw [hk]; exact hs)
  unfold keyExpr key
  rw [ho.1,ho.2,hk]
  by_cases hs0 : s = 0
  · simp only [hs0,ite_true,NumExpr.eval,addN,mulN,hN,hcb]
    rw [template_hi t w env hj hc ht hlen K hK]
  · by_cases hlast : s+1 = t.literals.length
    · simp only [hs0,hlast,ite_false,ite_true,NumExpr.eval,addN,mulN,hN,hK,hcb]
      rw [template_lo t w env hj hc ht hlen K hK]
    · simp only [hs0,hlast,ite_false,NumExpr.eval,addN,mulN,hN,hK]

/-- Every occurrence descriptor of a correctly addressed source clause has
exactly the registered numeric index, variable, page and angular key. -/
theorem templateOccurrences_correct {n : Nat} {f : CNF}
    (live : Test n) (N K cb lb : NumExpr n) (t : Template n)
    (w : SAT.Word) (env : Env n) {j : Nat}
    (hN : N.eval env = f.length) (hK : K.eval env = nK f)
    (hcb : cb.eval env = j) (hlb : lb.eval env = off f j)
    (hj : j < f.length) (hc : f[j] = t.eval w env) (ht : t.top = isTop f j) :
    ∀ p ∈ templateOccurrences live N K cb lb t, EntryCorrect f (p.eval w env) := by
  intro p hp
  obtain ⟨⟨l,s⟩,hls,rfl⟩ := List.mem_map.mp hp
  obtain ⟨hs,he⟩ := List.mem_zipIdx' hls
  have hk := template_clause_length t w env hj hc
  have hos := occ_eq f j s hj (by rw [hk]; exact hs)
  unfold EntryCorrect
  intro _
  change lb.eval env+s < nM f ∧ l.1.eval env = vr f (oj f (lb.eval env+s)) (ot f (lb.eval env+s)) ∧
    t.top = isTop f (oj f (lb.eval env+s)) ∧
    (keyExpr N K cb t s).eval env = key f (lb.eval env+s)
  rw [hlb,hos.1,hos.2]
  refine ⟨off_add_lt f j s hj (by rw [hk]; exact hs), ?_, ht, ?_⟩
  · rw [template_variable t w env hj hc s hs,← he]
  · exact keyExpr_correct t w env N K cb hN hK hcb hj hc ht s hs

/-- Correct clause/occurrence bases lift the single-template result to an
entire fixed block without any assumption about target successor edges. -/
theorem blockOccurrences_correct {n : Nat} {f : CNF}
    (live : Test n) (N K cb lb : NumExpr n) (ts : List (Template n))
    (w : SAT.Word) (env : Env n)
    (hN : N.eval env = f.length) (hK : K.eval env = nK f)
    (hlb : lb.eval env = off f (cb.eval env))
    (hsource : ∀ i (hi : i < ts.length), ∃ hj : cb.eval env+i < f.length,
      f[cb.eval env+i] = ts[i].eval w env ∧ ts[i].top = isTop f (cb.eval env+i)) :
    ∀ p ∈ blockOccurrences live N K cb lb ts, EntryCorrect f (p.eval w env) := by
  induction ts generalizing cb lb with
  | nil => simp [blockOccurrences]
  | cons t ts ih =>
    obtain ⟨hj,hc,ht⟩ := hsource 0 (by simp)
    simp only [Nat.add_zero,List.getElem_cons_zero] at hj hc ht
    have hk := template_clause_length t w env hj hc
    have hlb' : (addN lb t.literals.length).eval env = off f ((addN cb 1).eval env) := by
      change lb.eval env+t.literals.length = off f (cb.eval env+1)
      rw [hlb,off_succ f _ hj,hk]
    have hs' : ∀ i (hi : i < ts.length), ∃ hj : (addN cb 1).eval env+i < f.length,
        f[(addN cb 1).eval env+i] = ts[i].eval w env ∧
          ts[i].top = isTop f ((addN cb 1).eval env+i) := by
      intro i hi
      have hh := hsource (i+1) (by simp; omega)
      simpa only [addN,NumExpr.eval,List.getElem_cons_succ,Nat.add_assoc,Nat.add_comm 1 i] using hh
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact templateOccurrences_correct live N K cb lb t w env hN hK rfl hlb hj hc ht p hp
    · exact ih (addN cb 1) (addN lb t.literals.length) hlb' hs' p hp

end STACS2027.PlanarSource.RotationTable

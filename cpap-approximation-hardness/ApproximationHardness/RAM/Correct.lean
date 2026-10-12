module

public import ApproximationHardness.RAM.PassB
public import NPHardness.SizeBounds
import Lean.Elab.Tactic.Omega

/-!
# The RAM program computes the Theorem 8 graph in linear time

`ram_computes`: on the input `ramInput f` of every formula whose clauses have two
or three literals, the program halts with output `ramOutput k f` (the budget
`|f|` and the endpoints of the edges of `formulaGraph k f`) within
`ramConst k · (|f| + n + 1)` steps, `n = variableBound f`, reading and writing only the
addresses below `N + 3n` (`N = |ramInput f|`: the input, the occurrence counts `N + 2v + s`
and the block table `N + 2n + v`).
`ram_linear_time`: for bounded-occurrence formulas, within `ramLinConst k · (n + 1)` steps and
the same space.
-/

@[expose] public section

namespace STACS2027.RAM

open Complexity.SAT

/-! ### The clause loop -/

theorem loopFree_endpointCode (len a : Nat) : LoopFree (seqs (endpointCode len a)) := by
  unfold endpointCode
  split
  · split <;> simp [seqs, LoopFree]
  · simp [seqs, LoopFree]

theorem loopFree_clauseEmit (k len : Nat) : LoopFree (seqs (clauseEmit k len)) :=
  loopFree_flatMap _ _ (fun e => loopFree_seqs_append (loopFree_seqs_append
    (loopFree_seqs_append (loopFree_endpointCode _ _) (by simp [seqs, LoopFree])) (loopFree_endpointCode _ _))
    (by simp [seqs, LoopFree]))

theorem loopFree_readLit (i : Nat) : LoopFree (readLit i) := by
  simp [readLit, seqs, LoopFree]

theorem loopFree_clauseB (k : Nat) : LoopFree (clauseB k) := by
  simp only [clauseB, seqs, LoopFree]
  exact ⟨trivial, trivial, trivial, loopFree_readLit 0, loopFree_readLit 1, trivial, trivial,
    ⟨loopFree_clauseEmit k 2, loopFree_readLit 2, loopFree_clauseEmit k 3⟩, trivial, trivial⟩

def passBpre : Stmt := seqs [Stmt.const Reg.p 0, Stmt.load Reg.m Reg.p, Stmt.add Reg.p Reg.p Reg.one]

theorem passB_eq (k : Nat) : passB k = Stmt.seq passBpre (Stmt.loop Reg.m (clauseB k)) := rfl

/-- The invariant of the clause loop. -/
def InvB (k : Nat) (f : CNF) (n N : Nat) (c : Config) : Prop := ∃ pre suf, StateB k f n N pre suf c

/-- The state after the second pass, as needed by the third. -/
structure AfterV (k : Nat) (f : CNF) (n N : Nat) (c : Config) : Prop where
  hout : c.out = f.length :: edgeWord (varPairs k 0 n)
  hcb : c.reg Reg.cb = gadgetWidth k * n
  hW : c.reg Reg.W = gadgetWidth k
  hN : c.reg Reg.N = N
  hB : c.reg Reg.B = N + n + n
  hone : c.reg Reg.one = 1
  hlow : ∀ i, i < N + n + n → c.mem i = (ramInput f).getD i 0
  htable : ∀ u, u < n → c.mem (N + n + n + u) = gadgetWidth k * u
  hlen : N = (ramInput f).length

theorem InvB.start {k : Nat} {f : CNF} {n N : Nat} {c : Config} (h : AfterV k f n N c) :
    InvB k f n N (run passBpre c) := by
  have hmem : (run passBpre c).mem = c.mem := by simp [passBpre, run]
  have hp : (run passBpre c).reg Reg.p = 1 := by simp +decide [passBpre, run, h.hone]
  have hfr : ∀ r, r ≠ Reg.p → r ≠ Reg.m → (run passBpre c).reg r = c.reg r := by
    intro r a1 a2; simp [passBpre, run, a1, a2]
  have hN0 : 0 < N := by rw [h.hlen]; simp [ramInput]
  refine ⟨[], f, ⟨rfl, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩⟩
  · simp +decide [passBpre, run, h.hlow 0 (by omega), ramInput]
  · intro i hi
    rw [hp, hmem, h.hlow _ (by rw [h.hlen]; simp [ramInput] at hi ⊢; omega)]
    simp [ramInput, Nat.add_comm 1 i]
  · rw [hp, h.hlen]; simp [ramInput]; omega
  · rw [hfr _ (by decide) (by decide), h.hN]
  · rw [hfr _ (by decide) (by decide), h.hB]
  · rw [hfr _ (by decide) (by decide), h.hW]
  · rw [hfr _ (by decide) (by decide), h.hone]
  · intro v hv s hs
    rw [hmem, h.hlow _ (by omega)]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [← h.hlen]; omega)]
    simp
  · intro u hu; rw [hmem]; exact h.htable u hu
  · rw [hfr _ (by decide) (by decide), h.hcb]; simp
  · simp [passBpre, run, h.hout, clausePairsFrom]

def passBModel (k : Nat) (c : Config) : Config :=
  iterate (run (clauseB k)) ((run passBpre c).reg Reg.m) (run passBpre c)

def passBCost (k : Nat) (f : CNF) : Nat := size passBpre + (f.length * (size (clauseB k) + 1) + 1)

/-- The third pass, within every space bound `S ≥ N + 3n`. -/
theorem sat_passB (k : Nat) (f : CNF) (n N : Nat) (hf : ∀ cl ∈ f, cl.length = 2 ∨ cl.length = 3)
    (hvars : ∀ cl ∈ f, ∀ l ∈ cl, l.var < n) {S : Nat} (hS : N + n + n + n ≤ S) :
    SatB S (passB k) (AfterV k f n N) (passBModel k) (passBCost k f) := by
  have h₁ := SatB.ofLoopFree (S := S) (s := passBpre) (by simp [passBpre, seqs, LoopFree]) (P := AfterV k f n N)
    (fun c hc => by
      have : 0 < N := by rw [hc.hlen]; simp [ramInput]
      simp +decide [passBpre, run]; omega)
  have hstep : ∀ c, InvB k f n N c → c.reg Reg.m ≠ 0 → AddrOK S (clauseB k) c ∧
      InvB k f n N (run (clauseB k) c) ∧ (run (clauseB k) c).reg Reg.m + 1 = c.reg Reg.m := by
    rintro c ⟨pre, suf, hB⟩ hm
    obtain ⟨hA, cl, suf', -, hB', hdec⟩ := hB.step hm hf hvars hS
    exact ⟨hA, ⟨_, _, hB'⟩, hdec⟩
  have h₂ := SatB.loop (a := Reg.m) (body := clauseB k) (P := InvB k f n N) (m := run (clauseB k)) (L := f.length)
    (SatB.ofLoopFree (loopFree_clauseB k) (fun c hc => (hstep c hc.1 hc.2).1)) (fun c hc hm => (hstep c hc hm).2.1)
    (fun c hc hm => (hstep c hc hm).2.2)
    (by
      rintro c ⟨pre, suf, hB⟩
      rw [hB.hm, ← hB.hsplit]; simp)
  have h := h₁.seq (Q := InvB k f n N) (fun c hc => InvB.start hc) h₂
  rw [passB_eq]
  exact (h.mono (fun c hc => hc) (by simp only [passBCost]; omega)).congr (fun c _ => rfl)

theorem passBModel_out (k : Nat) (f : CNF) (n N : Nat) (hf : ∀ cl ∈ f, cl.length = 2 ∨ cl.length = 3)
    (hvars : ∀ cl ∈ f, ∀ l ∈ cl, l.var < n) {c : Config} (h : AfterV k f n N c) :
    (passBModel k c).out = f.length :: edgeWord (varPairs k 0 n ++ clausePairsFrom k n 0 [] f) := by
  have hstep : ∀ c, InvB k f n N c → c.reg Reg.m ≠ 0 →
      InvB k f n N (run (clauseB k) c) ∧ (run (clauseB k) c).reg Reg.m + 1 = c.reg Reg.m := by
    rintro c ⟨pre, suf, hS⟩ hm
    obtain ⟨-, cl, suf', -, hS', hdec⟩ := hS.step hm hf hvars (S := N + n + n + n) (Nat.le_refl _)
    exact ⟨⟨_, _, hS'⟩, hdec⟩
  obtain ⟨⟨pre, suf, hS⟩, hm0⟩ := iterate_invariant (a := Reg.m) (P := InvB k f n N) (m := run (clauseB k))
    (fun c hc hm => (hstep c hc hm).1) (fun c hc hm => (hstep c hc hm).2) _ _ (InvB.start h) rfl
  have hsuf : suf = [] := by
    have := hS.hm; rw [hm0] at this; exact List.eq_nil_of_length_eq_zero this.symm
  subst hsuf
  have hpre : pre = f := by simpa using hS.hsplit
  subst hpre
  exact hS.hout

/-! ### The whole program -/

/-- The step bound of the program: linear in `|f| + n`. -/
def ramConst (k : Nat) : Nat :=
  size passApre + size passApost + clauseACost + 3 + size (passVpre k) + size passVpost + size (varBody k) +
    size passBpre + size (clauseB k)

/-- The program computes the Theorem 8 graph within `ramConst k · (|f| + n + 1)` steps and the space
`N + 3n`, `N = |ramInput f|`. -/
theorem ram_computes (k : Nat) (f : CNF) (hf : ∀ cl ∈ f, cl.length = 2 ∨ cl.length = 3) :
    ∃ t, ComputesIn (program k) (ramInput f) (ramOutput k f) t
        ((ramInput f).length + variableBound f + variableBound f + variableBound f) ∧
      t ≤ ramConst k * (f.length + variableBound f + 1) := by
  let n := variableBound f
  let N := (ramInput f).length
  have hf3 : ∀ cl ∈ f, cl.length ≤ 3 := fun cl hc => by rcases hf cl hc with h | h <;> omega
  have hvars : ∀ cl ∈ f, ∀ l ∈ cl, l.var < n := fun cl hc l hl => literal_lt_variableBound hc hl
  obtain ⟨mA, oA, oneA, zeroA, nA, NA, BA⟩ := passAModel_initial f
  have hAfterA : AfterA f.length n N (N + n + n) (initial (ramInput f)).mem (passAModel (initial (ramInput f))) :=
    ⟨nA, NA, BA, oneA, zeroA, oA, mA⟩
  obtain ⟨vo, vcb, vW, vN, vB, vn, vone, vzero, vlow, vtab⟩ := passVModel_spec (k := k) hAfterA
  have hAfterV : AfterV k f n N (passVModel k (passAModel (initial (ramInput f)))) :=
    ⟨vo, vcb, vW, vN, vB, vone, fun i hi => by rw [vlow i hi]; rfl, vtab, rfl⟩
  have hA := sat_passA f hf3 (S := N + n + n + n) (by omega)
  have hV := sat_passV k f.length n N (N + n + n) (initial (ramInput f)).mem (S := N + n + n + n) (Nat.le_refl _)
  have hB := sat_passB k f n N hf hvars (S := N + n + n + n) (Nat.le_refl _)
  have h := hA.seq (Q := AfterA f.length n N (N + n + n) (initial (ramInput f)).mem)
    (by rintro c rfl; exact hAfterA)
    (hV.seq (Q := AfterV k f n N) (by
      intro c hc
      have := passVModel_spec (k := k) hc
      obtain ⟨vo, vcb, vW, vN, vB, vn, vone, vzero, vlow, vtab⟩ := this
      refine ⟨vo, vcb, vW, vN, vB, vone, fun i hi => ?_, vtab, rfl⟩
      rw [vlow i hi]; rfl) hB)
  obtain ⟨t, he, ht⟩ := h (initial (ramInput f)) rfl
  refine ⟨t, ⟨_, he, ?_⟩, ?_⟩
  · rw [passBModel_out k f n N hf hvars hAfterV]; rfl
  · have hb : passACost f + (passVCost k n + passBCost k f) ≤ ramConst k * (f.length + n + 1) := by
      simp only [passACost, passVCost, passBCost, ramConst]
      generalize size passApre = a₁
      generalize size passApost = a₂
      generalize clauseACost = a₃
      generalize size (passVpre k) = a₄
      generalize size passVpost = a₅
      generalize size (varBody k) = a₆
      generalize size passBpre = a₇
      generalize size (clauseB k) = a₈
      generalize f.length = m
      simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul, Nat.mul_comm]
      omega
    exact Nat.le_trans ht hb

theorem mul_le_three_mul (K m n : Nat) (h : m + n + 1 ≤ 3 * (n + 1)) : K * (m + n + 1) ≤ 3 * K * (n + 1) := by
  rw [Nat.mul_comm 3 K, Nat.mul_assoc]
  exact Nat.mul_le_mul_left K h

/-- The constant of the linear time and space bound. -/
def ramLinConst (k : Nat) : Nat := 3 * ramConst k + 17

/-- **Linear time and space on bounded-occurrence formulas.** For every formula in which each clause
has two or three literals and each variable occurs at most once positively and twice negatively, the
program halts with output `ramOutput k f` within `ramLinConst k · (n + 1)` steps, `n = variableBound f`,
reading and writing only the addresses below `ramLinConst k · (n + 1)`. -/
theorem ram_linear_time (k : Nat) (f : CNF) (hf : BoundedOccurrence f) :
    ∃ t, ComputesIn (program k) (ramInput f) (ramOutput k f) t (ramLinConst k * (variableBound f + 1)) ∧
      t ≤ ramLinConst k * (variableBound f + 1) := by
  have h2 : ∀ c ∈ f, c.length = 2 ∨ c.length = 3 := hf.1
  obtain ⟨t, hc, ht⟩ := ram_computes k f h2
  have hm := hf.clause_count_variableBound
  have hle : f.length + variableBound f + 1 ≤ 3 * (variableBound f + 1) := by omega
  have hN := clauseCodes_length_le f (fun c hc => by rcases h2 c hc with h | h <;> omega)
  have hN' : (ramInput f).length = 1 + (f.flatMap clauseCode).length := by simp [ramInput]; omega
  have hK : ramLinConst k * (variableBound f + 1) = 3 * ramConst k * (variableBound f + 1) + 17 * (variableBound f + 1) := by
    unfold ramLinConst; rw [Nat.add_mul]
  refine ⟨t, hc.mono (by rw [hK]; omega), Nat.le_trans ht ?_⟩
  rw [hK]
  exact Nat.le_trans (mul_le_three_mul (ramConst k) _ _ hle) (Nat.le_add_right _ _)

end STACS2027.RAM

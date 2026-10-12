module

public import ApproximationHardness.RAM.Orient.Spec
import Lean.Elab.Tactic.Omega

/-!
# The orientation program: one literal occurrence
-/

@[expose] public section

namespace STACS2027.RAM

open Complexity.SAT Complexity.Planar.Comb PlanarAssembly

/-! ### The layout -/

/-- The start of the tables: twice the length of `ramInput f`. -/
def orE (f : CNF) : Nat := 2 * (ramInput f).length
/-- The start of the occurrence records. -/
def orB (f : CNF) : Nat := orE f + 2 * variableBound f

/-- The space of the orientation program: the input and its copy area below `orE f`, the two
cells of every variable, and the four cells of every occurrence record. -/
def orSpace (f : CNF) : Nat := orB f + 4 * f.flatten.length

/-- The constants and layout registers. -/
structure Layout (f : CNF) (c : Config) : Prop where
  one : c.reg Reg.one = 1
  zero : c.reg Reg.zero = 0
  two : c.reg OR.two = 2
  three : c.reg OR.three = 3
  five : c.reg OR.five = 5
  N : c.reg Reg.N = (ramInput f).length
  n : c.reg Reg.n = variableBound f
  E : c.reg OR.E = orE f
  B : c.reg OR.B = orB f

/-- The registers `Layout` reads. -/
def layoutRegs : List Nat := [Reg.one, Reg.zero, OR.two, OR.three, OR.five, Reg.N, Reg.n, OR.E, OR.B]

theorem Layout.frame {f : CNF} {c c' : Config} (h : Layout f c) (hr : ∀ r ∈ layoutRegs, c'.reg r = c.reg r) :
    Layout f c' :=
  ⟨(hr _ (by simp [layoutRegs])).trans h.one, (hr _ (by simp [layoutRegs])).trans h.zero,
    (hr _ (by simp [layoutRegs])).trans h.two, (hr _ (by simp [layoutRegs])).trans h.three,
    (hr _ (by simp [layoutRegs])).trans h.five, (hr _ (by simp [layoutRegs])).trans h.N,
    (hr _ (by simp [layoutRegs])).trans h.n, (hr _ (by simp [layoutRegs])).trans h.E,
    (hr _ (by simp [layoutRegs])).trans h.B⟩

/-- The memory after reading the literals `past`: the input below `orE f`, the counters of negative
occurrences and the positive-occurrence codes of the variables, the records of the occurrences
read, and zeros after them. -/
structure MemInv (f : CNF) (rot : List Nat) (past : List Literal) (M : Nat → Nat) : Prop where
  input : ∀ a, a < orE f → M a = (orInput f rot).getD a 0
  neg : ∀ v, v < variableBound f → M (orE f + 2 * v) = past.count ⟨v, false⟩
  pos : ∀ v, v < variableBound f → M (orE f + 2 * v + 1) = posCode past v
  recs : ∀ i, i < past.length → M (orB f + 4 * i) = occPort f i ∧ M (orB f + 4 * i + 1) = occVar f i ∧
    M (orB f + 4 * i + 2) = occPort f i ∧ M (orB f + 4 * i + 3) = csBit f rot i
  free : ∀ a, orB f + 4 * past.length ≤ a → M a = 0

theorem At.agree {c c' : Config} {w u : List Nat} (h : At c (w ++ u))
    (hp : c'.reg Reg.p = c.reg Reg.p + w.length)
    (hm : ∀ i, i < u.length → c'.mem (c'.reg Reg.p + i) = c.mem (c'.reg Reg.p + i)) : At c' u := by
  intro i hi
  rw [hm i hi, hp, Nat.add_assoc]
  have := h (w.length + i) (by simp; omega)
  rw [this, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
  simp

theorem literal_var_lt {f : CNF} {l : Literal} (h : l ∈ f.flatten) : l.var < variableBound f := by
  obtain ⟨c, hc, hl⟩ := List.mem_flatten.mp h
  exact literal_lt_variableBound hc hl

/-! ### One literal -/

/-- The port stored for the literal `l` on the memory `M`. -/
def litPortM (f : CNF) (M : Nat → Nat) (l : Literal) : Nat :=
  if l.positive then 0 else M (orE f + 2 * l.var) + 1

/-- The memory after one literal, as a function. -/
def litMem (f : CNF) (M : Nat → Nat) (i : Nat) (l : Literal) (csv : Nat) (a : Nat) : Nat :=
  if a = orB f + 4 * i + 3 then csv
  else if a = orB f + 4 * i + 2 then litPortM f M l
  else if a = orB f + 4 * i + 1 then l.var
  else if a = orB f + 4 * i then litPortM f M l
  else if l.positive then
    (if a = orE f + 2 * l.var + 1 ∧ M (orE f + 2 * l.var + 1) = 0 then i + 1 else M a)
  else (if a = orE f + 2 * l.var then M (orE f + 2 * l.var) + 1 else M a)

theorem orLit_mem (f : CNF) (c : Config) (l : Literal) (w : List Nat) (hL : Layout f c)
    (hAt : At c (litCode l ++ w)) :
    (run orLit c).mem = litMem f c.mem (c.reg OR.occ) l (c.reg OR.cs) := by
  have g0 := hAt 0 (by simp [litCode])
  have g1 := hAt 1 (by simp [litCode])
  simp only [litCode, List.cons_append, List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at g0 g1
  funext a
  have hone := hL.one
  have hE := hL.E
  have hB := hL.B
  have e3 : ∀ o, orB f + o + o + o + o + 1 + 1 + 1 = orB f + 4 * o + 3 := fun o => by omega
  have e4 : ∀ o, orB f + o + o + o + o + 1 + 1 = orB f + 4 * o + 2 := fun o => by omega
  have e5 : ∀ o, orB f + o + o + o + o + 1 = orB f + 4 * o + 1 := fun o => by omega
  have e1 : ∀ o, orB f + o + o + o + o = orB f + 4 * o := fun o => by omega
  have e2 : orE f + l.var + l.var = orE f + 2 * l.var := by omega
  cases hp : l.positive
  · have hs : signCode l = 0 := by simp [signCode, hp]
    simp +decide only [orLit, run_seqs_cons, run_seqs_nil, run, setReg_reg, setReg_mem, setMem_mem, setMem_reg,
      ↓reduceIte, g0, g1, hs, hone, hE, hB]
    unfold litMem litPortM
    simp only [hp, Bool.false_eq_true, ↓reduceIte, e1, e2]
  · have hs : signCode l = 1 := by simp [signCode, hp]
    by_cases hq : c.mem (orE f + 2 * l.var + 1) = 0
    · have hq' : c.mem (orE f + l.var + l.var + 1) = 0 := by rw [← hq]; congr 1; omega
      simp +decide only [orLit, run_seqs_cons, run_seqs_nil, run, setReg_reg, setReg_mem, setMem_mem, setMem_reg,
        ↓reduceIte, g0, g1, hs, hone, hE, hB, hq']
      unfold litMem litPortM
      simp only [hp, ↓reduceIte, e1, e2, hq, and_true]
    · have hq' : c.mem (orE f + l.var + l.var + 1) ≠ 0 := by rw [show orE f + l.var + l.var + 1 = orE f + 2 * l.var + 1 by omega]; exact hq
      simp +decide only [orLit, run_seqs_cons, run_seqs_nil, run, setReg_reg, setReg_mem, setMem_mem, setMem_reg,
        ↓reduceIte, g0, g1, hs, hone, hE, hB, hq']
      unfold litMem litPortM
      simp only [hp, ↓reduceIte, e1, hq, and_false]

theorem litMem_other (f : CNF) (M : Nat → Nat) (i : Nat) (l : Literal) (csv a : Nat)
    (h3 : a ≠ orB f + 4 * i + 3) (h2 : a ≠ orB f + 4 * i + 2) (h1 : a ≠ orB f + 4 * i + 1)
    (h0 : a ≠ orB f + 4 * i) (hn : a ≠ orE f + 2 * l.var) (hp : a ≠ orE f + 2 * l.var + 1) :
    litMem f M i l csv a = M a := by
  unfold litMem
  rw [ite_eq_right h3, ite_eq_right h2, ite_eq_right h1, ite_eq_right h0]
  cases l.positive <;> simp [hn, hp]

theorem orLit_regs (f : CNF) (c : Config) (l : Literal) (w : List Nat) (hL : Layout f c)
    (hAt : At c (litCode l ++ w)) :
    (run orLit c).reg OR.occ = c.reg OR.occ + 1 ∧ (run orLit c).reg Reg.p = c.reg Reg.p + 2 ∧
      (run orLit c).reg OR.cnt = c.reg OR.cnt - 1 := by
  have g0 := hAt 0 (by simp [litCode])
  have g1 := hAt 1 (by simp [litCode])
  simp only [litCode, List.cons_append, List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at g0 g1
  have hone := hL.one
  refine ⟨?_, ?_, ?_⟩ <;>
  · simp +decide only [orLit, run_seqs_cons, run_seqs_nil, run, setReg_reg, setReg_mem, setMem_reg,
      reg_ite, ↓reduceIte, ite_self, hone]

/-- One literal reads the two input cells at `p`, the cell `E + 2v` or `E + 2v + 1` of its variable
`v < n`, and writes its record at `B + 4 occ`. -/
theorem orLit_addrOK {S : Nat} (f : CNF) (c : Config) (l : Literal) (w : List Nat) (hL : Layout f c)
    (hAt : At c (litCode l ++ w)) (hv : l.var < variableBound f) (hp : c.reg Reg.p + 2 ≤ S)
    (hocc : orB f + 4 * c.reg OR.occ + 4 ≤ S) : AddrOK S orLit c := by
  have g0 := hAt 0 (by simp [litCode])
  have g1 := hAt 1 (by simp [litCode])
  simp only [litCode, List.cons_append, List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at g0 g1
  have hEB : orB f = orE f + 2 * variableBound f := rfl
  simp +decide [orLit, run, hL.one, hL.E, hL.B, g0, g1]
  omega

/-- One literal: the memory invariant is extended by the literal. -/
theorem orLit_step (f : CNF) (rot : List Nat) (c : Config) (past rest : List Literal) (l : Literal)
    (w : List Nat) (hpast : past ++ l :: rest = f.flatten) (hL : Layout f c) (hM : MemInv f rot past c.mem)
    (hocc : c.reg OR.occ = past.length) (hcs : c.reg OR.cs = csBit f rot past.length)
    (hAt : At c (litCode l ++ w)) (hin : c.reg Reg.p + 2 + w.length ≤ (ramInput f).length) :
    Layout f (run orLit c) ∧ MemInv f rot (past ++ [l]) (run orLit c).mem ∧
      (run orLit c).reg OR.occ = past.length + 1 ∧ (run orLit c).reg Reg.p = c.reg Reg.p + 2 ∧
      (run orLit c).reg OR.cnt = c.reg OR.cnt - 1 ∧ At (run orLit c) w ∧ (run orLit c).out = c.out ∧
      ∀ r, r ∉ regsW orLit → (run orLit c).reg r = c.reg r := by
  have hfr : ∀ r, r ∉ regsW orLit → (run orLit c).reg r = c.reg r := fun r h => run_reg_frame _ _ _ h
  obtain ⟨r1, r2, r3⟩ := orLit_regs f c l w hL hAt
  have hmem := orLit_mem f c l w hL hAt
  have hv : l.var < variableBound f := literal_var_lt (by rw [← hpast]; simp)
  have hEB : orB f = orE f + 2 * variableBound f := rfl
  have hNE : (ramInput f).length ≤ orE f := by unfold orE; omega
  obtain ⟨hget, htake⟩ := getElem_prefix hpast
  have hport : occPort f past.length = litPort past l := by
    rw [occPort_flat, hget, htake]; rfl
  have hvar : occVar f past.length = l.var := by rw [occVar_flat, hget]; rfl
  have hPM : litPortM f c.mem l = litPort past l := by
    unfold litPortM litPort
    cases hp : l.positive
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [hM.neg _ hv]
      cases l; simp only at hp; subst hp; rfl
    · rfl
  refine ⟨hL.frame (fun r hr => hfr r (by revert r; decide)), ⟨?_, ?_, ?_, ?_, ?_⟩, by rw [r1, hocc], r2, r3, ?_,
    run_out_frame _ _ (by decide), hfr⟩
  · intro a ha
    rw [hmem, hocc, litMem_other _ _ _ _ _ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
    exact hM.input a ha
  · intro v' hv'
    rw [hmem, hocc, List.count_append, List.count_singleton]
    by_cases he : v' = l.var
    · subst he
      unfold litMem
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
      cases hp : l.positive
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rw [hM.neg _ hv']
        cases l; simp only at hp; subst hp; simp
      · simp only [↓reduceIte]
        rw [ite_eq_right (by omega), hM.neg _ hv']
        cases l; simp only at hp; subst hp; simp
    · rw [litMem_other _ _ _ _ _ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
        hM.neg _ hv']
      have : (l == ⟨v', false⟩) = false := by
        cases l; simp only [beq_eq_false_iff_ne, ne_eq, Literal.mk.injEq, not_and]; intro h; exact absurd h.symm he
      simp [this]
  · intro v' hv'
    rw [hmem, hocc, posCode_snoc]
    by_cases he : v' = l.var
    · subst he
      unfold litMem
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
      cases hp : l.positive
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rw [ite_eq_right (by omega), hM.pos _ hv']
        have : l ≠ ⟨l.var, true⟩ := by cases l; simp only at hp; subst hp; simp
        simp [this]
      · simp only [↓reduceIte, true_and]
        rw [hM.pos _ hv']
        have : l = ⟨l.var, true⟩ := by cases l; simp only at hp; subst hp; rfl
        simp only [← this, and_true]
    · rw [litMem_other _ _ _ _ _ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
        hM.pos _ hv']
      have : l ≠ ⟨v', true⟩ := by cases l; simp only [ne_eq, Literal.mk.injEq, not_and]; intro h; exact absurd h.symm he
      simp [this]
  · intro i hi
    rw [hmem, hocc]
    rw [List.length_append, List.length_singleton] at hi
    by_cases he : i = past.length
    · subst he
      unfold litMem
      simp only [↓reduceIte, show orB f + 4 * past.length ≠ orB f + 4 * past.length + 3 by omega,
        show orB f + 4 * past.length + 1 ≠ orB f + 4 * past.length + 3 by omega,
        show orB f + 4 * past.length + 2 ≠ orB f + 4 * past.length + 3 by omega,
        show orB f + 4 * past.length ≠ orB f + 4 * past.length + 2 by omega,
        show orB f + 4 * past.length + 1 ≠ orB f + 4 * past.length + 2 by omega,
        show orB f + 4 * past.length ≠ orB f + 4 * past.length + 1 by omega]
      exact ⟨by rw [hPM, hport], by rw [hvar], by rw [hPM, hport], hcs⟩
    · have hi' : i < past.length := by omega
      rw [litMem_other _ _ _ _ _ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
        litMem_other _ _ _ _ _ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
        litMem_other _ _ _ _ _ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
        litMem_other _ _ _ _ _ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
      exact hM.recs i hi'
  · intro a ha
    rw [List.length_append, List.length_singleton] at ha
    rw [hmem, hocc, litMem_other _ _ _ _ _ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
    exact hM.free a (by omega)
  · apply At.agree hAt (by rw [r2]; rfl)
    intro i hi
    rw [hmem, hocc, litMem_other _ _ _ _ _ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]

end STACS2027.RAM

module

public import ApproximationHardness.Sim.XLogic
public import ApproximationHardness.RAM.Program
import Lean.Elab.Tactic.Omega

/-!
# Reading the code of a formula

`parseCNF` reads the code `encode f` of a formula (the registered foundation's format: unary
numbers, lists as their length followed by their elements) bit by bit and writes the RAM input
`ramInput f` to the even memory cells `0, 2, 4, …` (`xok_parseCNF`), in time linear in the length of
the code.
-/

@[expose] public section

namespace STACS2027.Sim

open Complexity.SAT

/-- A loop over the items of a list, with costs depending on the items. -/
theorem xok_listLoop {α : Type} {a : Nat} {body : XStmt} (xs : List α) (I : List α → XConfig → Prop) (b : α → Nat)
    (hstep : ∀ pre x suf c, pre ++ x :: suf = xs → I pre c → c.reg a ≠ 0 ∧ ∃ c', XOk body c c' (b x) ∧ I (pre ++ [x]) c')
    (hend : ∀ c, I xs c → c.reg a = 0) :
    ∀ c, I [] c → ∃ c', XOk (.loop a body) c c' ((xs.map fun x => b x + 1).sum + 1) ∧ I xs c' := by
  have key : ∀ suf pre c, pre ++ suf = xs → I pre c →
      ∃ c', XOk (.loop a body) c c' ((suf.map fun x => b x + 1).sum + 1) ∧ I xs c' := by
    intro suf
    induction suf with
    | nil =>
      intro pre c hp hI
      simp only [List.append_nil] at hp; subst hp
      exact ⟨c, ⟨1, XExec.loopDone (hend c hI), by simp⟩, hI⟩
    | cons x suf ih =>
      intro pre c hp hI
      obtain ⟨ha, c₁, ⟨t, he, ht⟩, hI₁⟩ := hstep pre x suf c hp hI
      obtain ⟨c₂, ⟨t', he', ht'⟩, hI₂⟩ := ih (pre ++ [x]) c₁ (by simp [← hp]) hI₁
      exact ⟨c₂, ⟨t + t' + 1, XExec.loopNext ha he he', by simp only [List.map_cons, List.sum_cons]; omega⟩, hI₂⟩
  intro c hc
  exact key xs [] c rfl hc

theorem writeNat_eq (v : Nat) : writeNat v = List.replicate v true ++ [false] := by
  induction v with
  | zero => rfl
  | succ v ih => simp [writeNat, ih, List.replicate_succ]

theorem writeNat_length' (v : Nat) : (writeNat v).length = v + 1 := by simp [writeNat_eq]

theorem sum_const_map {α : Type} (xs : List α) (b : Nat) : (xs.map fun _ => b).sum = xs.length * b := by
  induction xs with
  | nil => simp
  | cons _ _ ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih, Nat.succ_mul]; omega

/-! ### Registers of the parser -/

@[simp] abbrev pB : Nat := 100
@[simp] abbrev pFL : Nat := 101
@[simp] abbrev pT : Nat := 102
@[simp] abbrev pP : Nat := 104
@[simp] abbrev pCNT : Nat := 105
@[simp] abbrev pCL : Nat := 106
@[simp] abbrev pS : Nat := 107
@[simp] abbrev pV : Nat := 108
@[simp] abbrev pONE : Nat := 109
@[simp] abbrev pTWO : Nat := 110
@[simp] abbrev pZ : Nat := 111

/-! ### Unary numbers -/

/-- Read a bit; `pFL := 1` if it is `1`, else `0` (also at the end of the input). -/
def getFlag : XStmt := xseqs [.getBit pB, .sub pT pB pONE, .add pT pT pT, .sub pFL pB pT]

theorem xok_getFlag (c : XConfig) (hone : c.reg pONE = 1) :
    ∃ c', XOk getFlag c c' 5 ∧ c'.reg pFL = (if c.inp.head? = some true then 1 else 0) ∧ c'.inp = c.inp.tail ∧
      c'.mem = c.mem ∧ c'.out = c.out ∧ ∀ i, i ≠ pB → i ≠ pT → i ≠ pFL → c'.reg i = c.reg i := by
  have h := (xok_getBit pB c).seq ((xok_sub pT pB pONE _).seq ((xok_add pT pT pT _).seq ((xok_sub pFL pB pT _).seq
    (xok_skip _))))
  refine ⟨_, h, ?_, ?_, rfl, rfl, ?_⟩
  · cases hi : c.inp with
    | nil => simp [XConfig.setReg, XConfig.getBit, hi, bitVal, hone]
    | cons b w => cases b <;> simp [XConfig.setReg, XConfig.getBit, hi, bitVal, hone]
  · simp [XConfig.setReg, XConfig.getBit]
  · intro i h1 h2 h3; simp [XConfig.setReg, XConfig.getBit, h1, h2, h3]

/-- Read a unary number into `x`. -/
def readNat (x : Nat) : XStmt := xseqs [.const x 0, getFlag, .loop pFL (.seq (.add x x pONE) getFlag)]

theorem drop_writeNat {v k : Nat} (hk : k ≤ v) : (writeNat v).drop k = List.replicate (v - k) true ++ [false] := by
  rw [writeNat_eq, List.drop_append_of_le_length (by simp; omega), List.drop_replicate]

theorem xok_readNat (x : Nat) (h1 : x ≠ pB) (h2 : x ≠ pT) (h3 : x ≠ pFL) (h4 : x ≠ pONE) (c : XConfig) (v : Nat)
    (rest : List Bool) (hin : c.inp = writeNat v ++ rest) (hone : c.reg pONE = 1) :
    ∃ c', XOk (readNat x) c c' (7 * v + 8) ∧ c'.reg x = v ∧ c'.inp = rest ∧ c'.mem = c.mem ∧ c'.out = c.out ∧
      ∀ i, i ≠ x → i ≠ pB → i ≠ pT → i ≠ pFL → c'.reg i = c.reg i := by
  have s1 := xok_const x 0 c
  obtain ⟨c2, s2, f2, i2, m2, o2, r2⟩ := xok_getFlag (c.setReg x 0) (by simp [XConfig.setReg, h4.symm, hone])
  let I : List Unit → XConfig → Prop := fun pre d =>
    d.reg x = pre.length ∧ d.inp = (writeNat v).drop (pre.length + 1) ++ rest ∧
      d.reg pFL = (if pre.length < v then 1 else 0) ∧ d.mem = c.mem ∧ d.out = c.out ∧
      ∀ i, i ≠ x → i ≠ pB → i ≠ pT → i ≠ pFL → d.reg i = c.reg i
  have hI0 : I [] c2 := by
    refine ⟨?_, ?_, ?_, m2, o2, fun i a1 a2 a3 a4 => ?_⟩
    · rw [r2 x h1 h2 h3]; simp [XConfig.setReg]
    · rw [i2]; simp [XConfig.setReg, hin]; cases v <;> simp [writeNat]
    · rw [f2]; simp only [XConfig.setReg, hin]
      cases v with
      | zero => simp [writeNat]
      | succ v => simp [writeNat]
    · rw [r2 i a2 a3 a4]; simp [XConfig.setReg, a1]
  obtain ⟨c3, s3, hI3⟩ := xok_listLoop (a := pFL) (body := .seq (.add x x pONE) getFlag) (List.replicate v ())
    I (fun _ => 6)
    (by
      intro pre u suf d hp ⟨d1, d2, d3, d4, d5, d6⟩
      have hl : pre.length < v := by
        have := congrArg List.length hp; simp at this; omega
      refine ⟨by rw [d3, ite_eq_left hl]; omega, ?_⟩
      have hone' : (d.setReg x (d.reg x + d.reg pONE)).reg pONE = 1 := by
        simp [XConfig.setReg, h4.symm, d6 pONE (Ne.symm h4) (by decide) (by decide) (by decide), hone]
      obtain ⟨d', s', f', i', m', o', r'⟩ := xok_getFlag _ hone'
      refine ⟨d', (xok_add x x pONE d).seq s', ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [r' x h1 h2 h3]
        simp [XConfig.setReg, d1, d6 pONE (Ne.symm h4) (by decide) (by decide) (by decide), hone]
      · rw [i']; simp only [XConfig.setReg, d2, List.length_append, List.length_singleton]
        rw [drop_writeNat (by omega)]
        by_cases hh : pre.length + 1 < v
        · rw [drop_writeNat (by omega), show v - (pre.length + 1) = (v - (pre.length + 1 + 1)) + 1 by omega]
          simp [List.replicate_succ]
        · rw [show v - (pre.length + 1) = 0 by omega, List.drop_eq_nil_of_le (by simp [writeNat_eq]; omega)]
          simp
      · rw [f']; simp only [XConfig.setReg, d2, List.length_append, List.length_singleton]
        rw [drop_writeNat (by omega)]
        by_cases hh : pre.length + 1 < v
        · rw [ite_eq_left hh, show v - (pre.length + 1) = (v - (pre.length + 1) - 1) + 1 by omega]
          simp [List.replicate_succ]
        · rw [ite_eq_right hh, show v - (pre.length + 1) = 0 by omega]; simp
      · rw [m']; exact d4
      · rw [o']; exact d5
      · intro i a1 a2 a3 a4
        rw [r' i a2 a3 a4]; simp [XConfig.setReg, a1, d6 i a1 a2 a3 a4])
    (by intro d ⟨_, _, d3, _⟩; rw [d3]; simp)
    c2 hI0
  obtain ⟨e1, e2, -, e4, e5, e6⟩ := hI3
  simp only [List.length_replicate] at e1 e2
  refine ⟨c3, (s1.seq (s2.seq (s3.seq (xok_skip _)))).mono ?_, e1, ?_, e4, e5, e6⟩
  · rw [sum_const_map, List.length_replicate]; omega
  · rw [e2, List.drop_eq_nil_of_le (by simp)]; rfl

/-! ### Writing to the even cells -/

/-- The even cells hold `L`, everything else is `0`. -/
def memOf (L : List Nat) (a : Nat) : Nat := if a % 2 = 0 then L.getD (a / 2) 0 else 0

theorem memOf_nil : memOf [] = fun _ => 0 := by funext a; simp [memOf]

theorem memOf_snoc (L : List Nat) (v : Nat) :
    (fun a => if a = 2 * L.length then v else memOf L a) = memOf (L ++ [v]) := by
  funext a
  unfold memOf
  by_cases ha : a = 2 * L.length
  · subst ha; simp
  · rw [ite_eq_right ha]
    split
    · rename_i h2
      have hne : a / 2 ≠ L.length := fun e => ha (by omega)
      rcases Nat.lt_or_gt_of_ne hne with hl | hl
      · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hl]
      · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (show L.length ≤ a / 2 by omega),
          List.getElem?_eq_none (show (L ++ [v]).length ≤ a / 2 by simp; omega)]
    · rfl

/-- Write `x` at the cell `pP` and advance `pP` by two. -/
def putNum (x : Nat) : XStmt := .seq (.store pP x) (.add pP pP pTWO)

theorem xok_putNum (x : Nat) (_hx : x ≠ pP) (c : XConfig) (L : List Nat) (hP : c.reg pP = 2 * L.length)
    (hm : c.mem = memOf L) (htwo : c.reg pTWO = 2) :
    ∃ c', XOk (putNum x) c c' 2 ∧ c'.mem = memOf (L ++ [c.reg x]) ∧ c'.reg pP = 2 * (L ++ [c.reg x]).length ∧
      c'.inp = c.inp ∧ c'.out = c.out ∧ ∀ i, i ≠ pP → c'.reg i = c.reg i := by
  refine ⟨_, (xok_store pP x c).seq (xok_add pP pP pTWO _), ?_, ?_, rfl, rfl, ?_⟩
  · simp only [XConfig.setReg, XConfig.setMem]; rw [hP, hm, memOf_snoc]
  · simp [XConfig.setReg, XConfig.setMem, hP, htwo]; omega
  · intro i hi; simp [XConfig.setReg, XConfig.setMem, hi]

/-! ### Literals, clauses, formulas -/

def parseLit : XStmt := xseqs [.sub pCL pCL pONE, .getBit pS, readNat pV, putNum pV, putNum pS]

/-- The parser's own registers. -/
abbrev ParseFree (i : Nat) : Prop :=
  i ≠ pB ∧ i ≠ pFL ∧ i ≠ pT ∧ i ≠ pP ∧ i ≠ pCNT ∧ i ≠ pCL ∧ i ≠ pS ∧ i ≠ pV

theorem xok_parseLit (l : Literal) (rest : List Bool) (c : XConfig) (L : List Nat)
    (hin : c.inp = encodeLiteral l ++ rest) (hP : c.reg pP = 2 * L.length) (hm : c.mem = memOf L)
    (hone : c.reg pONE = 1) (htwo : c.reg pTWO = 2) :
    ∃ c', XOk parseLit c c' (8 * (encodeLiteral l).length) ∧ c'.inp = rest ∧ c'.mem = memOf (L ++ RAM.litCode l) ∧
      c'.reg pP = 2 * (L ++ RAM.litCode l).length ∧ c'.reg pCL = c.reg pCL - 1 ∧ c'.out = c.out ∧
      ∀ i, i ≠ pCL → i ≠ pS → i ≠ pV → i ≠ pB → i ≠ pT → i ≠ pFL → i ≠ pP → c'.reg i = c.reg i := by
  have s1 := xok_sub pCL pCL pONE c
  have s2 := xok_getBit pS (c.setReg pCL (c.reg pCL - c.reg pONE))
  generalize hc2 : (c.setReg pCL (c.reg pCL - c.reg pONE)).getBit pS = c2 at s2
  have c2i : c2.inp = writeNat l.var ++ rest := by rw [← hc2]; simp [XConfig.getBit, XConfig.setReg, hin, encodeLiteral]
  have c2S : c2.reg pS = RAM.signCode l := by
    rw [← hc2]; simp [XConfig.getBit, XConfig.setReg, hin, encodeLiteral, RAM.signCode]
    cases l.positive <;> rfl
  have c2r : ∀ i, i ≠ pS → i ≠ pCL → c2.reg i = c.reg i := by
    intro i h1 h2; rw [← hc2]; simp [XConfig.getBit, XConfig.setReg, h1, h2]
  have c2CL : c2.reg pCL = c.reg pCL - 1 := by rw [← hc2]; simp [XConfig.getBit, XConfig.setReg, hone]
  obtain ⟨c3, s3, v3, i3, m3, o3, r3⟩ := xok_readNat pV (by decide) (by decide) (by decide) (by decide) c2 l.var rest
    c2i (by rw [c2r pONE (by decide) (by decide), hone])
  have hm3 : c3.mem = memOf L := by rw [m3, ← hc2]; exact hm
  have hP3 : c3.reg pP = 2 * L.length := by
    rw [r3 pP (by decide) (by decide) (by decide) (by decide), c2r pP (by decide) (by decide), hP]
  have ht3 : c3.reg pTWO = 2 := by
    rw [r3 pTWO (by decide) (by decide) (by decide) (by decide), c2r pTWO (by decide) (by decide), htwo]
  obtain ⟨c4, s4, m4, p4, i4, o4, r4⟩ := xok_putNum pV (by decide) c3 L hP3 hm3 ht3
  obtain ⟨c5, s5, m5, p5, i5, o5, r5⟩ := xok_putNum pS (by decide) c4 (L ++ [c3.reg pV]) p4 m4
    (by rw [r4 pTWO (by decide), ht3])
  have e4S : c4.reg pS = RAM.signCode l := by
    rw [r4 pS (by decide), r3 pS (by decide) (by decide) (by decide) (by decide), c2S]
  rw [v3, e4S] at m5 p5
  refine ⟨c5, (s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (xok_skip _)))))).mono ?_, by rw [i5, i4, i3], ?_, ?_, ?_,
    by rw [o5, o4, o3, ← hc2]; rfl, ?_⟩
  · simp [encodeLiteral]; omega
  · rw [m5]; simp [RAM.litCode]
  · rw [p5]; simp [RAM.litCode]
  · rw [r5 pCL (by decide), r4 pCL (by decide), r3 pCL (by decide) (by decide) (by decide) (by decide), c2CL]
  · intro i a1 a2 a3 a4 a5 a6 a7
    rw [r5 i a7, r4 i a7, r3 i a3 a4 a5 a6, c2r i a2 a1]

theorem sum_cost_le {α : Type} (enc : α → List Bool) (henc : ∀ x, 1 ≤ (enc x).length) (k : Nat) :
    ∀ xs : List α, (xs.map fun x => k * (enc x).length + 1).sum ≤ (k + 1) * (writeValues enc xs).length := by
  intro xs
  induction xs with
  | nil => simp [writeValues]
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, writeValues, List.length_append, Nat.mul_add]
    have := henc x
    have : (k + 1) * (enc x).length = k * (enc x).length + (enc x).length := by rw [Nat.add_mul, Nat.one_mul]
    omega

def parseClause : XStmt := xseqs [.sub pCNT pCNT pONE, readNat pCL, putNum pCL, .loop pCL parseLit]

theorem encodeLiteral_length (l : Literal) : (encodeLiteral l).length = l.var + 2 := by
  simp [encodeLiteral]

theorem writeValues_cons {α : Type} (enc : α → List Bool) (x : α) (xs : List α) :
    writeValues enc (x :: xs) = enc x ++ writeValues enc xs := rfl

theorem writeValues_drop {α : Type} (enc : α → List Bool) {xs pre suf : List α} {x : α} (h : pre ++ x :: suf = xs) :
    writeValues enc (xs.drop pre.length) = enc x ++ writeValues enc suf := by
  subst h; simp [writeValues_cons]

theorem xok_parseClause (cl : Clause) (rest : List Bool) (c : XConfig) (L : List Nat)
    (hin : c.inp = encodeClause cl ++ rest) (hP : c.reg pP = 2 * L.length) (hm : c.mem = memOf L)
    (hone : c.reg pONE = 1) (htwo : c.reg pTWO = 2) :
    ∃ c', XOk parseClause c c' (13 * (encodeClause cl).length) ∧ c'.inp = rest ∧
      c'.mem = memOf (L ++ RAM.clauseCode cl) ∧ c'.reg pP = 2 * (L ++ RAM.clauseCode cl).length ∧
      c'.reg pCNT = c.reg pCNT - 1 ∧ c'.out = c.out ∧ ∀ i, ParseFree i → c'.reg i = c.reg i := by
  have s1 := xok_sub pCNT pCNT pONE c
  obtain ⟨c2, s2, v2, i2, m2, o2, r2⟩ := xok_readNat pCL (by decide) (by decide) (by decide) (by decide)
    (c.setReg pCNT (c.reg pCNT - c.reg pONE)) cl.length (writeValues encodeLiteral cl ++ rest)
    (by simp [XConfig.setReg, hin, encodeClause, writeList])
    (by simp [XConfig.setReg, hone])
  have hP2 : c2.reg pP = 2 * L.length := by
    rw [r2 pP (by decide) (by decide) (by decide) (by decide)]; simp [XConfig.setReg, hP]
  obtain ⟨c3, s3, m3, p3, i3, o3, r3⟩ := xok_putNum pCL (by decide) c2 L hP2 (by rw [m2]; exact hm)
    (by rw [r2 pTWO (by decide) (by decide) (by decide) (by decide)]; simp [XConfig.setReg, htwo])
  rw [v2] at m3 p3
  let I : List Literal → XConfig → Prop := fun pre d =>
    d.inp = writeValues encodeLiteral (cl.drop pre.length) ++ rest ∧
      d.mem = memOf (L ++ [cl.length] ++ pre.flatMap RAM.litCode) ∧
      d.reg pP = 2 * (L ++ [cl.length] ++ pre.flatMap RAM.litCode).length ∧ d.reg pCL = cl.length - pre.length ∧
      d.out = c.out ∧ ∀ i, i ≠ pCL → i ≠ pS → i ≠ pV → i ≠ pB → i ≠ pT → i ≠ pFL → i ≠ pP → d.reg i = c3.reg i
  have hI0 : I [] c3 := ⟨by rw [i3, i2]; rfl, by rw [m3]; simp, by rw [p3]; simp,
    by rw [r3 pCL (by decide), v2]; simp, by rw [o3, o2]; rfl, fun _ _ _ _ _ _ _ _ => rfl⟩
  have hone3 : c3.reg pONE = 1 := by
    rw [r3 pONE (by decide), r2 pONE (by decide) (by decide) (by decide) (by decide)]; simp [XConfig.setReg, hone]
  have htwo3 : c3.reg pTWO = 2 := by
    rw [r3 pTWO (by decide), r2 pTWO (by decide) (by decide) (by decide) (by decide)]; simp [XConfig.setReg, htwo]
  obtain ⟨c4, s4, hI4⟩ := xok_listLoop (a := pCL) (body := parseLit) cl I (fun l => 8 * (encodeLiteral l).length)
    (by
      intro pre l suf d hp ⟨d1, d2, d3, d4, d5, d6⟩
      have hl : pre.length < cl.length := by have := congrArg List.length hp; simp at this; omega
      refine ⟨by rw [d4]; omega, ?_⟩
      rw [writeValues_drop encodeLiteral hp] at d1
      obtain ⟨d', s', i', m', p', cl', o', r'⟩ := xok_parseLit l (writeValues encodeLiteral suf ++ rest) d _
        (by rw [d1, List.append_assoc]) d3 d2
        (by rw [d6 pONE (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hone3])
        (by rw [d6 pTWO (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), htwo3])
      refine ⟨d', s', ?_, ?_, ?_, ?_, by rw [o', d5], fun i a1 a2 a3 a4 a5 a6 a7 => by
        rw [r' i a1 a2 a3 a4 a5 a6 a7, d6 i a1 a2 a3 a4 a5 a6 a7]⟩
      · rw [i']; simp only [List.length_append, List.length_singleton]
        rw [show cl.drop (pre.length + 1) = suf by subst hp; simp]
      · rw [m']; simp
      · rw [p']; simp
      · rw [cl', d4]; simp; omega)
    (by intro d ⟨_, _, _, d4, _⟩; rw [d4]; simp)
    c3 hI0
  obtain ⟨e1, e2, e3, -, e5, e6⟩ := hI4
  have hlen : (encodeClause cl).length = cl.length + 1 + (writeValues encodeLiteral cl).length := by
    simp [encodeClause, writeList]
  have hsum := sum_cost_le encodeLiteral (fun l => by rw [encodeLiteral_length]; omega) 8 cl
  refine ⟨c4, (s1.seq (s2.seq (s3.seq (s4.seq (xok_skip _))))).mono ?_, ?_, ?_, ?_, ?_, by rw [e5], ?_⟩
  · rw [hlen]; omega
  · rw [e1, List.drop_eq_nil_of_le (Nat.le_refl _)]; rfl
  · rw [e2]; simp [RAM.clauseCode]
  · rw [e3]; simp [RAM.clauseCode]
  · rw [e6 pCNT (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      r3 pCNT (by decide), r2 pCNT (by decide) (by decide) (by decide) (by decide)]
    simp [XConfig.setReg, hone]
  · intro i ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩
    rw [e6 i a6 a7 a8 a1 a3 a2 a4, r3 i a4, r2 i a6 a1 a3 a2]; simp [XConfig.setReg, a5]

def parseCNF : XStmt :=
  xseqs [.const pONE 1, .const pTWO 2, readNat pCNT, .store pZ pCNT, .const pP 2, .loop pCNT parseClause]

theorem encodeClause_length_pos (cl : Clause) : 1 ≤ (encodeClause cl).length := by
  simp [encodeClause, writeList]; omega

theorem xok_parseCNF (f : CNF) (rest : List Bool) (c : XConfig) (hin : c.inp = encode f ++ rest)
    (hm : c.mem = fun _ => 0) (hz : c.reg pZ = 0) :
    ∃ c', XOk parseCNF c c' (14 * ((encode f).length + 1)) ∧ c'.inp = rest ∧ c'.mem = memOf (RAM.ramInput f) ∧
      c'.out = c.out ∧ c'.reg pONE = 1 ∧ c'.reg pTWO = 2 ∧ c'.reg pP = 2 * (RAM.ramInput f).length ∧
      ∀ i, ParseFree i → i ≠ pONE → i ≠ pTWO → c'.reg i = c.reg i := by
  have s1a := xok_const pONE 1 c
  have s1 := xok_const pTWO 2 (c.setReg pONE 1)
  generalize hc2 : (c.setReg pONE 1).setReg pTWO 2 = c2 at s1
  have c2one : c2.reg pONE = 1 := by rw [← hc2]; simp [XConfig.setReg]
  have c2two : c2.reg pTWO = 2 := by rw [← hc2]; simp [XConfig.setReg]
  have c2r : ∀ i, i ≠ pONE → i ≠ pTWO → c2.reg i = c.reg i := by
    intro i h1 h2; rw [← hc2]; simp [XConfig.setReg, h1, h2]
  obtain ⟨c3, s3, v3, i3, m3, o3, r3⟩ := xok_readNat pCNT (by decide) (by decide) (by decide) (by decide) c2 f.length
    (writeValues encodeClause f ++ rest) (by rw [← hc2]; simp [XConfig.setReg, hin, encode, writeList]) c2one
  have s4 := xok_store pZ pCNT c3
  have s5 := xok_const pP 2 (c3.setMem (c3.reg pZ) (c3.reg pCNT))
  generalize hc5 : (c3.setMem (c3.reg pZ) (c3.reg pCNT)).setReg pP 2 = c5 at s5
  have z3 : c3.reg pZ = 0 := by
    rw [r3 pZ (by decide) (by decide) (by decide) (by decide), c2r pZ (by decide) (by decide), hz]
  have c5m : c5.mem = memOf [f.length] := by
    rw [← hc5]; simp only [XConfig.setReg, XConfig.setMem, z3, v3, m3]
    rw [← hc2]; simp only [XConfig.setReg, hm]
    have := memOf_snoc [] f.length; rw [memOf_nil] at this; simpa using this
  have c5P : c5.reg pP = 2 * [f.length].length := by rw [← hc5]; simp [XConfig.setReg]
  have c5r : ∀ i, i ≠ pP → c5.reg i = c3.reg i := by intro i hi; rw [← hc5]; simp [XConfig.setReg, XConfig.setMem, hi]
  let I : List Clause → XConfig → Prop := fun pre d =>
    d.inp = writeValues encodeClause (f.drop pre.length) ++ rest ∧
      d.mem = memOf (f.length :: pre.flatMap RAM.clauseCode) ∧
      d.reg pP = 2 * (f.length :: pre.flatMap RAM.clauseCode).length ∧ d.reg pCNT = f.length - pre.length ∧
      d.reg pONE = 1 ∧ d.reg pTWO = 2 ∧ d.out = c.out ∧ ∀ i, ParseFree i → i ≠ pONE → i ≠ pTWO → d.reg i = c.reg i
  have hI0 : I [] c5 := by
    refine ⟨by rw [← hc5]; simp [XConfig.setReg, XConfig.setMem, i3], by rw [c5m]; simp, by rw [c5P]; simp, ?_, ?_, ?_,
      by rw [← hc5]; simp [XConfig.setReg, XConfig.setMem, o3, ← hc2], fun i hi h1 h2 => ?_⟩
    · rw [c5r pCNT (by decide), v3]; simp
    · rw [c5r pONE (by decide), r3 pONE (by decide) (by decide) (by decide) (by decide), c2one]
    · rw [c5r pTWO (by decide), r3 pTWO (by decide) (by decide) (by decide) (by decide), c2two]
    · obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := hi
      rw [c5r i a4, r3 i a5 a1 a3 a2, c2r i h1 h2]
  obtain ⟨c6, s6, hI6⟩ := xok_listLoop (a := pCNT) (body := parseClause) f I (fun cl => 13 * (encodeClause cl).length)
    (by
      intro pre cl suf d hp ⟨d1, d2, d3, d4, d5, d6, d7, d8⟩
      have hl : pre.length < f.length := by have := congrArg List.length hp; simp at this; omega
      refine ⟨by rw [d4]; omega, ?_⟩
      rw [writeValues_drop encodeClause hp] at d1
      obtain ⟨d', s', i', m', p', n', o', r'⟩ := xok_parseClause cl (writeValues encodeClause suf ++ rest) d _
        (by rw [d1, List.append_assoc]) d3 d2 d5 d6
      refine ⟨d', s', ?_, ?_, ?_, ?_, ?_, ?_, by rw [o', d7], fun i hi h1 h2 => by rw [r' i hi, d8 i hi h1 h2]⟩
      · rw [i', show f.drop (pre ++ [cl]).length = suf by subst hp; simp]
      · rw [m']; simp
      · rw [p']; simp
      · rw [n', d4]; simp; omega
      · rw [r' pONE (by decide), d5]
      · rw [r' pTWO (by decide), d6])
    (by intro d ⟨_, _, _, d4, _⟩; rw [d4]; simp)
    c5 hI0
  obtain ⟨e1, e2, e3, -, e5, e6, e7, e8⟩ := hI6
  have hlen : (encode f).length = f.length + 1 + (writeValues encodeClause f).length := by
    simp [encode, writeList]
  have hsum := sum_cost_le encodeClause encodeClause_length_pos 13 f
  refine ⟨c6, (s1a.seq (s1.seq (s3.seq (s4.seq (s5.seq (s6.seq (xok_skip _))))))).mono ?_, ?_, ?_, e7, e5, e6,
    by rw [e3]; rfl, e8⟩
  · rw [hlen]; omega
  · rw [e1, List.drop_eq_nil_of_le (Nat.le_refl _)]; rfl
  · rw [e2]; rfl

end STACS2027.Sim

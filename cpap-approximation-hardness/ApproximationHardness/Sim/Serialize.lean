module

public import ApproximationHardness.Sim.Parse
import Lean.Elab.Tactic.Omega

/-!
# Writing the code of a formula

`serCNF` reads `ramInput g` from the odd memory cells `1, 3, 5, …` (where `tr` puts the output of a
RAM program) and writes the code `encode g` as output bits (`xok_serCNF`), in time linear in the
length of the code. `serBits` writes the numbers of the odd cells as bits.
-/

@[expose] public section

namespace STACS2027.Sim

open Complexity.SAT

@[simp] abbrev sQ : Nat := 120
@[simp] abbrev sCNT : Nat := 122
@[simp] abbrev sCL : Nat := 124
@[simp] abbrev sV : Nat := 125
@[simp] abbrev sS : Nat := 126
@[simp] abbrev sY : Nat := 127
@[simp] abbrev sONE : Nat := 128
@[simp] abbrev sTWO : Nat := 129
@[simp] abbrev sZ : Nat := 130

/-- The odd cells hold `L`. -/
def Buf (L : List Nat) (d : XConfig) : Prop := ∀ j, d.mem (2 * j + 1) = L.getD j 0

/-- Write the unary code of `x`. -/
def emitNat (x : Nat) : XStmt := xseqs [.add sY x sZ, .loop sY (.seq (.sub sY sY sONE) (.emit sONE)), .emit sZ]

theorem xok_emitNat (x : Nat) (_hx : x ≠ sY) (c : XConfig) (hone : c.reg sONE = 1) (hz : c.reg sZ = 0) :
    ∃ c', XOk (emitNat x) c c' (3 * c.reg x + 4) ∧ c'.out = c.out ++ writeNat (c.reg x) ∧ c'.mem = c.mem ∧
      c'.inp = c.inp ∧ ∀ i, i ≠ sY → c'.reg i = c.reg i := by
  have s1 := xok_add sY x sZ c
  let I : List Unit → XConfig → Prop := fun pre d =>
    d.reg sY = c.reg x - pre.length ∧ d.out = c.out ++ List.replicate pre.length true ∧ d.mem = c.mem ∧
      d.inp = c.inp ∧ ∀ i, i ≠ sY → d.reg i = c.reg i
  obtain ⟨c2, s2, e1, e2, e3, e4, e5⟩ := xok_listLoop (a := sY) (body := .seq (.sub sY sY sONE) (.emit sONE))
    (List.replicate (c.reg x) ()) I (fun _ => 2)
    (by
      intro pre u suf d hp ⟨d1, d2, d3, d4, d5⟩
      have hl : pre.length < c.reg x := by have := congrArg List.length hp; simp at this; omega
      refine ⟨by rw [d1]; omega, _, (xok_sub sY sY sONE d).seq (xok_emit sONE _), ?_, ?_, ?_, ?_, ?_⟩
      · simp [XConfig.setReg, XConfig.emit, d1, d5 sONE (by decide), hone]; omega
      · simp [XConfig.setReg, XConfig.emit, d2, d5 sONE (by decide), hone, List.replicate_succ']
      · simp [XConfig.setReg, XConfig.emit, d3]
      · simp [XConfig.setReg, XConfig.emit, d4]
      · intro i hi; simp [XConfig.setReg, XConfig.emit, hi, d5 i hi])
    (by intro d ⟨d1, _⟩; rw [d1]; simp)
    (c.setReg sY (c.reg x + c.reg sZ))
    ⟨by simp [XConfig.setReg, hz], by simp [XConfig.setReg], rfl, rfl, fun i hi => by simp [XConfig.setReg, hi]⟩
  simp only [List.length_replicate] at e2
  have s3 := xok_emit sZ c2
  refine ⟨_, (s1.seq (s2.seq (s3.seq (xok_skip _)))).mono ?_, ?_, by simp [XConfig.emit, e3], by simp [XConfig.emit, e4],
    fun i hi => by simp [XConfig.emit, e5 i hi]⟩
  · rw [sum_const_map, List.length_replicate]; omega
  · simp [XConfig.emit, e2, e5 sZ (by decide), hz, writeNat_eq]

/-- Read the next number of the buffer into `x`. -/
def readBuf (x : Nat) : XStmt := .seq (.load x sQ) (.add sQ sQ sTWO)

theorem xok_readBuf (x : Nat) (hx : x ≠ sQ) (hx2 : x ≠ sTWO) (c : XConfig) (L : List Nat) (hb : Buf L c) (i : Nat)
    (hq : c.reg sQ = 2 * i + 1) (htwo : c.reg sTWO = 2) :
    ∃ c', XOk (readBuf x) c c' 2 ∧ c'.reg x = L.getD i 0 ∧ c'.reg sQ = 2 * (i + 1) + 1 ∧ Buf L c' ∧
      c'.out = c.out ∧ c'.inp = c.inp ∧ ∀ j, j ≠ x → j ≠ sQ → c'.reg j = c.reg j := by
  refine ⟨_, (xok_load x sQ c).seq (xok_add sQ sQ sTWO _), ?_, ?_, fun j => by simp [XConfig.setReg]; exact hb j,
    rfl, rfl, fun j h1 h2 => by simp [XConfig.setReg, h1, h2]⟩
  · simp only [XConfig.setReg, ite_eq_right hx, ite_true, hq]; exact hb i
  · simp only [XConfig.setReg, ite_true, ite_eq_right (Ne.symm hx), ite_eq_right (show sTWO ≠ x from Ne.symm hx2), hq, htwo]
    omega

theorem getD_of_drop {L r : List Nat} {i a : Nat} (h : L.drop i = a :: r) : L.getD i 0 = a ∧ L.drop (i + 1) = r := by
  constructor
  · have : L[i]? = some a := by
      rw [← List.head?_drop]; rw [h]; rfl
    simp [List.getD_eq_getElem?_getD, this]
  · rw [← List.drop_drop, h]; rfl

/-! ### Literals, clauses, formulas -/

def serLit : XStmt := xseqs [.sub sCL sCL sONE, readBuf sV, readBuf sS, .emit sS, emitNat sV]

/-- The constants of the serializer. -/
def SerConst (d : XConfig) : Prop := d.reg sONE = 1 ∧ d.reg sTWO = 2 ∧ d.reg sZ = 0

/-- A register the serializer does not write. -/
abbrev SerFree (i : Nat) : Prop := i ≠ sQ ∧ i ≠ sCNT ∧ i ≠ sCL ∧ i ≠ sV ∧ i ≠ sS ∧ i ≠ sY

theorem xok_serLit (l : Literal) (L r : List Nat) (c : XConfig) (hb : Buf L c) (i : Nat) (hq : c.reg sQ = 2 * i + 1)
    (hL : L.drop i = RAM.litCode l ++ r) (hk : SerConst c) :
    ∃ c', XOk serLit c c' (3 * (encodeLiteral l).length + 5) ∧ c'.out = c.out ++ encodeLiteral l ∧
      c'.reg sQ = 2 * (i + 2) + 1 ∧ c'.reg sCL = c.reg sCL - 1 ∧ Buf L c' ∧ c'.inp = c.inp ∧
      ∀ j, j ≠ sQ → j ≠ sCL → j ≠ sV → j ≠ sS → j ≠ sY → c'.reg j = c.reg j := by
  obtain ⟨k1, k2, k3⟩ := hk
  simp only [RAM.litCode, List.cons_append, List.nil_append] at hL
  obtain ⟨g1, hL1⟩ := getD_of_drop hL
  obtain ⟨g2, -⟩ := getD_of_drop hL1
  have s1 := xok_sub sCL sCL sONE c
  generalize hc1 : c.setReg sCL (c.reg sCL - c.reg sONE) = c1 at s1
  have c1r : ∀ j, j ≠ sCL → c1.reg j = c.reg j := by intro j hj; rw [← hc1]; simp [XConfig.setReg, hj]
  have c1b : Buf L c1 := by rw [← hc1]; exact hb
  obtain ⟨c2, s2, v2, q2, b2, o2, n2, r2⟩ := xok_readBuf sV (by decide) (by decide) c1 L c1b i
    (by rw [c1r sQ (by decide), hq]) (by rw [c1r sTWO (by decide), k2])
  obtain ⟨c3, s3, v3, q3, b3, o3, n3, r3⟩ := xok_readBuf sS (by decide) (by decide) c2 L b2 (i + 1) q2
    (by rw [r2 sTWO (by decide) (by decide), c1r sTWO (by decide), k2])
  have s4 := xok_emit sS c3
  obtain ⟨c5, s5, o5, m5, n5, r5⟩ := xok_emitNat sV (by decide) (c3.emit sS)
    (by simp [XConfig.emit, r3 sONE (by decide) (by decide), r2 sONE (by decide) (by decide), c1r sONE (by decide), k1])
    (by simp [XConfig.emit, r3 sZ (by decide) (by decide), r2 sZ (by decide) (by decide), c1r sZ (by decide), k3])
  have eV : (c3.emit sS).reg sV = l.var := by
    show c3.reg sV = l.var; rw [r3 sV (by decide) (by decide), v2, g1]
  have eS : c3.reg sS = RAM.signCode l := by rw [v3, g2]
  refine ⟨c5, (s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (xok_skip _)))))).mono ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [eV, encodeLiteral_length]; omega
  · rw [o5, eV]
    show c3.out ++ [decide (c3.reg sS ≠ 0)] ++ writeNat l.var = c.out ++ encodeLiteral l
    rw [eS, o3, o2, ← hc1]
    cases hp : l.positive <;> simp [RAM.signCode, hp, encodeLiteral, XConfig.setReg]
  · rw [r5 sQ (by decide)]; simp [XConfig.emit, q3]
  · rw [r5 sCL (by decide)]; simp [XConfig.emit, r3 sCL (by decide) (by decide), r2 sCL (by decide) (by decide),
      ← hc1, XConfig.setReg, k1]
  · intro j; rw [m5]; simp [XConfig.emit]; exact b3 j
  · rw [n5]; simp [XConfig.emit, n3, n2, ← hc1, XConfig.setReg]
  · intro j a1 a2 a3 a4 a5
    rw [r5 j a5]; simp [XConfig.emit, r3 j a4 a1, r2 j a3 a1, c1r j a2]

theorem writeValues_append {α : Type} (enc : α → List Bool) (xs ys : List α) :
    writeValues enc (xs ++ ys) = writeValues enc xs ++ writeValues enc ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [writeValues_cons, ih]

theorem flatMap_litCode_length (cl : Clause) : (cl.flatMap RAM.litCode).length = 2 * cl.length := by
  induction cl with
  | nil => rfl
  | cons l cl ih => simp [RAM.litCode] at ih ⊢; omega

theorem sum_lit_cost (cl : Clause) :
    (cl.map fun l => 3 * (encodeLiteral l).length + 5 + 1).sum ≤ 6 * (writeValues encodeLiteral cl).length := by
  induction cl with
  | nil => simp [writeValues]
  | cons l cl ih =>
    simp only [List.map_cons, List.sum_cons, writeValues_cons, List.length_append]
    have := encodeLiteral_length l
    omega

theorem sum_clause_cost (g : CNF) :
    (g.map fun cl => 6 * (encodeClause cl).length + 3 + 1).sum ≤ 10 * (writeValues encodeClause g).length := by
  induction g with
  | nil => simp [writeValues]
  | cons cl g ih =>
    simp only [List.map_cons, List.sum_cons, writeValues_cons, List.length_append]
    have := encodeClause_length_pos cl
    omega

def serClause : XStmt := xseqs [.sub sCNT sCNT sONE, readBuf sCL, emitNat sCL, .loop sCL serLit]

theorem xok_serClause (cl : Clause) (L r : List Nat) (c : XConfig) (hb : Buf L c) (i : Nat) (hq : c.reg sQ = 2 * i + 1)
    (hL : L.drop i = RAM.clauseCode cl ++ r) (hk : SerConst c) :
    ∃ c', XOk serClause c c' (6 * (encodeClause cl).length + 3) ∧ c'.out = c.out ++ encodeClause cl ∧
      c'.reg sQ = 2 * (i + (RAM.clauseCode cl).length) + 1 ∧ c'.reg sCNT = c.reg sCNT - 1 ∧ Buf L c' ∧
      c'.inp = c.inp ∧ ∀ j, SerFree j → c'.reg j = c.reg j := by
  obtain ⟨k1, k2, k3⟩ := hk
  simp only [RAM.clauseCode, List.cons_append] at hL
  obtain ⟨g1, hL1⟩ := getD_of_drop hL
  have s1 := xok_sub sCNT sCNT sONE c
  generalize hc1 : c.setReg sCNT (c.reg sCNT - c.reg sONE) = c1 at s1
  have c1r : ∀ j, j ≠ sCNT → c1.reg j = c.reg j := by intro j hj; rw [← hc1]; simp [XConfig.setReg, hj]
  obtain ⟨c2, s2, v2, q2, b2, o2, n2, r2⟩ := xok_readBuf sCL (by decide) (by decide) c1 L (by rw [← hc1]; exact hb) i
    (by rw [c1r sQ (by decide), hq]) (by rw [c1r sTWO (by decide), k2])
  rw [g1] at v2
  obtain ⟨c3, s3, o3, m3, n3, r3⟩ := xok_emitNat sCL (by decide) c2
    (by rw [r2 sONE (by decide) (by decide), c1r sONE (by decide), k1])
    (by rw [r2 sZ (by decide) (by decide), c1r sZ (by decide), k3])
  have hk3 : SerConst c3 := ⟨by rw [r3 sONE (by decide), r2 sONE (by decide) (by decide), c1r sONE (by decide), k1],
    by rw [r3 sTWO (by decide), r2 sTWO (by decide) (by decide), c1r sTWO (by decide), k2],
    by rw [r3 sZ (by decide), r2 sZ (by decide) (by decide), c1r sZ (by decide), k3]⟩
  let I : List Literal → XConfig → Prop := fun pre d =>
    Buf L d ∧ d.reg sQ = 2 * (i + 1 + (pre.flatMap RAM.litCode).length) + 1 ∧
      d.out = c.out ++ writeNat cl.length ++ writeValues encodeLiteral pre ∧ d.reg sCL = cl.length - pre.length ∧
      SerConst d ∧ d.inp = c.inp ∧ ∀ j, j ≠ sQ → j ≠ sCL → j ≠ sV → j ≠ sS → j ≠ sY → d.reg j = c3.reg j
  have hI0 : I [] c3 := ⟨fun j => by rw [m3]; exact b2 j, by rw [r3 sQ (by decide), q2]; simp,
    by rw [o3, v2, o2, ← hc1]; simp [XConfig.setReg, writeValues],
    by rw [r3 sCL (by decide), v2]; simp, hk3, by rw [n3, n2, ← hc1]; rfl, fun _ _ _ _ _ _ => rfl⟩
  obtain ⟨c4, s4, hI4⟩ := xok_listLoop (a := sCL) (body := serLit) cl I (fun l => 3 * (encodeLiteral l).length + 5)
    (by
      intro pre l suf d hp ⟨d1, d2, d3, d4, d5, d6, d7⟩
      have hl : pre.length < cl.length := by have := congrArg List.length hp; simp at this; omega
      refine ⟨by rw [d4]; omega, ?_⟩
      have hd : L.drop (i + 1 + (pre.flatMap RAM.litCode).length) = RAM.litCode l ++ (suf.flatMap RAM.litCode ++ r) := by
        rw [← List.drop_drop, hL1, ← hp, List.flatMap_append, List.flatMap_cons, List.append_assoc,
          List.drop_left' rfl, List.append_assoc]
      obtain ⟨d', s', o', q', n', b', i', r'⟩ := xok_serLit l L _ d d1 _ d2 hd d5
      refine ⟨d', s', b', ?_, ?_, ?_, ?_, by rw [i', d6], fun j a1 a2 a3 a4 a5 => by
        rw [r' j a1 a2 a3 a4 a5, d7 j a1 a2 a3 a4 a5]⟩
      · rw [q']; simp [List.flatMap_append, RAM.litCode]; omega
      · rw [o', d3]; simp [writeValues_append, writeValues]
      · rw [n', d4]; simp; omega
      · exact ⟨by rw [r' sONE (by decide) (by decide) (by decide) (by decide) (by decide)]; exact d5.1,
          by rw [r' sTWO (by decide) (by decide) (by decide) (by decide) (by decide)]; exact d5.2.1,
          by rw [r' sZ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact d5.2.2⟩)
    (by intro d ⟨_, _, _, d4, _⟩; rw [d4]; simp)
    c3 hI0
  obtain ⟨e1, e2, e3, -, -, e6, e7⟩ := hI4
  have hlen : (encodeClause cl).length = cl.length + 1 + (writeValues encodeLiteral cl).length := by
    simp [encodeClause, writeList]
  have hsum := sum_lit_cost cl
  refine ⟨c4, (s1.seq (s2.seq (s3.seq (s4.seq (xok_skip _))))).mono ?_, ?_, ?_, ?_, e1, ?_, ?_⟩
  · rw [hlen, v2]; omega
  · rw [e3]; simp [encodeClause, writeList]
  · rw [e2]; simp [RAM.clauseCode]; omega
  · rw [e7 sCNT (by decide) (by decide) (by decide) (by decide) (by decide), r3 sCNT (by decide),
      r2 sCNT (by decide) (by decide), ← hc1]; simp [XConfig.setReg, k1]
  · rw [e6]
  · intro j ⟨a1, a2, a3, a4, a5, a6⟩
    rw [e7 j a1 a3 a4 a5 a6, r3 j a6, r2 j a3 a1, c1r j a2]

def serCNF : XStmt := xseqs [.const sONE 1, .const sTWO 2, .const sQ 1, readBuf sCNT, emitNat sCNT, .loop sCNT serClause]

theorem xok_serCNF (g : CNF) (c : XConfig) (hb : Buf (RAM.ramInput g) c) (hz : c.reg sZ = 0) :
    ∃ c', XOk serCNF c c' (10 * (encode g).length + 1) ∧ c'.out = c.out ++ encode g ∧ c'.inp = c.inp := by
  have s1 := xok_const sONE 1 c
  have s2 := xok_const sTWO 2 (c.setReg sONE 1)
  have s3 := xok_const sQ 1 ((c.setReg sONE 1).setReg sTWO 2)
  generalize hc3 : ((c.setReg sONE 1).setReg sTWO 2).setReg sQ 1 = c3 at s3
  have hk3 : SerConst c3 := ⟨by rw [← hc3]; simp [XConfig.setReg], by rw [← hc3]; simp [XConfig.setReg],
    by rw [← hc3]; simp [XConfig.setReg, hz]⟩
  have hb3 : Buf (RAM.ramInput g) c3 := by rw [← hc3]; exact hb
  have hL0 : (RAM.ramInput g).drop 0 = g.length :: g.flatMap RAM.clauseCode := rfl
  obtain ⟨g0, hL1⟩ := getD_of_drop hL0
  obtain ⟨c4, s4, v4, q4, b4, o4, n4, r4⟩ := xok_readBuf sCNT (by decide) (by decide) c3 _ hb3 0
    (by rw [← hc3]; simp [XConfig.setReg]) hk3.2.1
  rw [g0] at v4
  obtain ⟨c5, s5, o5, m5, n5, r5⟩ := xok_emitNat sCNT (by decide) c4
    (by rw [r4 sONE (by decide) (by decide)]; exact hk3.1) (by rw [r4 sZ (by decide) (by decide)]; exact hk3.2.2)
  have hk5 : SerConst c5 := ⟨by rw [r5 sONE (by decide), r4 sONE (by decide) (by decide)]; exact hk3.1,
    by rw [r5 sTWO (by decide), r4 sTWO (by decide) (by decide)]; exact hk3.2.1,
    by rw [r5 sZ (by decide), r4 sZ (by decide) (by decide)]; exact hk3.2.2⟩
  let I : List Clause → XConfig → Prop := fun pre d =>
    Buf (RAM.ramInput g) d ∧ d.reg sQ = 2 * (1 + (pre.flatMap RAM.clauseCode).length) + 1 ∧
      d.out = c.out ++ writeNat g.length ++ writeValues encodeClause pre ∧ d.reg sCNT = g.length - pre.length ∧
      SerConst d ∧ d.inp = c.inp
  have hI0 : I [] c5 := ⟨fun j => by rw [m5]; exact b4 j, by rw [r5 sQ (by decide), q4]; simp,
    by rw [o5, v4, o4, ← hc3]; simp [XConfig.setReg, writeValues], by rw [r5 sCNT (by decide), v4]; simp, hk5,
    by rw [n5, n4, ← hc3]; rfl⟩
  obtain ⟨c6, s6, hI6⟩ := xok_listLoop (a := sCNT) (body := serClause) g I (fun cl => 6 * (encodeClause cl).length + 3)
    (by
      intro pre cl suf d hp ⟨d1, d2, d3, d4, d5, d6⟩
      have hl : pre.length < g.length := by have := congrArg List.length hp; simp at this; omega
      refine ⟨by rw [d4]; omega, ?_⟩
      have hd : (RAM.ramInput g).drop (1 + (pre.flatMap RAM.clauseCode).length) =
          RAM.clauseCode cl ++ suf.flatMap RAM.clauseCode := by
        rw [← List.drop_drop, hL1, ← hp, List.flatMap_append, List.flatMap_cons, List.drop_left' rfl]
      obtain ⟨d', s', o', q', n', b', i', r'⟩ := xok_serClause cl _ _ d d1 _ d2 hd d5
      refine ⟨d', s'.mono (by have := encodeClause_length_pos cl; omega), b', ?_, ?_, ?_, ?_, by rw [i', d6]⟩
      · rw [q']; simp [List.flatMap_append]; omega
      · rw [o', d3]; simp [writeValues_append, writeValues]
      · rw [n', d4]; simp; omega
      · exact ⟨by rw [r' sONE ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩]; exact d5.1,
          by rw [r' sTWO ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩]; exact d5.2.1,
          by rw [r' sZ ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩]; exact d5.2.2⟩)
    (by intro d ⟨_, _, _, d4, _⟩; rw [d4]; simp)
    c5 hI0
  obtain ⟨-, -, e3, -, -, e6⟩ := hI6
  have hlen : (encode g).length = g.length + 1 + (writeValues encodeClause g).length := by
    simp [encode, writeList]
  have hsum := sum_clause_cost g
  refine ⟨c6, (s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq (xok_skip _))))))).mono ?_, ?_, e6⟩
  · rw [hlen, v4]; omega
  · rw [e3]; simp [encode, writeList]

end STACS2027.Sim

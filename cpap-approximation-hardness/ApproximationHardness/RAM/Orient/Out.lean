module

public import ApproximationHardness.RAM.Orient.Clause
import Lean.Elab.Tactic.Omega

/-!
# The orientation program: the output pass
-/

@[expose] public section

namespace STACS2027.RAM

open Complexity.SAT Complexity.Planar.Comb PlanarAssembly
open Stmt

/-! ### The three stages of one output step -/

def orOutA : List Stmt :=
  [sub OR.cnt OR.cnt Reg.one,
    add OR.a OR.B OR.i, add OR.a OR.a OR.i, add OR.a OR.a OR.i, add OR.a OR.a OR.i,
    Stmt.load OR.port OR.a, add OR.a OR.a Reg.one, Stmt.load OR.v OR.a, add OR.a OR.a Reg.one,
    add OR.a OR.a Reg.one, Stmt.load OR.cs OR.a,
    const OR.a1 0, ifz OR.port (const OR.a1 1) skip]

def orOutC : List Stmt :=
  [add OR.sm OR.a1 OR.vs, add OR.sm OR.sm OR.cs,
    sub OR.t OR.sm Reg.one, sub OR.t2 Reg.one OR.sm, add OR.t OR.t OR.t2,
    ifz OR.t (write Reg.one) (seqs [sub OR.t OR.sm OR.three, sub OR.t2 OR.three OR.sm, add OR.t OR.t OR.t2,
      ifz OR.t (write Reg.one) (write Reg.zero)]),
    add OR.i OR.i Reg.one]

theorem orOut_eq : orOut = seqs ((orOutA ++ orVarSign) ++ orOutC) := rfl

theorem run_orOut (c : Config) :
    run orOut c = run (seqs orOutC) (run (seqs orVarSign) (run (seqs orOutA) c)) := by
  rw [orOut_eq, run_seqs_app, run_seqs_app]

theorem orOutA_run (f : CNF) (c : Config) (hL : Layout f c) :
    (run (seqs orOutA) c).reg OR.port = c.mem (orB f + 4 * c.reg OR.i) ∧
      (run (seqs orOutA) c).reg OR.v = c.mem (orB f + 4 * c.reg OR.i + 1) ∧
      (run (seqs orOutA) c).reg OR.cs = c.mem (orB f + 4 * c.reg OR.i + 3) ∧
      (run (seqs orOutA) c).reg OR.a1 = (if c.mem (orB f + 4 * c.reg OR.i) = 0 then 1 else 0) ∧
      (run (seqs orOutA) c).reg OR.cnt = c.reg OR.cnt - 1 ∧
      (run (seqs orOutA) c).mem = c.mem ∧ (run (seqs orOutA) c).out = c.out ∧
      ∀ r, r ∉ regsW (seqs orOutA) → (run (seqs orOutA) c).reg r = c.reg r := by
  have hone := hL.one
  have hB := hL.B
  have e3 : ∀ o, orB f + o + o + o + o + 1 + 1 + 1 = orB f + 4 * o + 3 := fun o => by omega
  have e5 : ∀ o, orB f + o + o + o + o + 1 = orB f + 4 * o + 1 := fun o => by omega
  have e1 : ∀ o, orB f + o + o + o + o = orB f + 4 * o := fun o => by omega
  refine ⟨?_, ?_, ?_, ?_, ?_, run_mem_frame _ _ (by decide), run_out_frame _ _ (by decide),
    fun r h => run_reg_frame _ _ _ h⟩ <;>
  · simp +decide only [orOutA, run_seqs_cons, run_seqs_nil, run, setReg_reg, setReg_mem, reg_ite,
      ↓reduceIte, ite_self, hone, hB, e1]

/-- The variable sign computed by `orVarSign`, on the memory `M`. -/
def vsOf (f : CNF) (M : Nat → Nat) (v : Nat) : Nat :=
  if M (orE f + 2 * v + 1) = 0 then 0
  else if M (orB f + 2 * M ((ramInput f).length + 2 * (M (orE f + 2 * v + 1) - 1))) = 2 then 1 else 0

theorem orVarSign_run (f : CNF) (c : Config) (hL : Layout f c) :
    (run (seqs orVarSign) c).reg OR.vs = vsOf f c.mem (c.reg OR.v) ∧
      (run (seqs orVarSign) c).mem = c.mem ∧ (run (seqs orVarSign) c).out = c.out ∧
      ∀ r, r ∉ regsW (seqs orVarSign) → (run (seqs orVarSign) c).reg r = c.reg r := by
  have hone := hL.one
  have hB := hL.B
  have hE := hL.E
  have hN := hL.N
  have h2 := hL.two
  refine ⟨?_, run_mem_frame _ _ (by decide), run_out_frame _ _ (by decide), fun r h => run_reg_frame _ _ _ h⟩
  have e1 : orE f + c.reg OR.v + c.reg OR.v + 1 = orE f + 2 * c.reg OR.v + 1 := by omega
  unfold vsOf
  by_cases hq : c.mem (orE f + 2 * c.reg OR.v + 1) = 0
  · simp +decide only [orVarSign, run_seqs_cons, run_seqs_nil, run, setReg_reg, setReg_mem, 
      ↓reduceIte, hone, hE, e1, hq]
  · simp +decide only [orVarSign, run_seqs_cons, run_seqs_nil, run, setReg_reg, setReg_mem, reg_ite,
      ↓reduceIte, hone, hB, hE, hN, h2, e1, hq]
    generalize c.mem (orE f + 2 * c.reg OR.v + 1) = q at *
    have e2 : ∀ x : Nat, (ramInput f).length + x + x = (ramInput f).length + 2 * x := fun x => by omega
    have e3 : ∀ x : Nat, orB f + x + x = orB f + 2 * x := fun x => by omega
    simp only [e2, e3]
    split <;> split <;> omega

theorem orOutC_run (f : CNF) (c : Config) (hL : Layout f c) (ha : c.reg OR.a1 ≤ 1) (hv : c.reg OR.vs ≤ 1)
    (hc : c.reg OR.cs ≤ 1) :
    (run (seqs orOutC) c).out =
        c.out ++ [if (c.reg OR.a1 + c.reg OR.vs + c.reg OR.cs) % 2 = 1 then 1 else 0] ∧
      (run (seqs orOutC) c).reg OR.i = c.reg OR.i + 1 ∧ (run (seqs orOutC) c).mem = c.mem ∧
      ∀ r, r ∉ regsW (seqs orOutC) → (run (seqs orOutC) c).reg r = c.reg r := by
  have hone := hL.one
  have hzero := hL.zero
  have h3 := hL.three
  refine ⟨?_, ?_, run_mem_frame _ _ (by decide), fun r h => run_reg_frame _ _ _ h⟩
  · generalize ea : c.reg OR.a1 = a at *
    generalize ev : c.reg OR.vs = v at *
    generalize ec : c.reg OR.cs = w at *
    rcases (show a = 0 ∨ a = 1 by omega) with rfl | rfl <;>
    rcases (show v = 0 ∨ v = 1 by omega) with rfl | rfl <;>
    rcases (show w = 0 ∨ w = 1 by omega) with rfl | rfl <;>
    simp +decide only [orOutC, run_seqs_cons, run_seqs_nil, run, setReg_reg, setReg_out, emit_out,
      emit_reg, ↓reduceIte, hone, hzero, h3, ea, ev, ec]
  · simp +decide only [orOutC, run_seqs_cons, run_seqs_nil, run, setReg_reg, emit_reg, 
      reg_ite, ↓reduceIte, ite_self, hone]

/-! ### The semantics of one output step -/

/-- The output number of occurrence `i`. -/
def bitNat (f : CNF) (rot : List Nat) (i : Nat) : Nat := if flipBit f (rotFun rot) i then 1 else 0

theorem portRead {f : CNF} {rot : List Nat} {M : Nat → Nat} (hM : MemInv f rot f.flatten M) (d : Nat) :
    M (orB f + 2 * d) = occPort f (d / 2) := by
  by_cases hd : d / 2 < f.flatten.length
  · rcases Nat.mod_two_eq_zero_or_one d with h | h
    · rw [show orB f + 2 * d = orB f + 4 * (d / 2) by omega]
      exact (hM.recs _ hd).1
    · rw [show orB f + 2 * d = orB f + 4 * (d / 2) + 2 by omega]
      exact (hM.recs _ hd).2.2.1
  · rw [hM.free _ (by omega), occPort_flat, List.getElem?_eq_none (by omega)]
    rfl

theorem occVar_lt (f : CNF) {i : Nat} (hi : i < f.flatten.length) : occVar f i < variableBound f := by
  rw [occVar_flat, List.getElem?_eq_getElem hi]
  exact literal_var_lt (List.getElem_mem hi)

theorem vsOf_eq {f : CNF} {rot : List Nat} {M : Nat → Nat} (hM : MemInv f rot f.flatten M)
    (_hrot : rot.length ≤ (ramInput f).length) {v : Nat} (hv : v < variableBound f) :
    vsOf f M v = if variableSign f (rotFun rot) v then 1 else 0 := by
  have hNl := ramInput_length_eq f
  unfold vsOf variableSign
  rw [hM.pos v hv, posCode_eq, occList_length]
  by_cases hp : positiveIndex f v < f.flatten.length
  · simp only [hp, ↓reduceIte, Nat.add_one_ne_zero, Nat.add_sub_cancel, decide_true, Bool.true_and]
    rw [hM.input ((ramInput f).length + 2 * positiveIndex f v) (by unfold orE; omega), orInput_getD_rot,
      portRead hM]
    unfold rotFun
    by_cases h2 : occPort f (rot.getD (2 * positiveIndex f v) 0 / 2) = 2 <;> simp []
  · simp only [hp, ↓reduceIte, decide_false, Bool.false_and, Bool.false_eq_true]

theorem csBit_le (f : CNF) (rot : List Nat) (i : Nat) : csBit f rot i ≤ 1 := by
  unfold csBit; split <;> omega

/-! ### The memory accesses of one output step -/

/-- The first stage reads the record `B + 4i`, `B + 4i + 1`, `B + 4i + 3`. -/
theorem orOutA_addrOK {S : Nat} (f : CNF) (c : Config) (hL : Layout f c) (hi : orB f + 4 * c.reg OR.i + 4 ≤ S) :
    AddrOK S (seqs orOutA) c := by
  simp +decide [orOutA, run, hL.one, hL.B]; omega

/-- The variable sign reads the cell `E + 2v + 1`, the rotation cell `N + 2 i₀` of the positive
occurrence `i₀`, and the record cell `B + 2d` of the dart `d` read there: below `orSpace f` when the
darts of the rotation list are below `2 |f.flatten|`. -/
theorem orVarSign_addrOK {S : Nat} (f : CNF) (rot : List Nat) (c : Config) (hL : Layout f c) {M : Nat → Nat}
    (hM : MemInv f rot f.flatten M) (hm : c.mem = M) (hv : c.reg OR.v < variableBound f)
    (hrv : ∀ x ∈ rot, x < 2 * f.flatten.length) (hS : orSpace f ≤ S) : AddrOK S (seqs orVarSign) c := by
  have hNl := ramInput_length_eq f
  have hSE : orE f + 2 * variableBound f + 4 * f.flatten.length ≤ S := hS
  have e1 : orE f + c.reg OR.v + c.reg OR.v + 1 = orE f + 2 * c.reg OR.v + 1 := by omega
  have hq := hM.pos _ hv
  rw [posCode_eq, occList_length] at hq
  by_cases hp : positiveIndex f (c.reg OR.v) < f.flatten.length
  · rw [ite_eq_left hp] at hq
    have hd : M ((ramInput f).length + positiveIndex f (c.reg OR.v) + positiveIndex f (c.reg OR.v)) <
        2 * f.flatten.length := by
      rw [hM.input _ (by unfold orE; omega), show (ramInput f).length + positiveIndex f (c.reg OR.v) +
        positiveIndex f (c.reg OR.v) = (ramInput f).length + 2 * positiveIndex f (c.reg OR.v) by omega,
        orInput_getD_rot, List.getD_eq_getElem?_getD]
      cases h : rot[2 * positiveIndex f (c.reg OR.v)]? with
      | none => simp only [Option.getD_none]; omega
      | some x => simp only [Option.getD_some]; exact hrv x (List.mem_of_getElem? h)
    simp +decide [orVarSign, run, hL.one, hL.E, hL.N, hL.B, hm, e1, hq]
    unfold orB orE at *; omega
  · rw [ite_eq_right hp] at hq
    simp +decide [orVarSign, run, hL.one, hL.E, hL.N, hL.B, hm, e1, hq]
    unfold orB orE at *; omega

/-- The invariant of the output loop after `j` occurrences. -/
structure OrOutInv (f : CNF) (rot : List Nat) (M : Nat → Nat) (j : Nat) (c : Config) : Prop where
  layout : Layout f c
  mem : c.mem = M
  i : c.reg OR.i = j
  out : c.out = (List.range j).map (bitNat f rot)

/-- One output step, within the space `S ≥ orSpace f` when the darts of `rot` are below `2 |f.flatten|`. -/
theorem orOut_step (f : CNF) (rot : List Nat) (hrot : rot.length ≤ (ramInput f).length) (M : Nat → Nat)
    (hM : MemInv f rot f.flatten M) {S : Nat} (hS : orSpace f ≤ S) (hrv : ∀ x ∈ rot, x < 2 * f.flatten.length) :
    ∀ j c, j < f.flatten.length → OrOutInv f rot M j c → c.reg OR.cnt = f.flatten.length - j →
      ∃ t c', ExecB S orOut c t c' ∧ t ≤ size orOut ∧ OrOutInv f rot M (j + 1) c' ∧
        c'.reg OR.cnt + 1 = c.reg OR.cnt := by
  intro j c hj ⟨hL, hm, hi, hout⟩ hcnt
  have hA : AddrOK S orOut c := by
    obtain ⟨-, a2, -, -, -, a6, -, a8⟩ := orOutA_run f c hL
    rw [orOut_eq, addrOK_seqs_append, addrOK_seqs_append]
    have hv : (run (seqs orOutA) c).reg OR.v < variableBound f := by
      rw [a2, hm, hi, (hM.recs j hj).2.1]; exact occVar_lt f hj
    refine ⟨⟨orOutA_addrOK f c hL (by rw [hi]; have : orSpace f = orB f + 4 * f.flatten.length := rfl; omega),
      orVarSign_addrOK f rot _ (hL.frame (fun r hr => a8 r (by revert r; decide))) hM (by rw [a6, hm]) hv hrv hS⟩,
      AddrOK.of_memFree rfl⟩
  obtain ⟨t, e, ht⟩ := exec_loopFree (S := S) (s := orOut) (by simp [orOut, seqs, LoopFree, orVarSign]) c hA
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := orOutA_run f c hL
  generalize hc1 : run (seqs orOutA) c = c1 at a1 a2 a3 a4 a5 a6 a7 a8
  have hL1 : Layout f c1 := hL.frame (fun r hr => a8 r (by revert r; decide))
  obtain ⟨b1, b2, b3, b4⟩ := orVarSign_run f c1 hL1
  generalize hc2 : run (seqs orVarSign) c1 = c2 at b1 b2 b3 b4
  have hL2 : Layout f c2 := hL1.frame (fun r hr => b4 r (by revert r; decide))
  have hrec := hM.recs j hj
  rw [hm, hi] at a1 a2 a3 a4
  rw [hrec.1] at a1 a4
  rw [hrec.2.1] at a2
  rw [hrec.2.2.2] at a3
  have hv := occVar_lt f hj
  have hvs : c2.reg OR.vs = if variableSign f (rotFun rot) (occVar f j) then 1 else 0 := by
    rw [b1, a6, hm, a2, vsOf_eq hM hrot hv]
  have ha1 : c2.reg OR.a1 = if occPort f j = 0 then 1 else 0 := by rw [b4 _ (by decide), a4]
  have hcs : c2.reg OR.cs = csBit f rot j := by rw [b4 _ (by decide), a3]
  obtain ⟨d1, d2, d3, d4⟩ := orOutC_run f c2 hL2 (by rw [ha1]; split <;> omega)
    (by rw [hvs]; split <;> omega) (by rw [hcs]; exact csBit_le f rot j)
  refine ⟨t, _, e, ht, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [run_orOut, hc1, hc2]
    exact hL2.frame (fun r hr => d4 r (by revert r; decide))
  · rw [run_orOut, hc1, hc2, d3, b2, a6, hm]
  · rw [run_orOut, hc1, hc2, d2, b4 _ (by decide), a8 _ (by decide), hi]
  · rw [run_orOut, hc1, hc2, d1, b3, a7, hout, List.range_succ, List.map_append]
    congr 2
    rw [ha1, hvs, hcs]
    unfold bitNat flipBit csBit
    have hz : (if occPort f j = 0 then 1 else 0) = (if (occPort f j == 0) = true then 1 else 0) := by simp
    rw [hz]
    generalize (occPort f j == 0) = b1
    generalize variableSign f (rotFun rot) (occVar f j) = b2
    generalize clauseSign f (rotFun rot) (oj f j) = b3
    cases b1 <;> cases b2 <;> cases b3 <;> rfl
  · rw [run_orOut, hc1, hc2, d4 _ (by decide), b4 _ (by decide), a5]
    omega

end STACS2027.RAM

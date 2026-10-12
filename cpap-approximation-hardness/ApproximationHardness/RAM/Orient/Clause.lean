module

public import ApproximationHardness.RAM.Orient.Lit
public import ApproximationHardness.RAM.Decode.Paths
import Lean.Elab.Tactic.Omega

/-!
# The orientation program: one clause
-/

@[expose] public section

namespace STACS2027.RAM

open Complexity.SAT Complexity.Planar.Comb PlanarAssembly

theorem flatMap_clauseCode_length (g : CNF) :
    (g.flatMap clauseCode).length = g.length + 2 * g.flatten.length := by
  induction g with
  | nil => rfl
  | cons c g ih => simp only [List.flatMap_cons, List.length_append, clauseCode_length, ih, List.flatten_cons,
      List.length_cons]; omega

theorem ramInput_length_eq (f : CNF) : (ramInput f).length = 1 + f.length + 2 * f.flatten.length := by
  simp only [ramInput, List.length_cons, flatMap_clauseCode_length]; omega

theorem orInput_getD_rot (f : CNF) (rot : List Nat) (d : Nat) :
    (orInput f rot).getD ((ramInput f).length + d) 0 = rot.getD d 0 := by
  simp only [orInput, List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_add_right _ _),
    Nat.add_sub_cancel_left]

theorem orInput_getD_left (f : CNF) (rot : List Nat) {a : Nat} (ha : a < (ramInput f).length) :
    (orInput f rot).getD a 0 = (ramInput f).getD a 0 := by
  simp only [orInput, List.getD_eq_getElem?_getD, List.getElem?_append_left ha]

/-- The clause-sign bit computed from the first occurrence `o` of a clause. -/
def csOf (rot : List Nat) (cl : Clause) (o : Nat) : Nat :=
  if cl.length = 3 ∧ rot.getD (2 * o + 1) 0 = 2 * (o + 2) + 1 then 1 else 0

theorem csBit_prefix {f pre suf : CNF} {cl : Clause} (h : pre ++ cl :: suf = f) (rot : List Nat)
    {t : Nat} (ht : t < cl.length) :
    csBit f rot (pre.flatten.length + t) = csOf rot cl pre.flatten.length := by
  unfold csBit csOf clauseSign
  rw [oj_prefix h ht, kl_prefix h, off_prefix (show pre ++ (cl :: suf) = f from h)]
  unfold rotFun
  by_cases h3 : cl.length = 3 <;> by_cases hr : rot.getD (2 * pre.flatten.length + 1) 0 =
    2 * (pre.flatten.length + 2) + 1 <;> simp [h3]

/-! ### The clause header -/

theorem orClausePre_run (f : CNF) (rot : List Nat) (c : Config) (cl : Clause) (w : List Nat)
    (hL : Layout f c) (hAt : At c (clauseCode cl ++ w))
    (hM : ∀ a, a < orE f → c.mem a = (orInput f rot).getD a 0)
    (hbound : cl.length = 3 → 2 * c.reg OR.occ + 1 < (ramInput f).length) :
    (run orClausePre c).reg OR.cnt = cl.length ∧
      (run orClausePre c).reg OR.cs = csOf rot cl (c.reg OR.occ) ∧
      (run orClausePre c).reg Reg.p = c.reg Reg.p + 1 ∧ (run orClausePre c).reg Reg.m = c.reg Reg.m - 1 ∧
      (run orClausePre c).mem = c.mem ∧ (run orClausePre c).out = c.out ∧
      ∀ r, r ∉ regsW orClausePre → (run orClausePre c).reg r = c.reg r := by
  have g0 : c.mem (c.reg Reg.p) = cl.length := by
    have := hAt 0 (by simp [clauseCode])
    simpa [clauseCode] using this
  have hone := hL.one
  have hzero := hL.zero
  have h3 := hL.three
  have h5 := hL.five
  have hN := hL.N
  refine ⟨?_, ?_, ?_, ?_, run_mem_frame _ _ (by decide), run_out_frame _ _ (by decide),
    fun r h => run_reg_frame _ _ _ h⟩
  · simp +decide only [orClausePre, run_seqs_cons, run_seqs_nil, run, setReg_reg, setReg_mem, reg_ite,
      ↓reduceIte, ite_self, g0, hzero, Nat.add_zero]
  · by_cases hl : cl.length = 3
    · have hx : c.mem ((ramInput f).length + c.reg OR.occ + c.reg OR.occ + 1) =
          rot.getD (2 * c.reg OR.occ + 1) 0 := by
        rw [hM _ (by have := hbound hl; unfold orE; omega),
          show (ramInput f).length + c.reg OR.occ + c.reg OR.occ + 1 =
            (ramInput f).length + (2 * c.reg OR.occ + 1) by omega, orInput_getD_rot]
      simp +decide only [orClausePre, run_seqs_cons, run_seqs_nil, run, setReg_reg, setReg_mem, reg_ite,
        ↓reduceIte, ite_self, g0, hone, h3, h5, hN, hl, Nat.sub_self, Nat.add_zero, hx]
      unfold csOf
      by_cases hr : rot.getD (2 * c.reg OR.occ + 1) 0 = 2 * (c.reg OR.occ + 2) + 1
      · simp only [hl, hr, and_self, ↓reduceIte]
        split <;> omega
      · simp only [hl, hr, and_false, ↓reduceIte]
        split <;> omega
    · have ht : cl.length - 3 + (3 - cl.length) ≠ 0 := by omega
      simp +decide only [orClausePre, run_seqs_cons, run_seqs_nil, run, setReg_reg, setReg_mem, 
        ↓reduceIte, g0, h3, ht]
      unfold csOf
      simp only [hl, false_and, ↓reduceIte]
  · simp +decide only [orClausePre, run_seqs_cons, run_seqs_nil, run, setReg_reg, setReg_mem, reg_ite,
      ↓reduceIte, ite_self, hone]
  · simp +decide only [orClausePre, run_seqs_cons, run_seqs_nil, run, setReg_reg, setReg_mem, reg_ite,
      ↓reduceIte, ite_self, hone]

/-- The clause header reads the length at `p` and, for three literals, the rotation cell
`N + 2 occ + 1`. -/
theorem orClausePre_addrOK {S : Nat} (f : CNF) (c : Config) (cl : Clause) (w : List Nat) (hL : Layout f c)
    (hAt : At c (clauseCode cl ++ w)) (hp : c.reg Reg.p < S)
    (hb : cl.length = 3 → (ramInput f).length + 2 * c.reg OR.occ + 1 < S) : AddrOK S orClausePre c := by
  have g0 : c.mem (c.reg Reg.p) = cl.length := by
    have := hAt 0 (by simp [clauseCode])
    simpa [clauseCode] using this
  simp +decide [orClausePre, run, hL.one, hL.three, hL.five, hL.N, g0]
  omega

/-! ### One clause -/

/-- The invariant of the clause pass after the clauses `pre`. -/
structure ClauseInv (f : CNF) (rot : List Nat) (pre : CNF) (c : Config) : Prop where
  layout : Layout f c
  mem : MemInv f rot pre.flatten c.mem
  occ : c.reg OR.occ = pre.flatten.length
  p : c.reg Reg.p = 1 + (pre.flatMap clauseCode).length
  out : c.out = []

/-- The step bound of one clause. -/
def orClauseCost (cl : Clause) : Nat := size orClausePre + (cl.length * (size orLit + 1) + 1)

/-- One clause, within the space `S ≥ orSpace f`. -/
theorem orClause_step (f : CNF) (rot : List Nat) (pre suf : CNF) (cl : Clause) (c : Config)
    (hxs : pre ++ cl :: suf = f) (hI : ClauseInv f rot pre c) (hm : c.reg Reg.m = suf.length + 1)
    (hAt : At c (clauseCode cl ++ suf.flatMap clauseCode)) {S : Nat} (hS : orSpace f ≤ S) :
    ∃ t c', ExecB S orClause c t c' ∧ t ≤ orClauseCost cl ∧ ClauseInv f rot (pre ++ [cl]) c' ∧
      c'.reg Reg.m = suf.length ∧ At c' (suf.flatMap clauseCode) := by
  obtain ⟨hL, hM, hocc, hp, hout⟩ := hI
  have hlen : (ramInput f).length = 1 + (pre.flatMap clauseCode).length + (1 + 2 * cl.length) +
      (suf.flatMap clauseCode).length := by
    rw [← hxs]; simp only [ramInput, List.length_cons, List.flatMap_append, List.flatMap_cons,
      List.length_append, clauseCode_length]; omega
  have hpre := flatMap_clauseCode_length pre
  have hfl : f.flatten.length = pre.flatten.length + cl.length + suf.flatten.length := by
    rw [← hxs]; simp; omega
  have hNl := ramInput_length_eq f
  -- the header
  have hb : cl.length = 3 → 2 * c.reg OR.occ + 1 < (ramInput f).length := by intro; rw [hocc]; omega
  obtain ⟨a1cnt, a1cs, a1p, a1m, a1mem, a1out, a1fr⟩ := orClausePre_run f rot c cl _ hL hAt hM.input hb
  have hSE : orE f + 2 * variableBound f + 4 * f.flatten.length ≤ S := hS
  have hNE : (ramInput f).length ≤ orE f := by unfold orE; omega
  obtain ⟨t1, e1, ht1⟩ := exec_loopFree (S := S) (s := orClausePre) (by simp [orClausePre, seqs, LoopFree]) c
    (orClausePre_addrOK f c cl _ hL hAt (by rw [hp]; omega) (fun h3 => by have := hb h3; omega))
  generalize hc1 : run orClausePre c = c1 at e1 a1cnt a1cs a1p a1m a1mem a1out a1fr
  have hL1 : Layout f c1 := hL.frame (fun r hr => a1fr r (by revert r; decide))
  have hAt1 : At c1 (cl.flatMap litCode ++ suf.flatMap clauseCode) := by
    have h := hAt
    simp only [clauseCode, List.cons_append] at h
    exact h.tail a1mem a1p
  -- the literals
  let I : List Literal → Config → Prop := fun lpre d =>
    Layout f d ∧ MemInv f rot (pre.flatten ++ lpre) d.mem ∧ d.reg OR.occ = (pre.flatten ++ lpre).length ∧
      d.reg OR.cs = csOf rot cl pre.flatten.length ∧ d.reg Reg.p = c1.reg Reg.p + 2 * lpre.length ∧
      d.reg Reg.m = suf.length ∧ d.out = []
  have hstep : ∀ lpre l lsuf d, lpre ++ l :: lsuf = cl → I lpre d → d.reg OR.cnt = lsuf.length + 1 →
      At d (litCode l ++ lsuf.flatMap litCode) →
      ∃ t d', ExecB S orLit d t d' ∧ t ≤ size orLit ∧ I (lpre ++ [l]) d' ∧ d'.reg OR.cnt = lsuf.length ∧
        At d' (lsuf.flatMap litCode) := by
    intro lpre l lsuf d hcl ⟨dL, dM, docc, dcs, dp, dm, dout⟩ dcnt dAt
    have hcll : cl.length = lpre.length + 1 + lsuf.length := by rw [← hcl]; simp; omega
    have hlsuf : (lsuf.flatMap litCode).length = 2 * lsuf.length := by
      have := edgeCodes_length (lsuf.map fun l => (l.var, signCode l))
      simpa [litCode, edgeCode, List.flatMap_map] using this
    obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩ := orLit_step f rot d (pre.flatten ++ lpre) (lsuf ++ suf.flatten) l
      (lsuf.flatMap litCode) (flatten_prefix hxs lpre hcl) dL dM docc
      (by rw [dcs, List.length_append, csBit_prefix hxs rot (t := lpre.length) (by omega)]) dAt
      (by rw [dp, a1p, hp]; omega)
    obtain ⟨t, e, ht⟩ := exec_loopFree (S := S) (s := orLit) (by simp [orLit, seqs, LoopFree]) d
      (orLit_addrOK f d l _ dL dAt (literal_var_lt (by rw [← hxs, ← hcl]; simp)) (by rw [dp, a1p, hp]; omega)
        (by rw [docc]; simp only [List.length_append]; unfold orB; omega))
    refine ⟨t, _, e, ht, ⟨b1, by rw [← List.append_assoc]; exact b2, by rw [b3]; simp; omega, ?_, ?_, ?_, ?_⟩,
      by rw [b5, dcnt]; rfl, b6⟩
    · rw [b8 _ (by decide), dcs]
    · rw [b4, dp]; simp; omega
    · rw [b8 _ (by decide), dm]
    · rw [b7, dout]
  have hI0 : I [] c1 := ⟨hL1, by rw [List.append_nil, a1mem]; exact hM,
    by rw [a1fr _ (by decide), hocc]; simp, by rw [a1cs, hocc], by simp, by rw [a1m, hm]; rfl,
    by rw [a1out, hout]⟩
  obtain ⟨t2, c2, e2, ht2, hI2⟩ := exec_listPass litCode cl (cnt := OR.cnt) (body := orLit) I
    (fun _ => size orLit) hstep c1 hI0 a1cnt hAt1.append_left
  obtain ⟨c2L, c2M, c2occ, -, c2p, c2m, c2out⟩ := hI2
  refine ⟨t1 + t2, c2, ExecB.seq e1 e2, ?_, ⟨c2L, ?_, ?_, ?_, c2out⟩, c2m, ?_⟩
  · unfold orClauseCost
    rw [sum_map_const_succ] at ht2
    omega
  · simpa using c2M
  · rw [c2occ]; simp
  · rw [c2p, a1p, hp]; simp [clauseCode_length]; omega
  · apply At.agree hAt (by rw [c2p, a1p, clauseCode_length]; omega)
    intro i hi
    rw [c2M.input _ (by rw [c2p, a1p, hp]; unfold orE; omega), hM.input _ (by rw [c2p, a1p, hp]; unfold orE; omega)]

end STACS2027.RAM

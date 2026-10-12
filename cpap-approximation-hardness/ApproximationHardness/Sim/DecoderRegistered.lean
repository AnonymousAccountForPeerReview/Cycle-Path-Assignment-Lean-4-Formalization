module

public import ApproximationHardness.Sim.Pipeline
public import ApproximationHardness.Sim.ParsePaths
public import ApproximationHardness.Sim.PolarizeRegistered
public import ApproximationHardness.RAM.Decode.Linear
import Lean.Elab.Tactic.Omega

/-!
# The decoding map of Theorem 11 in polynomial time in the registered model

`decX k`: read `encode f ++ encodePaths ps`, run the linear-time RAM decoder (`RAM.decProgram k`) on
`decInput f ps`, and write the bits of the decoded assignment. On the formulas of Definition 7 and
the valid choices `ps` for the cycles of `formulaGraph k f` it halts within
`decXConst k · (|input| + 1)` steps (`decX_run`); by `xram_polyTime` the decoding map is computed by
a polynomial-time single-tape machine of the registered foundation (`decoder_polyTime`).
-/

@[expose] public section

namespace STACS2027.Sim

open Complexity.SAT

/-! ### Writing the bits of the output -/

def serBitsBody : XStmt := xseqs [.sub sCNT sCNT sONE, readBuf sV, .emit sV]

/-- Write the numbers of the first `tPTR` odd cells as bits. -/
def serBits : XStmt :=
  xseqs [.const sONE 1, .const sTWO 2, .const sQ 1, .add sCNT tPTR sZ, .loop sCNT serBitsBody]

theorem xok_serBits (L : List Nat) (c : XConfig) (hb : Buf L c) (hz : c.reg sZ = 0) (hp : c.reg tPTR = L.length) :
    ∃ c', XOk serBits c c' (7 * L.length + 6) ∧ c'.out = c.out ++ L.map (fun x => decide (x ≠ 0)) := by
  have s1 := xok_const sONE 1 c
  have s2 := xok_const sTWO 2 (c.setReg sONE 1)
  have s3 := xok_const sQ 1 ((c.setReg sONE 1).setReg sTWO 2)
  have s4 := xok_add sCNT tPTR sZ (((c.setReg sONE 1).setReg sTWO 2).setReg sQ 1)
  generalize hc4 : (((c.setReg sONE 1).setReg sTWO 2).setReg sQ 1).setReg sCNT
    ((((c.setReg sONE 1).setReg sTWO 2).setReg sQ 1).reg tPTR + (((c.setReg sONE 1).setReg sTWO 2).setReg sQ 1).reg sZ)
    = c4 at s4
  let I : List Nat → XConfig → Prop := fun pre d =>
    Buf L d ∧ d.reg sQ = 2 * pre.length + 1 ∧ d.reg sCNT = L.length - pre.length ∧
      d.out = c.out ++ pre.map (fun x => decide (x ≠ 0)) ∧ d.reg sONE = 1 ∧ d.reg sTWO = 2
  have hI0 : I [] c4 := by
    rw [← hc4]
    refine ⟨fun j => by simp [XConfig.setReg]; exact hb j, by simp [XConfig.setReg], ?_, by simp [XConfig.setReg],
      by simp [XConfig.setReg], by simp [XConfig.setReg]⟩
    simp [XConfig.setReg, tPTR, hp, hz]
  obtain ⟨c5, s5, -, -, -, e4, -, -⟩ := xok_listLoop (a := sCNT) (body := serBitsBody) L I (fun _ => 5)
    (by
      intro pre x suf d hpre ⟨d1, d2, d3, d4, d5, d6⟩
      have hl : pre.length < L.length := by have := congrArg List.length hpre; simp at this; omega
      refine ⟨by rw [d3]; omega, ?_⟩
      have hdx : L.getD pre.length 0 = x := by
        subst hpre; simp [List.getD_eq_getElem?_getD]
      obtain ⟨d', s', v', q', b', o', -, r'⟩ := xok_readBuf sV (by decide) (by decide)
        (d.setReg sCNT (d.reg sCNT - d.reg sONE)) L (fun j => by simp [XConfig.setReg]; exact d1 j) pre.length
        (by simp [XConfig.setReg, d2]) (by simp [XConfig.setReg, d6])
      refine ⟨_, ((xok_sub sCNT sCNT sONE d).seq (s'.seq ((xok_emit sV d').seq (xok_skip _)))).mono (by omega),
        fun j => by simp [XConfig.emit]; exact b' j, ?_, ?_, ?_, ?_, ?_⟩
      · simp [XConfig.emit, q']
      · simp [XConfig.emit, r' sCNT (by decide) (by decide), XConfig.setReg, d3, d5]; omega
      · show d'.out ++ [decide (d'.reg sV ≠ 0)] = c.out ++ (pre ++ [x]).map (fun x => decide (x ≠ 0))
        rw [o', v', hdx]; simp [XConfig.setReg, d4]
      · simp [XConfig.emit, r' sONE (by decide) (by decide), XConfig.setReg, d5]
      · simp [XConfig.emit, r' sTWO (by decide) (by decide), XConfig.setReg, d6])
    (by intro d ⟨_, _, d3, _⟩; rw [d3]; simp)
    c4 hI0
  refine ⟨c5, (s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (xok_skip _)))))).mono ?_, e4⟩
  rw [sum_const_map]; omega

/-! ### The program -/

/-- Read `encode f ++ encodePaths ps`, run the RAM decoder, write the bits of the assignment. -/
def decX (k : Nat) : XStmt :=
  xseqs [parseCNF, parsePaths, resetC parseRegs, .const tONE 1, .const tPTR 0, tr (RAM.decProgram k), .const sZ 0,
    serBits]

/-- The step constant of `decX k`. -/
def decXConst (k : Nat) : Nat := 60 + 4 * RAM.decLinConst k

theorem decX_run {k : Nat} (hk : 5 ≤ k) {f : CNF} (hf : LeOneLeTwoCNF f) {ps : List (List Edge)}
    (hv : ValidChoices ((cycles (formulaGraph k f) k).map selectedOptions) ps) :
    ∃ t c', XExec (decX k) (xinit (encode f ++ encodePaths ps)) t c' ∧
      t ≤ decXConst k * ((encode f ++ encodePaths ps).length + 1) ^ 1 ∧
      c'.out = (List.range (variableBound f)).map (decodeAssign k ps) := by
  -- parse the formula and the paths
  obtain ⟨c1, s1, i1, m1, o1, n1, t1, p1, r1⟩ := xok_parseCNF f (encodePaths ps) (xinit (encode f ++ encodePaths ps))
    (by simp [xinit]) rfl rfl
  obtain ⟨c2, s2, i2, m2, o2, r2⟩ := xok_parsePaths ps [] c1 (RAM.ramInput f) (by rw [i1]; simp) p1 m1 n1 t1
  -- reset
  obtain ⟨c3, s3, r3, m3, i3, o3⟩ := xok_resetC parseRegs c2
  have hreg3 : ∀ i, c3.reg i = 0 := by
    intro i
    rw [r3 i]
    split
    · rfl
    · rename_i hi
      simp only [parseRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
      obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := hi
      rw [r2 i ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩, r1 i ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ a9 a10]; rfl
  have s4a := xok_const tONE 1 c3
  have s4 := xok_const tPTR 0 (c3.setReg tONE 1)
  generalize hc4 : (c3.setReg tONE 1).setReg tPTR 0 = c4 at s4
  have hT : TRel (RAM.initial (RAM.decInput f ps)) c4 := by
    rw [← hc4]
    refine ⟨fun i hi => ?_, ?_, ?_, fun a => ?_, fun j => ?_⟩
    · simp only [XConfig.setReg, tONE, tPTR]; rw [ite_eq_right (by omega), ite_eq_right (by omega), hreg3]; rfl
    · simp [XConfig.setReg, tONE, tPTR]
    · simp [XConfig.setReg, RAM.initial]
    · simp only [XConfig.setReg, m3, m2, memOf, RAM.initial, RAM.decInput]; simp
    · simp only [XConfig.setReg, m3, m2, memOf, RAM.initial]; simp; try omega
  -- the RAM decoder
  obtain ⟨t, ⟨cR, hR, hout⟩, ht⟩ := RAM.decoder_linear_time hk hf hv
  obtain ⟨t5, c5, e5, hT5, i5, o5, l5⟩ := tr_exec hR.exec (regsLt_of_b _ _ (by rfl)) c4 hT
  have s5 : XOk (tr (RAM.decProgram k)) c4 c5 t5 := ⟨t5, e5, Nat.le_refl _⟩
  -- write the bits
  have s6 := xok_const sZ 0 c5
  have hb : Buf (RAM.decOutput k f ps) (c5.setReg sZ 0) := fun j => by
    simp only [XConfig.setReg]; rw [hT5.odd j, hout]
  obtain ⟨c7, s7, o7⟩ := xok_serBits (RAM.decOutput k f ps) (c5.setReg sZ 0) hb (by simp [XConfig.setReg])
    (by simp only [XConfig.setReg, sZ, tPTR]; rw [ite_eq_right (by omega), hT5.ptr, hout])
  obtain ⟨tt, ett, htt⟩ := s1.seq (s2.seq (s3.seq (s4a.seq (s4.seq (s5.seq (s6.seq (s7.seq (xok_skip _))))))))
  refine ⟨tt, c7, ett, ?_, ?_⟩
  · have hN := encode_length_ge f
    have hdo : (RAM.decOutput k f ps).length = variableBound f := by simp [RAM.decOutput]
    rw [hdo] at htt
    simp only [parseRegs, List.length_cons, List.length_nil] at htt
    simp only [List.length_append, Nat.pow_one]
    unfold decXConst
    generalize (encode f).length = A at *
    generalize (encodePaths ps).length = P at *
    have h1 : RAM.decLinConst k * (variableBound f + 1) ≤ RAM.decLinConst k * (A + P + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    rw [Nat.add_mul, Nat.mul_assoc]
    omega
  · rw [o7]; simp [XConfig.setReg, o5, ← hc4, o3, o2, o1, xinit, RAM.decOutput]

/-! ### The registered polynomial-time map -/

theorem decX_regsOK (k : Nat) : RegsOK (decX k) := regsOK_of_b _ (by
  simp only [decX, regsOKb_xseqs, List.all_cons, List.all_nil]
  rw [regsOKb_tr _ (by rfl)]
  rfl)

theorem decX_depth (k : Nat) : depth (decX k) ≤ 16 := by
  simp only [decX, depth_xseqs, List.map_cons, List.map_nil, depth_tr]
  have : depthR (RAM.decProgram k) = 2 := by rfl
  rw [this]
  decide

/-- **The decoding map of Theorem 11 is computable in polynomial time in the registered model.** For
`k ≥ 5` there is a word function `g` computed by a polynomial-time single-tape machine of the
registered foundation (`Complexity.PolyTime`) such that for every formula `f` of Definition 7 and
every valid choice `ps` of paths for the cycles of `formulaGraph k f`, `g` maps the code of `f`
followed by the code of `ps` to the bits of the assignment `decodeAssign k ps` on the variables
`0, …, n − 1`; and this assignment satisfies the inequality `S + C ≤ sat(A) + cost(ps)` of Theorem 11
for the optima `S` and `C`. -/
theorem decoder_polyTime {k : Nat} (hk : 5 ≤ k) :
    ∃ g : List Bool → List Bool, Complexity.PolyTime g ∧
      ∀ f ps, LeOneLeTwoCNF f → ValidChoices ((cycles (formulaGraph k f) k).map selectedOptions) ps →
        g (encode f ++ encodePaths ps) = (List.range (variableBound f)).map (decodeAssign k ps) ∧
        ∀ S C, IsMaxSat f S → IsMinCost (formulaGraph k f) k C →
          S + C ≤ satisfiedCount (decodeAssign k ps) f + STACS2027.cost ps := by
  obtain ⟨g, hg, hc⟩ := xram_polyTime (decX k) (decX_regsOK k) (decX_depth k) (decXConst k) 1
  refine ⟨g, hg, fun f ps hf hv => ⟨?_, fun S C hS hC => cpap_lreduction_decoder hk f hf S C hS hC ps hv⟩⟩
  obtain ⟨t, c', he, ht, ho⟩ := decX_run hk hf hv
  rw [hc _ t c' he ht, ho]

end STACS2027.Sim

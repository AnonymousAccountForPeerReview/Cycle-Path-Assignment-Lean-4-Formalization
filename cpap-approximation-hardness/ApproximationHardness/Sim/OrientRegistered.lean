module

public import ApproximationHardness.Sim.DecoderRegistered
public import ApproximationHardness.RAM.Orient.Correct
import Lean.Elab.Tactic.Omega

/-!
# The planar orientation in polynomial time in the registered model

`orX`: read `encode f ++ encodeRot rot` (the formula, then the rotation list with its numbers in
unary), run the linear-time RAM program `RAM.orProgram` on `ramInput f ++ rot`, and write the
orientation bits. On every Definition 7 instance with a planar rotation list of its incidence
graph it halts within `orXConst · (|input| + 1)` steps (`orX_run`); by `xram_polyTime` the map
is computed by a polynomial-time single-tape machine of the registered foundation
(`orientation_polyTime`), and its output is a planar orientation of the gadgets.
-/

@[expose] public section

namespace STACS2027.Sim

open Complexity Complexity.SAT PlanarAssembly

/-! ### Reading a rotation list -/

/-- The code of a rotation list: the list of its numbers, each in unary. -/
def encodeRot (rot : List Nat) : List Bool := writeList writeNat rot

def parseRotEntry : XStmt := xseqs [.sub pCNT pCNT pONE, readNat pV, putNum pV]

def parseRot : XStmt := xseqs [readNat pCNT, .loop pCNT parseRotEntry]

theorem xok_parseRot (rot : List Nat) (rest : List Bool) (c : XConfig) (L : List Nat)
    (hin : c.inp = encodeRot rot ++ rest) (hP : c.reg pP = 2 * L.length) (hm : c.mem = memOf L)
    (hone : c.reg pONE = 1) (htwo : c.reg pTWO = 2) :
    ∃ c', XOk parseRot c c' (14 * ((encodeRot rot).length + 1)) ∧ c'.inp = rest ∧
      c'.mem = memOf (L ++ rot) ∧ c'.out = c.out ∧ ∀ i, ParseFree i → c'.reg i = c.reg i := by
  obtain ⟨c1, s1, v1, i1, m1, o1, r1⟩ := xok_readNat pCNT (by decide) (by decide) (by decide) (by decide) c
    rot.length (writeValues writeNat rot ++ rest) (by rw [hin]; simp [encodeRot, writeList]) hone
  let I : List Nat → XConfig → Prop := fun pre d =>
    d.inp = writeValues writeNat (rot.drop pre.length) ++ rest ∧ d.mem = memOf (L ++ pre) ∧
      d.reg pP = 2 * (L ++ pre).length ∧ d.reg pCNT = rot.length - pre.length ∧
      d.reg pONE = 1 ∧ d.reg pTWO = 2 ∧ d.out = c.out ∧ ∀ i, ParseFree i → d.reg i = c.reg i
  have hI0 : I [] c1 := ⟨by rw [i1]; rfl, by rw [m1, hm]; simp,
    by rw [r1 pP (by decide) (by decide) (by decide) (by decide), hP]; simp, by rw [v1]; simp,
    by rw [r1 pONE (by decide) (by decide) (by decide) (by decide), hone],
    by rw [r1 pTWO (by decide) (by decide) (by decide) (by decide), htwo], o1,
    fun i ⟨a1, a2, a3, _, a5, _, _, _⟩ => r1 i a5 a1 a3 a2⟩
  obtain ⟨c2, s2, hI2⟩ := xok_listLoop (a := pCNT) (body := parseRotEntry) rot I
    (fun x => 12 * (writeNat x).length)
    (by
      intro pre x suf d hp ⟨d1, d2, d3, d4, d5, d6, d7, d8⟩
      have hl : pre.length < rot.length := by have := congrArg List.length hp; simp at this; omega
      refine ⟨by rw [d4]; omega, ?_⟩
      rw [writeValues_drop writeNat hp] at d1
      have s1 := xok_sub pCNT pCNT pONE d
      generalize he1 : d.setReg pCNT (d.reg pCNT - d.reg pONE) = e1 at s1
      have e1r : ∀ i, i ≠ pCNT → e1.reg i = d.reg i := by intro i hi; rw [← he1]; simp [XConfig.setReg, hi]
      obtain ⟨e2, s2, v2, i2, m2, o2, r2⟩ := xok_readNat pV (by decide) (by decide) (by decide) (by decide) e1 x
        (writeValues writeNat suf ++ rest) (by rw [← he1]; simp [XConfig.setReg, d1])
        (by rw [e1r pONE (by decide), d5])
      obtain ⟨e3, s3, m3, p3, i3, o3, r3⟩ := xok_putNum pV (by decide) e2 (L ++ pre)
        (by rw [r2 pP (by decide) (by decide) (by decide) (by decide), e1r pP (by decide), d3])
        (by rw [m2, ← he1]; exact d2)
        (by rw [r2 pTWO (by decide) (by decide) (by decide) (by decide), e1r pTWO (by decide), d6])
      rw [v2] at m3 p3
      refine ⟨e3, (s1.seq (s2.seq (s3.seq (xok_skip _)))).mono (by rw [writeNat_length']; omega), ?_, ?_, ?_, ?_, ?_,
        ?_, ?_, ?_⟩
      · rw [i3, i2, show rot.drop (pre ++ [x]).length = suf by subst hp; simp]
      · rw [m3]; simp
      · rw [p3]; simp
      · rw [r3 pCNT (by decide), r2 pCNT (by decide) (by decide) (by decide) (by decide)]
        rw [← he1]; simp [XConfig.setReg, d4, d5]; omega
      · rw [r3 pONE (by decide), r2 pONE (by decide) (by decide) (by decide) (by decide), e1r pONE (by decide), d5]
      · rw [r3 pTWO (by decide), r2 pTWO (by decide) (by decide) (by decide) (by decide), e1r pTWO (by decide), d6]
      · rw [o3, o2, ← he1]; exact d7
      · intro i ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩
        rw [r3 i a4, r2 i a8 a1 a3 a2, e1r i a5, d8 i ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩])
    (by intro d ⟨_, _, _, d4, _⟩; rw [d4]; simp)
    c1 hI0
  obtain ⟨e1, e2, -, -, -, -, e7, e8⟩ := hI2
  have hlen : (encodeRot rot).length = rot.length + 1 + (writeValues writeNat rot).length := by
    simp [encodeRot, writeList]
  have hsum := sum_cost_le writeNat (fun x => by rw [writeNat_length']; omega) 12 rot
  refine ⟨c2, (s1.seq (s2.seq (xok_skip _))).mono ?_, ?_, e2, e7, e8⟩
  · rw [hlen]; omega
  · rw [e1, List.drop_eq_nil_of_le (Nat.le_refl _)]; rfl

/-! ### Sizes -/

theorem ramInput_le_encode (f : CNF) : (RAM.ramInput f).length ≤ (encode f).length := by
  have hc : ∀ cl : Clause, (RAM.clauseCode cl).length ≤ (encodeClause cl).length := by
    intro cl
    have hv : ∀ cl : Clause, 2 * cl.length ≤ (writeValues encodeLiteral cl).length := by
      intro cl
      induction cl with
      | nil => simp [writeValues]
      | cons l cl ih => simp only [writeValues_cons, List.length_append, encodeLiteral_length, List.length_cons]; omega
    have := hv cl
    have h1 : (encodeClause cl).length = cl.length + 1 + (writeValues encodeLiteral cl).length := by
      simp [encodeClause, writeList]
    rw [RAM.clauseCode_length]; omega
  have key : ∀ g : CNF, (g.flatMap RAM.clauseCode).length ≤ (writeValues encodeClause g).length := by
    intro g
    induction g with
    | nil => simp [writeValues]
    | cons cl g ih =>
      have := hc cl
      simp only [List.flatMap_cons, List.length_append, writeValues_cons]; omega
  have := key f
  have h1 : (encode f).length = f.length + 1 + (writeValues encodeClause f).length := by
    simp [encode, writeList]
  simp only [RAM.ramInput, List.length_cons]; omega

theorem rot_le_encodeRot (rot : List Nat) : rot.length ≤ (encodeRot rot).length := by
  simp [encodeRot, writeList]; omega

/-! ### The program -/

/-- Read `encode f ++ encodeRot rot`, run the RAM orientation program, write the bits. -/
def orX : XStmt :=
  xseqs [parseCNF, parseRot, resetC parseRegs, .const tONE 1, .const tPTR 0, tr RAM.orProgram, .const sZ 0,
    serBits]

/-- The step constant of `orX`. -/
def orXConst : Nat := 80 + 8 * RAM.orConst

theorem orX_run {f : CNF} (hf : BoundedOccurrence f) {rot : List Nat} (h : IsPlanarRotation f rot) :
    ∃ t c', XExec orX (xinit (encode f ++ encodeRot rot)) t c' ∧
      t ≤ orXConst * ((encode f ++ encodeRot rot).length + 1) ^ 1 ∧
      c'.out = orientationBits f (RAM.rotFun rot) := by
  -- parse the formula and the rotation list
  obtain ⟨c1, s1, i1, m1, o1, n1, t1, p1, r1⟩ := xok_parseCNF f (encodeRot rot) (xinit (encode f ++ encodeRot rot))
    (by simp [xinit]) rfl rfl
  obtain ⟨c2, s2, i2, m2, o2, r2⟩ := xok_parseRot rot [] c1 (RAM.ramInput f) (by rw [i1]; simp) p1 m1 n1 t1
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
  have hT : TRel (RAM.initial (RAM.orInput f rot)) c4 := by
    rw [← hc4]
    refine ⟨fun i hi => ?_, ?_, ?_, fun a => ?_, fun j => ?_⟩
    · simp only [XConfig.setReg, tONE, tPTR]; rw [ite_eq_right (by omega), ite_eq_right (by omega), hreg3]; rfl
    · simp [XConfig.setReg, tONE, tPTR]
    · simp [XConfig.setReg, RAM.initial]
    · simp only [XConfig.setReg, m3, m2, memOf, RAM.initial, RAM.orInput]; simp
    · simp only [XConfig.setReg, m3, m2, memOf, RAM.initial]; simp; try omega
  -- the RAM program
  obtain ⟨t, ⟨cR, hR, hout⟩, ht, -⟩ := RAM.orientation_linear_time 0 hf h
  obtain ⟨t5, c5, e5, hT5, i5, o5, l5⟩ := tr_exec hR.exec (regsLt_of_b _ _ (by rfl)) c4 hT
  have s5 : XOk (tr RAM.orProgram) c4 c5 t5 := ⟨t5, e5, Nat.le_refl _⟩
  -- write the bits
  have s6 := xok_const sZ 0 c5
  have hb : Buf (RAM.orOutput f rot) (c5.setReg sZ 0) := fun j => by
    simp only [XConfig.setReg]; rw [hT5.odd j, hout]
  obtain ⟨c7, s7, o7⟩ := xok_serBits (RAM.orOutput f rot) (c5.setReg sZ 0) hb (by simp [XConfig.setReg])
    (by simp only [XConfig.setReg, sZ, tPTR]; rw [ite_eq_right (by omega), hT5.ptr, hout])
  obtain ⟨tt, ett, htt⟩ := s1.seq (s2.seq (s3.seq (s4a.seq (s4.seq (s5.seq (s6.seq (s7.seq (xok_skip _))))))))
  refine ⟨tt, c7, ett, ?_, ?_⟩
  · have hN := ramInput_le_encode f
    have hR' := rot_le_encodeRot rot
    have hM : (RAM.orOutput f rot).length ≤ (RAM.orInput f rot).length := by
      rw [RAM.orOutput_eq]
      simp only [List.length_map, List.length_range, RAM.orInput, List.length_append]
      have := RAM.ramInput_length_eq f
      omega
    have hI : (RAM.orInput f rot).length ≤ (encode f).length + (encodeRot rot).length := by
      simp only [RAM.orInput, List.length_append]; omega
    simp only [parseRegs, List.length_cons, List.length_nil] at htt
    simp only [List.length_append, Nat.pow_one]
    unfold orXConst
    generalize (encode f).length = A at *
    generalize (encodeRot rot).length = P at *
    generalize (RAM.orInput f rot).length = Q at *
    generalize (RAM.orOutput f rot).length = O at *
    have h1 : RAM.orConst * (Q + 1) ≤ RAM.orConst * (A + P + 1) := Nat.mul_le_mul_left _ (by omega)
    rw [Nat.add_mul, Nat.mul_assoc]
    omega
  · rw [o7]
    simp only [XConfig.setReg, o5, ← hc4, o3, o2, o1, xinit, List.nil_append]
    rw [← RAM.orOutput_bits]
    apply List.map_congr_left
    intro x hx
    unfold RAM.orOutput at hx
    obtain ⟨b, -, rfl⟩ := List.mem_map.mp hx
    cases b <;> rfl

/-! ### The registered polynomial-time map -/

theorem orX_regsOK : RegsOK orX := regsOK_of_b _ (by
  simp only [orX, regsOKb_xseqs, List.all_cons, List.all_nil]
  rw [regsOKb_tr _ (by rfl)]
  rfl)

theorem orX_depth : depth orX ≤ 16 := by
  simp only [orX, depth_xseqs, List.map_cons, List.map_nil, depth_tr]
  have : depthR RAM.orProgram = 2 := by rfl
  rw [this]
  decide

/-- **The planar orientation is computable in polynomial time in the registered model.** There is
a word function `g` computed by a polynomial-time single-tape machine of the registered foundation
(`Complexity.PolyTime`) such that for every formula `f` of bounded occurrence (each clause of two
or three literals, at most one positive and two negative occurrences of each variable) and every
planar rotation list `rot` of its incidence graph, `g` maps the code of `f` followed by the code
of `rot` to the explicit orientation bits, and the oriented formula graph built with these bits is
planar for every gadget parameter `k`. -/
theorem orientation_polyTime :
    ∃ g : List Bool → List Bool, Complexity.PolyTime g ∧
      ∀ f rot, BoundedOccurrence f → IsPlanarRotation f rot →
        g (encode f ++ encodeRot rot) = orientationBits f (RAM.rotFun rot) ∧
        ∀ k, PlanarGraph (orientedFormulaGraph (choicesOfBits f (g (encode f ++ encodeRot rot))) k f) := by
  obtain ⟨g, hg, hc⟩ := xram_polyTime orX orX_regsOK orX_depth orXConst 1
  refine ⟨g, hg, fun f rot hf h => ?_⟩
  obtain ⟨t, c', he, ht, ho⟩ := orX_run hf h
  have hgo : g (encode f ++ encodeRot rot) = orientationBits f (RAM.rotFun rot) := by
    rw [hc _ t c' he ht, ho]
  exact ⟨hgo, fun k => by rw [hgo]; exact orientationBits_planar k hf h⟩

end STACS2027.Sim

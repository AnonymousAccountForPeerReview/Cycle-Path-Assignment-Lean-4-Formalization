module

public import ApproximationHardness.Sim.Pipeline
public import ApproximationHardness.RAM.Polarize.Correct
import Lean.Elab.Tactic.Omega

/-!
# Lemma 10's transformation in polynomial time in the registered model

`polX`: read `encode f`, run the linear-time RAM program of Lemma 10 (`RAM.polProgram`) on
`ramInput f`, write `encode (polarize f)`. On every 3-OCCURRENCE MAX-3-SAT instance it halts within
`polXConst · (|encode f| + 1)²` steps (`polX_run`), so by `xram_polyTime` the map
`encode f ↦ encode (polarize f)` is computed by a polynomial-time single-tape machine of the
registered foundation (`polarize_polyTime`).
-/

@[expose] public section

namespace STACS2027.Sim

open Complexity.SAT

/-! ### Sizes of codes -/

theorem clauseBound_le_code : ∀ c : Clause, clauseBound c ≤ (writeValues encodeLiteral c).length := by
  intro c
  induction c with
  | nil => simp [clauseBound, writeValues]
  | cons l c ih => simp only [clauseBound, writeValues_cons, List.length_append, encodeLiteral_length]; omega

theorem variableBound_le_code : ∀ f : CNF, variableBound f ≤ (writeValues encodeClause f).length := by
  intro f
  induction f with
  | nil => simp [variableBound, writeValues]
  | cons c f ih =>
    have := clauseBound_le_code c
    have hc : (encodeClause c).length = c.length + 1 + (writeValues encodeLiteral c).length := by
      simp [encodeClause, writeList]
    simp only [variableBound, writeValues_cons, List.length_append]; omega

theorem encode_length_ge (f : CNF) : f.length + variableBound f ≤ (encode f).length := by
  have := variableBound_le_code f
  have h : (encode f).length = f.length + 1 + (writeValues encodeClause f).length := by
    simp [encode, writeList]
  omega

theorem encode_length_le (V : Nat) : ∀ g : CNF, (∀ c ∈ g, c.length ≤ 3 ∧ ∀ l ∈ c, l.var < V) →
    (encode g).length ≤ (g.length + 1) * (3 * V + 10) := by
  have hcl : ∀ c : Clause, c.length ≤ 3 → (∀ l ∈ c, l.var < V) → (encodeClause c).length ≤ 3 * V + 7 := by
    intro c h1 h2
    have hv : ∀ c : Clause, (∀ l ∈ c, l.var < V) → (writeValues encodeLiteral c).length ≤ c.length * (V + 1) := by
      intro c
      induction c with
      | nil => intro _; simp [writeValues]
      | cons l c ih =>
        intro h
        have := h l (by simp)
        have := ih (fun r hr => h r (by simp [hr]))
        simp only [writeValues_cons, List.length_append, encodeLiteral_length, List.length_cons]
        rw [Nat.add_mul, Nat.one_mul]
        omega
    have := hv c h2
    have hc : (encodeClause c).length = c.length + 1 + (writeValues encodeLiteral c).length := by
      simp [encodeClause, writeList]
    have : c.length * (V + 1) ≤ 3 * (V + 1) := Nat.mul_le_mul_right _ h1
    omega
  have key : ∀ g : CNF, (∀ c ∈ g, c.length ≤ 3 ∧ ∀ l ∈ c, l.var < V) →
      (writeValues encodeClause g).length ≤ g.length * (3 * V + 7) := by
    intro g
    induction g with
    | nil => intro _; simp [writeValues]
    | cons c g ih =>
      intro h
      have := hcl c (h c (by simp)).1 (h c (by simp)).2
      have := ih (fun d hd => h d (by simp [hd]))
      simp only [writeValues_cons, List.length_append, List.length_cons]
      rw [Nat.add_mul, Nat.one_mul]
      omega
  intro g h
  have := key g h
  have hl : (encode g).length = g.length + 1 + (writeValues encodeClause g).length := by
    simp [encode, writeList]
  have e1 : g.length * (3 * V + 8) = g.length * (3 * V + 7) + g.length := by
    rw [show 3 * V + 8 = (3 * V + 7) + 1 by omega, Nat.mul_add, Nat.mul_one]
  have e2 : g.length * (3 * V + 8) ≤ g.length * (3 * V + 10) := Nat.mul_le_mul_left _ (by omega)
  rw [hl, Nat.add_mul, Nat.one_mul]; omega

theorem polarize_shape (f : CNF) (hf : ∀ c ∈ f, c.length ≤ 3) :
    ∀ c ∈ polarize f, c.length ≤ 3 ∧ ∀ l ∈ c, l.var < variableBound f + 2 * f.length := by
  intro c hc
  unfold polarize at hc
  rcases List.mem_append.mp hc with hc | hc
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    have hdf : d ∈ f := (List.mem_filter.mp hd).1
    refine ⟨by simp; exact hf d hdf, fun l hl => ?_⟩
    obtain ⟨l', hl', rfl⟩ := List.mem_map.mp hl
    have := literal_lt_variableBound hdf hl'
    unfold flipLiteral; split <;> simp <;> omega
  · unfold padding at hc
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hc
    have hj' := List.mem_range.mp hj
    have := RAM.deletedCount_le f
    refine ⟨by simp, fun l hl => ?_⟩
    simp at hl
    rcases hl with rfl | rfl <;> simp <;> omega

/-! ### The program -/

/-- The parser's registers. -/
def parseRegs : List Nat := [pB, pFL, pT, pP, pCNT, pCL, pS, pV, pONE, pTWO]

/-- Read `encode f`, run Lemma 10's RAM program, write `encode (polarize f)`. -/
def polX : XStmt :=
  xseqs [parseCNF, resetC parseRegs, .const tONE 1, .const tPTR 0, tr RAM.polProgram, .const sZ 0, serCNF]

/-- The step constant of `polX`. -/
def polXConst : Nat := 360 + 4 * RAM.polConst

theorem polX_run (f : CNF) (hf : ThreeOccurrence f) :
    ∃ t c', XExec polX (xinit (encode f)) t c' ∧ t ≤ polXConst * ((encode f).length + 1) ^ 2 ∧
      c'.out = encode (polarize f) := by
  have hf2 := hf.1
  have hf3 : ∀ c ∈ f, c.length ≤ 3 := fun c hc => by rcases hf2 c hc with h | h <;> omega
  -- parse
  obtain ⟨c1, s1, i1, m1, o1, -, -, -, r1⟩ := xok_parseCNF f [] (xinit (encode f)) (by simp [xinit]) rfl rfl
  -- reset
  obtain ⟨c2, s2, r2, m2, i2, o2⟩ := xok_resetC parseRegs c1
  have hreg2 : ∀ i, c2.reg i = 0 := by
    intro i
    rw [r2 i]
    split
    · rfl
    · rename_i hi
      simp only [parseRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
      obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := hi
      rw [r1 i ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ a9 a10]; rfl
  -- the registers of the transformation
  have s3a := xok_const tONE 1 c2
  have s3 := xok_const tPTR 0 (c2.setReg tONE 1)
  generalize hc3 : (c2.setReg tONE 1).setReg tPTR 0 = c3 at s3
  have hT : TRel (RAM.initial (RAM.ramInput f)) c3 := by
    rw [← hc3]
    refine ⟨fun i hi => ?_, ?_, ?_, fun a => ?_, fun j => ?_⟩
    · simp only [XConfig.setReg, tONE, tPTR]; rw [ite_eq_right (by omega), ite_eq_right (by omega), hreg2]; rfl
    · simp [XConfig.setReg, tONE, tPTR]
    · simp [XConfig.setReg, RAM.initial]
    · simp only [XConfig.setReg, m2, m1, memOf, RAM.initial]; simp
    · simp only [XConfig.setReg, m2, m1, memOf, RAM.initial]; simp; try omega
  -- the RAM program
  obtain ⟨t, ⟨cR, hR, hout⟩, ht⟩ := RAM.pol_computes f hf2
  obtain ⟨t4, c4, e4, hT4, i4, o4, l4⟩ := tr_exec hR.exec (regsLt_of_b _ _ (by decide)) c3 hT
  -- write the result
  have s5 := xok_const sZ 0 c4
  have hb : Buf (RAM.ramInput (polarize f)) (c4.setReg sZ 0) := fun j => by
    simp only [XConfig.setReg]; rw [hT4.odd j, hout]
  obtain ⟨c6, s6, o6, -⟩ := xok_serCNF (polarize f) (c4.setReg sZ 0) hb (by simp [XConfig.setReg])
  have s4 : XOk (tr RAM.polProgram) c3 c4 t4 := ⟨t4, e4, Nat.le_refl _⟩
  have s := s1.seq (s2.seq (s3a.seq (s3.seq (s4.seq (s5.seq (s6.seq (xok_skip _)))))))
  obtain ⟨tt, ett, htt⟩ := s
  refine ⟨tt, c6, ett, ?_, ?_⟩
  · -- the time bound
    have hpc := RAM.polCost_le f
    have hN := encode_length_ge f
    have hg := encode_length_le (variableBound f + 2 * f.length) (polarize f) (polarize_shape f hf3)
    rw [RAM.polarize_length] at hg
    generalize hW : (encode f).length + 1 = W at *
    have hg' : (encode (polarize f)).length ≤ 20 * (W * W) := by
      have h1 : f.length + 1 ≤ 2 * W := by omega
      have h2 : 3 * (variableBound f + 2 * f.length) + 10 ≤ 10 * W := by omega
      have := Nat.mul_le_mul h1 h2
      rw [Nat.mul_mul_mul_comm] at this; omega
    have hW1 : W ≤ W * W := Nat.le_mul_of_pos_left W (by omega)
    have hp : RAM.polConst * (f.length + 1) ≤ RAM.polConst * (W * W) := Nat.mul_le_mul_left _ (by omega)
    rw [Nat.pow_two]
    unfold polXConst
    rw [Nat.add_mul, Nat.mul_assoc]
    simp only [parseRegs, List.length_cons, List.length_nil] at htt
    omega
  · rw [o6]; simp [XConfig.setReg, o4, ← hc3, o2, o1, xinit]

/-! ### The registered polynomial-time map -/

theorem polX_regsOK : RegsOK polX := regsOK_of_b _ (by
  simp only [polX, regsOKb_xseqs, List.all_cons, List.all_nil]
  rw [regsOKb_tr _ (by decide)]
  decide)

theorem polX_depth : depth polX ≤ 16 := by
  simp only [polX, depth_xseqs, List.map_cons, List.map_nil, depth_tr]
  decide

/-- **Lemma 10's transformation is computable in polynomial time in the registered model.** There is a
word function `g` computed by a polynomial-time single-tape machine of the registered foundation
(`Complexity.PolyTime`) with `g (encode f) = encode (polarize f)` for every 3-OCCURRENCE MAX-3-SAT
instance `f`. -/
theorem polarize_polyTime :
    ∃ g : List Bool → List Bool, Complexity.PolyTime g ∧ ∀ f, ThreeOccurrence f → g (encode f) = encode (polarize f) := by
  obtain ⟨g, hg, hc⟩ := xram_polyTime polX polX_regsOK polX_depth polXConst 2
  refine ⟨g, hg, fun f hf => ?_⟩
  obtain ⟨t, c', he, ht, ho⟩ := polX_run f hf
  rw [hc _ t c' he ht, ho]

end STACS2027.Sim

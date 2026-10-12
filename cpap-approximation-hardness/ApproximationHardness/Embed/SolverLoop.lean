module

public import ApproximationHardness.Embed.SolverNodeBounds
public import ApproximationHardness.Embed.SolverTempRAM
public import ApproximationHardness.Embed.SolverRun
public import ApproximationHardness.RAM.Pass

/-! # The fixed-budget RAM solver loop -/

@[expose] public section

set_option maxRecDepth 10000

namespace STACS2027.Embed.RAMSolver

open RAM

def solverBody : Stmt := .seq mstepProgram (.sub 80 80 1)
def solverLoop : Stmt := .loop 80 solverBody

theorem Rep.high {L : Layout} {c : Config} {s : SMS} (hr : Rep L c s)
    (r value : Nat) (hlo : 72 ≤ r) : Rep L (c.setReg r value) s := by
  have hf : ∀ i, i < 72 → (c.setReg r value).reg i = c.reg i := by
    intro i hi; simp [Config.setReg, show i ≠ r by omega]
  have hb : Bases L (c.setReg r value) := by
    rcases hr.bases with ⟨hz, ho, hbase, hw, hb⟩
    refine ⟨(hf 0 (by omega)).trans hz, (hf 1 (by omega)).trans ho,
      (hf 2 (by omega)).trans hbase, (hf 3 (by omega)).trans hw, ?_⟩
    intro j hj; rw [hf (50 + j) (by omega)]; exact hb j hj
  refine ⟨hb, hr.arrays, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals rw [hf _ (by omega)]
  all_goals first | exact hr.index | exact hr.mode | exact hr.node | exact hr.group |
    exact hr.upperLow | exact hr.resultLow | exact hr.upperHead | exact hr.lowerHead |
    exact hr.positiveHead | exact hr.positiveTail | exact hr.negativeHead |
    exact hr.negativeTail | exact hr.lowerClassHead | exact hr.lowerClassTail

theorem mstepProgram_reg_high (c : Config) (r : Nat) (hr : 80 ≤ r) :
    (run mstepProgram c).reg r = c.reg r := by
  apply run_reg_frame
  have h : (regsW mstepProgram).all (fun r => decide (r < 80)) = true := by decide
  intro hm
  have hb : r < 80 := of_decide_eq_true ((List.all_eq_true.mp h) r hm)
  omega

theorem mstepProgram_out (c : Config) : (run mstepProgram c).out = c.out :=
  run_out_frame _ _ (by decide)

/-- An actual bounded run leaves every cell beyond its address bound unchanged. -/
theorem boundedRun_memAbove {bound : Nat} {p : Stmt} {c d : Config} {t : Nat}
    (he : ExecB bound p c t d) : ∀ a, bound ≤ a → d.mem a = c.mem a := by
  induction he with
  | skip c | const r v c | add r a b c | sub r a b c | load r a c h | write r c =>
    intro a ha; rfl
  | store address r c h =>
    intro a ha
    simp [Config.setMem, show a ≠ c.reg address by omega]
  | seq he he' ih ih' => intro a ha; exact (ih' a ha).trans (ih a ha)
  | ifzTrue hz he ih | ifzFalse hn he ih => exact ih
  | loopDone hz => intro a ha; rfl
  | loopNext hn he he' ih ih' => intro a ha; exact (ih' a ha).trans (ih a ha)

/-- The loop executes the scalar-machine transition exactly a fixed number of times. -/
theorem solverLoop_refines {L : Layout} {S : Sol} {post : List Nat} {vertices darts : Nat}
    (hstep : ∀ (c : Config) (s : SMS), Rep L c s → Tables L c S post vertices darts →
      StateBounds L s darts → s.k ≤ post.length →
      ∃ t, ExecB L.limit mstepProgram c t (run mstepProgram c) ∧ t ≤ 2000 ∧
        Rep L (run mstepProgram c) (S.mstep post s) ∧
        Tables L (run mstepProgram c) S post vertices darts)
    (budget : Nat) (init : SMS) (c : Config)
    (hr : Rep L c init) (ht : Tables L c S post vertices darts)
    (hb : StateBounds L init darts) (hk : init.k ≤ post.length) (hc : c.reg 80 = budget) :
    ∃ t c', ExecB L.limit solverLoop c t c' ∧ t ≤ 2002 * budget + 1 ∧
      Rep L c' ((S.mstep post)^[budget] init) ∧
      Tables L c' S post vertices darts ∧ c'.out = c.out ∧
      (∀ r, 80 < r → c'.reg r = c.reg r) ∧
      (∀ a, L.limit ≤ a → c'.mem a = c.mem a) := by
  let I : Nat → Config → Prop := fun j d =>
    Rep L d ((S.mstep post)^[j] init) ∧ Tables L d S post vertices darts ∧
      d.out = c.out ∧ (∀ r, 80 < r → d.reg r = c.reg r) ∧
      (∀ a, L.limit ≤ a → d.mem a = c.mem a)
  have Hstep : ∀ j d, j < budget → I j d → d.reg 80 = budget - j →
      ∃ t d', ExecB L.limit solverBody d t d' ∧ t ≤ 2001 ∧ I (j + 1) d' ∧
        d'.reg 80 + 1 = d.reg 80 := by
    intro j d hj hd hcounter
    obtain ⟨Hdr, Hdt, Hout, Hreg, Hmem⟩ := hd
    obtain ⟨t, He, Ht, Hr, Htb⟩ := hstep d _ Hdr Hdt
      (mstep_iterate_bounded hb ht j) (mstep_iterate_index_le S post hk j)
    let d' := (run mstepProgram d).setReg 80 ((run mstepProgram d).reg 80 -
      (run mstepProgram d).reg 1)
    have Hone : (run mstepProgram d).reg 1 = 1 := Hr.bases.2.1
    have Hcount : (run mstepProgram d).reg 80 = d.reg 80 := mstepProgram_reg_high d 80 (by omega)
    have Hrep : Rep L d' (S.mstep post ((S.mstep post)^[j] init)) := by
      exact Hr.high 80 _ (by omega)
    have Htable : Tables L d' S post vertices darts := Htb.temp 80 _ (by omega)
    refine ⟨t + 1, d', .seq He (.sub 80 80 1 _), by omega, ?_, ?_⟩
    · refine ⟨?_, Htable, ?_, ?_, ?_⟩
      · simpa only [Function.iterate_succ_apply'] using Hrep
      · exact (mstepProgram_out d).trans Hout
      · intro r hrr
        change (d'.reg r) = c.reg r
        simp only [d', Config.setReg]
        rw [ite_eq_right (by omega), mstepProgram_reg_high d r (by omega)]
        exact Hreg r hrr
      · intro a ha; exact (boundedRun_memAbove He a ha).trans (Hmem a ha)
    · change ((run mstepProgram d).setReg 80 _).reg 80 + 1 = _
      simp only [Config.setReg, ↓reduceIte]
      rw [Hone, Hcount]
      omega
  obtain ⟨t, c', He, Ht, Hfinal⟩ := exec_countLoop budget I 2001 Hstep c
    ⟨hr, ht, rfl, fun _ _ => rfl, fun _ _ => rfl⟩ hc
  exact ⟨t, c', He, by omega, Hfinal⟩

end STACS2027.Embed.RAMSolver

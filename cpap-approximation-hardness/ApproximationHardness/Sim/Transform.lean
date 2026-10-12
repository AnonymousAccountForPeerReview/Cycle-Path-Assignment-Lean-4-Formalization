module

public import ApproximationHardness.Sim.XLogic
import Lean.Elab.Tactic.Omega

/-!
# Running a RAM program inside a program with bit input and output

`tr s` runs the program `s` of `ApproximationHardness.RAM.Model` with its memory cell `a` at the cell `2a` and
its output written to the odd cells `1, 3, 5, …` (the `j`-th output number at `2j + 1`, counted by
the register `tPTR`), so that a program run after it can read the output of `s`
(`tr_exec`). Every step of `s` takes at most four steps of `tr s`.
-/

@[expose] public section

namespace STACS2027.Sim

/-- The registers of the transformation, above those of the transformed programs. -/
abbrev tONE : Nat := 188
abbrev tPTR : Nat := 189
abbrev tTMP : Nat := 190

/-- Memory cell `a` at `2a`; the output at the odd cells. -/
def tr : RAM.Stmt → XStmt
  | .skip => .skip
  | .const d c => .const d c
  | .add d a b => .add d a b
  | .sub d a b => .sub d a b
  | .load d a => .seq (.add tTMP a a) (.load d tTMP)
  | .store a b => .seq (.add tTMP a a) (.store tTMP b)
  | .write a => .seq (.add tTMP tPTR tPTR) (.seq (.add tTMP tTMP tONE) (.seq (.store tTMP a) (.add tPTR tPTR tONE)))
  | .seq s t => .seq (tr s) (tr t)
  | .ifz a s t => .ifz a (tr s) (tr t)
  | .loop a body => .loop a (tr body)

/-- All registers of a RAM program below `R`. -/
def RegsLt : RAM.Stmt → Nat → Prop
  | .skip, _ => True
  | .const d _, R => d < R
  | .add d a b, R => d < R ∧ a < R ∧ b < R
  | .sub d a b, R => d < R ∧ a < R ∧ b < R
  | .load d a, R => d < R ∧ a < R
  | .store a b, R => a < R ∧ b < R
  | .write a, R => a < R
  | .seq s t, R => RegsLt s R ∧ RegsLt t R
  | .ifz a s t, R => a < R ∧ RegsLt s R ∧ RegsLt t R
  | .loop a body, R => a < R ∧ RegsLt body R

/-- The configuration `d` of `tr s` represents the configuration `c` of `s`. -/
structure TRel (c : RAM.Config) (d : XConfig) : Prop where
  reg : ∀ i, i < 188 → d.reg i = c.reg i
  one : d.reg tONE = 1
  ptr : d.reg tPTR = c.out.length
  even : ∀ a, d.mem (2 * a) = c.mem a
  odd : ∀ j, d.mem (2 * j + 1) = c.out.getD j 0

theorem TRel.setReg {c : RAM.Config} {d : XConfig} (h : TRel c d) {x : Nat} (hx : x < 188) (v : Nat) :
    TRel (c.setReg x v) (d.setReg x v) := by
  have h1 := h.one; have h2 := h.ptr
  simp only [tONE, tPTR] at h1 h2
  refine ⟨fun i hi => ?_, ?_, ?_, h.even, h.odd⟩
  · simp only [XConfig.setReg, RAM.Config.setReg]; split
    · rfl
    · exact h.reg i hi
  · simp only [XConfig.setReg, tONE]; rw [ite_eq_right (by omega)]; exact h1
  · simp only [XConfig.setReg, RAM.Config.setReg, tPTR]; rw [ite_eq_right (by omega)]; exact h2

theorem TRel.setTmp {c : RAM.Config} {d : XConfig} (h : TRel c d) (v : Nat) : TRel c (d.setReg tTMP v) := by
  have h1 := h.one; have h2 := h.ptr
  simp only [tONE, tPTR] at h1 h2
  refine ⟨fun i hi => ?_, ?_, ?_, h.even, h.odd⟩
  · simp only [XConfig.setReg, tTMP]; rw [ite_eq_right (by omega)]; exact h.reg i hi
  · simp only [XConfig.setReg, tONE, tTMP]; exact h1
  · simp only [XConfig.setReg, tPTR, tTMP]; exact h2

theorem RAM_exec_out {s : RAM.Stmt} {c c' : RAM.Config} {t : Nat} (h : RAM.Exec s c t c') :
    ∃ δ, c'.out = c.out ++ δ ∧ δ.length ≤ t := by
  induction h with
  | write a c => exact ⟨[c.reg a], rfl, by simp⟩
  | seq _ _ ih₁ ih₂ =>
    obtain ⟨δ₁, h₁, l₁⟩ := ih₁; obtain ⟨δ₂, h₂, l₂⟩ := ih₂
    exact ⟨δ₁ ++ δ₂, by rw [h₂, h₁, List.append_assoc], by simp; omega⟩
  | ifzTrue _ _ ih => obtain ⟨δ, h, l⟩ := ih; exact ⟨δ, h, by omega⟩
  | ifzFalse _ _ ih => obtain ⟨δ, h, l⟩ := ih; exact ⟨δ, h, by omega⟩
  | loopDone _ => exact ⟨[], by simp, by simp⟩
  | loopNext _ _ _ ih₁ ih₂ =>
    obtain ⟨δ₁, h₁, l₁⟩ := ih₁; obtain ⟨δ₂, h₂, l₂⟩ := ih₂
    exact ⟨δ₁ ++ δ₂, by rw [h₂, h₁, List.append_assoc], by simp; omega⟩
  | _ => exact ⟨[], by simp [RAM.Config.setReg, RAM.Config.setMem], by simp⟩

/-- **The transformation runs the RAM program.** -/
theorem tr_exec {s : RAM.Stmt} {c c' : RAM.Config} {t : Nat} (h : RAM.Exec s c t c') :
    RegsLt s 188 → ∀ d, TRel c d → ∃ t' d', XExec (tr s) d t' d' ∧ TRel c' d' ∧ d'.inp = d.inp ∧
      d'.out = d.out ∧ t' ≤ 4 * t := by
  induction h with
  | skip c => intro _ d hd; exact ⟨1, d, XExec.skip d, hd, rfl, rfl, by omega⟩
  | const x v c =>
    intro hs d hd
    exact ⟨1, _, XExec.const x v d, hd.setReg hs v, rfl, rfl, by omega⟩
  | add x a b c =>
    intro hs d hd
    obtain ⟨h1, h2, h3⟩ := hs
    refine ⟨1, _, XExec.add x a b d, ?_, rfl, rfl, by omega⟩
    rw [hd.reg a h2, hd.reg b h3]; exact hd.setReg h1 _
  | sub x a b c =>
    intro hs d hd
    obtain ⟨h1, h2, h3⟩ := hs
    refine ⟨1, _, XExec.sub x a b d, ?_, rfl, rfl, by omega⟩
    rw [hd.reg a h2, hd.reg b h3]; exact hd.setReg h1 _
  | load x a c =>
    intro hs d hd
    obtain ⟨h1, h2⟩ := hs
    refine ⟨2, _, XExec.seq (XExec.add tTMP a a d) (XExec.load x tTMP _), ?_, rfl, rfl, by omega⟩
    have e : (d.setReg tTMP (d.reg a + d.reg a)).mem ((d.setReg tTMP (d.reg a + d.reg a)).reg tTMP) = c.mem (c.reg a) := by
      simp only [XConfig.setReg, ite_true]; rw [hd.reg a h2, ← Nat.two_mul, hd.even]
    rw [e]
    exact (hd.setTmp _).setReg h1 _
  | store a b c =>
    intro hs d hd
    obtain ⟨h1, h2⟩ := hs
    refine ⟨2, _, XExec.seq (XExec.add tTMP a a d) (XExec.store tTMP b _), ?_, rfl, rfl, by omega⟩
    have r1 : (d.setReg tTMP (d.reg a + d.reg a)).reg tTMP = 2 * c.reg a := by
      simp only [XConfig.setReg, ite_true]; rw [hd.reg a h1]; omega
    have r2 : (d.setReg tTMP (d.reg a + d.reg a)).reg b = c.reg b := by
      simp only [XConfig.setReg, tTMP]; rw [ite_eq_right (by omega), hd.reg b h2]
    rw [r1, r2]
    have hd' := hd.setTmp (d.reg a + d.reg a)
    refine ⟨hd'.reg, hd'.one, hd'.ptr, fun x => ?_, fun j => ?_⟩
    · simp only [XConfig.setMem, RAM.Config.setMem]
      by_cases hx : x = c.reg a
      · subst hx; simp
      · rw [ite_eq_right (by omega), ite_eq_right hx]; exact hd'.even x
    · simp only [XConfig.setMem, RAM.Config.setMem]
      rw [ite_eq_right (by omega)]; exact hd'.odd j
  | write a c =>
    intro hs d hd
    refine ⟨4, _, XExec.seq (XExec.add tTMP tPTR tPTR d) (XExec.seq (XExec.add tTMP tTMP tONE _)
      (XExec.seq (XExec.store tTMP a _) (XExec.add tPTR tPTR tONE _))), ?_, rfl, rfl, by omega⟩
    have hp := hd.ptr; have ho := hd.one; have ha := hd.reg a hs
    have a1 : a ≠ 190 := by simp [RegsLt] at hs; omega
    have a2 : a ≠ 189 := by simp [RegsLt] at hs; omega
    simp only [tPTR, tONE] at hp ho
    refine ⟨fun i hi => ?_, ?_, ?_, fun x => ?_, fun j => ?_⟩
    · have i1 : i ≠ 190 := by omega
      have i2 : i ≠ 189 := by omega
      simp [tTMP, tPTR, tONE, XConfig.setReg, XConfig.setMem, RAM.Config.emit, i1, i2, hd.reg i hi]
    · simp [tTMP, tPTR, tONE, XConfig.setReg, XConfig.setMem, ho]
    · simp [tTMP, tPTR, tONE, XConfig.setReg, XConfig.setMem, RAM.Config.emit, hp, ho]
    · simp [tTMP, tPTR, tONE, XConfig.setReg, XConfig.setMem, RAM.Config.emit, hp, ho]
      rw [ite_eq_right (by omega)]; exact hd.even x
    · simp [tTMP, tPTR, tONE, XConfig.setReg, XConfig.setMem, RAM.Config.emit, hp, ho, a1, ha]
      by_cases hj : j = c.out.length
      · subst hj; simp; intro h; exact absurd (by omega) h
      · rw [ite_eq_right (by omega), hd.odd j]
        rcases Nat.lt_or_gt_of_ne hj with hl | hl
        · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hl]
        · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (show c.out.length ≤ j by omega),
            List.getElem?_eq_none (show (c.out ++ [c.reg a]).length ≤ j by simp; omega)]
  | seq _ _ ih₁ ih₂ =>
    intro hs d hd
    obtain ⟨t₁, d₁, e₁, r₁, i₁, o₁, l₁⟩ := ih₁ hs.1 d hd
    obtain ⟨t₂, d₂, e₂, r₂, i₂, o₂, l₂⟩ := ih₂ hs.2 d₁ r₁
    exact ⟨t₁ + t₂, d₂, XExec.seq e₁ e₂, r₂, by rw [i₂, i₁], by rw [o₂, o₁], by omega⟩
  | ifzTrue ha _ ih =>
    intro hs d hd
    obtain ⟨t₁, d₁, e₁, r₁, i₁, o₁, l₁⟩ := ih hs.2.1 d hd
    exact ⟨t₁ + 1, d₁, XExec.ifzTrue (by rw [hd.reg _ hs.1]; exact ha) e₁, r₁, i₁, o₁, by omega⟩
  | ifzFalse ha _ ih =>
    intro hs d hd
    obtain ⟨t₁, d₁, e₁, r₁, i₁, o₁, l₁⟩ := ih hs.2.2 d hd
    exact ⟨t₁ + 1, d₁, XExec.ifzFalse (by rw [hd.reg _ hs.1]; exact ha) e₁, r₁, i₁, o₁, by omega⟩
  | loopDone ha =>
    intro hs d hd
    exact ⟨1, d, XExec.loopDone (by rw [hd.reg _ hs.1]; exact ha), hd, rfl, rfl, by omega⟩
  | loopNext ha _ _ ih₁ ih₂ =>
    intro hs d hd
    obtain ⟨t₁, d₁, e₁, r₁, i₁, o₁, l₁⟩ := ih₁ hs.2 d hd
    obtain ⟨t₂, d₂, e₂, r₂, i₂, o₂, l₂⟩ := ih₂ hs d₁ r₁
    exact ⟨t₁ + t₂ + 1, d₂, XExec.loopNext (by rw [hd.reg _ hs.1]; exact ha) e₁ e₂, r₂, by rw [i₂, i₁],
      by rw [o₂, o₁], by omega⟩

end STACS2027.Sim

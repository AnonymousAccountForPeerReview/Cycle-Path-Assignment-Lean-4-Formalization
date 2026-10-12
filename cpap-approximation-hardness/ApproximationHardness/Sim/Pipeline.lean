module

public import ApproximationHardness.Sim.Serialize
public import ApproximationHardness.Sim.Transform
public import ApproximationHardness.Sim.PolyTime
import Lean.Elab.Tactic.Omega

/-!
# Checking the static conditions, and resetting registers
-/

@[expose] public section

namespace STACS2027.Sim

/-- `RegsLt` as a computable test. -/
def regsLtB : RAM.Stmt → Nat → Bool
  | .skip, _ => true
  | .const d _, R => decide (d < R)
  | .add d a b, R => decide (d < R) && decide (a < R) && decide (b < R)
  | .sub d a b, R => decide (d < R) && decide (a < R) && decide (b < R)
  | .load d a, R => decide (d < R) && decide (a < R)
  | .store a b, R => decide (a < R) && decide (b < R)
  | .write a, R => decide (a < R)
  | .seq s t, R => regsLtB s R && regsLtB t R
  | .ifz a s t, R => decide (a < R) && regsLtB s R && regsLtB t R
  | .loop a body, R => decide (a < R) && regsLtB body R

theorem regsLt_of_b : ∀ (s : RAM.Stmt) (R : Nat), regsLtB s R = true → RegsLt s R := by
  intro s R
  induction s with
  | seq s t ihs iht => intro h; simp [regsLtB] at h; exact ⟨ihs h.1, iht h.2⟩
  | ifz a s t ihs iht => intro h; simp [regsLtB] at h; exact ⟨h.1.1, ihs h.1.2, iht h.2⟩
  | loop a b ih => intro h; simp [regsLtB] at h; exact ⟨h.1, ih h.2⟩
  | _ => intro h; simp [regsLtB] at h; simp [RegsLt]; try omega

theorem regsLt_mono : ∀ (s : RAM.Stmt) {R R' : Nat}, R ≤ R' → RegsLt s R → RegsLt s R' := by
  intro s R R' hR
  induction s with
  | seq s t ihs iht => intro h; exact ⟨ihs h.1, iht h.2⟩
  | ifz a s t ihs iht => intro h; exact ⟨by have := h.1; omega, ihs h.2.1, iht h.2.2⟩
  | loop a b ih => intro h; exact ⟨by have := h.1; omega, ih h.2⟩
  | skip => intro _; trivial
  | const => intro h; simp only [RegsLt] at h ⊢; omega
  | add => intro h; simp only [RegsLt] at h ⊢; omega
  | sub => intro h; simp only [RegsLt] at h ⊢; omega
  | load => intro h; simp only [RegsLt] at h ⊢; omega
  | store => intro h; simp only [RegsLt] at h ⊢; omega
  | write => intro h; simp only [RegsLt] at h ⊢; omega

/-- `RegsOK` as a computable test. -/
def regsOKb : XStmt → Bool
  | .skip => true
  | .const d _ => decide (d < 192)
  | .add d a b => decide (d < 192) && decide (a < 192) && decide (b < 192)
  | .sub d a b => decide (d < 192) && decide (a < 192) && decide (b < 192)
  | .load d a => decide (d < 192) && decide (a < 192)
  | .store a b => decide (a < 192) && decide (b < 192)
  | .getBit d => decide (d < 192)
  | .emit a => decide (a < 192)
  | .seq s t => regsOKb s && regsOKb t
  | .ifz a s t => decide (a < 192) && regsOKb s && regsOKb t
  | .loop a body => decide (a < 192) && regsOKb body

theorem regsOK_of_b : ∀ s : XStmt, regsOKb s = true → RegsOK s := by
  intro s
  induction s with
  | seq s t ihs iht => intro h; simp [regsOKb] at h; exact ⟨ihs h.1, iht h.2⟩
  | ifz a s t ihs iht => intro h; simp [regsOKb] at h; exact ⟨h.1.1, ihs h.1.2, iht h.2⟩
  | loop a b ih => intro h; simp [regsOKb] at h; exact ⟨h.1, ih h.2⟩
  | _ => intro h; simp [regsOKb] at h; simp [RegsOK]; try omega

theorem regsOKb_tr : ∀ s : RAM.Stmt, regsLtB s 188 = true → regsOKb (tr s) = true := by
  intro s
  induction s with
  | seq s t ihs iht => intro h; simp [regsLtB] at h; simp [tr, regsOKb, ihs h.1, iht h.2]
  | ifz a s t ihs iht => intro h; simp [regsLtB] at h; simp [tr, regsOKb, ihs h.1.2, iht h.2]; omega
  | loop a b ih => intro h; simp [regsLtB] at h; simp [tr, regsOKb, ih h.2]; omega
  | _ => intro h; simp [regsLtB] at h; simp [tr, regsOKb, tTMP, tPTR, tONE]; try omega

/-- The loop depth of a RAM program. -/
def depthR : RAM.Stmt → Nat
  | .seq s t => max (depthR s) (depthR t)
  | .ifz _ s t => max (depthR s) (depthR t)
  | .loop _ body => depthR body + 1
  | _ => 0

theorem depth_tr : ∀ s : RAM.Stmt, depth (tr s) = depthR s := by
  intro s
  induction s with
  | seq s t ihs iht => simp [tr, depth, depthR, ihs, iht]
  | ifz a s t ihs iht => simp [tr, depth, depthR, ihs, iht]
  | loop a b ih => simp [tr, depth, depthR, ih]
  | _ => simp [tr, depth, depthR]

theorem depth_xseqs : ∀ ss : List XStmt, depth (xseqs ss) = (ss.map depth).foldr max 0 := by
  intro ss
  induction ss with
  | nil => rfl
  | cons s ss ih => simp [xseqs, depth, ih]

theorem regsOKb_xseqs : ∀ ss : List XStmt, regsOKb (xseqs ss) = ss.all regsOKb := by
  intro ss
  induction ss with
  | nil => rfl
  | cons s ss ih => simp [xseqs, regsOKb, ih]

/-! ### Resetting registers -/

def resetC (rs : List Nat) : XStmt := xseqs (rs.map fun r => .const r 0)

theorem xok_resetC : ∀ (rs : List Nat) (c : XConfig), ∃ c', XOk (resetC rs) c c' (rs.length + 1) ∧
    (∀ i, c'.reg i = if i ∈ rs then 0 else c.reg i) ∧ c'.mem = c.mem ∧ c'.inp = c.inp ∧ c'.out = c.out := by
  intro rs
  induction rs with
  | nil => intro c; exact ⟨c, xok_skip c, fun i => by simp, rfl, rfl, rfl⟩
  | cons r rs ih =>
    intro c
    obtain ⟨c', s', h1, h2, h3, h4⟩ := ih (c.setReg r 0)
    refine ⟨c', ((xok_const r 0 c).seq s').mono (by simp; omega), fun i => ?_, h2, h3, h4⟩
    rw [h1]; simp only [XConfig.setReg, List.mem_cons]
    by_cases hi : i = r
    · simp [hi]
    · simp [hi]

end STACS2027.Sim

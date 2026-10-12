module

public import Outerplanar.RAM.BoundedLib
import Mathlib.Tactic

/-!
# Finite register predicates compiled to the RAM

All comparisons use subtraction and zero tests. The compiler reads only its
listed source registers and changes only the macro temporary before executing
the selected continuation. Artifact date: 2026-10-12.
-/

@[expose] public section

namespace STACS2027.Runtimes.GeneralCycles

open STACS2027.RAM

inductive RegTest where
  | truth (b : Bool)
  | equal (a b : ℕ)
  | less (a b : ℕ)
  | both (p q : RegTest)
  | either (p q : RegTest)
  | neg (p : RegTest)
  deriving Repr

namespace RegTest

def sources : RegTest → List ℕ
  | .truth _ => []
  | .equal a b | .less a b => [a, b]
  | .both p q | .either p q => sources p ++ sources q
  | .neg p => sources p

def eval : RegTest → Config → Bool
  | .truth b, _ => b
  | .equal a b, c => decide (c.reg a = c.reg b)
  | .less a b, c => decide (c.reg a < c.reg b)
  | .both p q, c => eval p c && eval q c
  | .either p q, c => eval p c || eval q c
  | .neg p, c => !(eval p c)

def branch : RegTest → Stmt → Stmt → Stmt
  | .truth b, s, u => if b then s else u
  | .equal a b, s, u => ifEq a b s u
  | .less a b, s, u => ifLt a b s u
  | .both p q, s, u => branch p (branch q s u) u
  | .either p q, s, u => branch p s (branch q s u)
  | .neg p, s, u => branch p u s

theorem eval_setReg (p : RegTest) (h : rT ∉ p.sources) (c : Config) (v : ℕ) :
    p.eval (c.setReg rT v) = p.eval c := by
  induction p with
  | truth b => rfl
  | equal a b => simp_all [sources, eval, setReg_reg, eq_comm]
  | less a b => simp_all [sources, eval, setReg_reg, eq_comm]
  | both p q hp hq => simp_all [sources, eval]
  | either p q hp hq => simp_all [sources, eval]
  | neg p hp => simpa [sources, eval] using congrArg Bool.not (hp h)

/-- The selected continuation sees the original state with only the macro
temporary changed. No word-size assumption is used by comparisons. -/
theorem run_branch (p : RegTest) (h : rT ∉ p.sources) (s u : Stmt) (c : Config) :
    ∃ v, run (p.branch s u) c =
      run (if p.eval c then s else u) (c.setReg rT v) := by
  induction p generalizing s u c with
  | truth b =>
    exact ⟨c.reg rT, by rw [setReg_self]; rfl⟩
  | equal a b =>
    have hh : a ≠ rT ∧ b ≠ rT := by simpa [sources, eq_comm] using h
    have ha := hh.1
    have hb := hh.2
    by_cases he : c.reg a = c.reg b
    · exact ⟨0, by simp [branch, eval, run_ifEq ha hb, he]⟩
    · exact ⟨c.reg a - c.reg b + (c.reg b - c.reg a),
        by simp [branch, eval, run_ifEq ha hb, he]⟩
  | less a b =>
    exact ⟨c.reg b - c.reg a, by
      by_cases he : c.reg a < c.reg b <;> simp [branch, eval, run_ifLt, he]⟩
  | both p q hp hq =>
    have hh : rT ∉ p.sources ∧ rT ∉ q.sources := by simpa [sources] using h
    obtain ⟨v, hv⟩ := hp hh.1 (q.branch s u) u c
    rw [branch, hv]
    cases ep : p.eval c with
    | false => exact ⟨v, by simp [eval, ep]⟩
    | true =>
      simp only [↓reduceIte]
      obtain ⟨w, hw⟩ := hq hh.2 s u (c.setReg rT v)
      exact ⟨w, by simpa [eval, ep, eval_setReg q hh.2, setReg_setReg] using hw⟩
  | either p q hp hq =>
    have hh : rT ∉ p.sources ∧ rT ∉ q.sources := by simpa [sources] using h
    obtain ⟨v, hv⟩ := hp hh.1 s (q.branch s u) c
    rw [branch, hv]
    cases ep : p.eval c with
    | true => exact ⟨v, by simp [eval, ep]⟩
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      obtain ⟨w, hw⟩ := hq hh.2 s u (c.setReg rT v)
      exact ⟨w, by simpa [eval, ep, eval_setReg q hh.2, setReg_setReg] using hw⟩
  | neg p hp =>
    obtain ⟨v, hv⟩ := hp h u s c
    exact ⟨v, by cases ep : p.eval c <;> simpa [branch, eval, ep] using hv⟩

theorem branch_loopFree (p : RegTest) {s u : Stmt}
    (hs : LoopFree s) (hu : LoopFree u) : LoopFree (p.branch s u) := by
  induction p generalizing s u with
  | truth b => cases b <;> assumption
  | equal a b => simpa [branch] using And.intro hs hu
  | less a b => simpa [branch] using And.intro hs hu
  | both p q hp hq => exact hp (hq hs hu) hu
  | either p q hp hq => exact hp hs (hq hs hu)
  | neg p hp => exact hp hu hs

theorem branch_memFree (p : RegTest) {s u : Stmt}
    (hs : memFree s = true) (hu : memFree u = true) :
    memFree (p.branch s u) = true := by
  induction p generalizing s u with
  | truth b => cases b <;> assumption
  | equal a b => simp [branch, hs, hu]
  | less a b => simp [branch, hs, hu]
  | both p q hp hq => exact hp (hq hs hu) hu
  | either p q hp hq => exact hp hs (hq hs hu)
  | neg p hp => exact hp hu hs

theorem branch_stores (p : RegTest) {s u : Stmt}
    (hs : stores s = false) (hu : stores u = false) :
    stores (p.branch s u) = false := by
  induction p generalizing s u with
  | truth b => cases b <;> assumption
  | equal a b => simp [branch, hs, hu]
  | less a b => simp [branch, hs, hu]
  | both p q hp hq => exact hp (hq hs hu) hu
  | either p q hp hq => exact hp hs (hq hs hu)
  | neg p hp => exact hp hu hs

theorem branch_writes (p : RegTest) {s u : Stmt}
    (hs : writes s = false) (hu : writes u = false) :
    writes (p.branch s u) = false := by
  induction p generalizing s u with
  | truth b => cases b <;> assumption
  | equal a b => simp [branch, hs, hu]
  | less a b => simp [branch, hs, hu]
  | both p q hp hq => exact hp (hq hs hu) hu
  | either p q hp hq => exact hp hs (hq hs hu)
  | neg p hp => exact hp hu hs

theorem branch_wregs (p : RegTest) {s u : Stmt} {r : ℕ}
    (hr : r ∈ wregs (p.branch s u)) : r = rT ∨ r ∈ wregs s ∨ r ∈ wregs u := by
  induction p generalizing s u with
  | truth b => cases b <;> simp_all [branch]
  | equal a b => simpa [branch, or_assoc, or_left_comm, or_comm] using hr
  | less a b => simpa [branch, or_assoc, or_left_comm, or_comm] using hr
  | both p q hp hq =>
    rcases hp hr with h | h | h
    · exact Or.inl h
    · rcases hq h with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inr h)
  | either p q hp hq =>
    rcases hp hr with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · rcases hq h with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
  | neg p hp =>
    rcases hp hr with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)

def flag (p : RegTest) (d : ℕ) : Stmt := p.branch (.const d 1) (.const d 0)

theorem run_flag (p : RegTest) (h : rT ∉ p.sources) (d : ℕ) (c : Config) :
    (run (p.flag d) c).reg d = if p.eval c then 1 else 0 := by
  obtain ⟨v, hv⟩ := p.run_branch h (.const d 1) (.const d 0) c
  rw [flag, hv]
  cases p.eval c <;> simp

def clear (p : RegTest) (d : ℕ) : Stmt := p.branch (.const d 0) .skip

theorem run_clear (p : RegTest) (h : rT ∉ p.sources) {d : ℕ} (hd : d ≠ rT)
    (c : Config) : (run (p.clear d) c).reg d = if p.eval c then 0 else c.reg d := by
  obtain ⟨v, hv⟩ := p.run_branch h (.const d 0) .skip c
  rw [clear, hv]
  cases p.eval c <;> simp [setReg_reg, hd]

end RegTest

end STACS2027.Runtimes.GeneralCycles

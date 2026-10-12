module

public import ApproximationHardness.RAM.Pass
import Lean.Elab.Tactic.Omega

/-! # Register frames for actual bounded executions, including loops -/

@[expose] public section

namespace STACS2027.RAM

theorem ExecB.reg_frame {S : Nat} {s : Stmt} {c c' : Config} {t r : Nat}
    (h : ExecB S s c t c') (hr : r∉regsW s) : c'.reg r=c.reg r := by
  induction h with
  | skip => rfl
  | const d v c => simp [regsW] at hr;simp [hr]
  | add d a b c => simp [regsW] at hr;simp [hr]
  | sub d a b c => simp [regsW] at hr;simp [hr]
  | load d a c ha => simp [regsW] at hr;simp [hr]
  | store a b c ha => rfl
  | write a c => rfl
  | seq hs ht ihs iht =>
    simp only [regsW,List.mem_append,not_or] at hr
    exact (iht hr.2).trans (ihs hr.1)
  | ifzTrue hz hs ih =>
    simp only [regsW,List.mem_append,not_or] at hr
    exact ih hr.1
  | ifzFalse hz hs ih =>
    simp only [regsW,List.mem_append,not_or] at hr
    exact ih hr.2
  | loopDone hz => rfl
  | loopNext hz hb hl ihb ihl =>
    exact (ihl hr).trans (ihb hr)

end STACS2027.RAM

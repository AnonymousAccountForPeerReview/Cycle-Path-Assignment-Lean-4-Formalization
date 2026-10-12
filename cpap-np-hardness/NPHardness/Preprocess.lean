module

public import NPHardness.BoundedSAT

/-!
Explicitly remove clauses containing opposite literals of the same variable.
The satisfiability-preserving preprocessing is proved below and does not
impose an extra promise on the original input formula.
-/

@[expose] public section
namespace STACS2027
open Complexity.SAT

def tautological (c : Clause) : Bool :=
  c.any fun l => c.any fun r => l.var == r.var && l.positive != r.positive

def removeTautologies (f : CNF) : CNF := f.filter fun c => !tautological c

theorem tautological_eval {c : Clause} (h : tautological c = true) (a : Assignment) :
    evalClause a c = true := by
  simp only [tautological, List.any_eq_true, Bool.and_eq_true, beq_iff_eq,
    bne_iff_ne] at h
  obtain ⟨l, hl, r, hr, hv, hs⟩ := h
  apply List.any_eq_true.mpr
  by_cases he : evalLiteral a l = true
  · exact ⟨l, hl, he⟩
  · refine ⟨r, hr, ?_⟩
    cases l with | mk lv lp =>
      cases r with | mk rv rp =>
        simp only at hv hs he ⊢
        subst rv
        cases lp <;> cases rp <;> simp_all [evalLiteral]

theorem removeTautologies_eval (f : CNF) (a : Assignment) :
    evalCNF a (removeTautologies f) = evalCNF a f := by
  induction f with
  | nil => rfl
  | cons c f ih =>
    cases ht : tautological c with
    | false => simpa [removeTautologies, ht] using congrArg (fun b => evalClause a c && b) ih
    | true => simpa [removeTautologies, ht, tautological_eval ht a] using ih

end STACS2027

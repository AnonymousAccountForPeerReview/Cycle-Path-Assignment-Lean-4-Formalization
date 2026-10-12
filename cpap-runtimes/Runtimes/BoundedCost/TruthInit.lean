module

public import Runtimes.BoundedCost.CandidateDecode
import Mathlib.Tactic

/-! The initial all-false assignment is written into the dense positive and
negative literal truth cells by a linear bounded RAM scan. -/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost.TruthInit

open STACS2027 STACS2027.RAM Complexity.SAT

abbrev candidateBase : ℕ := 203
abbrev variableCount : ℕ := 220
abbrev index : ℕ := 420
abbrev codeIndex : ℕ := 421
abbrev value : ℕ := 422

def body : Stmt :=
  .seq (.add codeIndex index index)
    (.seq (.const value 0) (.seq (st candidateBase codeIndex value)
      (.seq (inc codeIndex) (.seq (.const value 1) (st candidateBase codeIndex value)))))

def program : Stmt := forUp index variableCount body

def Inv (candidate n : ℕ) (memory : ℕ → ℕ) (out : List ℕ) (j : ℕ) (c : Config) : Prop :=
  c.reg candidateBase = candidate ∧ c.reg variableCount = n ∧
    c.mem = CandidateDecode.prefixMemory memory candidate (fun _ => false) j ∧ c.out = out

theorem body_spec {S candidate n : ℕ} {memory : ℕ → ℕ} {out : List ℕ}
    (hS : candidate + 2 * n ≤ S) (j : ℕ) (hj : j < n) :
    HTB S body
      (fun c => Inv candidate n memory out j c ∧ c.reg index = j ∧ c.reg variableCount = n)
      (fun c => Inv candidate n memory out (j + 1) c ∧
        c.reg index = j ∧ c.reg variableCount = n) 12 := by
  refine HTB.run_le (by decide) (by decide) ?_
  rintro c ⟨⟨hc, hn, hm, ho⟩, hi, _⟩
  have hstep : upd (upd (CandidateDecode.prefixMemory memory candidate (fun _ => false) j)
      (candidate + 2 * j) 0) (candidate + 2 * j + 1) 1 =
        CandidateDecode.prefixMemory memory candidate (fun _ => false) (j + 1) := by
    simpa only [CandidateDecode.bit, Bool.not_false, Bool.false_eq_true, eq_self, ↓reduceIte] using
      CandidateDecode.prefixMemory_succ memory candidate (fun _ => false) j
  refine ⟨?_, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · addr_ok [body, hc, hi]
  all_goals simp +decide only [Inv, body, run_seq', run_add, run_const, run_st, run_inc,
    setReg_reg, setReg_mem, setMem_reg, setMem_mem_upd, setReg_out, setMem_out,
    hc, hn, hm, ho, hi, ↓reduceIte, show j + j = 2 * j by omega,
    show j + j + 1 = 2 * j + 1 by omega, ← Nat.add_assoc, hstep]

theorem program_spec {S candidate n : ℕ} {memory : ℕ → ℕ} {out : List ℕ}
    (hS : candidate + 2 * n ≤ S) :
    HTB S program
      (fun c => c.reg candidateBase = candidate ∧ c.reg variableCount = n ∧
        c.mem = memory ∧ c.out = out)
      (fun c => c.reg candidateBase = candidate ∧ c.reg variableCount = n ∧
        c.mem = CandidateDecode.prefixMemory memory candidate (fun _ => false) n ∧ c.out = out)
      (16 * n + 3) := by
  have hl := HTB.forUpC (S := S) (i := index) (n := variableCount)
    (N := n) (body := body) (Inv candidate n memory out) 12
    (by decide) (by decide) (by decide) (fun _ => by indep [Inv])
    (fun j hj => body_spec hS j hj)
  refine hl.mono ?_ (fun c hc => hc.1) (by omega)
  rintro c ⟨hc, hn, hm, ho⟩
  exact ⟨⟨hc, hn, by simpa using hm, ho⟩, hn⟩

end STACS2027.Runtimes.BoundedCost.TruthInit

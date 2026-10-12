module

public import Runtimes.BoundedCost.ArrayBlocks
import Mathlib.Tactic

/-! A counted RAM loop computes the factor fifteen to the current budget.
Each multiplication uses four doublings and one subtraction. -/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost.OptPowerRAM

open STACS2027 STACS2027.RAM

abbrev budget : ℕ := 622
abbrev value : ℕ := 663
abbrev counter : ℕ := 671
abbrev temporary : ℕ := 672

def body : Stmt :=
  .seq (.add temporary value value)
    (.seq (.add temporary temporary temporary)
      (.seq (.add temporary temporary temporary)
        (.seq (.add temporary temporary temporary) (.sub value temporary value))))

def program : Stmt := .seq (.const value 1) (forUp counter budget body)

theorem body_spec {S p j : ℕ} :
    HTB S body (fun c => c.reg value = 15 ^ j ∧ c.reg counter = j ∧ c.reg budget = p)
      (fun c => c.reg value = 15 ^ (j + 1) ∧ c.reg counter = j ∧ c.reg budget = p) 5 := by
  refine HTB.run_le (by decide) (by decide) ?_
  rintro c ⟨hv, hc, hp⟩
  refine ⟨AddrOK.of_memFree (by decide), ?_, ?_, ?_⟩
  · simp +decide only [body, run_seq', run_add, run_sub, setReg_reg, temporary, value,
      counter, budget, ↓reduceIte, hv, Nat.pow_succ]
    omega
  · simpa +decide [body] using hc
  · simpa +decide [body] using hp

theorem program_spec {S p : ℕ} (c₀ : Config) (hp : c₀.reg budget = p) :
    HTB S program (· = c₀)
      (fun c => c.reg value = 15 ^ p ∧ c.reg budget = p ∧
        c.mem = c₀.mem ∧ c.out = c₀.out ∧ Frame program c₀ c)
      (100 * (p + 1)) := by
  let Inv := fun j (c : Config) => c.reg value = 15 ^ j
  have hloop := HTB.forUpC (S := S) (i := counter) (n := budget) (N := p) (body := body)
    Inv 5 (by decide) (by decide) (by decide)
    (fun j => by indep [Inv, value, counter, rT])
    (fun j _ => body_spec (S := S) (p := p) (j := j))
  have hinit : HTB S (.const value 1) (· = c₀) (fun c => Inv 0 c ∧ c.reg budget = p) 1 := by
    refine HTB.run_le (by decide) (by decide) ?_
    intro c hc
    subst c
    exact ⟨AddrOK.of_memFree (by decide), by simp [Inv], by simpa +decide [value, budget] using hp⟩
  intro c hc
  subst c
  obtain ⟨c, time, he, hpost, ht⟩ := (hinit.seq hloop) c₀ rfl
  exact ⟨c, time, he, ⟨hpost.1, hpost.2.2, he.mem_frame (by decide),
    he.out_frame (by decide), he.frame⟩, by omega⟩

theorem program_registerFrame {S time : ℕ} {c c' : Config}
    (he : ExecB S program c time c') {r : ℕ}
    (hr : r ≠ value ∧ r ≠ counter ∧ r ≠ temporary ∧ r ≠ rT) :
    c'.reg r = c.reg r := by
  apply he.reg_frame
  simp +decide [program, body, forUp, upLoop, inc, addc, wregs,
    hr.1, hr.2.1, hr.2.2.1, hr.2.2.2]

end STACS2027.Runtimes.BoundedCost.OptPowerRAM

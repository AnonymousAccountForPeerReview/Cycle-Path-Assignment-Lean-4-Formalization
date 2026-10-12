module

public import Runtimes.BoundedCost.Form
import Mathlib.Tactic

/-!
# Theorem 4 on the RAM: the construction writes the solver's input

`stepOut_spec`: with the codes of `Γ'` in memory, the output phase writes `Ψ`, `|Γ'|` and the
codes plus `2`, which is `a2In (shiftF Γ') Ψ` (`codes_shiftF`: renaming every variable `v` to
`v + 1` adds `2` to its codes), within `18 |Γ'| + 6` steps; it reads the code array only.
`build5_spec`: the whole construction `build5 = form5 ; stepOut`, from the input
`boundedCostInput g k Ψ`, within `formCost g k Ψ + 18 |Γ'| + 6` steps and the addresses below
`bC5 g k + 2 |Γ'|`.
-/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 STACS2027.RAM STACS2027.Runtimes.ZeroCost Complexity.SAT

variable {S : ℕ}

/-- The output after `q` codes. -/
def OutI (g : Graph) (k Ψ : ℕ) (cl : List ℕ) (q : ℕ) (c : Config) : Prop :=
  Arr c.mem (bC5 g k) cl ∧ c.reg gCL = bC5 g k ∧
    c.out = Ψ :: (cl.length / 2) :: (cl.take q).map (· + 2)

theorem outBody_spec (g : Graph) (k Ψ : ℕ) (cl : List ℕ) (hS : bC5 g k + cl.length ≤ S) (q : ℕ)
    (hq : q < cl.length) :
    HTB S outBody (fun c => OutI g k Ψ cl q c ∧ c.reg sQ = q ∧ c.reg sX = cl.length)
      (fun c => OutI g k Ψ cl (q + 1) c ∧ c.reg sQ = q ∧ c.reg sX = cl.length) 5 := by
  refine HTB.run_le (by decide) (by decide) fun c ⟨⟨hA, hC, ho⟩, hQ, hX⟩ => ?_
  refine ⟨by addr_ok [outBody, hC, hQ], ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  all_goals simp +decide only [outBody, run_seq', run_ld, run_addc (show sY ≠ rT by decide),
    run_write, setReg_reg, setReg_mem, setReg_out, emit_reg, emit_mem, emit_out, ↓reduceIte, hC, hQ,
    hX, ho]
  · exact hA
  · rw [hA _ hq, List.take_add_one, List.getElem?_eq_getElem hq]
    simp only [List.map_append, Option.toList_some, List.map_cons, List.map_nil, List.cons_append]

/-- **The output phase**: `a2In (shiftF Γ') Ψ`. -/
theorem stepOut_spec (g : Graph) (k Ψ : ℕ)
    (hS : bC5 g k + (TwoSat.codes (almostFormula g k Ψ)).length ≤ S) :
    HTB S stepOut (fun c => HS g k (fun _ => 0) (almostFormula g k Ψ) c ∧ c.reg gPSI = Ψ)
      (fun c => c.out = a2In (shiftF (almostFormula g k Ψ)) Ψ)
      (18 * (almostFormula g k Ψ).length + 6) := by
  set f := almostFormula g k Ψ
  set cl := TwoSat.codes f
  have hcl : cl.length = 2 * f.length := length_codes_almost g k Ψ
  have h0 : HTB S (.seq (.seq (.write gPSI) (.write gNC)) (.add sX gNC gNC))
      (fun c => HS g k (fun _ => 0) f c ∧ c.reg gPSI = Ψ)
      (fun c => OutI g k Ψ cl 0 c ∧ c.reg sX = cl.length) 3 := HTB.of_HT rfl <| by
    refine HT.run_le (by decide) (by decide) fun c ⟨⟨hG, hfr, hn, hM, ho⟩, hp⟩ => ?_
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    all_goals simp +decide only [run_seq', run_write, run_add, setReg_reg, setReg_mem, setReg_out,
      emit_reg, emit_mem, emit_out, ↓reduceIte, hp, hn, ho, hG.rcl]
    · exact hM.mcodes
    · simp [hcl]
    · omega
  have hl := HTB.forUpC (S := S) (i := sQ) (n := sX) (N := cl.length) (body := outBody)
    (OutI g k Ψ cl) 5 (by decide) (by decide) (by decide) (fun j => by indep [OutI])
    (fun q hq => outBody_spec g k Ψ cl (by omega) q hq)
  refine (HTB.assoc (HTB.assoc (h0.seq hl))).mono (fun _ h => h) (fun c ⟨⟨_, _, ho⟩, _, _⟩ => ?_)
    (by omega)
  rw [ho, List.take_length, a2In, codes_shiftF, length_shiftF, hcl]
  simp [cl]

/-- The cost of the construction. -/
def buildCost (g : Graph) (k Ψ : ℕ) : ℕ := formCost g k Ψ + (18 * (almostFormula g k Ψ).length + 6)

/-- The space of the construction (and of the machine for `Ψ = 0`, up to the 2-SAT phase). -/
def formSpace (g : Graph) (k Ψ : ℕ) : ℕ := bC5 g k + 2 * (almostFormula g k Ψ).length

/-- **The construction of Theorem 4**: writes the solver's input `a2In (shiftF Γ') Ψ`. -/
theorem build5_spec (g : Graph) (k Ψ : ℕ) :
    HTB (formSpace g k Ψ) build5 (fun c => c = initial (boundedCostInput g k Ψ))
      (fun c => c.out = a2In (shiftF (almostFormula g k Ψ)) Ψ) (buildCost g k Ψ) := by
  have hS : bC5 g k + (TwoSat.codes (almostFormula g k Ψ)).length ≤ formSpace g k Ψ := by
    rw [length_codes_almost]; rfl
  exact (form5_spec g k Ψ hS).seq (stepOut_spec g k Ψ hS)

end STACS2027.Runtimes.BoundedCost

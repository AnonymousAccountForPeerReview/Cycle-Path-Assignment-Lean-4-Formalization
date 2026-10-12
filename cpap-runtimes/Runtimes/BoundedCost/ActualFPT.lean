module

public import Runtimes.BoundedCost.ActualCompilerRAM
public import Runtimes.BoundedCost.All

/-! The manuscript's bounded-cost runtime follows from the executed Almost
2-SAT compiler and retains only the cited almost-linear flow contract. -/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 STACS2027.RAM

theorem boundedCost_ram_fpt_from_citedFlow {F : Stmt} {T : ℕ → ℕ}
    (hF : Flow.MinCostFlowSolver F T) (hAL : Flow.AlmostLinear T) :
    ∃ (prog : RAM.Stmt) (C : ℕ), ∀ (g : Graph) (k budget : ℕ), 4 ≤ k →
      ∃ (out : List ℕ) (steps : ℕ),
        RAM.ComputesIn prog (boundedCostInput g k budget) out steps
          (C * (15 ^ budget * budget * ((budget + 1) * k * k * (cycles g k).length +
            k * (cycles g k).length * (cycles g k).length) ^ 3 + k * k * (cycles g k).length +
            k * (cycles g k).length * (cycles g k).length + g.length + 1)) ∧
        steps ≤ C * (15 ^ budget * budget * ((budget + 1) * k * k * (cycles g k).length +
            k * (cycles g k).length * (cycles g k).length) ^ 3 + k * k * (cycles g k).length +
            k * (cycles g k).length * (cycles g k).length + g.length + 1) ∧
        BoundedCostAnswer g k budget out := by
  obtain ⟨constant, hsolver, hbound⟩ := actualCompilerRAM_fpt hF hAL
  exact boundedCost_ram_fpt hsolver hbound

/-- The manuscript's bound for every cycle length at least three uses one
executed program and the same sole cited flow contract. -/
theorem boundedCost_ram_all_from_citedFlow {F : Stmt} {T : ℕ → ℕ}
    (hF : Flow.MinCostFlowSolver F T) (hAL : Flow.AlmostLinear T) :
    ∃ (prog : RAM.Stmt) (C : ℕ), ∀ (g : Graph) (k budget : ℕ), 3 ≤ k →
      ∃ (out : List ℕ) (steps : ℕ),
        RAM.ComputesIn prog (boundedCostInput g k budget) out steps
          (C * (15 ^ budget * budget * ((budget + 1) * k * k * (cycles g k).length +
            k * (cycles g k).length * (cycles g k).length) ^ 3 + k * k * (cycles g k).length +
            k * (cycles g k).length * (cycles g k).length + g.length + 1)) ∧
        steps ≤ C * (15 ^ budget * budget * ((budget + 1) * k * k * (cycles g k).length +
            k * (cycles g k).length * (cycles g k).length) ^ 3 + k * k * (cycles g k).length +
            k * (cycles g k).length * (cycles g k).length + g.length + 1) ∧
        BoundedCostAnswer g k budget out := by
  obtain ⟨constant, hsolver, hbound⟩ := actualCompilerRAM_fpt hF hAL
  exact boundedCost_ram_all_almostLinear hF hAL hsolver hbound

end STACS2027.Runtimes.BoundedCost

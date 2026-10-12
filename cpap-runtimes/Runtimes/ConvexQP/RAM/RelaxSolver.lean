module

public import Runtimes.ConvexQP.RAM.Main
public import Runtimes.ConvexQP.RAM.ParseRam
public import Runtimes.ConvexQP.RAM.EllRam
public import Runtimes.ConvexQP.RAM.KmoRam

/-!
# Lemma 16 on the RAM

The relaxation of Section 7.2 is solved **exactly** in polynomial time on the unit-cost
add/subtract RAM: the machine `relaxSolverMachine` (the parser with the constants `parseProg`,
Phase E `ellProg` — the rational central-cut ellipsoid method — and Phases K, M, O `kmoProg` —
the KKT pattern, the move to a vertex with bordered adjugates, and the output) reads the graph,
`k` and the enumerated `k`-cycles (`zeroCostInput g k`, as for Corollary 5) and writes an optimal
fractional solution `D :: W₀ ++ ⋯ ++ W_{t−1}` within `C · (|input| + 2)^10` steps and as many
memory cells.

* `relaxSolver_ram`: the output is exactly `solveExact` (the algorithm EXACT);
* `relaxSolver_ram_optimal`: the output is an optimal fractional solution
  (`OptimalFractional`, the hypothesis of Theorems 17 and 18), with `t` weight lists of length
  `k`.

Both are stated for time **and** space (`ComputesIn`: every address the run reads or writes is
below `C · (|input| + 2)^10`, the input included), as `relaxSolver_ram_space_of` /
`relaxSolver_ram_optimal_space_of` applied to the bounded specifications of the three parts: the
parser `parse_ramB` (no memory indexed by a vertex label: the sorting front end `Sort.front`),
Phase E `phaseE_ramB` and Phases K, M, O `phaseKMO_ramB`.

On this RAM every step adds at most one bit to the numbers, so the polynomial step bound is also
a polynomial bound on the bit complexity.
-/

@[expose] public section

namespace STACS2027.Runtimes.QPRam

open STACS2027 STACS2027.RAM STACS2027.Runtimes.ConvexQP

/-- **The machine of Lemma 16**. -/
def relaxSolverMachine : Stmt := relaxSolverProg parseProg ellProg kmoProg

/-- **Lemma 16 on the RAM within polynomial time and space** (output), given the bounded
specifications of Phase E and Phases K, M, O. -/
theorem relaxSolver_ram_space_of (h₂ : PhaseERamB ellProg) (h₃ : PhaseKMORamB kmoProg) :
    ∃ C : ℕ, ∀ (g : Graph) (k : ℕ), g.Nodup →
      ∃ T, ComputesIn relaxSolverMachine (ZeroCost.zeroCostInput g k)
          ((solveExact g k ((cycles g k).map selectedOptions)).1 ::
            (solveExact g k ((cycles g k).map selectedOptions)).2.flatten) T
          (C * ((ZeroCost.zeroCostInput g k).length + 2) ^ 10) ∧
        T ≤ C * ((ZeroCost.zeroCostInput g k).length + 2) ^ 10 :=
  relaxSolver_ram_of parse_ramB h₂ h₃

/-- **Lemma 16 on the RAM within polynomial time and space** (optimality), given the bounded
specifications of Phase E and Phases K, M, O. -/
theorem relaxSolver_ram_optimal_space_of (h₂ : PhaseERamB ellProg) (h₃ : PhaseKMORamB kmoProg) :
    ∃ C : ℕ, ∀ (g : Graph) (k : ℕ), g.Nodup →
      ∃ (D : ℕ) (W : List (List ℕ)) (T : ℕ),
        ComputesIn relaxSolverMachine (ZeroCost.zeroCostInput g k) (D :: W.flatten) T
          (C * ((ZeroCost.zeroCostInput g k).length + 2) ^ 10) ∧
        T ≤ C * ((ZeroCost.zeroCostInput g k).length + 2) ^ 10 ∧
        W.length = (cycles g k).length ∧ (∀ w ∈ W, w.length = k) ∧
        OptimalFractional g D (((cycles g k).map selectedOptions).zip W) :=
  relaxSolver_ram_optimal_of parse_ramB h₂ h₃

/-- **Lemma 16 on the RAM** (output, running time and space): on
`zeroCostInput g k` for a duplicate-free graph `g`, the machine outputs `solveExact`'s common
denominator `D` and then the weights, cycle by cycle, within `C · (|input| + 2)^10` steps, by a
run that accesses only the addresses below `C · (|input| + 2)^10` (the input included). -/
theorem relaxSolver_ram : ∃ C : ℕ, ∀ (g : Graph) (k : ℕ), g.Nodup →
    ∃ T, ComputesIn relaxSolverMachine (ZeroCost.zeroCostInput g k)
        ((solveExact g k ((cycles g k).map selectedOptions)).1 ::
          (solveExact g k ((cycles g k).map selectedOptions)).2.flatten) T
        (C * ((ZeroCost.zeroCostInput g k).length + 2) ^ 10) ∧
      T ≤ C * ((ZeroCost.zeroCostInput g k).length + 2) ^ 10 :=
  relaxSolver_ram_space_of phaseE_ramB phaseKMO_ramB

/-- **Lemma 16 on the RAM** (duplicate-free `g`): `D :: W₀ ++ ⋯ ++ W_{t−1}`, an optimal solution of
the relaxation of Section 7.2, within `C (|input| + 2)^10` steps and addresses. -/
theorem relaxSolver_ram_optimal : ∃ (prog : Stmt) (C : ℕ), ∀ (g : Graph) (k : ℕ), g.Nodup →
    ∃ (D : ℕ) (W : List (List ℕ)) (T : ℕ),
      ComputesIn prog (ZeroCost.zeroCostInput g k) (D :: W.flatten) T
        (C * ((ZeroCost.zeroCostInput g k).length + 2) ^ 10) ∧
      T ≤ C * ((ZeroCost.zeroCostInput g k).length + 2) ^ 10 ∧
      W.length = (cycles g k).length ∧ (∀ w ∈ W, w.length = k) ∧
      OptimalFractional g D (((cycles g k).map selectedOptions).zip W) :=
  ⟨relaxSolverMachine, relaxSolver_ram_optimal_space_of phaseE_ramB phaseKMO_ramB⟩

end STACS2027.Runtimes.QPRam

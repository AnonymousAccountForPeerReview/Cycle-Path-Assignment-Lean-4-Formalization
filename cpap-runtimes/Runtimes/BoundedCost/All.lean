module

public import Runtimes.BoundedCost.Main
public import Runtimes.BoundedCost.Top
public import Runtimes.BoundedCost.Triangle
public import Runtimes.BoundedCost.TriCheck
public import Runtimes.BoundedCost.TriDecide

/-!
# Theorem 4 on the RAM: all files

The cited Almost 2-SAT algorithm (ANONYMIZED–ANONYMIZED, `O(15^Ψ Ψ m³)`) is the hypothesis
`Almost2SatSolver F T` (`Runtimes.BoundedCost.Solver`, with `FPTBound T` for the manuscript's form),
like the min-cost flow algorithm (`Runtimes/Flow/Solver.lean`); every other program is proved
with its time and its memory (`RAM.ComputesIn`).

* `Runtimes.BoundedCost.Main`: `boundedCost_ram` (`k ≥ 4`): the programs `zero5` (`Ψ = 0`, the formalized
  linear 2-SAT), `build5` (the formula `Γ'` in the solver's input format) and `extract5` (the
  paths from the solver's answer), each within `C ((Ψ+1)k²t + kt² + m + 1)` steps and addresses,
  and the solver within `T Ψ N'` on the formula's input of length `N' = 2|Γ'| + 2`;
* `Runtimes.BoundedCost.Top`: the single program `boundedCostTop F` (`boundedCost_single`) and the manuscript's
  bound `O(15^Ψ Ψ ((Ψ+1)k²t + kt²)³ + k²t + kt² + m)` in time and memory (`boundedCost_ram_fpt`);
* `Runtimes.BoundedCost.TriDecide`: `boundedCost_triangle`, `boundedCost_triangle_almostLinear` (`k = 3`,
  under the min-cost flow hypothesis; the flow construction with the sorting front end,
  `Runtimes/Flow/SortTri.lean`); `boundedCost_ram_all`, `boundedCost_ram_all_almostLinear`: one machine
  for all `k ≥ 3`;
* `Runtimes.BoundedCost.TriCheck`: the cost check `triCheck` used by the decision for `k = 3`;
* `Runtimes.BoundedCost.Triangle`: `boundedCost_triangle_opt`, `boundedCost_triangle_opt_almostLinear` (`k = 3`,
  optimization form).

The phases (`Init`, `Pc`, `Ov`, `Form`, `Out`, `Extract`, `Zero`) are `HTB S` triples; for every
`k ≥ 3` the cycle vertices are relabelled by the sorting front end `Sort.front` (no memory is
indexed by a vertex label, and no memory bound contains `labelBound g`).
-/

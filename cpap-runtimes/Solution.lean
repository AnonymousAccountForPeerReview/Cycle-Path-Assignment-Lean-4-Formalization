module

public import Runtimes

/-! Proofs of the 31 compared theorems listed in `comparator.json`, all in the namespace
`STACS2027.Runtimes`: `TwoSat.exists_linear_twoSat` (`Runtimes/TwoSatMain.lean`),
`ZeroCost.zeroCost_ram` (`Runtimes/ZeroCost.lean`), `C4.fourCycles_ram_semantic`,
`C4.fourCycles_ram_paper_semantic` and `C4.fourCycles_ram_simple_semantic`
(`Runtimes/C4/Statement.lean`), `Flow.cpap4_flow_ram_semantic` and `Flow.triangle_ram_semantic`
(`Runtimes/Flow/Statement.lean`), `Flow.cpap4_flow_ram_almostLinear` and
`Flow.triangle_ram_almostLinear` (`Runtimes/Flow/Main.lean`), `Flow.cpap4_flow_single`,
`Flow.cpap4_flow_single_almostLinear`, `Flow.triangle_single` and
`Flow.triangle_single_almostLinear` (`Runtimes/Flow/Single.lean`),
`cpap4_enum_ram_explicit_semantic` and `cpap4_enum_ram_semantic` (`Runtimes/Cpap4EnumStatement.lean`),
`BoundedCost.boundedCost_ram` (`Runtimes/BoundedCost/Main.lean`), `BoundedCost.boundedCost_ram_fpt`
(`Runtimes/BoundedCost/Top.lean`), `BoundedCost.boundedCost_triangle`, `BoundedCost.boundedCost_triangle_almostLinear`,
`BoundedCost.boundedCost_ram_all` and `BoundedCost.boundedCost_ram_all_almostLinear` (`Runtimes/BoundedCost/TriDecide.lean`),
`Greedy.greedy_ram` and `Greedy.greedy_guarantee_ram` (`Runtimes/Greedy/Main.lean`), and
`QPRam.relaxSolver_ram_optimal` (`Runtimes/ConvexQP/RAM/RelaxSolver.lean`), plus the exact claim
`Flow.sortedNetworkConstruction` (`Runtimes/Flow/EnumeratedConstruction.lean`). Importing `Runtimes` brings
in, and audits, the whole library. -/

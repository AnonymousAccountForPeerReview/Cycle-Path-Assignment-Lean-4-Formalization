# Use of the NP-completeness foundation, the `cpap-np-hardness` formalization and Max3SAT-MaxSNP-APX-Lean4

This project depends on three Lean developments, each a Lake dependency and never copied into this package (the foundation is fetched by git
at a full commit; the formalizations of the other sections are taken from this repository by
path):

* The NP-completeness foundation `NPCompleteness-Lean4` (commit
  `3e603e795b44fedcf7d6dd65b7d1e30547ead925`). The library imports
  `Complexity.SAT` for CNF formulas, truth assignments and their unary code
  `encode`, and, for `cpap_lreduction_polyTime`, the foundation's machine
  model: single-tape machines and `PolyTime` (`Complexity.Classes`,
  `Complexity.PolynomialBound`), its structured stack language with exact
  instruction costs (`Complexity.StackTableauProgram`,
  `Complexity.Restricted.Commands`, `Complexity.Restricted.LeExtract`) and the
  compiler theorem `StackCompile.polyTime_of_stack` (`Complexity.StackCompile`),
  which turns a stack
  program with a polynomial bound on its instruction count into a
  `PolyTime` word function. Nothing in the foundation is modified or re-proved;
  the instance map is a new stack program (`ApproximationHardness/Registered/`) whose
  correctness and cost are proved here.
* `cpap-np-hardness`, the formalization of Section 5 of the same manuscript, in this repository (the Lake path dependency `../cpap-np-hardness`), which requires the same
  foundation at the same commit. The library imports `NPHardness.GlobalReduction`
  (and through it the Theorem 8 construction, its gadget lemmas and the cost
  decomposition of the glued graph), and `NPHardness.GraphEncoding` for its CPAP
  record format (`GraphOutput`), in which the polynomial-time instance map
  writes its output.
* Max3SAT-MaxSNP-APX-Lean4 (commit
  `10079b2a14bd0df47d2a24364133f6008b9c207f`, the commit that restricts MaxSNP₀ to structures of
  fixed signatures on the universe of the instance and MaxSNP to NPO problems; not modified here), Lake
  package `pcp`, in a derived packaging at commit `5a0499a4b577115d25c8e8c7f08c3aee99441f1e`.
  The library imports its optimization problems, L-reductions, MaxSNP, APX and PTAS
  (`ComplexityExt.Approx.Defs`, `ComplexityExt.PCP.Defs`), its `PT` framework for polynomial
  time (`PT.All`), and its hardness theorems (`Hardness.Occ.Main`, `Hardness.Final.Main`,
  `Hardness.Final.Max3SAT`, `Hardness.Witness.Main`), and through them Mathlib `v4.35.0-rc2`.
  The derived packaging exists because Lake resolves an import by module name alone (every
  package whose libraries match the name provides the module, and two packages may not both
  provide it): the foundation's library `Complexity` claims every module `Complexity.*`. The
  upstream `Complexity/` directory holds 75 files byte-identical to the foundation at
  `3e603e7`, which are removed (the foundation provides them), and 12 others
  (`Approx/Defs`, `PCP/Defs`, `Reg`, `Reg/*`, `Witness/*`), which are moved under the prefix
  `ComplexityExt`; the `import` lines naming them are rewritten, and nothing else changes (the
  declarations keep their names and namespaces, `Complexity.OptProblem` and so on). The package
  ships `DERIVED.md`, `derive_pcp.sh`, which rebuilds it from the upstream commit, and
  `verify_derived_pcp.sh`, which undoes the move and the rewriting and compares every file byte
  for byte with the upstream commit and the foundation (308 unchanged, 75 provided by the
  foundation, 12 moved). The URL in `lakefile.toml` must be replaced by that of a published
  repository of the derived packaging.

`lakefile.toml` requires all three and `lake-manifest.json` records them;
`scripts/check_repository.py` checks the pin of the foundation, the paths of the other
dependencies and that no copy is vendored.

## What the Challenge copies

Following the foundation's `docs/FOUNDATION.md` and the `cpap-np-hardness` formalization's
`docs/FOUNDATION.md` ("Reusing this formalization downstream"), `Challenge.lean`
copies, verbatim, with docstrings and in the same order:

* from the foundation's own `Challenge.lean`, its machine model as one block,
  `Symbol` through `NPComplete` (symbols, words, tapes, single-tape machines,
  runs, `PolyTime`, `InNP`, `NPHard`, `NPComplete`), so that `PolyTime` in the
  compared statements is the foundation's definition, followed by `InP` from
  `Complexity/Classes.lean` (used by `PEqNP`);
* from the foundation's `Complexity/SAT.lean`, the `Complexity.SAT`
  declarations `Word`, `Assignment`, `Literal`, `Clause`, `CNF`,
  `evalLiteral`, `evalClause`, `evalCNF`, `Satisfiable`, `IsThreeCNF`, `clauseBound`,
  `variableBound` and the unary code `writeNat`, `writeValues`, `writeList`,
  `encodeLiteral`, `encodeClause`, `encode`; from `Complexity/PlanarSAT.lean`
  the incidence graph `incidenceGraph`; and from `Complexity/Planarity.lean`
  its definition of planarity, `iterate`, `Hypermap`, `cycleCount`,
  `Hypermap.linked`, `componentCount`, `eulerLhs`, `eulerRhs`, `genus`,
  `Planar`, `halfEdgeEnd`, `PlanarGraph`;
* from the `cpap-np-hardness` library, the `STACS2027` declarations of the cycle-path
  assignment problem (`Edge` through `HasAssignment`, exactly the declarations
  the Section 5 Challenge copies for its own statement), the Theorem 8
  construction (`Link` through `formulaGraph`: `NPHardness/Gadgets.lean`,
  `SubdivisionPrograms.lean`, `OccurrencePorts.lean`, `VertexGluing.lean`,
  `GraphRelabel.lean`, `GlobalGraph.lean`), the occurrence counts of
  Definition 7 (`occurrences`, `BoundedOccurrence`, `ClauseVariablesDistinct`),
  `tautological`, the CPAP record format of `NPHardness/GraphEncoding.lean`
  (`validGraphRecord`, `recordEdge`, `instructionGraph`, `instructionBudget`,
  `ValidGraphInstructions`), and the oriented construction of
  Theorem 8 for planar formulas (`Oriented.Orientation`, `Oriented.orientSide`,
  `Oriented.clauseVertex`, `Oriented.placedClauseGraph`, `Oriented.formulaGraph`
  of `OrientedVertexGluing.lean` and `OrientedGlobalGraph.lean`, with the section
  variable `[Orientation]`, and `EndpointChoices`, `orientedFormulaGraph` of
  `OrientedGluing.lean`);
* from Max3SAT-MaxSNP-APX-Lean4 (`ComplexityExt/PCP/Defs.lean`, `ComplexityExt/Approx/Defs.lean`
  of the derived package, `Complexity/PCP/Defs.lean`, `Complexity/Approx/Defs.lean` upstream),
  the declarations its own Challenge copies for its statements, as far as Theorem 11 and
  Corollary 12 use them: `PEqNP`, `SAT.satCount`, `SAT.assignmentOf`, `OptProblem`,
  `OptProblem.IsOpt`, `WithinRatio`, `ApproxAlgorithm`, `ApproximableWithin`, `unary`,
  `UniformPolyTime`, `ComputableNat`, `OptProblem.HasPTAS`, `natBitsFuel`, `natBits`, `NPO`,
  `absDiff`, `LReducible`, `QF`, `Relations`, `Relations.holds`, `QF.eval`, `tuples`,
  `encodeRelations`, `Relations.Fits`, `QF.WellFormed`, `maxSNP0`, `InMaxSNP`, `MaxSNPHard`,
  `SAT.occurrences`, `SAT.IsThreeOcc`, `max3SAT3`, `InAPX`, `PTASReducible`, `APXHard`. They come after the `STACS2027`
  declarations, so that `Complexity.SAT.occurrences` is not in scope where the Section 5
  `occurrences` is used.

`scripts/generate_challenge.py` reads them from the Lake dependencies, located through `lake-manifest.json` (`Challenge.lean` of `np-completeness` for the machine block,
`Complexity/SAT.lean` of `np-completeness` for the formulas, whose
`Literal` derives `DecidableEq` as Section 5 requires,
`Complexity/PlanarSAT.lean`, `Complexity/Planarity.lean` and `Complexity/Classes.lean`,
`NPHardness/` of `cpap-np-hardness`, and `ComplexityExt/` of `pcp`), so a copy
cannot drift from the library text. Where a Section 5 declaration has no documentation comment, the
generator inserts one (its `DOCS` and `FILE_DOCS` tables); the declaration itself is unchanged.
Comparator then checks that each copied declaration is the same term as the
library's. The Section 6 definitions (`satisfiedCount` through `polarize`, the
RAM of `ApproximationHardness/RAM/Model.lean`, its space-bounded runs `ExecB` and `ComputesIn` of
`ApproximationHardness/RAM/Bounded.lean`, the input and output codes of
`ApproximationHardness/RAM/Program.lean`, the unary
codes of `ApproximationHardness/Sim/`, and `occList`, `IsPlanarRotation`, `choicesOfBits` of
`ApproximationHardness/Planar/ExplicitOrientation.lean`, and `cpapProblem` of
`ApproximationHardness/Hardness/Problem.lean`) are copied from `ApproximationHardness/` the same way. To stay within
the 1,000-line limit for the Challenge, consecutive declarations of one source file are
not separated by blank lines (the foundation's machine block is copied as it stands).

## The RAM is not part of the foundation

The foundation's only machine model is the single-tape machine, and it has no
linear-time class; Theorem 8's `O(n)` is therefore stated on a unit-cost RAM
defined in this formalization (`ApproximationHardness/RAM/Model.lean`, copied into the Challenge
with docstrings). It is a modelling choice made explicit, not a dependency:
Comparator checks the definition as stated, and a reader must accept it as a
faithful rendering of the usual unit-cost RAM (ANONYMIZED and ANONYMIZED 1973) for the
`O(n)` claim to mean what the manuscript says. `docs/paper-map.md` records the
choices (structured control flow instead of jumps; one step per instruction
and per test; unbounded naturals in registers and cells, as in the unit-cost
model, with only `+` and truncated `-` as arithmetic).

The memory of the RAM is unbounded, so a time bound alone would allow a program to
use, say, a table indexed by an unbounded quantity at no cost. The RAM theorems
therefore bound the space as well, by the same linear term as the time (for the
planar orientation `C · (N + n + 1)`, see `docs/paper-map.md`): `ComputesIn prog input
output time space` holds when the run (`ExecB space`, the run relation `Exec` with
the premise `reg a < space` on every `load d a` and `store a b`) reads and writes
only the addresses `0, …, space − 1`, input cells included. Its result does not
depend on the memory at or above `space` (`ExecB.congr`, `ComputesIn.of_mem`). The two
definitions are copied verbatim from the outerplanar formalization (`Outerplanar/RAM/Bounded.lean`),
whose `Model.lean` is a copy of this formalization's, so that the two Challenges state the same
notion; `ComputesIn.computes` recovers the time-only `Computes`.

## Two elaboration pitfalls

A definition that uses `decide` on a proposition whose instance carries a proof
(such as `decide (e ∈ l)`) elaborates to a proof auxiliary named after the
first declaration of its file that needs it, which differs between the
Challenge and the library. The new definitions therefore use Boolean
operations (`List.contains`, `==`, `countP`), as the Section 5 definitions do.

Lean shares, within one module, the auxiliary `match` functions of
pattern-matching definitions of the same shape. `Complexity.SAT.variableBound`
and `STACS2027.placeFormula` both match on a `CNF`, and
`Complexity.SAT.writeNat` and `STACS2027.subdividedEdge` both on a `Nat`, and
`STACS2027.clauseVertex` and its oriented version `STACS2027.Oriented.clauseVertex`
both on an `attachmentAt` result; in the libraries each lives in a different
module and has its own matcher, but in the single-module Challenge the second
of each pair would reuse the first's and elaborate to a different constant. The
generator therefore prefixes the copied `placeFormula`, `subdividedEdge` and
`Oriented.clauseVertex` with
`set_option bootstrap.genMatcherCode false in`, which changes only the
matcher's code generation and gives each a fresh auxiliary with the library's
name and value (Comparator confirms the match).

## Publishing this package on its own

In this repository `cpap-np-hardness` is a Lake path dependency (`../cpap-np-hardness`). To
publish this package separately, require it by git at a full commit of its published
repository instead and run `lake update cpap-np-hardness`; `scripts/dependencies.py` then finds
its sources under `.lake/packages/`, and the sibling check of `scripts/check_repository.py`
must be adapted to the git form.

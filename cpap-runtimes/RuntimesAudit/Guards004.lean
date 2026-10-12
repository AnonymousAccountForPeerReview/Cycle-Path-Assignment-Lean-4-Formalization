module

import all Runtimes
import all Runtimes.Basic
import all Runtimes.BoundedCost.ActualCompilerRAM
import all Runtimes.BoundedCost.ActualCompressionRAM
import all Runtimes.BoundedCost.ActualFPT
import all Runtimes.BoundedCost.ActualInnerRAM
import all Runtimes.BoundedCost.ActualOuterRAM
import all Runtimes.BoundedCost.ActualPathNode
import all Runtimes.BoundedCost.ActualPathRAM
import all Runtimes.BoundedCost.All
import all Runtimes.BoundedCost.Annotated
import all Runtimes.BoundedCost.AnnotatedNode
import all Runtimes.BoundedCost.Answer
import all Runtimes.BoundedCost.ArrayBlocks
import all Runtimes.BoundedCost.BranchRegisters
import all Runtimes.BoundedCost.Branching
import all Runtimes.BoundedCost.CallerRegisters
import all Runtimes.BoundedCost.CandidateDecode
import all Runtimes.BoundedCost.CertificateRAM
import all Runtimes.BoundedCost.CompilerBounds
import all Runtimes.BoundedCost.CompilerCostBridge
import all Runtimes.BoundedCost.CompilerExecution
import all Runtimes.BoundedCost.CompilerFrames
import all Runtimes.BoundedCost.CompilerInit
import all Runtimes.BoundedCost.CompilerLayout
import all Runtimes.BoundedCost.CompilerOutput
import all Runtimes.BoundedCost.CompilerProgram
import all Runtimes.BoundedCost.CompilerRegisterFrame
import all Runtimes.BoundedCost.CompilerState
import all Runtimes.BoundedCost.Compression
import all Runtimes.BoundedCost.CompressionInputs
import all Runtimes.BoundedCost.CompressionPaths
import all Runtimes.BoundedCost.CompressionSeedRAM
import all Runtimes.BoundedCost.CompressionSeedSemantics
import all Runtimes.BoundedCost.CompressionSeedVectors
import all Runtimes.BoundedCost.CompressionSetupBridge
import all Runtimes.BoundedCost.CompressionSetupRAM
import all Runtimes.BoundedCost.CompressionSetupSemantics
import all Runtimes.BoundedCost.CompressionStart
import all Runtimes.BoundedCost.Contraction
import all Runtimes.BoundedCost.ContractionBuild
import all Runtimes.BoundedCost.ContractionData
import all Runtimes.BoundedCost.ContractionHeader
import all Runtimes.BoundedCost.ContractionRAM
import all Runtimes.BoundedCost.ContractionRows
import all Runtimes.BoundedCost.CoreRAM
import all Runtimes.BoundedCost.CoreReuse
import all Runtimes.BoundedCost.CutFactory
import all Runtimes.BoundedCost.CutGraph
import all Runtimes.BoundedCost.CutNetwork
import all Runtimes.BoundedCost.DenseState
import all Runtimes.BoundedCost.DenseTables
import all Runtimes.BoundedCost.DenseTransitions
import all Runtimes.BoundedCost.Domain
import all Runtimes.BoundedCost.EncodedIterative
import all Runtimes.BoundedCost.Exchange
import all Runtimes.BoundedCost.Exhaustive
import all Runtimes.BoundedCost.Extract
import all Runtimes.BoundedCost.FirstSuccess
import all Runtimes.BoundedCost.Form
import all Runtimes.BoundedCost.Init
import all Runtimes.BoundedCost.InitialCompilerRAM
import all Runtimes.BoundedCost.InnerCompilerBridge
import all Runtimes.BoundedCost.InnerDigitUpdates
import all Runtimes.BoundedCost.InnerHeader
import all Runtimes.BoundedCost.InnerIndependence
import all Runtimes.BoundedCost.InnerPathBody
import all Runtimes.BoundedCost.InnerRegisterFrame
import all Runtimes.BoundedCost.InnerRepresentation
import all Runtimes.BoundedCost.InnerRestore
import all Runtimes.BoundedCost.InnerSearchRAM
import all Runtimes.BoundedCost.InnerTransport
import all Runtimes.BoundedCost.Iterative
import all Runtimes.BoundedCost.LayoutRAM
import all Runtimes.BoundedCost.LeastCutBounds
import all Runtimes.BoundedCost.LeastCutLayout
import all Runtimes.BoundedCost.LeastCutRAM
import all Runtimes.BoundedCost.LoopHeaders
import all Runtimes.BoundedCost.Main
import all Runtimes.BoundedCost.NodeActionTables
import all Runtimes.BoundedCost.NodeFrames
import all Runtimes.BoundedCost.NodeSemantics
import all Runtimes.BoundedCost.NormalizedAnswer
import all Runtimes.BoundedCost.OccurrenceTables
import all Runtimes.BoundedCost.OptArithmeticRAM
import all Runtimes.BoundedCost.OptBounds
import all Runtimes.BoundedCost.OptCall
import all Runtimes.BoundedCost.OptControl
import all Runtimes.BoundedCost.OptEmit
import all Runtimes.BoundedCost.OptGeometric
import all Runtimes.BoundedCost.OptLoop
import all Runtimes.BoundedCost.OptMain
import all Runtimes.BoundedCost.OptMemory
import all Runtimes.BoundedCost.OptPowerRAM
import all Runtimes.BoundedCost.OptSpanBounds
import all Runtimes.BoundedCost.OptSpanRAM
import all Runtimes.BoundedCost.OptStep
import all Runtimes.BoundedCost.OptTotalBound
import all Runtimes.BoundedCost.OptimalBudgetSum
import all Runtimes.BoundedCost.Out
import all Runtimes.BoundedCost.OuterBodyRAM
import all Runtimes.BoundedCost.OuterHeader
import all Runtimes.BoundedCost.OuterIndependence
import all Runtimes.BoundedCost.OuterRepresentation
import all Runtimes.BoundedCost.OuterSeedTransport
import all Runtimes.BoundedCost.OuterTransport
import all Runtimes.BoundedCost.Ov
import all Runtimes.BoundedCost.PathActionRepresentation
import all Runtimes.BoundedCost.PathBasicFrame
import all Runtimes.BoundedCost.PathControl
import all Runtimes.BoundedCost.PathLiveControl
import all Runtimes.BoundedCost.PathRegisterFrame
import all Runtimes.BoundedCost.PathRepresentation
import all Runtimes.BoundedCost.PathRestore
import all Runtimes.BoundedCost.PathRestoreTables
import all Runtimes.BoundedCost.PathState
import all Runtimes.BoundedCost.Pc
import all Runtimes.BoundedCost.PrefixCheckRAM
import all Runtimes.BoundedCost.PrefixLoopRAM
import all Runtimes.BoundedCost.PrefixMaskRAM
import all Runtimes.BoundedCost.PrefixRAM
import all Runtimes.BoundedCost.PrefixRepresentation
import all Runtimes.BoundedCost.Prog
import all Runtimes.BoundedCost.ReferenceCopyRAM
import all Runtimes.BoundedCost.Requirements
import all Runtimes.BoundedCost.Search
import all Runtimes.BoundedCost.SearchBound
import all Runtimes.BoundedCost.SearchMemory
import all Runtimes.BoundedCost.SearchNodeRAM
import all Runtimes.BoundedCost.SearchPaths
import all Runtimes.BoundedCost.SearchRows
import all Runtimes.BoundedCost.SearchScan
import all Runtimes.BoundedCost.SearchSemantics
import all Runtimes.BoundedCost.SearchWork
import all Runtimes.BoundedCost.Solver
import all Runtimes.BoundedCost.Spec
import all Runtimes.BoundedCost.State
import all Runtimes.BoundedCost.TernaryControl
import all Runtimes.BoundedCost.TernaryScan
import all Runtimes.BoundedCost.TernaryStateControl
import all Runtimes.BoundedCost.Top
import all Runtimes.BoundedCost.TriCheck
import all Runtimes.BoundedCost.TriDecide
import all Runtimes.BoundedCost.Triangle
import all Runtimes.BoundedCost.TruthInit
import all Runtimes.BoundedCost.Zero
import all Runtimes.C4.Bounds
import all Runtimes.C4.Buckets
import all Runtimes.C4.Canon
import all Runtimes.C4.EnumInsert
import all Runtimes.C4.EnumLists
import all Runtimes.C4.EnumLoops
import all Runtimes.C4.EnumRep
import all Runtimes.C4.EnumScan
import all Runtimes.C4.Grouped
import all Runtimes.C4.Iface
import all Runtimes.C4.Main
import all Runtimes.C4.OrientRAM
import all Runtimes.C4.Output
import all Runtimes.C4.Paths
import all Runtimes.C4.Peel
import all Runtimes.C4.PeelProg
import all Runtimes.C4.PeelRAM
import all Runtimes.C4.RamBase
import all Runtimes.C4.SizeRAM
import all Runtimes.C4.Spec
import all Runtimes.C4.Statement
import all Runtimes.C4.Supersat
import all Runtimes.ConvexQP.Border
import all Runtimes.ConvexQP.Cut
import all Runtimes.ConvexQP.EllGeneric
import all Runtimes.ConvexQP.EllMag
import all Runtimes.ConvexQP.EllPhase
import all Runtimes.ConvexQP.EllSuccess
import all Runtimes.ConvexQP.Exact
import all Runtimes.ConvexQP.Inst
import all Runtimes.ConvexQP.Loewner
import all Runtimes.ConvexQP.Move
import all Runtimes.ConvexQP.Numeric
import all Runtimes.ConvexQP.QP
import all Runtimes.ConvexQP.RAM.ArithCore
import all Runtimes.ConvexQP.RAM.ArithMacros
import all Runtimes.ConvexQP.RAM.ArithSigned
import all Runtimes.ConvexQP.RAM.ArithSqrt
import all Runtimes.ConvexQP.RAM.Consts
import all Runtimes.ConvexQP.RAM.EllBound
import all Runtimes.ConvexQP.RAM.EllCost
import all Runtimes.ConvexQP.RAM.EllFeas
import all Runtimes.ConvexQP.RAM.EllGap
import all Runtimes.ConvexQP.RAM.EllGrad
import all Runtimes.ConvexQP.RAM.EllInit
import all Runtimes.ConvexQP.RAM.EllIter
import all Runtimes.ConvexQP.RAM.EllLayout
import all Runtimes.ConvexQP.RAM.EllLoop
import all Runtimes.ConvexQP.RAM.EllRam
import all Runtimes.ConvexQP.RAM.EllScan
import all Runtimes.ConvexQP.RAM.EllUpd
import all Runtimes.ConvexQP.RAM.EllUpd2
import all Runtimes.ConvexQP.RAM.EllUpd3
import all Runtimes.ConvexQP.RAM.KmoArg
import all Runtimes.ConvexQP.RAM.KmoBits
import all Runtimes.ConvexQP.RAM.KmoCost
import all Runtimes.ConvexQP.RAM.KmoInv
import all Runtimes.ConvexQP.RAM.KmoK1
import all Runtimes.ConvexQP.RAM.KmoK2
import all Runtimes.ConvexQP.RAM.KmoK3
import all Runtimes.ConvexQP.RAM.KmoK4
import all Runtimes.ConvexQP.RAM.KmoK5
import all Runtimes.ConvexQP.RAM.KmoK6
import all Runtimes.ConvexQP.RAM.KmoK7
import all Runtimes.ConvexQP.RAM.KmoLayout
import all Runtimes.ConvexQP.RAM.KmoLoops
import all Runtimes.ConvexQP.RAM.KmoOut
import all Runtimes.ConvexQP.RAM.KmoRam
import all Runtimes.ConvexQP.RAM.KmoSpec
import all Runtimes.ConvexQP.RAM.KmoStep
import all Runtimes.ConvexQP.RAM.KmoStepA
import all Runtimes.ConvexQP.RAM.KmoStepB
import all Runtimes.ConvexQP.RAM.KmoStepC
import all Runtimes.ConvexQP.RAM.Main
import all Runtimes.ConvexQP.RAM.ParseConsts
import all Runtimes.ConvexQP.RAM.ParseConstsBound
import all Runtimes.ConvexQP.RAM.ParseH
import all Runtimes.ConvexQP.RAM.ParseHLoop
import all Runtimes.ConvexQP.RAM.ParseHStep
import all Runtimes.ConvexQP.RAM.ParseKS
import all Runtimes.ConvexQP.RAM.ParseRam
import all Runtimes.ConvexQP.RAM.ParseSpec
import all Runtimes.ConvexQP.RAM.QPIface
import all Runtimes.ConvexQP.RAM.RelaxSolver
import all Runtimes.ConvexQP.RAM.Vec
import all Runtimes.ConvexQP.RAM.VecLin
import all Runtimes.Cpap4Enum
import all Runtimes.Cpap4EnumStatement
import all Runtimes.CpapSingle.Complete
import all Runtimes.CpapSingle.GraphLength
import all Runtimes.CpapSingle.HeaderEnumeration
import all Runtimes.Flow.Augment
import all Runtimes.Flow.CutFacts
import all Runtimes.Flow.EdgeSpec
import all Runtimes.Flow.Edges
import all Runtimes.Flow.Enc4
import all Runtimes.Flow.EnumeratedConstruction
import all Runtimes.Flow.Extract
import all Runtimes.Flow.Four
import all Runtimes.Flow.Front
import all Runtimes.Flow.HornQuery
import all Runtimes.Flow.HornRAM
import all Runtimes.Flow.HornSeparator
import all Runtimes.Flow.Indexed
import all Runtimes.Flow.IndexedFacts
import all Runtimes.Flow.Main
import all Runtimes.Flow.MaxFlowNetwork
import all Runtimes.Flow.MaxFlowProjection
import all Runtimes.Flow.OffsetCall
import all Runtimes.Flow.Out
import all Runtimes.Flow.PaddedEncoding
import all Runtimes.Flow.PaddedNetwork
import all Runtimes.Flow.PaddedProjection
import all Runtimes.Flow.Pipe
import all Runtimes.Flow.PolynomialBound
import all Runtimes.Flow.Prog
import all Runtimes.Flow.Reloc
import all Runtimes.Flow.ReusableCall
import all Runtimes.Flow.ReverseReach
import all Runtimes.Flow.ReverseScan
import all Runtimes.Flow.Separator
import all Runtimes.Flow.Single
import all Runtimes.Flow.Solver
import all Runtimes.Flow.SortTri
import all Runtimes.Flow.SortedConstruction
import all Runtimes.Flow.Statement
import all Runtimes.Flow.StridedCall
import all Runtimes.Flow.Tri
import all Runtimes.GeneralCycles.Assembly
import all Runtimes.GeneralCycles.Bounds
import all Runtimes.GeneralCycles.Composition
import all Runtimes.GeneralCycles.Counter
import all Runtimes.GeneralCycles.Definitions
import all Runtimes.GeneralCycles.EdgeScan
import all Runtimes.GeneralCycles.Fold
import all Runtimes.GeneralCycles.Main
import all Runtimes.GeneralCycles.Output
import all Runtimes.GeneralCycles.PairScan
import all Runtimes.GeneralCycles.Polynomial
import all Runtimes.GeneralCycles.Program
import all Runtimes.GeneralCycles.RegTests
import all Runtimes.GeneralCycles.RegisterPredicates
import all Runtimes.GeneralCycles.Spec
import all Runtimes.GeneralCycles.TupleLoop
import all Runtimes.GeneralCycles.Validity
import all Runtimes.Greedy.Cycle
import all Runtimes.Greedy.Main
import all Runtimes.Greedy.Prog
import all Runtimes.Greedy.Spec
import all Runtimes.NamedHoles
import all Runtimes.Sort.EnumeratedFront
import all Runtimes.Sort.EnumeratedPairs
import all Runtimes.Sort.EnumeratedProg
import all Runtimes.Sort.Front
import all Runtimes.Sort.FrontPairs
import all Runtimes.Sort.FrontProg
import all Runtimes.Sort.Merge
import all Runtimes.Sort.MergeProg
import all Runtimes.Sort.MergeSpec
import all Runtimes.TwoSatCsr
import all Runtimes.TwoSatLoop
import all Runtimes.TwoSatMain
import all Runtimes.TwoSatPhase
import all Runtimes.TwoSatProg
import all Runtimes.TwoSatScc
import all Runtimes.TwoSatSearch
import all Runtimes.TwoSatSpec
import all Runtimes.ZeroCost
import all Runtimes.ZeroCostEdges
import all Runtimes.ZeroCostFormula
import all Runtimes.ZeroCostGen
import all Runtimes.ZeroCostInit
import all Runtimes.ZeroCostProg
import all Runtimes.ZeroCostRec
import all Runtimes.ZeroCostSpec

/-!
Exact-message axiom guards for every explicitly named Runtimes declaration.
Each guard fails if its transitive axiom report changes. The generator rejects
axioms outside propext, Classical.choice, and Quot.sound before writing this
file. Regenerate with scripts/generate_audit.py.
-/

set_option maxRecDepth 100000

/-- info: 'STACS2027.Runtimes.GeneralCycles.programConstant_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.programConstant_lower

/-- info: 'STACS2027.Runtimes.GeneralCycles.program_space_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.program_space_bound

/-- info: 'STACS2027.Runtimes.GeneralCycles.enumerateProgram_polynomial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.enumerateProgram_polynomial

/-- info: 'STACS2027.Runtimes.GeneralCycles.inputEdgeCount' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.inputEdgeCount

/-- info: 'STACS2027.Runtimes.GeneralCycles.checkerScratch' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.checkerScratch

/-- info: 'STACS2027.Runtimes.GeneralCycles.ValiditySpec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.ValiditySpec

/-- info: 'STACS2027.Runtimes.GeneralCycles.outputInvariant' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.outputInvariant

/-- info: 'STACS2027.Runtimes.GeneralCycles.rejectionInvariant' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.rejectionInvariant

/-- info: 'STACS2027.Runtimes.GeneralCycles.counterBody' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.counterBody

/-- info: 'STACS2027.Runtimes.GeneralCycles.representativeBody' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.representativeBody

/-- info: 'STACS2027.Runtimes.GeneralCycles.initCounts' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.initCounts

/-- info: 'STACS2027.Runtimes.GeneralCycles.enumerateProgram' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.enumerateProgram

/-- info: 'STACS2027.Runtimes.GeneralCycles.placed_indep_of' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.placed_indep_of

/-- info: 'STACS2027.Runtimes.GeneralCycles.outputInvariant_indep' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.outputInvariant_indep

/-- info: 'STACS2027.Runtimes.GeneralCycles.outputInvariant_outer_indep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.outputInvariant_outer_indep

/-- info: 'STACS2027.Runtimes.GeneralCycles.rejectionInvariant_inner_indep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.rejectionInvariant_inner_indep

/-- info: 'STACS2027.Runtimes.GeneralCycles.checker_placed_indep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.checker_placed_indep

/-- info: 'STACS2027.Runtimes.GeneralCycles.checker_output_indep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.checker_output_indep

/-- info: 'STACS2027.Runtimes.GeneralCycles.clear_placed_indep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.clear_placed_indep

/-- info: 'STACS2027.Runtimes.GeneralCycles.counterBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.counterBody_spec

/-- info: 'STACS2027.Runtimes.GeneralCycles.RegTest' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.RegTest

/-- info: 'STACS2027.Runtimes.GeneralCycles.RegTest.sources' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.RegTest.sources

/-- info: 'STACS2027.Runtimes.GeneralCycles.RegTest.eval' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.RegTest.eval

/-- info: 'STACS2027.Runtimes.GeneralCycles.RegTest.branch' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.RegTest.branch

/-- info: 'STACS2027.Runtimes.GeneralCycles.RegTest.eval_setReg' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.RegTest.eval_setReg

/-- info: 'STACS2027.Runtimes.GeneralCycles.RegTest.run_branch' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.RegTest.run_branch

/-- info: 'STACS2027.Runtimes.GeneralCycles.RegTest.branch_loopFree' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.RegTest.branch_loopFree

/-- info: 'STACS2027.Runtimes.GeneralCycles.RegTest.branch_memFree' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.RegTest.branch_memFree

/-- info: 'STACS2027.Runtimes.GeneralCycles.RegTest.branch_stores' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.RegTest.branch_stores

/-- info: 'STACS2027.Runtimes.GeneralCycles.RegTest.branch_writes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.RegTest.branch_writes

/-- info: 'STACS2027.Runtimes.GeneralCycles.RegTest.branch_wregs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.RegTest.branch_wregs

/-- info: 'STACS2027.Runtimes.GeneralCycles.RegTest.flag' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.RegTest.flag

/-- info: 'STACS2027.Runtimes.GeneralCycles.RegTest.run_flag' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.RegTest.run_flag

/-- info: 'STACS2027.Runtimes.GeneralCycles.RegTest.clear' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.RegTest.clear

/-- info: 'STACS2027.Runtimes.GeneralCycles.RegTest.run_clear' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.RegTest.run_clear

/-- info: 'STACS2027.Runtimes.GeneralCycles.regValues' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.regValues

/-- info: 'STACS2027.Runtimes.GeneralCycles.equalTest' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.equalTest

/-- info: 'STACS2027.Runtimes.GeneralCycles.lexTest' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.lexTest

/-- info: 'STACS2027.Runtimes.GeneralCycles.allTest' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.allTest

/-- info: 'STACS2027.Runtimes.GeneralCycles.anyTest' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.anyTest

/-- info: 'STACS2027.Runtimes.GeneralCycles.adjacentRegs' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.adjacentRegs

/-- info: 'STACS2027.Runtimes.GeneralCycles.cyclicRegs' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.cyclicRegs

/-- info: 'STACS2027.Runtimes.GeneralCycles.edgeTest' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.edgeTest

/-- info: 'STACS2027.Runtimes.GeneralCycles.subsetTest' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.subsetTest

/-- info: 'STACS2027.Runtimes.GeneralCycles.sameCycleTest' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.sameCycleTest

/-- info: 'STACS2027.Runtimes.GeneralCycles.earlierTest' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.earlierTest

/-- info: 'STACS2027.Runtimes.GeneralCycles.equalTest_eval' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.equalTest_eval

/-- info: 'STACS2027.Runtimes.GeneralCycles.lexTest_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.lexTest_eval

/-- info: 'STACS2027.Runtimes.GeneralCycles.allTest_eval' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.allTest_eval

/-- info: 'STACS2027.Runtimes.GeneralCycles.anyTest_eval' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.anyTest_eval

/-- info: 'STACS2027.Runtimes.GeneralCycles.edgeTest_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.edgeTest_eval

/-- info: 'STACS2027.Runtimes.GeneralCycles.adjacentRegs_map' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.adjacentRegs_map

/-- info: 'STACS2027.Runtimes.GeneralCycles.cyclicRegs_map' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.cyclicRegs_map

/-- info: 'STACS2027.Runtimes.GeneralCycles.subsetTest_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.subsetTest_eval

/-- info: 'STACS2027.Runtimes.GeneralCycles.sameCycleTest_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.sameCycleTest_eval

/-- info: 'STACS2027.Runtimes.GeneralCycles.earlierTest_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.earlierTest_eval

/-- info: 'STACS2027.Runtimes.GeneralCycles.equalTest_safe' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.equalTest_safe

/-- info: 'STACS2027.Runtimes.GeneralCycles.lexTest_safe' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.lexTest_safe

/-- info: 'STACS2027.Runtimes.GeneralCycles.allTest_safe' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.allTest_safe

/-- info: 'STACS2027.Runtimes.GeneralCycles.anyTest_safe' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.anyTest_safe

/-- info: 'STACS2027.Runtimes.GeneralCycles.adjacentRegs_safe' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.adjacentRegs_safe

/-- info: 'STACS2027.Runtimes.GeneralCycles.cyclicRegs_safe' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.cyclicRegs_safe

/-- info: 'STACS2027.Runtimes.GeneralCycles.subsetTest_safe' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.subsetTest_safe

/-- info: 'STACS2027.Runtimes.GeneralCycles.sameCycleTest_safe' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.sameCycleTest_safe

/-- info: 'STACS2027.Runtimes.GeneralCycles.earlierTest_safe' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.earlierTest_safe

/-- info: 'STACS2027.Runtimes.GeneralCycles.distinctTest' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.distinctTest

/-- info: 'STACS2027.Runtimes.GeneralCycles.distinctTest_eval' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.distinctTest_eval

/-- info: 'STACS2027.Runtimes.GeneralCycles.allTest_sources' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.allTest_sources

/-- info: 'STACS2027.Runtimes.GeneralCycles.distinctTest_sources' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.distinctTest_sources

/-- info: 'STACS2027.Runtimes.GeneralCycles.distinctTest_safe' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.distinctTest_safe

/-- info: 'STACS2027.Runtimes.GeneralCycles.adjacentRegs_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.adjacentRegs_mem

/-- info: 'STACS2027.Runtimes.GeneralCycles.cyclicRegs_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.cyclicRegs_mem

/-- info: 'STACS2027.Runtimes.GeneralCycles.mem_tuples' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.mem_tuples

/-- info: 'STACS2027.Runtimes.GeneralCycles.tuples_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.tuples_nodup

/-- info: 'STACS2027.Runtimes.GeneralCycles.length_tuples' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.length_tuples

/-- info: 'STACS2027.Runtimes.GeneralCycles.length_endpoints' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.length_endpoints

/-- info: 'STACS2027.Runtimes.GeneralCycles.mem_endpoints_of_edge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.mem_endpoints_of_edge

/-- info: 'STACS2027.Runtimes.GeneralCycles.cycle_vertices_endpoints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.cycle_vertices_endpoints

/-- info: 'STACS2027.Runtimes.GeneralCycles.exists_indices' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.exists_indices

/-- info: 'STACS2027.Runtimes.GeneralCycles.accepted_labels_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.accepted_labels_mem

/-- info: 'STACS2027.Runtimes.GeneralCycles.exists_accepted_of_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.exists_accepted_of_mem

/-- info: 'STACS2027.Runtimes.GeneralCycles.accepted_indices_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.accepted_indices_injective

/-- info: 'STACS2027.Runtimes.GeneralCycles.mem_outputCycles' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.mem_outputCycles

/-- info: 'STACS2027.Runtimes.GeneralCycles.outputCycles_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.outputCycles_nodup

/-- info: 'STACS2027.Runtimes.GeneralCycles.outputCycles_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.outputCycles_perm

/-- info: 'STACS2027.Runtimes.GeneralCycles.outputCycles_length_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.outputCycles_length_le

/-- info: 'STACS2027.Runtimes.GeneralCycles.outputCycles_cycle_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.outputCycles_cycle_length

/-- info: 'STACS2027.Runtimes.GeneralCycles.outputCycles_flatten_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.outputCycles_flatten_length

/-- info: 'STACS2027.Runtimes.GeneralCycles.outputCycles_flatten_length_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.outputCycles_flatten_length_le

/-- info: 'STACS2027.Runtimes.GeneralCycles.choiceAddr' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.choiceAddr

/-- info: 'STACS2027.Runtimes.GeneralCycles.endpointCount' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.endpointCount

/-- info: 'STACS2027.Runtimes.GeneralCycles.controlRegs' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.controlRegs

/-- info: 'STACS2027.Runtimes.GeneralCycles.Placed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.Placed

/-- info: 'STACS2027.Runtimes.GeneralCycles.readChoice' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.readChoice

/-- info: 'STACS2027.Runtimes.GeneralCycles.scanTuples' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.scanTuples

/-- info: 'STACS2027.Runtimes.GeneralCycles.foldTuples' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.foldTuples

/-- info: 'STACS2027.Runtimes.GeneralCycles.tupleTime' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.tupleTime

/-- info: 'STACS2027.Runtimes.GeneralCycles.placed_nil' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.placed_nil

/-- info: 'STACS2027.Runtimes.GeneralCycles.Placed.append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.Placed.append

/-- info: 'STACS2027.Runtimes.GeneralCycles.Placed.stem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.Placed.stem

/-- info: 'STACS2027.Runtimes.GeneralCycles.Placed.last' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.Placed.last

/-- info: 'STACS2027.Runtimes.GeneralCycles.placed_indep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.placed_indep

/-- info: 'STACS2027.Runtimes.GeneralCycles.readChoice_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.readChoice_spec

/-- info: 'STACS2027.Runtimes.GeneralCycles.scanTuples_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.scanTuples_spec

/-- info: 'STACS2027.Runtimes.GeneralCycles.tupleTime_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.tupleTime_bound

/-- info: 'STACS2027.Runtimes.GeneralCycles.registerValidTest' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.registerValidTest

/-- info: 'STACS2027.Runtimes.GeneralCycles.validRegisters' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.validRegisters

/-- info: 'STACS2027.Runtimes.GeneralCycles.validCheck' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.validCheck

/-- info: 'STACS2027.Runtimes.GeneralCycles.validityConstant' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.validityConstant

/-- info: 'STACS2027.Runtimes.GeneralCycles.held_values' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.held_values

/-- info: 'STACS2027.Runtimes.GeneralCycles.cyclicRegs_length_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.cyclicRegs_length_le

/-- info: 'STACS2027.Runtimes.GeneralCycles.allPairs_cyclic' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.allPairs_cyclic

/-- info: 'STACS2027.Runtimes.GeneralCycles.registerValidTest_eval' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.registerValidTest_eval

/-- info: 'STACS2027.Runtimes.GeneralCycles.registerValidTest_safe' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.registerValidTest_safe

/-- info: 'STACS2027.Runtimes.GeneralCycles.validRegisters_frozen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.validRegisters_frozen

/-- info: 'STACS2027.Runtimes.GeneralCycles.validCheck_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.validCheck_bound

/-- info: 'STACS2027.Runtimes.Greedy.GR' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.GR

/-- info: 'STACS2027.Runtimes.Greedy.GM' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.GM

/-- info: 'STACS2027.Runtimes.Greedy.CS' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.CS

/-- info: 'STACS2027.Runtimes.Greedy.sumBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.sumBody_spec

/-- info: 'STACS2027.Runtimes.Greedy.sumPhase_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.sumPhase_spec

/-- info: 'STACS2027.Runtimes.Greedy.ChInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.ChInv

/-- info: 'STACS2027.Runtimes.Greedy.ChMid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.ChMid

/-- info: 'STACS2027.Runtimes.Greedy.chooseInit_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.chooseInit_spec

/-- info: 'STACS2027.Runtimes.Greedy.readV_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.readV_spec

/-- info: 'STACS2027.Runtimes.Greedy.better_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.better_spec

/-- info: 'STACS2027.Runtimes.Greedy.notBetter_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.notBetter_spec

/-- info: 'STACS2027.Runtimes.Greedy.chooseBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.chooseBody_spec

/-- info: 'STACS2027.Runtimes.Greedy.choosePhase_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.choosePhase_spec

/-- info: 'STACS2027.Runtimes.Greedy.write_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.write_spec

/-- info: 'STACS2027.Runtimes.Greedy.UInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.UInv

/-- info: 'STACS2027.Runtimes.Greedy.updInit_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.updInit_spec

/-- info: 'STACS2027.Runtimes.Greedy.incLoad_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.incLoad_spec

/-- info: 'STACS2027.Runtimes.Greedy.updBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.updBody_spec

/-- info: 'STACS2027.Runtimes.Greedy.updPhase_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.updPhase_spec

/-- info: 'STACS2027.Runtimes.Greedy.nextBase_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.nextBase_spec

/-- info: 'STACS2027.Runtimes.Greedy.cycBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.cycBody_spec

/-- info: 'STACS2027.Runtimes.Greedy.stepLoad_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.stepLoad_spec

/-- info: 'STACS2027.Runtimes.Greedy.LoopInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.LoopInv

/-- info: 'STACS2027.Runtimes.Greedy.stepGreedy_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.stepGreedy_spec

/-- info: 'STACS2027.Runtimes.Greedy.CG' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.CG

/-- info: 'STACS2027.Runtimes.Greedy.grSpace_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.grSpace_le

/-- info: 'STACS2027.Runtimes.Greedy.greedyProg_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.greedyProg_spec

/-- info: 'STACS2027.Runtimes.Greedy.greedy_ram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.greedy_ram

/-- info: 'STACS2027.Runtimes.Greedy.greedy_guarantee_ram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.greedy_guarantee_ram

/-- info: 'STACS2027.Runtimes.Greedy.xLD' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.xLD

/-- info: 'STACS2027.Runtimes.Greedy.xB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.xB

/-- info: 'STACS2027.Runtimes.Greedy.xI' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.xI

/-- info: 'STACS2027.Runtimes.Greedy.xP' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.xP

/-- info: 'STACS2027.Runtimes.Greedy.xJ' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.xJ

/-- info: 'STACS2027.Runtimes.Greedy.xTot' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.xTot

/-- info: 'STACS2027.Runtimes.Greedy.xBV' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.xBV

/-- info: 'STACS2027.Runtimes.Greedy.xBJ' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.xBJ

/-- info: 'STACS2027.Runtimes.Greedy.xQ' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.xQ

/-- info: 'STACS2027.Runtimes.Greedy.xE' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.xE

/-- info: 'STACS2027.Runtimes.Greedy.xX' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.xX

/-- info: 'STACS2027.Runtimes.Greedy.xY' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.xY

/-- info: 'STACS2027.Runtimes.Greedy.xV' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.xV

/-- info: 'STACS2027.Runtimes.Greedy.xBP' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.xBP

/-- info: 'STACS2027.Runtimes.Greedy.grSpace' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.grSpace

/-- info: 'STACS2027.Runtimes.Greedy.bEID_kt_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.bEID_kt_le

/-- info: 'STACS2027.Runtimes.Greedy.fitsG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.fitsG

/-- info: 'STACS2027.Runtimes.Greedy.stepLoad' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.stepLoad

/-- info: 'STACS2027.Runtimes.Greedy.sumBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.sumBody

/-- info: 'STACS2027.Runtimes.Greedy.sumPhase' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.sumPhase

/-- info: 'STACS2027.Runtimes.Greedy.chooseInit' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.chooseInit

/-- info: 'STACS2027.Runtimes.Greedy.readV' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.readV

/-- info: 'STACS2027.Runtimes.Greedy.better' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.better

/-- info: 'STACS2027.Runtimes.Greedy.chooseBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.chooseBody

/-- info: 'STACS2027.Runtimes.Greedy.choosePhase' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.choosePhase

/-- info: 'STACS2027.Runtimes.Greedy.updInit' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.updInit

/-- info: 'STACS2027.Runtimes.Greedy.incLoad' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.incLoad

/-- info: 'STACS2027.Runtimes.Greedy.updBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.updBody

/-- info: 'STACS2027.Runtimes.Greedy.updPhase' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.updPhase

/-- info: 'STACS2027.Runtimes.Greedy.cycBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.cycBody

/-- info: 'STACS2027.Runtimes.Greedy.stepGreedy' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.stepGreedy

/-- info: 'STACS2027.Runtimes.Greedy.greedyProg' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.greedyProg

/-- info: 'STACS2027.Runtimes.Greedy.length_greedyFrom' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.length_greedyFrom

/-- info: 'STACS2027.Runtimes.Greedy.greedyFrom_getD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.greedyFrom_getD

/-- info: 'STACS2027.Runtimes.Greedy.chooseMin_eq_of_first' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.chooseMin_eq_of_first

/-- info: 'STACS2027.Runtimes.Greedy.scanMin' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.scanMin

/-- info: 'STACS2027.Runtimes.Greedy.scanMin_succ' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.scanMin_succ

/-- info: 'STACS2027.Runtimes.Greedy.scanMin_inv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.scanMin_inv

/-- info: 'STACS2027.Runtimes.Greedy.scanMin_first' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.scanMin_first

/-- info: 'STACS2027.Runtimes.Greedy.opts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.opts

/-- info: 'STACS2027.Runtimes.Greedy.acc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.acc

/-- info: 'STACS2027.Runtimes.Greedy.ldF' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.ldF

/-- info: 'STACS2027.Runtimes.Greedy.lp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.lp

/-- info: 'STACS2027.Runtimes.Greedy.tsum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.tsum

/-- info: 'STACS2027.Runtimes.Greedy.tot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.tot

/-- info: 'STACS2027.Runtimes.Greedy.val' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.val

/-- info: 'STACS2027.Runtimes.Greedy.pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.pos

/-- info: 'STACS2027.Runtimes.Greedy.ucnt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.ucnt

/-- info: 'STACS2027.Runtimes.Greedy.uF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.uF

/-- info: 'STACS2027.Runtimes.Greedy.prv' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.prv

/-- info: 'STACS2027.Runtimes.Greedy.prv_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.prv_lt

/-- info: 'STACS2027.Runtimes.Greedy.t_le_kt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.t_le_kt

/-- info: 'STACS2027.Runtimes.Greedy.k_ge_of_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.k_ge_of_lt

/-- info: 'STACS2027.Runtimes.Greedy.occIdx_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.occIdx_lt

/-- info: 'STACS2027.Runtimes.Greedy.length_greedy' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.length_greedy

/-- info: 'STACS2027.Runtimes.Greedy.opts_getD' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.opts_getD

/-- info: 'STACS2027.Runtimes.Greedy.greedy_getD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.greedy_getD

/-- info: 'STACS2027.Runtimes.Greedy.acc_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.acc_succ

/-- info: 'STACS2027.Runtimes.Greedy.acc_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.acc_zero

/-- info: 'STACS2027.Runtimes.Greedy.tsum_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.tsum_succ

/-- info: 'STACS2027.Runtimes.Greedy.tsum_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.tsum_zero

/-- info: 'STACS2027.Runtimes.Greedy.off_option_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.off_option_iff

/-- info: 'STACS2027.Runtimes.Greedy.val_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.val_eq

/-- info: 'STACS2027.Runtimes.Greedy.val_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.val_le

/-- info: 'STACS2027.Runtimes.Greedy.pos_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.pos_spec

/-- info: 'STACS2027.Runtimes.Greedy.pos_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.pos_lt

/-- info: 'STACS2027.Runtimes.Greedy.length_kCycle' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.length_kCycle

/-- info: 'STACS2027.Runtimes.Greedy.greedy_getD_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.greedy_getD_pos

/-- info: 'STACS2027.Runtimes.Greedy.zipWith_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.zipWith_pos

/-- info: 'STACS2027.Runtimes.Greedy.eoc_getD_eidOf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.eoc_getD_eidOf

/-- info: 'STACS2027.Runtimes.Greedy.ldF_eidOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.ldF_eidOf

/-- info: 'STACS2027.Runtimes.Greedy.eidOf_eq_iff_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.eidOf_eq_iff_edge

/-- info: 'STACS2027.Runtimes.Greedy.uF_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.uF_zero

/-- info: 'STACS2027.Runtimes.Greedy.uF_succ_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.uF_succ_apply

/-- info: 'STACS2027.Runtimes.Greedy.uF_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.uF_succ

/-- info: 'STACS2027.Runtimes.Greedy.ldF_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.ldF_succ

/-- info: 'STACS2027.Runtimes.Greedy.uF_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Greedy.uF_final

/-- info: 'STACS2027.Runtimes.Flow.PolynomialMinCostFlowSolverExists' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.PolynomialMinCostFlowSolverExists

/-- info: 'STACS2027.Runtimes.Flow.SortedNetworkConstruction' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.SortedNetworkConstruction

/-- info: 'STACS2027.Runtimes.BoundedCost.AlmostTwoSatFptSolverExists' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.AlmostTwoSatFptSolverExists

/-- info: 'STACS2027.Runtimes.GeneralCycleEnumerationRam' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycleEnumerationRam

/-- info: 'STACS2027.Runtimes.EnumeratedSort.FrontPost' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.EnumeratedSort.FrontPost

/-- info: 'STACS2027.Runtimes.EnumeratedSort.fEids_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.EnumeratedSort.fEids_spec

/-- info: 'STACS2027.Runtimes.EnumeratedSort.t_le_fL' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.EnumeratedSort.t_le_fL

/-- info: 'STACS2027.Runtimes.EnumeratedSort.CF' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.EnumeratedSort.CF

/-- info: 'STACS2027.Runtimes.EnumeratedSort.front_wregs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.EnumeratedSort.front_wregs

/-- info: 'STACS2027.Runtimes.EnumeratedSort.front_writes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.EnumeratedSort.front_writes

/-- info: 'STACS2027.Runtimes.EnumeratedSort.front_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.EnumeratedSort.front_spec

/-- info: 'STACS2027.Runtimes.EnumeratedSort.FG' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.EnumeratedSort.FG

/-- info: 'STACS2027.Runtimes.EnumeratedSort.FG.regIndep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.EnumeratedSort.FG.regIndep

/-- info: 'STACS2027.Runtimes.EnumeratedSort.FMem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.EnumeratedSort.FMem

/-- info: 'STACS2027.Runtimes.EnumeratedSort.FInv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.EnumeratedSort.FInv

/-- info: 'STACS2027.Runtimes.EnumeratedSort.FMem.put' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.EnumeratedSort.FMem.put

/-- info: 'STACS2027.Runtimes.EnumeratedSort.pIdOrd_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.EnumeratedSort.pIdOrd_run

/-- info: 'STACS2027.Runtimes.EnumeratedSort.pRead_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.EnumeratedSort.pRead_run

/-- info: 'STACS2027.Runtimes.EnumeratedSort.PJInv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.EnumeratedSort.PJInv

/-- info: 'STACS2027.Runtimes.EnumeratedSort.pBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.EnumeratedSort.pBody_spec

/-- info: 'STACS2027.Runtimes.EnumeratedSort.pRow_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.EnumeratedSort.pRow_spec

/-- info: 'STACS2027.Runtimes.EnumeratedSort.PairsPost' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.EnumeratedSort.PairsPost

/-- info: 'STACS2027.Runtimes.EnumeratedSort.fPairs_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.EnumeratedSort.fPairs_spec

/-- info: 'STACS2027.Runtimes.EnumeratedSort.fID' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.EnumeratedSort.fID

/-- info: 'STACS2027.Runtimes.EnumeratedSort.fL' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.EnumeratedSort.fL

/-- info: 'STACS2027.Runtimes.EnumeratedSort.fIDb' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.EnumeratedSort.fIDb

/-- info: 'STACS2027.Runtimes.EnumeratedSort.fPU' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.EnumeratedSort.fPU

/-- info: 'STACS2027.Runtimes.EnumeratedSort.fPV' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.EnumeratedSort.fPV

/-- info: 'STACS2027.Runtimes.EnumeratedSort.fPI' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.EnumeratedSort.fPI

/-- info: 'STACS2027.Runtimes.EnumeratedSort.fEID' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.EnumeratedSort.fEID

/-- info: 'STACS2027.Runtimes.EnumeratedSort.fCNT' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.EnumeratedSort.fCNT

/-- info: 'STACS2027.Runtimes.EnumeratedSort.fEnd' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.EnumeratedSort.fEnd

/-- info: 'STACS2027.Runtimes.EnumeratedSort.fEnd_eq' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.EnumeratedSort.fEnd_eq

/-- info: 'STACS2027.Runtimes.EnumeratedSort.fEID_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.EnumeratedSort.fEID_eq

/-- info: 'STACS2027.Runtimes.EnumeratedSort.fEnd_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.EnumeratedSort.fEnd_le

/-- info: 'STACS2027.Runtimes.EnumeratedSort.ffits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.EnumeratedSort.ffits

/-- info: 'STACS2027.Runtimes.EnumeratedSort.fSort' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.EnumeratedSort.fSort

/-- info: 'STACS2027.Runtimes.EnumeratedSort.vArgs' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.EnumeratedSort.vArgs

/-- info: 'STACS2027.Runtimes.EnumeratedSort.vBack' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.EnumeratedSort.vBack

/-- info: 'STACS2027.Runtimes.EnumeratedSort.fVids' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.EnumeratedSort.fVids

/-- info: 'STACS2027.Runtimes.EnumeratedSort.pIds' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.EnumeratedSort.pIds

/-- info: 'STACS2027.Runtimes.EnumeratedSort.pOrd' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.EnumeratedSort.pOrd

/-- info: 'STACS2027.Runtimes.EnumeratedSort.pRead' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.EnumeratedSort.pRead

/-- info: 'STACS2027.Runtimes.EnumeratedSort.pBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.EnumeratedSort.pBody

/-- info: 'STACS2027.Runtimes.EnumeratedSort.pRow' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.EnumeratedSort.pRow

/-- info: 'STACS2027.Runtimes.EnumeratedSort.fPairs' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.EnumeratedSort.fPairs

/-- info: 'STACS2027.Runtimes.EnumeratedSort.fEids' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.EnumeratedSort.fEids

/-- info: 'STACS2027.Runtimes.EnumeratedSort.front' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.EnumeratedSort.front

/-- info: 'STACS2027.Runtimes.EnumeratedSort.FrontIn' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.EnumeratedSort.FrontIn

/-- info: 'STACS2027.Runtimes.EnumeratedSort.frontIn_of_initPost' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.EnumeratedSort.frontIn_of_initPost

/-- info: 'STACS2027.Runtimes.EnumeratedSort.eids_verts' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.EnumeratedSort.eids_verts

/-- info: 'STACS2027.Runtimes.EnumeratedSort.length_verts'' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.EnumeratedSort.length_verts'

/-- info: 'STACS2027.Runtimes.EnumeratedSort.ga_of_frame_msort' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.EnumeratedSort.ga_of_frame_msort

/-- info: 'STACS2027.Runtimes.EnumeratedSort.SortedPost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.EnumeratedSort.SortedPost

/-- info: 'STACS2027.Runtimes.EnumeratedSort.fSort_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.EnumeratedSort.fSort_spec

/-- info: 'STACS2027.Runtimes.EnumeratedSort.VidsPost' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.EnumeratedSort.VidsPost

/-- info: 'STACS2027.Runtimes.EnumeratedSort.ga_of_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.EnumeratedSort.ga_of_frame

/-- info: 'STACS2027.Runtimes.EnumeratedSort.sortedLeads_wregs'' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.EnumeratedSort.sortedLeads_wregs'

/-- info: 'STACS2027.Runtimes.EnumeratedSort.rankIds_wregs'' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.EnumeratedSort.rankIds_wregs'

/-- info: 'STACS2027.Runtimes.EnumeratedSort.fVids_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.EnumeratedSort.fVids_spec

/-- info: 'STACS2027.Runtimes.Sort.FrontPost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.FrontPost

/-- info: 'STACS2027.Runtimes.Sort.fEids_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.fEids_spec

/-- info: 'STACS2027.Runtimes.Sort.t_le_fL' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.t_le_fL

/-- info: 'STACS2027.Runtimes.Sort.CF' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.CF

/-- info: 'STACS2027.Runtimes.Sort.front_wregs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.front_wregs

/-- info: 'STACS2027.Runtimes.Sort.front_writes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.front_writes

/-- info: 'STACS2027.Runtimes.Sort.front_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.front_spec

/-- info: 'STACS2027.Runtimes.Sort.FG' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.FG

/-- info: 'STACS2027.Runtimes.Sort.FG.regIndep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.FG.regIndep

/-- info: 'STACS2027.Runtimes.Sort.FMem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.FMem

/-- info: 'STACS2027.Runtimes.Sort.FInv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.FInv

/-- info: 'STACS2027.Runtimes.Sort.FMem.put' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.FMem.put

/-- info: 'STACS2027.Runtimes.Sort.pIdOrd_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.pIdOrd_run

/-- info: 'STACS2027.Runtimes.Sort.pRead_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.pRead_run

/-- info: 'STACS2027.Runtimes.Sort.PJInv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.PJInv

/-- info: 'STACS2027.Runtimes.Sort.pBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.pBody_spec

/-- info: 'STACS2027.Runtimes.Sort.pRow_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.pRow_spec

/-- info: 'STACS2027.Runtimes.Sort.PairsPost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.PairsPost

/-- info: 'STACS2027.Runtimes.Sort.fPairs_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.fPairs_spec

/-- info: 'STACS2027.Runtimes.Sort.fID' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.fID

/-- info: 'STACS2027.Runtimes.Sort.fL' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.fL

/-- info: 'STACS2027.Runtimes.Sort.fIDb' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.fIDb

/-- info: 'STACS2027.Runtimes.Sort.fPU' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.fPU

/-- info: 'STACS2027.Runtimes.Sort.fPV' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.fPV

/-- info: 'STACS2027.Runtimes.Sort.fPI' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.fPI

/-- info: 'STACS2027.Runtimes.Sort.fEID' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.fEID

/-- info: 'STACS2027.Runtimes.Sort.fCNT' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.fCNT

/-- info: 'STACS2027.Runtimes.Sort.fEnd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.fEnd

/-- info: 'STACS2027.Runtimes.Sort.fEnd_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.fEnd_eq

/-- info: 'STACS2027.Runtimes.Sort.fEID_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.fEID_eq

/-- info: 'STACS2027.Runtimes.Sort.fEnd_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.fEnd_le

/-- info: 'STACS2027.Runtimes.Sort.ffits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.ffits

/-- info: 'STACS2027.Runtimes.Sort.fSort' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.fSort

/-- info: 'STACS2027.Runtimes.Sort.vArgs' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.vArgs

/-- info: 'STACS2027.Runtimes.Sort.vBack' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.vBack

/-- info: 'STACS2027.Runtimes.Sort.fVids' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.fVids

/-- info: 'STACS2027.Runtimes.Sort.pIds' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.pIds

/-- info: 'STACS2027.Runtimes.Sort.pOrd' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.pOrd

/-- info: 'STACS2027.Runtimes.Sort.pRead' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.pRead

/-- info: 'STACS2027.Runtimes.Sort.pBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.pBody

/-- info: 'STACS2027.Runtimes.Sort.pRow' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.pRow

/-- info: 'STACS2027.Runtimes.Sort.fPairs' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.fPairs

/-- info: 'STACS2027.Runtimes.Sort.fEids' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.fEids

/-- info: 'STACS2027.Runtimes.Sort.front' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.front

/-- info: 'STACS2027.Runtimes.Sort.FrontIn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.FrontIn

/-- info: 'STACS2027.Runtimes.Sort.frontIn_of_initPost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.frontIn_of_initPost

/-- info: 'STACS2027.Runtimes.Sort.eids_verts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.eids_verts

/-- info: 'STACS2027.Runtimes.Sort.length_verts'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.length_verts'

/-- info: 'STACS2027.Runtimes.Sort.ga_of_frame_msort' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.ga_of_frame_msort

/-- info: 'STACS2027.Runtimes.Sort.SortedPost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.SortedPost

/-- info: 'STACS2027.Runtimes.Sort.fSort_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.fSort_spec

/-- info: 'STACS2027.Runtimes.Sort.VidsPost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.VidsPost

/-- info: 'STACS2027.Runtimes.Sort.ga_of_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.ga_of_frame

/-- info: 'STACS2027.Runtimes.Sort.sortedLeads_wregs'' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.sortedLeads_wregs'

/-- info: 'STACS2027.Runtimes.Sort.rankIds_wregs'' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.rankIds_wregs'

/-- info: 'STACS2027.Runtimes.Sort.fVids_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.fVids_spec

/-- info: 'STACS2027.Runtimes.Sort.BInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.BInv

/-- info: 'STACS2027.Runtimes.Sort.run_bSetup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.run_bSetup

/-- info: 'STACS2027.Runtimes.Sort.bSetup_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.bSetup_spec

/-- info: 'STACS2027.Runtimes.Sort.blkStep_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.blkStep_spec

/-- info: 'STACS2027.Runtimes.Sort.blkLoop_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.blkLoop_spec

/-- info: 'STACS2027.Runtimes.Sort.SInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.SInv

/-- info: 'STACS2027.Runtimes.Sort.passStep_AB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.passStep_AB

/-- info: 'STACS2027.Runtimes.Sort.passStep_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.passStep_spec

/-- info: 'STACS2027.Runtimes.Sort.passLoop_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.passLoop_spec

/-- info: 'STACS2027.Runtimes.Sort.SortIn' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.SortIn

/-- info: 'STACS2027.Runtimes.Sort.SortOut' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.SortOut

/-- info: 'STACS2027.Runtimes.Sort.CM' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.CM

/-- info: 'STACS2027.Runtimes.Sort.IInv' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.IInv

/-- info: 'STACS2027.Runtimes.Sort.initBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.initBody_spec

/-- info: 'STACS2027.Runtimes.Sort.sInit_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.sInit_spec

/-- info: 'STACS2027.Runtimes.Sort.w1_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.w1_spec

/-- info: 'STACS2027.Runtimes.Sort.pass0_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.pass0_spec

/-- info: 'STACS2027.Runtimes.Sort.msort_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.msort_spec

/-- info: 'STACS2027.Runtimes.Sort.msort_wregs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.msort_wregs

/-- info: 'STACS2027.Runtimes.Sort.msort_writes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.msort_writes

/-- info: 'STACS2027.Runtimes.Sort.oKB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.oKB

/-- info: 'STACS2027.Runtimes.Sort.oL' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.oL

/-- info: 'STACS2027.Runtimes.Sort.oSQ' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.oSQ

/-- info: 'STACS2027.Runtimes.Sort.oA' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.oA

/-- info: 'STACS2027.Runtimes.Sort.oB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.oB

/-- info: 'STACS2027.Runtimes.Sort.oW' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.oW

/-- info: 'STACS2027.Runtimes.Sort.oW2' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.oW2

/-- info: 'STACS2027.Runtimes.Sort.oLo' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.oLo

/-- info: 'STACS2027.Runtimes.Sort.oMid' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.oMid

/-- info: 'STACS2027.Runtimes.Sort.oHi' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.oHi

/-- info: 'STACS2027.Runtimes.Sort.oI' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.oI

/-- info: 'STACS2027.Runtimes.Sort.oJ' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.oJ

/-- info: 'STACS2027.Runtimes.Sort.oK' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.oK

/-- info: 'STACS2027.Runtimes.Sort.oX' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.oX

/-- info: 'STACS2027.Runtimes.Sort.oY' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.oY

/-- info: 'STACS2027.Runtimes.Sort.oKX' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.oKX

/-- info: 'STACS2027.Runtimes.Sort.oKY' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.oKY

/-- info: 'STACS2027.Runtimes.Sort.takeX' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.takeX

/-- info: 'STACS2027.Runtimes.Sort.takeY' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.takeY

/-- info: 'STACS2027.Runtimes.Sort.mBoth' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.mBoth

/-- info: 'STACS2027.Runtimes.Sort.mLeft' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.mLeft

/-- info: 'STACS2027.Runtimes.Sort.mRight' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.mRight

/-- info: 'STACS2027.Runtimes.Sort.mBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.mBody

/-- info: 'STACS2027.Runtimes.Sort.bSetup' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.bSetup

/-- info: 'STACS2027.Runtimes.Sort.blkBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.blkBody

/-- info: 'STACS2027.Runtimes.Sort.blkCond' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.blkCond

/-- info: 'STACS2027.Runtimes.Sort.passBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.passBody

/-- info: 'STACS2027.Runtimes.Sort.passCond' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.passCond

/-- info: 'STACS2027.Runtimes.Sort.initBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.initBody

/-- info: 'STACS2027.Runtimes.Sort.sInit' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.sInit

/-- info: 'STACS2027.Runtimes.Sort.msort' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.msort

/-- info: 'STACS2027.Runtimes.Sort.Lay' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.Lay

/-- info: 'STACS2027.Runtimes.Sort.PMem' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.PMem

/-- info: 'STACS2027.Runtimes.Sort.PMem.push' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.PMem.push

/-- info: 'STACS2027.Runtimes.Sort.PG' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.PG

/-- info: 'STACS2027.Runtimes.Sort.run_mBody' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.run_mBody

/-- info: 'STACS2027.Runtimes.Sort.mBody_addrOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.mBody_addrOK

/-- info: 'STACS2027.Runtimes.Sort.bk_getD' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.bk_getD

/-- info: 'STACS2027.Runtimes.Sort.take_succ_getD' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.take_succ_getD

/-- info: 'STACS2027.Runtimes.Sort.MInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.MInv

/-- info: 'STACS2027.Runtimes.Sort.MInv.indep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.MInv.indep

/-- info: 'STACS2027.Runtimes.Sort.mBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.mBody_spec

/-- info: 'STACS2027.Runtimes.Sort.mergeLoop_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.mergeLoop_spec

/-- info: 'STACS2027.Runtimes.Sort.KeyLe' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.KeyLe

/-- info: 'STACS2027.Runtimes.Sort.sortKey' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.sortKey

/-- info: 'STACS2027.Runtimes.Sort.sortKey_perm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.sortKey_perm

/-- info: 'STACS2027.Runtimes.Sort.pairwise_sortKey' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.pairwise_sortKey

/-- info: 'STACS2027.Runtimes.Sort.eq_sortKey' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.eq_sortKey

/-- info: 'STACS2027.Runtimes.Sort.length_sortKey' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.length_sortKey

/-- info: 'STACS2027.Runtimes.Sort.lt_of_mem_sortKey' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.lt_of_mem_sortKey

/-- info: 'STACS2027.Runtimes.Sort.mem_sortKey' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.mem_sortKey

/-- info: 'STACS2027.Runtimes.Sort.mergeK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.mergeK

/-- info: 'STACS2027.Runtimes.Sort.mergeK_nil_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.mergeK_nil_left

/-- info: 'STACS2027.Runtimes.Sort.mergeK_nil_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.mergeK_nil_right

/-- info: 'STACS2027.Runtimes.Sort.mergeK_cons_cons' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.mergeK_cons_cons

/-- info: 'STACS2027.Runtimes.Sort.mergeK_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.mergeK_perm

/-- info: 'STACS2027.Runtimes.Sort.mem_mergeK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.mem_mergeK

/-- info: 'STACS2027.Runtimes.Sort.length_mergeK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.length_mergeK

/-- info: 'STACS2027.Runtimes.Sort.key_le_of_keyLt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.key_le_of_keyLt

/-- info: 'STACS2027.Runtimes.Sort.mergeK_pairwise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.mergeK_pairwise

/-- info: 'STACS2027.Runtimes.Sort.mergeK_drop_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.mergeK_drop_left

/-- info: 'STACS2027.Runtimes.Sort.mergeK_drop_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.mergeK_drop_right

/-- info: 'STACS2027.Runtimes.Sort.MState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.MState

/-- info: 'STACS2027.Runtimes.Sort.mState_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.mState_zero

/-- info: 'STACS2027.Runtimes.Sort.MState.left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.MState.left

/-- info: 'STACS2027.Runtimes.Sort.MState.right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.MState.right

/-- info: 'STACS2027.Runtimes.Sort.sl' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.sl

/-- info: 'STACS2027.Runtimes.Sort.length_sl' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.length_sl

/-- info: 'STACS2027.Runtimes.Sort.getElem_sl' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.getElem_sl

/-- info: 'STACS2027.Runtimes.Sort.bk' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.bk

/-- info: 'STACS2027.Runtimes.Sort.length_flatMap_range' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.length_flatMap_range

/-- info: 'STACS2027.Runtimes.Sort.flatMap_range_eq_nil' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.flatMap_range_eq_nil

/-- info: 'STACS2027.Runtimes.Sort.flatMap_range_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.flatMap_range_congr

/-- info: 'STACS2027.Runtimes.Sort.sl_flatMap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.sl_flatMap

/-- info: 'STACS2027.Runtimes.Sort.blk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.blk

/-- info: 'STACS2027.Runtimes.Sort.pass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.pass

/-- info: 'STACS2027.Runtimes.Sort.sortP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.sortP

/-- info: 'STACS2027.Runtimes.Sort.Good' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.Good

/-- info: 'STACS2027.Runtimes.Sort.bk_one_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.bk_one_range

/-- info: 'STACS2027.Runtimes.Sort.bk_one_range_nil' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.bk_one_range_nil

/-- info: 'STACS2027.Runtimes.Sort.good_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.good_range

/-- info: 'STACS2027.Runtimes.Sort.Good.length_bk' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.Good.length_bk

/-- info: 'STACS2027.Runtimes.Sort.Good.mem_bk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.Good.mem_bk

/-- info: 'STACS2027.Runtimes.Sort.Good.length_blk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.Good.length_blk

/-- info: 'STACS2027.Runtimes.Sort.Good.blk_sorted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.Good.blk_sorted

/-- info: 'STACS2027.Runtimes.Sort.Good.blk_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.Good.blk_perm

/-- info: 'STACS2027.Runtimes.Sort.Good.length_pass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.Good.length_pass

/-- info: 'STACS2027.Runtimes.Sort.Good.bk_pass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.Good.bk_pass

/-- info: 'STACS2027.Runtimes.Sort.Good.next' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.Good.next

/-- info: 'STACS2027.Runtimes.Sort.good_sortP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.good_sortP

/-- info: 'STACS2027.Runtimes.Sort.Good.eq_sortKey' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.Good.eq_sortKey

/-- info: 'STACS2027.Runtimes.Sort.sortP_clog' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.sortP_clog

/-- info: 'STACS2027.Runtimes.Sort.Good.length_passPre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.Good.length_passPre

/-- info: 'STACS2027.Runtimes.Sort.Good.passPre_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Sort.Good.passPre_full

/-- info: 'STACS2027.Runtimes.TwoSat.outOf_append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.outOf_append

/-- info: 'STACS2027.Runtimes.TwoSat.app' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.app

/-- info: 'STACS2027.Runtimes.TwoSat.bmp' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.bmp

/-- info: 'STACS2027.Runtimes.TwoSat.outOf_take_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.outOf_take_succ

/-- info: 'STACS2027.Runtimes.TwoSat.cnt' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.cnt

/-- info: 'STACS2027.Runtimes.TwoSat.cnt_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.cnt_zero

/-- info: 'STACS2027.Runtimes.TwoSat.length_outOf_take_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.length_outOf_take_le

/-- info: 'STACS2027.Runtimes.TwoSat.length_app' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.length_app

/-- info: 'STACS2027.Runtimes.TwoSat.cnt_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.cnt_succ

/-- info: 'STACS2027.Runtimes.TwoSat.ps' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.ps

/-- info: 'STACS2027.Runtimes.TwoSat.ps_succ' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.ps_succ

/-- info: 'STACS2027.Runtimes.TwoSat.ps_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.ps_mono

/-- info: 'STACS2027.Runtimes.TwoSat.ps_add_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.ps_add_le

/-- info: 'STACS2027.Runtimes.TwoSat.sum_indicator' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.sum_indicator

/-- info: 'STACS2027.Runtimes.TwoSat.ps_total' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.ps_total

/-- info: 'STACS2027.Runtimes.TwoSat.arr_csr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.arr_csr

/-- info: 'STACS2027.Runtimes.TwoSat.au_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.au_eq

/-- info: 'STACS2027.Runtimes.TwoSat.av_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.av_eq

/-- info: 'STACS2027.Runtimes.TwoSat.degBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.degBody

/-- info: 'STACS2027.Runtimes.TwoSat.stepDeg' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.stepDeg

/-- info: 'STACS2027.Runtimes.TwoSat.preBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.preBody

/-- info: 'STACS2027.Runtimes.TwoSat.stepPre' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.stepPre

/-- info: 'STACS2027.Runtimes.TwoSat.fillBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.fillBody

/-- info: 'STACS2027.Runtimes.TwoSat.stepFill' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.stepFill

/-- info: 'STACS2027.Runtimes.TwoSat.stepCsr' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.stepCsr

/-- info: 'STACS2027.Runtimes.TwoSat.DegMem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.DegMem

/-- info: 'STACS2027.Runtimes.TwoSat.DegInv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.DegInv

/-- info: 'STACS2027.Runtimes.TwoSat.DegMem.bmp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.DegMem.bmp

/-- info: 'STACS2027.Runtimes.TwoSat.degBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.degBody_spec

/-- info: 'STACS2027.Runtimes.TwoSat.stepDeg_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.stepDeg_spec

/-- info: 'STACS2027.Runtimes.TwoSat.PreMem' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.PreMem

/-- info: 'STACS2027.Runtimes.TwoSat.PreInv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.PreInv

/-- info: 'STACS2027.Runtimes.TwoSat.PreMem.snoc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.PreMem.snoc

/-- info: 'STACS2027.Runtimes.TwoSat.preBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.preBody_spec

/-- info: 'STACS2027.Runtimes.TwoSat.stepPre_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.stepPre_spec

/-- info: 'STACS2027.Runtimes.TwoSat.FillMem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.FillMem

/-- info: 'STACS2027.Runtimes.TwoSat.FillInv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.FillInv

/-- info: 'STACS2027.Runtimes.TwoSat.FillMem.app' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.FillMem.app

/-- info: 'STACS2027.Runtimes.TwoSat.fillBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.fillBody_spec

/-- info: 'STACS2027.Runtimes.TwoSat.stepFill_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.stepFill_spec

/-- info: 'STACS2027.Runtimes.TwoSat.CsrMem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.CsrMem

/-- info: 'STACS2027.Runtimes.TwoSat.CsrMem.upd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.CsrMem.upd

/-- info: 'STACS2027.Runtimes.TwoSat.stepCsr_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.stepCsr_spec

/-- info: 'STACS2027.Runtimes.TwoSat.absOf' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.absOf

/-- info: 'STACS2027.Runtimes.TwoSat.muC' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.muC

/-- info: 'STACS2027.Runtimes.TwoSat.muC_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.muC_eq

/-- info: 'STACS2027.Runtimes.TwoSat.LoopInv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.LoopInv

/-- info: 'STACS2027.Runtimes.TwoSat.sccCond_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.sccCond_run

/-- info: 'STACS2027.Runtimes.TwoSat.sccInit_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.sccInit_spec

/-- info: 'STACS2027.Runtimes.TwoSat.sccRound_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.sccRound_spec

/-- info: 'STACS2027.Runtimes.TwoSat.sccLoop_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.sccLoop_spec

/-- info: 'STACS2027.Runtimes.TwoSat.stepScc_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.stepScc_spec

/-- info: 'STACS2027.Runtimes.TwoSat.twoSatInput' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.twoSatInput

/-- info: 'STACS2027.Runtimes.TwoSat.mainInit' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.mainInit

/-- info: 'STACS2027.Runtimes.TwoSat.outLoopBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.outLoopBody

/-- info: 'STACS2027.Runtimes.TwoSat.mainOut' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.mainOut

/-- info: 'STACS2027.Runtimes.TwoSat.twoSatMain' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.twoSatMain

/-- info: 'STACS2027.Runtimes.TwoSat.CM' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.CM

/-- info: 'STACS2027.Runtimes.TwoSat.spaceM' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.spaceM

/-- info: 'STACS2027.Runtimes.TwoSat.spaceM_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.spaceM_le

/-- info: 'STACS2027.Runtimes.TwoSat.mainInit_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.mainInit_spec

/-- info: 'STACS2027.Runtimes.TwoSat.BitInv' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.BitInv

/-- info: 'STACS2027.Runtimes.TwoSat.mainOut_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.mainOut_spec

/-- info: 'STACS2027.Runtimes.TwoSat.twoSatMain_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.twoSatMain_spec

/-- info: 'STACS2027.Runtimes.TwoSat.twoSat_computes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.twoSat_computes

/-- info: 'STACS2027.Runtimes.TwoSat.exists_linear_twoSat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.exists_linear_twoSat

/-- info: 'STACS2027.Runtimes.TwoSat.outRead' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.outRead

/-- info: 'STACS2027.Runtimes.TwoSat.outOk' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.outOk

/-- info: 'STACS2027.Runtimes.TwoSat.outBit' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.outBit

/-- info: 'STACS2027.Runtimes.TwoSat.outBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.outBody

/-- info: 'STACS2027.Runtimes.TwoSat.stepOut' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.stepOut

/-- info: 'STACS2027.Runtimes.TwoSat.twoSat' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.twoSat

/-- info: 'STACS2027.Runtimes.TwoSat.asgBits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.asgBits

/-- info: 'STACS2027.Runtimes.TwoSat.OutMem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.OutMem

/-- info: 'STACS2027.Runtimes.TwoSat.okv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.okv

/-- info: 'STACS2027.Runtimes.TwoSat.okv_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.okv_succ

/-- info: 'STACS2027.Runtimes.TwoSat.OutInv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.OutInv

/-- info: 'STACS2027.Runtimes.TwoSat.outBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.outBody_spec

/-- info: 'STACS2027.Runtimes.TwoSat.stepOut_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.stepOut_spec

/-- info: 'STACS2027.Runtimes.TwoSat.TwoSatOut' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.TwoSatOut

/-- info: 'STACS2027.Runtimes.TwoSat.CT' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.CT

/-- info: 'STACS2027.Runtimes.TwoSat.InBlock' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.InBlock

/-- info: 'STACS2027.Runtimes.TwoSat.inBlock_seq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.inBlock_seq

/-- info: 'STACS2027.Runtimes.TwoSat.twoSat_wregs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.twoSat_wregs

/-- info: 'STACS2027.Runtimes.TwoSat.twoSat_writes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.twoSat_writes

/-- info: 'STACS2027.Runtimes.TwoSat.twoSat_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.twoSat_core

/-- info: 'STACS2027.Runtimes.TwoSat.twoSat_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.twoSat_spec

/-- info: 'STACS2027.Runtimes.TwoSat.evalCNF_congr' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.evalCNF_congr

/-- info: 'STACS2027.Runtimes.TwoSat.twoSatOut_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.twoSatOut_correct

/-- info: 'STACS2027.Runtimes.TwoSat.tN' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.tN

/-- info: 'STACS2027.Runtimes.TwoSat.tM' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.tM

/-- info: 'STACS2027.Runtimes.TwoSat.tCL' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.tCL

/-- info: 'STACS2027.Runtimes.TwoSat.tOK' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.tOK

/-- info: 'STACS2027.Runtimes.TwoSat.tAS' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.tAS

/-- info: 'STACS2027.Runtimes.TwoSat.tN2' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.tN2

/-- info: 'STACS2027.Runtimes.TwoSat.tM2' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.tM2

/-- info: 'STACS2027.Runtimes.TwoSat.tNEG' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.tNEG

/-- info: 'STACS2027.Runtimes.TwoSat.tAU' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.tAU

/-- info: 'STACS2027.Runtimes.TwoSat.tAV' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.tAV

/-- info: 'STACS2027.Runtimes.TwoSat.tDEG' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.tDEG

/-- info: 'STACS2027.Runtimes.TwoSat.tOFF' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.tOFF

/-- info: 'STACS2027.Runtimes.TwoSat.tFIL' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.tFIL

/-- info: 'STACS2027.Runtimes.TwoSat.tADJ' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.tADJ

/-- info: 'STACS2027.Runtimes.TwoSat.tLAB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.tLAB

/-- info: 'STACS2027.Runtimes.TwoSat.tPTR' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.tPTR

/-- info: 'STACS2027.Runtimes.TwoSat.tSTK' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.tSTK

/-- info: 'STACS2027.Runtimes.TwoSat.tSS' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.tSS

/-- info: 'STACS2027.Runtimes.TwoSat.tBB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.tBB

/-- info: 'STACS2027.Runtimes.TwoSat.tSP' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.tSP

/-- info: 'STACS2027.Runtimes.TwoSat.tSSP' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.tSSP

/-- info: 'STACS2027.Runtimes.TwoSat.tBP' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.tBP

/-- info: 'STACS2027.Runtimes.TwoSat.tNXT' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.tNXT

/-- info: 'STACS2027.Runtimes.TwoSat.tVAL' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.tVAL

/-- info: 'STACS2027.Runtimes.TwoSat.sI' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.sI

/-- info: 'STACS2027.Runtimes.TwoSat.sX' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.sX

/-- info: 'STACS2027.Runtimes.TwoSat.sY' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.sY

/-- info: 'STACS2027.Runtimes.TwoSat.sU' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.sU

/-- info: 'STACS2027.Runtimes.TwoSat.sV' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.sV

/-- info: 'STACS2027.Runtimes.TwoSat.sP' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.sP

/-- info: 'STACS2027.Runtimes.TwoSat.sA' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.sA

/-- info: 'STACS2027.Runtimes.TwoSat.sB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.sB

/-- info: 'STACS2027.Runtimes.TwoSat.sW' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.sW

/-- info: 'STACS2027.Runtimes.TwoSat.sH' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.sH

/-- info: 'STACS2027.Runtimes.TwoSat.sAcc' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.sAcc

/-- info: 'STACS2027.Runtimes.TwoSat.sQ' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.sQ

/-- info: 'STACS2027.Runtimes.TwoSat.TwoSatIn' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.TwoSatIn

/-- info: 'STACS2027.Runtimes.TwoSat.bAU' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.bAU

/-- info: 'STACS2027.Runtimes.TwoSat.bAV' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.bAV

/-- info: 'STACS2027.Runtimes.TwoSat.bDEG' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.bDEG

/-- info: 'STACS2027.Runtimes.TwoSat.bOFF' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.bOFF

/-- info: 'STACS2027.Runtimes.TwoSat.bFIL' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.bFIL

/-- info: 'STACS2027.Runtimes.TwoSat.bADJ' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.bADJ

/-- info: 'STACS2027.Runtimes.TwoSat.bLAB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.bLAB

/-- info: 'STACS2027.Runtimes.TwoSat.bPTR' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.bPTR

/-- info: 'STACS2027.Runtimes.TwoSat.bSTK' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.bSTK

/-- info: 'STACS2027.Runtimes.TwoSat.bSS' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.bSS

/-- info: 'STACS2027.Runtimes.TwoSat.bBB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.bBB

/-- info: 'STACS2027.Runtimes.TwoSat.bAS' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.bAS

/-- info: 'STACS2027.Runtimes.TwoSat.endL' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.endL

/-- info: 'STACS2027.Runtimes.TwoSat.layout_eqs' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.layout_eqs

/-- info: 'STACS2027.Runtimes.TwoSat.endL_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.endL_le

/-- info: 'STACS2027.Runtimes.TwoSat.fits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.fits

/-- info: 'STACS2027.Runtimes.TwoSat.allocT' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.allocT

/-- info: 'STACS2027.Runtimes.TwoSat.negBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.negBody

/-- info: 'STACS2027.Runtimes.TwoSat.stepNeg' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.stepNeg

/-- info: 'STACS2027.Runtimes.TwoSat.arcBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.arcBody

/-- info: 'STACS2027.Runtimes.TwoSat.stepArc' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.stepArc

/-- info: 'STACS2027.Runtimes.TwoSat.Glob' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.Glob

/-- info: 'STACS2027.Runtimes.TwoSat.WT' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.WT

/-- info: 'STACS2027.Runtimes.TwoSat.Glob.regIndep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.Glob.regIndep

/-- info: 'STACS2027.Runtimes.TwoSat.codes_get' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.codes_get

/-- info: 'STACS2027.Runtimes.TwoSat.au' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.au

/-- info: 'STACS2027.Runtimes.TwoSat.av' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.av

/-- info: 'STACS2027.Runtimes.TwoSat.length_arcsOfCodes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.length_arcsOfCodes

/-- info: 'STACS2027.Runtimes.TwoSat.arcs_get' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.arcs_get

/-- info: 'STACS2027.Runtimes.TwoSat.NegMem' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.NegMem

/-- info: 'STACS2027.Runtimes.TwoSat.NegInv' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.NegInv

/-- info: 'STACS2027.Runtimes.TwoSat.allocT_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.allocT_spec

/-- info: 'STACS2027.Runtimes.TwoSat.NegMem.snoc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.NegMem.snoc

/-- info: 'STACS2027.Runtimes.TwoSat.negBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.negBody_spec

/-- info: 'STACS2027.Runtimes.TwoSat.stepNeg_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.stepNeg_spec

/-- info: 'STACS2027.Runtimes.TwoSat.ArcMem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.ArcMem

/-- info: 'STACS2027.Runtimes.TwoSat.ArcInv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.ArcInv

/-- info: 'STACS2027.Runtimes.TwoSat.ArcMem.snoc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.ArcMem.snoc

/-- info: 'STACS2027.Runtimes.TwoSat.arcBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.arcBody_spec

/-- info: 'STACS2027.Runtimes.TwoSat.stepArc_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.stepArc_spec

/-- info: 'STACS2027.Runtimes.TwoSat.Scc.Reach' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.Scc.Reach

/-- info: 'STACS2027.Runtimes.TwoSat.Scc.Reach.refl'' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.Scc.Reach.refl'

/-- info: 'STACS2027.Runtimes.TwoSat.Scc.Reach.trans'' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.Scc.Reach.trans'

/-- info: 'STACS2027.Runtimes.TwoSat.Scc.Reach.arc' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.Scc.Reach.arc

/-- info: 'STACS2027.Runtimes.TwoSat.Scc.Closed' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.Scc.Closed

/-- info: 'STACS2027.Runtimes.TwoSat.Scc.State' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.Scc.State

/-- info: 'STACS2027.Runtimes.TwoSat.Scc.SameGrp' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.Scc.SameGrp

/-- info: 'STACS2027.Runtimes.TwoSat.Scc.relab' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.Scc.relab

/-- info: 'STACS2027.Runtimes.TwoSat.Scc.bump' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.Scc.bump

/-- info: 'STACS2027.Runtimes.TwoSat.Scc.push' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.Scc.push

/-- info: 'STACS2027.Runtimes.TwoSat.Scc.popc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.Scc.popc

/-- info: 'STACS2027.Runtimes.TwoSat.Scc.step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.Scc.step

/-- info: 'STACS2027.Runtimes.TwoSat.Scc.init' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.Scc.init

/-- info: 'STACS2027.Runtimes.TwoSat.Scc.Halted' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.Scc.Halted

/-- info: 'STACS2027.Runtimes.TwoSat.Scc.run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.Scc.run

/-- info: 'STACS2027.Runtimes.TwoSat.Scc.Inv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.Scc.Inv

/-- info: 'STACS2027.Runtimes.TwoSat.Scc.getD_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.Scc.getD_mem

/-- info: 'STACS2027.Runtimes.TwoSat.Scc.getD_mem_or' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.Scc.getD_mem_or

/-- info: 'STACS2027.Runtimes.TwoSat.Scc.lab_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.Scc.lab_mem

/-- info: 'STACS2027.Runtimes.TwoSat.Scc.nodup_of_lab' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.Scc.nodup_of_lab

/-- info: 'STACS2027.Runtimes.TwoSat.Scc.eq_of_lab_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.Scc.eq_of_lab_eq

/-- info: 'STACS2027.Runtimes.TwoSat.Scc.mem_drop_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.Scc.mem_drop_iff

/-- info: 'STACS2027.Runtimes.TwoSat.Scc.mem_take_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.Scc.mem_take_iff

/-- info: 'STACS2027.Runtimes.TwoSat.Scc.length_le_of_pw' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.Scc.length_le_of_pw

/-- info: 'STACS2027.Runtimes.TwoSat.Scc.nodup_range_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.Scc.nodup_range_length

/-- info: 'STACS2027.Runtimes.TwoSat.Scc.pw_mem_cases' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.Scc.pw_mem_cases

/-- info: 'STACS2027.Runtimes.TwoSat.Scc.Inv.lab_S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.Scc.Inv.lab_S

/-- info: 'STACS2027.Runtimes.TwoSat.Scc.Inv.nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.Scc.Inv.nodup

/-- info: 'STACS2027.Runtimes.TwoSat.Scc.Inv.S_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.Scc.Inv.S_lt

/-- info: 'STACS2027.Runtimes.TwoSat.Scc.Inv.lab_le_N' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.Scc.Inv.lab_le_N

/-- info: 'STACS2027.Runtimes.TwoSat.Scc.Inv.mem_S_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.Scc.Inv.mem_S_iff

/-- info: 'STACS2027.Runtimes.TwoSat.Scc.Inv.stk_S_lab' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.Scc.Inv.stk_S_lab

/-- info: 'STACS2027.Runtimes.TwoSat.Scc.Inv.top_max' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.Scc.Inv.top_max

/-- info: 'STACS2027.Runtimes.TwoSat.Scc.Inv.not_mem_rest' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.Scc.Inv.not_mem_rest

/-- info: 'STACS2027.Runtimes.TwoSat.Scc.Inv.stk_reach' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.Scc.Inv.stk_reach

/-- info: 'STACS2027.Runtimes.TwoSat.Scc.Inv.head_ge' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.Scc.Inv.head_ge

/-- info: 'STACS2027.Runtimes.TwoSat.Scc.sameGrp_cons' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.Scc.sameGrp_cons

/-- info: 'STACS2027.Runtimes.TwoSat.Scc.sameGrp_refl' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.Scc.sameGrp_refl

/-- info: 'STACS2027.Runtimes.TwoSat.Scc.SameGrp.symm' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.Scc.SameGrp.symm

/-- info: 'STACS2027.Runtimes.TwoSat.Scc.SameGrp.of_cons' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.Scc.SameGrp.of_cons

/-- info: 'STACS2027.Runtimes.TwoSat.Scc.exists_max_le' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.Scc.exists_max_le

/-- info: 'STACS2027.Runtimes.TwoSat.Scc.pw_le_head' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.Scc.pw_le_head

/-- info: 'STACS2027.Runtimes.TwoSat.Scc.headD_mem' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.Scc.headD_mem

/-- info: 'STACS2027.Runtimes.TwoSat.Scc.Inv.root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.Scc.Inv.root

/-- info: 'STACS2027.Runtimes.TwoSat.Scc.Inv.head_le_top' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.Scc.Inv.head_le_top

/-- info: 'STACS2027.Runtimes.TwoSat.Scc.Inv.S_ne_of_stk' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.Scc.Inv.S_ne_of_stk

/-- info: 'STACS2027.Runtimes.TwoSat.Scc.Inv.B_ne_of_stk' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.Scc.Inv.B_ne_of_stk

/-- info: 'STACS2027.Runtimes.TwoSat.Scc.Inv.S_nil_of_stk' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.Scc.Inv.S_nil_of_stk

/-- info: 'STACS2027.Runtimes.TwoSat.Scc.Inv.B_nil_of_S' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.Scc.Inv.B_nil_of_S

/-- info: 'STACS2027.Runtimes.TwoSat.Scc.inv_init' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.Scc.inv_init

/-- info: 'STACS2027.Runtimes.TwoSat.Scc.inv_push' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.Scc.inv_push

/-- info: 'STACS2027.Runtimes.TwoSat.Scc.inv_bump' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.Scc.inv_bump

/-- info: 'STACS2027.Runtimes.TwoSat.Scc.inv_merge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.Scc.inv_merge

/-- info: 'STACS2027.Runtimes.TwoSat.Scc.inv_pop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.Scc.inv_pop

/-- info: 'STACS2027.Runtimes.TwoSat.Scc.inv_nxt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.Scc.inv_nxt

/-- info: 'STACS2027.Runtimes.TwoSat.Scc.inv_popc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.Scc.inv_popc

/-- info: 'STACS2027.Runtimes.TwoSat.Scc.push_bump' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.Scc.push_bump

/-- info: 'STACS2027.Runtimes.TwoSat.Scc.inv_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.Scc.inv_step

/-- info: 'STACS2027.Runtimes.TwoSat.Scc.mu' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.Scc.mu

/-- info: 'STACS2027.Runtimes.TwoSat.Scc.sum_map_le_aux' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.Scc.sum_map_le_aux

/-- info: 'STACS2027.Runtimes.TwoSat.Scc.sum_map_lt_aux' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.Scc.sum_map_lt_aux

/-- info: 'STACS2027.Runtimes.TwoSat.Scc.length_filter_eq_sum' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.Scc.length_filter_eq_sum

/-- info: 'STACS2027.Runtimes.TwoSat.Scc.unvisited_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.Scc.unvisited_lt

/-- info: 'STACS2027.Runtimes.TwoSat.Scc.ptrsum_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.Scc.ptrsum_lt

/-- info: 'STACS2027.Runtimes.TwoSat.Scc.unv' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.Scc.unv

/-- info: 'STACS2027.Runtimes.TwoSat.Scc.rem' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.Scc.rem

/-- info: 'STACS2027.Runtimes.TwoSat.Scc.mu_eq' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.Scc.mu_eq

/-- info: 'STACS2027.Runtimes.TwoSat.Scc.mu_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.Scc.mu_step

/-- info: 'STACS2027.Runtimes.TwoSat.Scc.step_halted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.Scc.step_halted

/-- info: 'STACS2027.Runtimes.TwoSat.Scc.run_halted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.Scc.run_halted

/-- info: 'STACS2027.Runtimes.TwoSat.Scc.inv_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.Scc.inv_run

/-- info: 'STACS2027.Runtimes.TwoSat.Scc.halted_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.Scc.halted_run

/-- info: 'STACS2027.Runtimes.TwoSat.Scc.run_add' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.Scc.run_add

/-- info: 'STACS2027.Runtimes.TwoSat.Scc.run_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.Scc.run_succ

/-- info: 'STACS2027.Runtimes.TwoSat.Scc.final' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.Scc.final

/-- info: 'STACS2027.Runtimes.TwoSat.Scc.final_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.Scc.final_inv

/-- info: 'STACS2027.Runtimes.TwoSat.Scc.final_halted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.Scc.final_halted

/-- info: 'STACS2027.Runtimes.TwoSat.Scc.run_eq_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.Scc.run_eq_final

/-- info: 'STACS2027.Runtimes.TwoSat.Scc.mu_init' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.Scc.mu_init

/-- info: 'STACS2027.Runtimes.TwoSat.Scc.mu_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.Scc.mu_congr

/-- info: 'STACS2027.Runtimes.TwoSat.Scc.final_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.Scc.final_spec

/-- info: 'STACS2027.Runtimes.TwoSat.Scc.Inv.stk_len' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.Scc.Inv.stk_len

/-- info: 'STACS2027.Runtimes.TwoSat.Scc.Inv.B_len' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.Scc.Inv.B_len

/-- info: 'STACS2027.Runtimes.TwoSat.step_nil_visit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.step_nil_visit

/-- info: 'STACS2027.Runtimes.TwoSat.step_nil_skip' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.step_nil_skip

/-- info: 'STACS2027.Runtimes.TwoSat.step_visit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.step_visit

/-- info: 'STACS2027.Runtimes.TwoSat.step_merge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.step_merge

/-- info: 'STACS2027.Runtimes.TwoSat.step_adv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.step_adv

/-- info: 'STACS2027.Runtimes.TwoSat.step_popc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.step_popc

/-- info: 'STACS2027.Runtimes.TwoSat.step_pop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.step_pop

/-- info: 'STACS2027.Runtimes.TwoSat.mid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.mid

/-- info: 'STACS2027.Runtimes.TwoSat.popc_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.popc_eq

/-- info: 'STACS2027.Runtimes.TwoSat.Scc.Inv.room' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.Scc.Inv.room

/-- info: 'STACS2027.Runtimes.TwoSat.SrchMem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.SrchMem

/-- info: 'STACS2027.Runtimes.TwoSat.SrchRep' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.SrchRep

/-- info: 'STACS2027.Runtimes.TwoSat.WS' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.WS

/-- info: 'STACS2027.Runtimes.TwoSat.SrchRep.indep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.SrchRep.indep

/-- info: 'STACS2027.Runtimes.TwoSat.SrchMem.push' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.SrchMem.push

/-- info: 'STACS2027.Runtimes.TwoSat.SrchMem.bump' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.SrchMem.bump

/-- info: 'STACS2027.Runtimes.TwoSat.SrchMem.tailB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.SrchMem.tailB

/-- info: 'STACS2027.Runtimes.TwoSat.SrchMem.popStk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.SrchMem.popStk

/-- info: 'STACS2027.Runtimes.TwoSat.SrchMem.setNxt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.SrchMem.setNxt

/-- info: 'STACS2027.Runtimes.TwoSat.SrchMem.toMid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.SrchMem.toMid

/-- info: 'STACS2027.Runtimes.TwoSat.SrchMem.popOne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.SrchMem.popOne

/-- info: 'STACS2027.Runtimes.TwoSat.visitT' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.visitT

/-- info: 'STACS2027.Runtimes.TwoSat.rootStep' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.rootStep

/-- info: 'STACS2027.Runtimes.TwoSat.topRead' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.topRead

/-- info: 'STACS2027.Runtimes.TwoSat.bumpV' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.bumpV

/-- info: 'STACS2027.Runtimes.TwoSat.headRead' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.headRead

/-- info: 'STACS2027.Runtimes.TwoSat.advance' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.advance

/-- info: 'STACS2027.Runtimes.TwoSat.popCond' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.popCond

/-- info: 'STACS2027.Runtimes.TwoSat.popBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.popBody

/-- info: 'STACS2027.Runtimes.TwoSat.popComp' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.popComp

/-- info: 'STACS2027.Runtimes.TwoSat.finRead' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.finRead

/-- info: 'STACS2027.Runtimes.TwoSat.finish' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.finish

/-- info: 'STACS2027.Runtimes.TwoSat.topStep' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.topStep

/-- info: 'STACS2027.Runtimes.TwoSat.sccBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.sccBody

/-- info: 'STACS2027.Runtimes.TwoSat.sccCond' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.sccCond

/-- info: 'STACS2027.Runtimes.TwoSat.sccInit' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.sccInit

/-- info: 'STACS2027.Runtimes.TwoSat.stepScc' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.stepScc

/-- info: 'STACS2027.Runtimes.TwoSat.wregs_visitT' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.wregs_visitT

/-- info: 'STACS2027.Runtimes.TwoSat.loopFree_visitT' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.loopFree_visitT

/-- info: 'STACS2027.Runtimes.TwoSat.visitT_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.visitT_run

/-- info: 'STACS2027.Runtimes.TwoSat.visitT_addrOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.visitT_addrOK

/-- info: 'STACS2027.Runtimes.TwoSat.incNxt_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.incNxt_run

/-- info: 'STACS2027.Runtimes.TwoSat.rootStep_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.rootStep_run

/-- info: 'STACS2027.Runtimes.TwoSat.topRead_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.topRead_run

/-- info: 'STACS2027.Runtimes.TwoSat.topRead_addrOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.topRead_addrOK

/-- info: 'STACS2027.Runtimes.TwoSat.wregs_bumpV' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.wregs_bumpV

/-- info: 'STACS2027.Runtimes.TwoSat.bumpV_addrOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.bumpV_addrOK

/-- info: 'STACS2027.Runtimes.TwoSat.bumpV_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.bumpV_run

/-- info: 'STACS2027.Runtimes.TwoSat.headD_eq_getLast' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.headD_eq_getLast

/-- info: 'STACS2027.Runtimes.TwoSat.headRead_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.headRead_run

/-- info: 'STACS2027.Runtimes.TwoSat.headRead_addrOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.headRead_addrOK

/-- info: 'STACS2027.Runtimes.TwoSat.advance_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.advance_run

/-- info: 'STACS2027.Runtimes.TwoSat.finRead_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.finRead_run

/-- info: 'STACS2027.Runtimes.TwoSat.finRead_addrOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.finRead_addrOK

/-- info: 'STACS2027.Runtimes.TwoSat.popStk_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.popStk_run

/-- info: 'STACS2027.Runtimes.TwoSat.SrchRep.toMid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.SrchRep.toMid

/-- info: 'STACS2027.Runtimes.TwoSat.PopInv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.PopInv

/-- info: 'STACS2027.Runtimes.TwoSat.popInit_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.popInit_spec

/-- info: 'STACS2027.Runtimes.TwoSat.popRound_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.popRound_spec

/-- info: 'STACS2027.Runtimes.TwoSat.popTail_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.popTail_run

/-- info: 'STACS2027.Runtimes.TwoSat.popComp_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.popComp_spec

/-- info: 'STACS2027.Runtimes.TwoSat.TopP' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.TopP

/-- info: 'STACS2027.Runtimes.TwoSat.finish_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.finish_spec

/-- info: 'STACS2027.Runtimes.TwoSat.sccBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.sccBody_spec

/-- info: 'STACS2027.Runtimes.TwoSat.code' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.code

/-- info: 'STACS2027.Runtimes.TwoSat.neg' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.neg

/-- info: 'STACS2027.Runtimes.TwoSat.nodeVal' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.nodeVal

/-- info: 'STACS2027.Runtimes.TwoSat.nodeVal_even' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.nodeVal_even

/-- info: 'STACS2027.Runtimes.TwoSat.nodeVal_odd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.nodeVal_odd

/-- info: 'STACS2027.Runtimes.TwoSat.nodeVal_code' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.nodeVal_code

/-- info: 'STACS2027.Runtimes.TwoSat.nodeVal_neg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.nodeVal_neg

/-- info: 'STACS2027.Runtimes.TwoSat.neg_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.neg_lt

/-- info: 'STACS2027.Runtimes.TwoSat.neg_even' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.neg_even

/-- info: 'STACS2027.Runtimes.TwoSat.neg_odd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.neg_odd

/-- info: 'STACS2027.Runtimes.TwoSat.code_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.code_lt

/-- info: 'STACS2027.Runtimes.TwoSat.IsTwoCNF' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.IsTwoCNF

/-- info: 'STACS2027.Runtimes.TwoSat.codes' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.codes

/-- info: 'STACS2027.Runtimes.TwoSat.arcsOfCodes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.arcsOfCodes

/-- info: 'STACS2027.Runtimes.TwoSat.outOf' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.outOf

/-- info: 'STACS2027.Runtimes.TwoSat.mem_outOf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.mem_outOf

/-- info: 'STACS2027.Runtimes.TwoSat.nbOf' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.nbOf

/-- info: 'STACS2027.Runtimes.TwoSat.CodesOk' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.CodesOk

/-- info: 'STACS2027.Runtimes.TwoSat.mem_arcsOfCodes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.mem_arcsOfCodes

/-- info: 'STACS2027.Runtimes.TwoSat.closed_nbOf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.closed_nbOf

/-- info: 'STACS2027.Runtimes.TwoSat.codes_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.codes_ok

/-- info: 'STACS2027.Runtimes.TwoSat.length_codes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.length_codes

/-- info: 'STACS2027.Runtimes.TwoSat.arcs_cons_clause' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.arcs_cons_clause

/-- info: 'STACS2027.Runtimes.TwoSat.clause_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.clause_eq

/-- info: 'STACS2027.Runtimes.TwoSat.clause_arcs_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.clause_arcs_mem

/-- info: 'STACS2027.Runtimes.TwoSat.arc_val' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.arc_val

/-- info: 'STACS2027.Runtimes.TwoSat.reach_val' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.reach_val

/-- info: 'STACS2027.Runtimes.TwoSat.criterion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.criterion

/-- info: 'STACS2027.Runtimes.TwoSat.lab' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.lab

/-- info: 'STACS2027.Runtimes.TwoSat.okB' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.okB

/-- info: 'STACS2027.Runtimes.TwoSat.asg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.asg

/-- info: 'STACS2027.Runtimes.TwoSat.twoSat_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.TwoSat.twoSat_correct

/-- info: 'STACS2027.Runtimes.ZeroCost.zeroCostSpace' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.zeroCostSpace

/-- info: 'STACS2027.Runtimes.ZeroCost.bCL_codes_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.bCL_codes_le

/-- info: 'STACS2027.Runtimes.ZeroCost.CS20' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.CS20

/-- info: 'STACS2027.Runtimes.ZeroCost.zeroCostSpace_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.zeroCostSpace_le

/-- info: 'STACS2027.Runtimes.ZeroCost.SatFacts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.SatFacts

/-- info: 'STACS2027.Runtimes.ZeroCost.SatPost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.SatPost

/-- info: 'STACS2027.Runtimes.ZeroCost.callSat_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.callSat_spec

/-- info: 'STACS2027.Runtimes.ZeroCost.ZeroCostAnswer' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.ZeroCostAnswer

/-- info: 'STACS2027.Runtimes.ZeroCost.stepRec_answer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.stepRec_answer

/-- info: 'STACS2027.Runtimes.ZeroCost.CZeroCost' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.CZeroCost

/-- info: 'STACS2027.Runtimes.ZeroCost.zeroCostProg_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.zeroCostProg_spec

/-- info: 'STACS2027.Runtimes.ZeroCost.zeroCost_ram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.zeroCost_ram

/-- info: 'STACS2027.Runtimes.ZeroCost.GE' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.GE

/-- info: 'STACS2027.Runtimes.ZeroCost.WE' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.WE

/-- info: 'STACS2027.Runtimes.ZeroCost.GE.regIndep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.GE.regIndep

/-- info: 'STACS2027.Runtimes.ZeroCost.EMem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.EMem

/-- info: 'STACS2027.Runtimes.ZeroCost.EInv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.EInv

/-- info: 'STACS2027.Runtimes.ZeroCost.occ_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.occ_lt

/-- info: 'STACS2027.Runtimes.ZeroCost.EMem.put' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.EMem.put

/-- info: 'STACS2027.Runtimes.ZeroCost.nextPos_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.nextPos_run

/-- info: 'STACS2027.Runtimes.ZeroCost.minmax_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.minmax_run

/-- info: 'STACS2027.Runtimes.ZeroCost.edgeA_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.edgeA_run

/-- info: 'STACS2027.Runtimes.ZeroCost.ldY_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.ldY_run

/-- info: 'STACS2027.Runtimes.ZeroCost.edgeIds_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.edgeIds_run

/-- info: 'STACS2027.Runtimes.ZeroCost.WR' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.WR

/-- info: 'STACS2027.Runtimes.ZeroCost.edgeRead_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.edgeRead_run

/-- info: 'STACS2027.Runtimes.ZeroCost.JInv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.JInv

/-- info: 'STACS2027.Runtimes.ZeroCost.not_mem_of_sub' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.not_mem_of_sub

/-- info: 'STACS2027.Runtimes.ZeroCost.edgeBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.edgeBody_spec

/-- info: 'STACS2027.Runtimes.ZeroCost.edgeRow_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.edgeRow_spec

/-- info: 'STACS2027.Runtimes.ZeroCost.EdgesPost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.EdgesPost

/-- info: 'STACS2027.Runtimes.ZeroCost.IdsPre' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.IdsPre

/-- info: 'STACS2027.Runtimes.ZeroCost.IdsMid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.IdsMid

/-- info: 'STACS2027.Runtimes.ZeroCost.tab_of_arr_map_range' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.tab_of_arr_map_range

/-- info: 'STACS2027.Runtimes.ZeroCost.pairIds_zeroCost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.pairIds_zeroCost

/-- info: 'STACS2027.Runtimes.ZeroCost.stepEdges_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.stepEdges_spec

/-- info: 'STACS2027.Runtimes.ZeroCost.OffInv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.OffInv

/-- info: 'STACS2027.Runtimes.ZeroCost.offBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.offBody_spec

/-- info: 'STACS2027.Runtimes.ZeroCost.OffPost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.OffPost

/-- info: 'STACS2027.Runtimes.ZeroCost.stepOff_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.stepOff_spec

/-- info: 'STACS2027.Runtimes.ZeroCost.pcCl' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.pcCl

/-- info: 'STACS2027.Runtimes.ZeroCost.pcList' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.pcList

/-- info: 'STACS2027.Runtimes.ZeroCost.pcList_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.pcList_eq

/-- info: 'STACS2027.Runtimes.ZeroCost.length_pcCl_le' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.length_pcCl_le

/-- info: 'STACS2027.Runtimes.ZeroCost.occClOf' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.occClOf

/-- info: 'STACS2027.Runtimes.ZeroCost.length_occClOf_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.length_occClOf_le

/-- info: 'STACS2027.Runtimes.ZeroCost.occCl' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.occCl

/-- info: 'STACS2027.Runtimes.ZeroCost.zcf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.zcf

/-- info: 'STACS2027.Runtimes.ZeroCost.occ_facts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.occ_facts

/-- info: 'STACS2027.Runtimes.ZeroCost.mem_occCl_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.mem_occCl_iff

/-- info: 'STACS2027.Runtimes.ZeroCost.mem_zcf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.mem_zcf

/-- info: 'STACS2027.Runtimes.ZeroCost.evalCNF_zcf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.evalCNF_zcf

/-- info: 'STACS2027.Runtimes.ZeroCost.zcf_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.zcf_two

/-- info: 'STACS2027.Runtimes.ZeroCost.length_pathConstraints_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.length_pathConstraints_le

/-- info: 'STACS2027.Runtimes.ZeroCost.length_zcf_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.length_zcf_le

/-- info: 'STACS2027.Runtimes.ZeroCost.posOk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.posOk

/-- info: 'STACS2027.Runtimes.ZeroCost.incident_edge' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.incident_edge

/-- info: 'STACS2027.Runtimes.ZeroCost.all_congr_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.all_congr_mem

/-- info: 'STACS2027.Runtimes.ZeroCost.omittedPosition_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.omittedPosition_eq

/-- info: 'STACS2027.Runtimes.ZeroCost.find?_range_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.find?_range_succ

/-- info: 'STACS2027.Runtimes.ZeroCost.all_range_succ' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.all_range_succ

/-- info: 'STACS2027.Runtimes.ZeroCost.zipWith_recover' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.zipWith_recover

/-- info: 'STACS2027.Runtimes.ZeroCost.GG' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.GG

/-- info: 'STACS2027.Runtimes.ZeroCost.GMem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.GMem

/-- info: 'STACS2027.Runtimes.ZeroCost.GState' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.GState

/-- info: 'STACS2027.Runtimes.ZeroCost.codes_append_clause' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.codes_append_clause

/-- info: 'STACS2027.Runtimes.ZeroCost.codes_append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.codes_append

/-- info: 'STACS2027.Runtimes.ZeroCost.code_pos' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.code_pos

/-- info: 'STACS2027.Runtimes.ZeroCost.code_neg' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.code_neg

/-- info: 'STACS2027.Runtimes.ZeroCost.GMem.push2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.GMem.push2

/-- info: 'STACS2027.Runtimes.ZeroCost.GMem.seen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.GMem.seen

/-- info: 'STACS2027.Runtimes.ZeroCost.WG' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.WG

/-- info: 'STACS2027.Runtimes.ZeroCost.GG.regIndep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.GG.regIndep

/-- info: 'STACS2027.Runtimes.ZeroCost.GState.emit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.GState.emit

/-- info: 'STACS2027.Runtimes.ZeroCost.GState.room' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.GState.room

/-- info: 'STACS2027.Runtimes.ZeroCost.pcI' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.pcI

/-- info: 'STACS2027.Runtimes.ZeroCost.pcA' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.pcA

/-- info: 'STACS2027.Runtimes.ZeroCost.pcB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.pcB

/-- info: 'STACS2027.Runtimes.ZeroCost.pcB_succ' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.pcB_succ

/-- info: 'STACS2027.Runtimes.ZeroCost.pcA_succ' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.pcA_succ

/-- info: 'STACS2027.Runtimes.ZeroCost.pcI_succ' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.pcI_succ

/-- info: 'STACS2027.Runtimes.ZeroCost.pcI_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.pcI_full

/-- info: 'STACS2027.Runtimes.ZeroCost.length_codes_pcB_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.length_codes_pcB_le

/-- info: 'STACS2027.Runtimes.ZeroCost.length_codes_pcA_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.length_codes_pcA_le

/-- info: 'STACS2027.Runtimes.ZeroCost.length_codes_pcI_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.length_codes_pcI_le

/-- info: 'STACS2027.Runtimes.ZeroCost.PcInv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.PcInv

/-- info: 'STACS2027.Runtimes.ZeroCost.pcEmit_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.pcEmit_run

/-- info: 'STACS2027.Runtimes.ZeroCost.pcCl_pos' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.pcCl_pos

/-- info: 'STACS2027.Runtimes.ZeroCost.pcCl_neg' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.pcCl_neg

/-- info: 'STACS2027.Runtimes.ZeroCost.PcInv.indep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.PcInv.indep

/-- info: 'STACS2027.Runtimes.ZeroCost.pcEmit_addrOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.pcEmit_addrOK

/-- info: 'STACS2027.Runtimes.ZeroCost.pcBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.pcBody_spec

/-- info: 'STACS2027.Runtimes.ZeroCost.MInv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.MInv

/-- info: 'STACS2027.Runtimes.ZeroCost.OInv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.OInv

/-- info: 'STACS2027.Runtimes.ZeroCost.pcRowA_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.pcRowA_spec

/-- info: 'STACS2027.Runtimes.ZeroCost.pcRow_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.pcRow_spec

/-- info: 'STACS2027.Runtimes.ZeroCost.PcPost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.PcPost

/-- info: 'STACS2027.Runtimes.ZeroCost.stepPc_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.stepPc_spec

/-- info: 'STACS2027.Runtimes.ZeroCost.occPre' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.occPre

/-- info: 'STACS2027.Runtimes.ZeroCost.occPre_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.occPre_succ

/-- info: 'STACS2027.Runtimes.ZeroCost.length_codes_occPre_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.length_codes_occPre_le

/-- info: 'STACS2027.Runtimes.ZeroCost.ORegs' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.ORegs

/-- info: 'STACS2027.Runtimes.ZeroCost.OSt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.OSt

/-- info: 'STACS2027.Runtimes.ZeroCost.oSt_indep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.oSt_indep

/-- info: 'STACS2027.Runtimes.ZeroCost.emit_regs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.emit_regs

/-- info: 'STACS2027.Runtimes.ZeroCost.frame_of_wregs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.frame_of_wregs

/-- info: 'STACS2027.Runtimes.ZeroCost.emit1_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.emit1_spec

/-- info: 'STACS2027.Runtimes.ZeroCost.emit2_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.emit2_spec

/-- info: 'STACS2027.Runtimes.ZeroCost.emit3_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.emit3_spec

/-- info: 'STACS2027.Runtimes.ZeroCost.HT.pre_fact' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.HT.pre_fact

/-- info: 'STACS2027.Runtimes.ZeroCost.occEmit_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.occEmit_spec

/-- info: 'STACS2027.Runtimes.ZeroCost.OccInv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.OccInv

/-- info: 'STACS2027.Runtimes.ZeroCost.occRead_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.occRead_run

/-- info: 'STACS2027.Runtimes.ZeroCost.occRead_addrOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.occRead_addrOK

/-- info: 'STACS2027.Runtimes.ZeroCost.occBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.occBody_spec

/-- info: 'STACS2027.Runtimes.ZeroCost.stepOcc_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.stepOcc_spec

/-- info: 'STACS2027.Runtimes.ZeroCost.GA' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.GA

/-- info: 'STACS2027.Runtimes.ZeroCost.InitPost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.InitPost

/-- info: 'STACS2027.Runtimes.ZeroCost.input_facts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.input_facts

/-- info: 'STACS2027.Runtimes.ZeroCost.initRead_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.initRead_spec

/-- info: 'STACS2027.Runtimes.ZeroCost.stepInit_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.stepInit_spec

/-- info: 'STACS2027.Runtimes.ZeroCost.MaxInv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.MaxInv

/-- info: 'STACS2027.Runtimes.ZeroCost.maxBody_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.maxBody_spec

/-- info: 'STACS2027.Runtimes.ZeroCost.stepMax_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.stepMax_spec

/-- info: 'STACS2027.Runtimes.ZeroCost.DictInv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.DictInv

/-- info: 'STACS2027.Runtimes.ZeroCost.dictInit_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.dictInit_spec

/-- info: 'STACS2027.Runtimes.ZeroCost.dictOf_vprefix_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.dictOf_vprefix_succ

/-- info: 'STACS2027.Runtimes.ZeroCost.dictBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.dictBody_spec

/-- info: 'STACS2027.Runtimes.ZeroCost.DictPost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.DictPost

/-- info: 'STACS2027.Runtimes.ZeroCost.stepDict_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.stepDict_spec

/-- info: 'STACS2027.Runtimes.ZeroCost.zeroCostInput' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.zeroCostInput

/-- info: 'STACS2027.Runtimes.ZeroCost.gK' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.gK

/-- info: 'STACS2027.Runtimes.ZeroCost.gT' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.gT

/-- info: 'STACS2027.Runtimes.ZeroCost.gV' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.gV

/-- info: 'STACS2027.Runtimes.ZeroCost.gKT' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.gKT

/-- info: 'STACS2027.Runtimes.ZeroCost.gNV' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.gNV

/-- info: 'STACS2027.Runtimes.ZeroCost.gMX' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.gMX

/-- info: 'STACS2027.Runtimes.ZeroCost.gD' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.gD

/-- info: 'STACS2027.Runtimes.ZeroCost.gN' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.gN

/-- info: 'STACS2027.Runtimes.ZeroCost.gPU' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.gPU

/-- info: 'STACS2027.Runtimes.ZeroCost.gPV' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.gPV

/-- info: 'STACS2027.Runtimes.ZeroCost.gEID' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.gEID

/-- info: 'STACS2027.Runtimes.ZeroCost.gCNT' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.gCNT

/-- info: 'STACS2027.Runtimes.ZeroCost.gNE' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.gNE

/-- info: 'STACS2027.Runtimes.ZeroCost.gOFF' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.gOFF

/-- info: 'STACS2027.Runtimes.ZeroCost.gSEEN' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.gSEEN

/-- info: 'STACS2027.Runtimes.ZeroCost.gCL' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.gCL

/-- info: 'STACS2027.Runtimes.ZeroCost.gNC' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.gNC

/-- info: 'STACS2027.Runtimes.ZeroCost.sQ' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.sQ

/-- info: 'STACS2027.Runtimes.ZeroCost.sI' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.sI

/-- info: 'STACS2027.Runtimes.ZeroCost.sJ' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.sJ

/-- info: 'STACS2027.Runtimes.ZeroCost.sX' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.sX

/-- info: 'STACS2027.Runtimes.ZeroCost.sY' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.sY

/-- info: 'STACS2027.Runtimes.ZeroCost.sP' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.sP

/-- info: 'STACS2027.Runtimes.ZeroCost.sU' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.sU

/-- info: 'STACS2027.Runtimes.ZeroCost.sV' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.sV

/-- info: 'STACS2027.Runtimes.ZeroCost.sW' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.sW

/-- info: 'STACS2027.Runtimes.ZeroCost.sZ' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.sZ

/-- info: 'STACS2027.Runtimes.ZeroCost.sC' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.sC

/-- info: 'STACS2027.Runtimes.ZeroCost.sAcc' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.sAcc

/-- info: 'STACS2027.Runtimes.ZeroCost.sBase' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.sBase

/-- info: 'STACS2027.Runtimes.ZeroCost.sE' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.sE

/-- info: 'STACS2027.Runtimes.ZeroCost.sR' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.sR

/-- info: 'STACS2027.Runtimes.ZeroCost.sO' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.sO

/-- info: 'STACS2027.Runtimes.ZeroCost.sS' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.sS

/-- info: 'STACS2027.Runtimes.ZeroCost.sA' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.sA

/-- info: 'STACS2027.Runtimes.ZeroCost.sB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.sB

/-- info: 'STACS2027.Runtimes.ZeroCost.sF' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.sF

/-- info: 'STACS2027.Runtimes.ZeroCost.sRes' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.sRes

/-- info: 'STACS2027.Runtimes.ZeroCost.sOk' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.sOk

/-- info: 'STACS2027.Runtimes.ZeroCost.bV' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.bV

/-- info: 'STACS2027.Runtimes.ZeroCost.bD' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.bD

/-- info: 'STACS2027.Runtimes.ZeroCost.bPU' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.bPU

/-- info: 'STACS2027.Runtimes.ZeroCost.bPV' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.bPV

/-- info: 'STACS2027.Runtimes.ZeroCost.bPI' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.bPI

/-- info: 'STACS2027.Runtimes.ZeroCost.bEID' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.bEID

/-- info: 'STACS2027.Runtimes.ZeroCost.bCNT' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.bCNT

/-- info: 'STACS2027.Runtimes.ZeroCost.bOFF' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.bOFF

/-- info: 'STACS2027.Runtimes.ZeroCost.bSEEN' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.bSEEN

/-- info: 'STACS2027.Runtimes.ZeroCost.bCL' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.bCL

/-- info: 'STACS2027.Runtimes.ZeroCost.bEID_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.bEID_eq

/-- info: 'STACS2027.Runtimes.ZeroCost.layout_eqs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.layout_eqs

/-- info: 'STACS2027.Runtimes.ZeroCost.idsEnd_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.idsEnd_eq

/-- info: 'STACS2027.Runtimes.ZeroCost.length_zeroCostInput' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.length_zeroCostInput

/-- info: 'STACS2027.Runtimes.ZeroCost.nE_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.nE_le

/-- info: 'STACS2027.Runtimes.ZeroCost.fits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.fits

/-- info: 'STACS2027.Runtimes.ZeroCost.push' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.push

/-- info: 'STACS2027.Runtimes.ZeroCost.run_push' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.run_push

/-- info: 'STACS2027.Runtimes.ZeroCost.ZeroFrom.upd_at' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.ZeroFrom.upd_at

/-- info: 'STACS2027.Runtimes.ZeroCost.HT.assoc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.HT.assoc

/-- info: 'STACS2027.Runtimes.ZeroCost.initRead' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.initRead

/-- info: 'STACS2027.Runtimes.ZeroCost.initFin' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.initFin

/-- info: 'STACS2027.Runtimes.ZeroCost.stepInit' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.stepInit

/-- info: 'STACS2027.Runtimes.ZeroCost.maxBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.maxBody

/-- info: 'STACS2027.Runtimes.ZeroCost.stepMax' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.stepMax

/-- info: 'STACS2027.Runtimes.ZeroCost.dictInit' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.dictInit

/-- info: 'STACS2027.Runtimes.ZeroCost.dictBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.dictBody

/-- info: 'STACS2027.Runtimes.ZeroCost.stepDict' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.stepDict

/-- info: 'STACS2027.Runtimes.ZeroCost.nextPos' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.nextPos

/-- info: 'STACS2027.Runtimes.ZeroCost.edgeA' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.edgeA

/-- info: 'STACS2027.Runtimes.ZeroCost.minmax' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.minmax

/-- info: 'STACS2027.Runtimes.ZeroCost.edgeIds' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.edgeIds

/-- info: 'STACS2027.Runtimes.ZeroCost.edgeRead' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.edgeRead

/-- info: 'STACS2027.Runtimes.ZeroCost.edgePut' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.edgePut

/-- info: 'STACS2027.Runtimes.ZeroCost.edgeBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.edgeBody

/-- info: 'STACS2027.Runtimes.ZeroCost.edgeRow' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.edgeRow

/-- info: 'STACS2027.Runtimes.ZeroCost.idsArgs' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.idsArgs

/-- info: 'STACS2027.Runtimes.ZeroCost.idsBack' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.idsBack

/-- info: 'STACS2027.Runtimes.ZeroCost.stepEdges' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.stepEdges

/-- info: 'STACS2027.Runtimes.ZeroCost.offBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.offBody

/-- info: 'STACS2027.Runtimes.ZeroCost.stepOff' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.stepOff

/-- info: 'STACS2027.Runtimes.ZeroCost.pcEmit' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.pcEmit

/-- info: 'STACS2027.Runtimes.ZeroCost.pcBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.pcBody

/-- info: 'STACS2027.Runtimes.ZeroCost.pcRowA' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.pcRowA

/-- info: 'STACS2027.Runtimes.ZeroCost.pcRow' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.pcRow

/-- info: 'STACS2027.Runtimes.ZeroCost.stepPc' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.stepPc

/-- info: 'STACS2027.Runtimes.ZeroCost.occRead' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.occRead

/-- info: 'STACS2027.Runtimes.ZeroCost.emit1' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.emit1

/-- info: 'STACS2027.Runtimes.ZeroCost.emit2' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.emit2

/-- info: 'STACS2027.Runtimes.ZeroCost.emit3' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.emit3

/-- info: 'STACS2027.Runtimes.ZeroCost.occEmit' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.occEmit

/-- info: 'STACS2027.Runtimes.ZeroCost.occBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.occBody

/-- info: 'STACS2027.Runtimes.ZeroCost.stepOcc' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.stepOcc

/-- info: 'STACS2027.Runtimes.ZeroCost.callSat' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.callSat

/-- info: 'STACS2027.Runtimes.ZeroCost.recCheck' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.recCheck

/-- info: 'STACS2027.Runtimes.ZeroCost.recBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.recBody

/-- info: 'STACS2027.Runtimes.ZeroCost.recUpd' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.recUpd

/-- info: 'STACS2027.Runtimes.ZeroCost.recA' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.recA

/-- info: 'STACS2027.Runtimes.ZeroCost.recRow' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.recRow

/-- info: 'STACS2027.Runtimes.ZeroCost.stepRec' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.stepRec

/-- info: 'STACS2027.Runtimes.ZeroCost.zeroCostProg' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.zeroCostProg

/-- info: 'STACS2027.Runtimes.ZeroCost.recPos' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.recPos

/-- info: 'STACS2027.Runtimes.ZeroCost.memAsg' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.memAsg

/-- info: 'STACS2027.Runtimes.ZeroCost.RG' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.RG

/-- info: 'STACS2027.Runtimes.ZeroCost.testTerm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.testTerm

/-- info: 'STACS2027.Runtimes.ZeroCost.RJ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.RJ

/-- info: 'STACS2027.Runtimes.ZeroCost.recCheck_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.recCheck_run

/-- info: 'STACS2027.Runtimes.ZeroCost.recCheck_addrOK' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.recCheck_addrOK

/-- info: 'STACS2027.Runtimes.ZeroCost.recBody_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.recBody_spec

/-- info: 'STACS2027.Runtimes.ZeroCost.RA' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.RA

/-- info: 'STACS2027.Runtimes.ZeroCost.recUpd_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.recUpd_spec

/-- info: 'STACS2027.Runtimes.ZeroCost.recA_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.recA_spec

/-- info: 'STACS2027.Runtimes.ZeroCost.RI' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.RI

/-- info: 'STACS2027.Runtimes.ZeroCost.recRow_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.recRow_spec

/-- info: 'STACS2027.Runtimes.ZeroCost.stepRec_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.stepRec_spec

/-- info: 'STACS2027.Runtimes.ZeroCost.length_flatten_uniform' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.length_flatten_uniform

/-- info: 'STACS2027.Runtimes.ZeroCost.getD_flatten_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.getD_flatten_uniform

/-- info: 'STACS2027.Runtimes.ZeroCost.take_flatten_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.take_flatten_uniform

/-- info: 'STACS2027.Runtimes.ZeroCost.verts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.verts

/-- info: 'STACS2027.Runtimes.ZeroCost.occs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.occs

/-- info: 'STACS2027.Runtimes.ZeroCost.cycles_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.cycles_length

/-- info: 'STACS2027.Runtimes.ZeroCost.length_verts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.length_verts

/-- info: 'STACS2027.Runtimes.ZeroCost.length_occs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.length_occs

/-- info: 'STACS2027.Runtimes.ZeroCost.verts_getD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.verts_getD

/-- info: 'STACS2027.Runtimes.ZeroCost.occs_getD_cycleEdgeAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.occs_getD_cycleEdgeAt

/-- info: 'STACS2027.Runtimes.ZeroCost.occs_getD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.occs_getD

/-- info: 'STACS2027.Runtimes.ZeroCost.pathEdges_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.pathEdges_mem

/-- info: 'STACS2027.Runtimes.ZeroCost.occs_mem_verts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.occs_mem_verts

/-- info: 'STACS2027.Runtimes.ZeroCost.occs_getD_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.occs_getD_mem

/-- info: 'STACS2027.Runtimes.ZeroCost.verts_getD_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.verts_getD_mem

/-- info: 'STACS2027.Runtimes.ZeroCost.occ_decomp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.occ_decomp

/-- info: 'STACS2027.Runtimes.ZeroCost.maxV' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.maxV

/-- info: 'STACS2027.Runtimes.ZeroCost.vprefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.vprefix

/-- info: 'STACS2027.Runtimes.ZeroCost.vl' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.vl

/-- info: 'STACS2027.Runtimes.ZeroCost.nV' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.nV

/-- info: 'STACS2027.Runtimes.ZeroCost.idv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.idv

/-- info: 'STACS2027.Runtimes.ZeroCost.le_maxV' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.le_maxV

/-- info: 'STACS2027.Runtimes.ZeroCost.vprefix_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.vprefix_succ

/-- info: 'STACS2027.Runtimes.ZeroCost.vprefix_full' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.vprefix_full

/-- info: 'STACS2027.Runtimes.ZeroCost.length_vprefix_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.length_vprefix_le

/-- info: 'STACS2027.Runtimes.ZeroCost.nV_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.nV_le

/-- info: 'STACS2027.Runtimes.ZeroCost.mem_vprefix_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.mem_vprefix_le

/-- info: 'STACS2027.Runtimes.ZeroCost.mem_vl' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.mem_vl

/-- info: 'STACS2027.Runtimes.ZeroCost.idv_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.idv_lt

/-- info: 'STACS2027.Runtimes.ZeroCost.dictOf_vl' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.dictOf_vl

/-- info: 'STACS2027.Runtimes.ZeroCost.idv_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.idv_inj

/-- info: 'STACS2027.Runtimes.ZeroCost.eprefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.eprefix

/-- info: 'STACS2027.Runtimes.ZeroCost.eidOf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.eidOf

/-- info: 'STACS2027.Runtimes.ZeroCost.cntF' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.cntF

/-- info: 'STACS2027.Runtimes.ZeroCost.rank' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.rank

/-- info: 'STACS2027.Runtimes.ZeroCost.offF' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.offF

/-- info: 'STACS2027.Runtimes.ZeroCost.edgesOnCycles_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.edgesOnCycles_eq

/-- info: 'STACS2027.Runtimes.ZeroCost.eprefix_full' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.eprefix_full

/-- info: 'STACS2027.Runtimes.ZeroCost.eprefix_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.eprefix_succ

/-- info: 'STACS2027.Runtimes.ZeroCost.mem_eprefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.mem_eprefix

/-- info: 'STACS2027.Runtimes.ZeroCost.length_eprefix_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.length_eprefix_le

/-- info: 'STACS2027.Runtimes.ZeroCost.eprefix_prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.eprefix_prefix

/-- info: 'STACS2027.Runtimes.ZeroCost.idxOf_edgesOnCycles' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.idxOf_edgesOnCycles

/-- info: 'STACS2027.Runtimes.ZeroCost.mem_edgesOnCycles_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.mem_edgesOnCycles_iff

/-- info: 'STACS2027.Runtimes.ZeroCost.occs_getD_mem_eoc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.occs_getD_mem_eoc

/-- info: 'STACS2027.Runtimes.ZeroCost.eidOf_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.eidOf_lt

/-- info: 'STACS2027.Runtimes.ZeroCost.eidOf_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.eidOf_eq_iff

/-- info: 'STACS2027.Runtimes.ZeroCost.cntF_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.cntF_zero

/-- info: 'STACS2027.Runtimes.ZeroCost.cntF_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.cntF_succ

/-- info: 'STACS2027.Runtimes.ZeroCost.cntF_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.cntF_le

/-- info: 'STACS2027.Runtimes.ZeroCost.cntF_eidOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.cntF_eidOf

/-- info: 'STACS2027.Runtimes.ZeroCost.sum_indicator' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.sum_indicator

/-- info: 'STACS2027.Runtimes.ZeroCost.count_occs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.count_occs

/-- info: 'STACS2027.Runtimes.ZeroCost.cntF_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.cntF_final

/-- info: 'STACS2027.Runtimes.ZeroCost.cntF_final_pos' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.cntF_final_pos

/-- info: 'STACS2027.Runtimes.ZeroCost.filter_range_split' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.filter_range_split

/-- info: 'STACS2027.Runtimes.ZeroCost.cyclesThrough_getD_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.cyclesThrough_getD_count

/-- info: 'STACS2027.Runtimes.ZeroCost.rank_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.rank_spec

/-- info: 'STACS2027.Runtimes.ZeroCost.offF_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.offF_succ

/-- info: 'STACS2027.Runtimes.ZeroCost.offF_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.offF_zero

/-- info: 'STACS2027.Runtimes.ZeroCost.takeWhile_ne_eq_take' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.takeWhile_ne_eq_take

/-- info: 'STACS2027.Runtimes.ZeroCost.offF_eidOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.offF_eidOf

/-- info: 'STACS2027.Runtimes.ZeroCost.eraseDups_map_injOn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.eraseDups_map_injOn

/-- info: 'STACS2027.Runtimes.ZeroCost.idxOf_map_injOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.idxOf_map_injOn

/-- info: 'STACS2027.Runtimes.ZeroCost.eids_map_injOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.eids_map_injOn

/-- info: 'STACS2027.Runtimes.ZeroCost.idPr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.idPr

/-- info: 'STACS2027.Runtimes.ZeroCost.prs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.prs

/-- info: 'STACS2027.Runtimes.ZeroCost.length_prs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.length_prs

/-- info: 'STACS2027.Runtimes.ZeroCost.prs_below' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.prs_below

/-- info: 'STACS2027.Runtimes.ZeroCost.idPr_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.idPr_inj

/-- info: 'STACS2027.Runtimes.ZeroCost.eids_occs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.eids_occs

/-- info: 'STACS2027.Runtimes.ZeroCost.eids_prs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.eids_prs

/-- info: 'STACS2027.Runtimes.ZeroCost.count_eids_prs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.count_eids_prs

/-- info: 'STACS2027.Runtimes.ZeroCost.length_eraseDups_prs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.length_eraseDups_prs

/-- info: 'STACS2027.Runtimes.ZeroCost.map_fst_prs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.map_fst_prs

/-- info: 'STACS2027.Runtimes.ZeroCost.map_snd_prs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.map_snd_prs

/-- info: 'STACS2027.Runtimes.ZeroCost.occs_mem_graph' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.occs_mem_graph

/-- info: 'STACS2027.Runtimes.ZeroCost.foldl_max_le' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.foldl_max_le

/-- info: 'STACS2027.Runtimes.ZeroCost.verts_le_maxLab' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.verts_le_maxLab

/-- info: 'STACS2027.Runtimes.ZeroCost.maxV_lt_labelBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ZeroCost.maxV_lt_labelBound

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

/-- info: 'STACS2027.Runtimes.BoundedCost.actualCompilerRAM_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.actualCompilerRAM_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.compilerExecutionCost_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.compilerExecutionCost_le

/-- info: 'STACS2027.Runtimes.BoundedCost.compilerFptTime' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.compilerFptTime

/-- info: 'STACS2027.Runtimes.BoundedCost.compilerFptTime_bound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.compilerFptTime_bound

/-- info: 'STACS2027.Runtimes.BoundedCost.actualCompilerRAM_fpt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.actualCompilerRAM_fpt

/-- info: 'STACS2027.Runtimes.BoundedCost.almostTwoSatFptSolverExists_of_citedFlow' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.almostTwoSatFptSolverExists_of_citedFlow

/-- info: 'STACS2027.Runtimes.BoundedCost.compressionCompilerCost' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.compressionCompilerCost

/-- info: 'STACS2027.Runtimes.BoundedCost.compressionFinish_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.compressionFinish_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.actualCompressionRAM_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.actualCompressionRAM_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.boundedCost_ram_fpt_from_citedFlow' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.boundedCost_ram_fpt_from_citedFlow

/-- info: 'STACS2027.Runtimes.BoundedCost.boundedCost_ram_all_from_citedFlow' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.boundedCost_ram_all_from_citedFlow

/-- info: 'STACS2027.Runtimes.BoundedCost.actualInnerCost' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.actualInnerCost

/-- info: 'STACS2027.Runtimes.BoundedCost.actualInnerRAM_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.actualInnerRAM_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.outerSearchCost' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.outerSearchCost

/-- info: 'STACS2027.Runtimes.BoundedCost.actualOuterRAM_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.actualOuterRAM_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.outerCompleteCost' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.outerCompleteCost

/-- info: 'STACS2027.Runtimes.BoundedCost.completeOuterRAM_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.completeOuterRAM_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.searchRowsOf_literal_bounds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.searchRowsOf_literal_bounds

/-- info: 'STACS2027.Runtimes.BoundedCost.actualPathNode_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.actualPathNode_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.FramedPathRep' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.FramedPathRep

/-- info: 'STACS2027.Runtimes.BoundedCost.framedPathRep_indep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.framedPathRep_indep

/-- info: 'STACS2027.Runtimes.BoundedCost.actualPathRAM_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.actualPathRAM_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.unsatisfiedCount' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.unsatisfiedCount

/-- info: 'STACS2027.Runtimes.BoundedCost.unsatisfiedCount_nil' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.unsatisfiedCount_nil

/-- info: 'STACS2027.Runtimes.BoundedCost.unsatisfiedCount_cons' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.unsatisfiedCount_cons

/-- info: 'STACS2027.Runtimes.BoundedCost.unsatisfiedCount_append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.unsatisfiedCount_append

/-- info: 'STACS2027.Runtimes.BoundedCost.almostSatisfiable_iff_unsatisfiedCount' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.almostSatisfiable_iff_unsatisfiedCount

/-- info: 'STACS2027.Runtimes.BoundedCost.AnnotatedAlmostSatisfiable' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.AnnotatedAlmostSatisfiable

/-- info: 'STACS2027.Runtimes.BoundedCost.forcedUnits' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.forcedUnits

/-- info: 'STACS2027.Runtimes.BoundedCost.evalCNF_forcedUnits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.evalCNF_forcedUnits

/-- info: 'STACS2027.Runtimes.BoundedCost.forcedUnits_twoCNF' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.forcedUnits_twoCNF

/-- info: 'STACS2027.Runtimes.BoundedCost.annotated_zero_iff_satisfiable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.annotated_zero_iff_satisfiable

/-- info: 'STACS2027.Runtimes.BoundedCost.CompressionBranch' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CompressionBranch

/-- info: 'STACS2027.Runtimes.BoundedCost.compressionBranches' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.compressionBranches

/-- info: 'STACS2027.Runtimes.BoundedCost.compressionBranches_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.compressionBranches_length

/-- info: 'STACS2027.Runtimes.BoundedCost.compressionBranches_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.compressionBranches_sound

/-- info: 'STACS2027.Runtimes.BoundedCost.compressionBranches_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.compressionBranches_complete

/-- info: 'STACS2027.Runtimes.BoundedCost.almostSatisfiable_compression' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.almostSatisfiable_compression

/-- info: 'STACS2027.Runtimes.BoundedCost.nodeBudget' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.nodeBudget

/-- info: 'STACS2027.Runtimes.BoundedCost.nodeForcedBase' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.nodeForcedBase

/-- info: 'STACS2027.Runtimes.BoundedCost.nodeSuccess' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.nodeSuccess

/-- info: 'STACS2027.Runtimes.BoundedCost.nodeLive' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.nodeLive

/-- info: 'STACS2027.Runtimes.BoundedCost.nodeChoice' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.nodeChoice

/-- info: 'STACS2027.Runtimes.BoundedCost.nodeIndex' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.nodeIndex

/-- info: 'STACS2027.Runtimes.BoundedCost.nodeValue' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.nodeValue

/-- info: 'STACS2027.Runtimes.BoundedCost.nodeChoiceTail' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.nodeChoiceTail

/-- info: 'STACS2027.Runtimes.BoundedCost.NodeAction' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.NodeAction

/-- info: 'STACS2027.Runtimes.BoundedCost.nodeAction' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.nodeAction

/-- info: 'STACS2027.Runtimes.BoundedCost.nodeActionMemory' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.nodeActionMemory

/-- info: 'STACS2027.Runtimes.BoundedCost.nodeActionBudget' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.nodeActionBudget

/-- info: 'STACS2027.Runtimes.BoundedCost.nodeActionLive' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.nodeActionLive

/-- info: 'STACS2027.Runtimes.BoundedCost.nodeActionSuccess' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.nodeActionSuccess

/-- info: 'STACS2027.Runtimes.BoundedCost.nodeAccept' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.nodeAccept

/-- info: 'STACS2027.Runtimes.BoundedCost.nodePrune' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.nodePrune

/-- info: 'STACS2027.Runtimes.BoundedCost.nodeDelete' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.nodeDelete

/-- info: 'STACS2027.Runtimes.BoundedCost.nodeForce' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.nodeForce

/-- info: 'STACS2027.Runtimes.BoundedCost.nodeBranch' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.nodeBranch

/-- info: 'STACS2027.Runtimes.BoundedCost.annotatedNodeUpdate' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.annotatedNodeUpdate

/-- info: 'STACS2027.Runtimes.BoundedCost.NodeGlobals' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.NodeGlobals

/-- info: 'STACS2027.Runtimes.BoundedCost.NodeUpdated' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.NodeUpdated

/-- info: 'STACS2027.Runtimes.BoundedCost.annotatedNodeUpdate_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.annotatedNodeUpdate_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.BoundedCostAnswer' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.BoundedCostAnswer

/-- info: 'STACS2027.Runtimes.BoundedCost.permitted_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.permitted_two

/-- info: 'STACS2027.Runtimes.BoundedCost.answer_of_table' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.answer_of_table

/-- info: 'STACS2027.Runtimes.BoundedCost.stepRec_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.stepRec_zero

/-- info: 'STACS2027.Runtimes.BoundedCost.ArrayBlocks.sourceBase' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.ArrayBlocks.sourceBase

/-- info: 'STACS2027.Runtimes.BoundedCost.ArrayBlocks.targetBase' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.ArrayBlocks.targetBase

/-- info: 'STACS2027.Runtimes.BoundedCost.ArrayBlocks.arrayLength' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.ArrayBlocks.arrayLength

/-- info: 'STACS2027.Runtimes.BoundedCost.ArrayBlocks.index' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.ArrayBlocks.index

/-- info: 'STACS2027.Runtimes.BoundedCost.ArrayBlocks.value' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.ArrayBlocks.value

/-- info: 'STACS2027.Runtimes.BoundedCost.ArrayBlocks.fillValue' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.ArrayBlocks.fillValue

/-- info: 'STACS2027.Runtimes.BoundedCost.ArrayBlocks.prefixMemory' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.ArrayBlocks.prefixMemory

/-- info: 'STACS2027.Runtimes.BoundedCost.ArrayBlocks.prefixMemory_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.ArrayBlocks.prefixMemory_zero

/-- info: 'STACS2027.Runtimes.BoundedCost.ArrayBlocks.prefixMemory_outside' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.ArrayBlocks.prefixMemory_outside

/-- info: 'STACS2027.Runtimes.BoundedCost.ArrayBlocks.prefixMemory_succ' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.ArrayBlocks.prefixMemory_succ

/-- info: 'STACS2027.Runtimes.BoundedCost.ArrayBlocks.prefixMemory_array' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.ArrayBlocks.prefixMemory_array

/-- info: 'STACS2027.Runtimes.BoundedCost.ArrayBlocks.copyBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.ArrayBlocks.copyBody

/-- info: 'STACS2027.Runtimes.BoundedCost.ArrayBlocks.copyArray' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.ArrayBlocks.copyArray

/-- info: 'STACS2027.Runtimes.BoundedCost.ArrayBlocks.fillBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.ArrayBlocks.fillBody

/-- info: 'STACS2027.Runtimes.BoundedCost.ArrayBlocks.fillArray' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.ArrayBlocks.fillArray

/-- info: 'STACS2027.Runtimes.BoundedCost.ArrayBlocks.CopyGlobals' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.ArrayBlocks.CopyGlobals

/-- info: 'STACS2027.Runtimes.BoundedCost.ArrayBlocks.CopyInv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.ArrayBlocks.CopyInv

/-- info: 'STACS2027.Runtimes.BoundedCost.ArrayBlocks.copyBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.ArrayBlocks.copyBody_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.ArrayBlocks.copyArray_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.ArrayBlocks.copyArray_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.ArrayBlocks.FillGlobals' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.ArrayBlocks.FillGlobals

/-- info: 'STACS2027.Runtimes.BoundedCost.ArrayBlocks.FillInv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.ArrayBlocks.FillInv

/-- info: 'STACS2027.Runtimes.BoundedCost.ArrayBlocks.fillBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.ArrayBlocks.fillBody_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.ArrayBlocks.fillArray_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.ArrayBlocks.fillArray_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.innerRegisterSwap' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.innerRegisterSwap

/-- info: 'STACS2027.Runtimes.BoundedCost.innerRegisterSwap_involutive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.innerRegisterSwap_involutive

/-- info: 'STACS2027.Runtimes.BoundedCost.innerRegisterSwap_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.innerRegisterSwap_injective

/-- info: 'STACS2027.Runtimes.BoundedCost.innerCallerRegister' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.innerCallerRegister

/-- info: 'STACS2027.Runtimes.BoundedCost.innerCallerRegister_injective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.innerCallerRegister_injective

/-- info: 'STACS2027.Runtimes.BoundedCost.innerCallerRegister_outside' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.innerCallerRegister_outside

/-- info: 'STACS2027.Runtimes.BoundedCost.innerCallerRegister_base' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.innerCallerRegister_base

/-- info: 'STACS2027.Runtimes.BoundedCost.innerCallerRegister_depth' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.innerCallerRegister_depth

/-- info: 'STACS2027.Runtimes.BoundedCost.innerCallerRegister_index' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.innerCallerRegister_index

/-- info: 'STACS2027.Runtimes.BoundedCost.innerCallerRegister_count' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.innerCallerRegister_count

/-- info: 'STACS2027.Runtimes.BoundedCost.innerCallerRegister_radix' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.innerCallerRegister_radix

/-- info: 'STACS2027.Runtimes.BoundedCost.innerCallerRegister_ne_temporary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.innerCallerRegister_ne_temporary

/-- info: 'STACS2027.Runtimes.BoundedCost.Requires' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Requires

/-- info: 'STACS2027.Runtimes.BoundedCost.IsLeastCut' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.IsLeastCut

/-- info: 'STACS2027.Runtimes.BoundedCost.cutCost_le_unsatisfiedCount' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.cutCost_le_unsatisfiedCount

/-- info: 'STACS2027.Runtimes.BoundedCost.leastCut_lower_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.leastCut_lower_bound

/-- info: 'STACS2027.Runtimes.BoundedCost.leastCut_requirement_increases' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.leastCut_requirement_increases

/-- info: 'STACS2027.Runtimes.BoundedCost.cutClause_eq_zero_of_all' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.cutClause_eq_zero_of_all

/-- info: 'STACS2027.Runtimes.BoundedCost.cutCost_cons_conflict' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.cutCost_cons_conflict

/-- info: 'STACS2027.Runtimes.BoundedCost.leastCut_remove_conflict' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.leastCut_remove_conflict

/-- info: 'STACS2027.Runtimes.BoundedCost.annotated_cons_branches' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.annotated_cons_branches

/-- info: 'STACS2027.Runtimes.BoundedCost.leastCut_conflict_branches' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.leastCut_conflict_branches

/-- info: 'STACS2027.Runtimes.BoundedCost.renameRegisters' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.renameRegisters

/-- info: 'STACS2027.Runtimes.BoundedCost.registerView' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.registerView

/-- info: 'STACS2027.Runtimes.BoundedCost.renameRegisters_wregs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.renameRegisters_wregs

/-- info: 'STACS2027.Runtimes.BoundedCost.renameRegisters_stores' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.renameRegisters_stores

/-- info: 'STACS2027.Runtimes.BoundedCost.renameRegisters_writes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.renameRegisters_writes

/-- info: 'STACS2027.Runtimes.BoundedCost.registerView_setReg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.registerView_setReg

/-- info: 'STACS2027.Runtimes.BoundedCost.registerView_setMem' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.registerView_setMem

/-- info: 'STACS2027.Runtimes.BoundedCost.registerView_emit' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.registerView_emit

/-- info: 'STACS2027.Runtimes.BoundedCost.renameRegisters_exec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.renameRegisters_exec

/-- info: 'STACS2027.Runtimes.BoundedCost.renameRegisters_htb' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.renameRegisters_htb

/-- info: 'STACS2027.Runtimes.BoundedCost.registerView_initial' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.registerView_initial

/-- info: 'STACS2027.Runtimes.BoundedCost.renameRegisters_computesIn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.renameRegisters_computesIn

/-- info: 'STACS2027.Runtimes.BoundedCost.callerRegister' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.callerRegister

/-- info: 'STACS2027.Runtimes.BoundedCost.callerRegister_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.callerRegister_injective

/-- info: 'STACS2027.Runtimes.BoundedCost.onCallerRegisters' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.onCallerRegisters

/-- info: 'STACS2027.Runtimes.BoundedCost.onCallerRegisters_htb' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.onCallerRegisters_htb

/-- info: 'STACS2027.Runtimes.BoundedCost.CandidateDecode.candidateBase' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CandidateDecode.candidateBase

/-- info: 'STACS2027.Runtimes.BoundedCost.CandidateDecode.referenceBase' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CandidateDecode.referenceBase

/-- info: 'STACS2027.Runtimes.BoundedCost.CandidateDecode.variableCount' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CandidateDecode.variableCount

/-- info: 'STACS2027.Runtimes.BoundedCost.CandidateDecode.labelBase' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CandidateDecode.labelBase

/-- info: 'STACS2027.Runtimes.BoundedCost.CandidateDecode.regionBase' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CandidateDecode.regionBase

/-- info: 'STACS2027.Runtimes.BoundedCost.CandidateDecode.index' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CandidateDecode.index

/-- info: 'STACS2027.Runtimes.BoundedCost.CandidateDecode.codeIndex' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CandidateDecode.codeIndex

/-- info: 'STACS2027.Runtimes.BoundedCost.CandidateDecode.node' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CandidateDecode.node

/-- info: 'STACS2027.Runtimes.BoundedCost.CandidateDecode.regionOffset' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CandidateDecode.regionOffset

/-- info: 'STACS2027.Runtimes.BoundedCost.CandidateDecode.regionValue' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CandidateDecode.regionValue

/-- info: 'STACS2027.Runtimes.BoundedCost.CandidateDecode.referenceValue' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CandidateDecode.referenceValue

/-- info: 'STACS2027.Runtimes.BoundedCost.CandidateDecode.positiveValue' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CandidateDecode.positiveValue

/-- info: 'STACS2027.Runtimes.BoundedCost.CandidateDecode.negativeValue' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CandidateDecode.negativeValue

/-- info: 'STACS2027.Runtimes.BoundedCost.CandidateDecode.oddIndex' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CandidateDecode.oddIndex

/-- info: 'STACS2027.Runtimes.BoundedCost.CandidateDecode.one' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CandidateDecode.one

/-- info: 'STACS2027.Runtimes.BoundedCost.CandidateDecode.body' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CandidateDecode.body

/-- info: 'STACS2027.Runtimes.BoundedCost.CandidateDecode.program' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CandidateDecode.program

/-- info: 'STACS2027.Runtimes.BoundedCost.CandidateDecode.decoded' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CandidateDecode.decoded

/-- info: 'STACS2027.Runtimes.BoundedCost.CandidateDecode.decoded_contracted' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CandidateDecode.decoded_contracted

/-- info: 'STACS2027.Runtimes.BoundedCost.CandidateDecode.bit' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CandidateDecode.bit

/-- info: 'STACS2027.Runtimes.BoundedCost.CandidateDecode.prefixMemory' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CandidateDecode.prefixMemory

/-- info: 'STACS2027.Runtimes.BoundedCost.CandidateDecode.prefixMemory_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CandidateDecode.prefixMemory_zero

/-- info: 'STACS2027.Runtimes.BoundedCost.CandidateDecode.prefixMemory_outside' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CandidateDecode.prefixMemory_outside

/-- info: 'STACS2027.Runtimes.BoundedCost.CandidateDecode.prefixMemory_succ' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CandidateDecode.prefixMemory_succ

/-- info: 'STACS2027.Runtimes.BoundedCost.CandidateDecode.Globals' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CandidateDecode.Globals

/-- info: 'STACS2027.Runtimes.BoundedCost.CandidateDecode.Inv' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CandidateDecode.Inv

/-- info: 'STACS2027.Runtimes.BoundedCost.CandidateDecode.Separated' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CandidateDecode.Separated

/-- info: 'STACS2027.Runtimes.BoundedCost.CandidateDecode.body_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CandidateDecode.body_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.CandidateDecode.program_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CandidateDecode.program_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.CandidateDecode.prefixMemory_truth' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CandidateDecode.prefixMemory_truth

/-- info: 'STACS2027.Runtimes.BoundedCost.Certificate.formulaBase' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Certificate.formulaBase

/-- info: 'STACS2027.Runtimes.BoundedCost.Certificate.clauseCount' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Certificate.clauseCount

/-- info: 'STACS2027.Runtimes.BoundedCost.Certificate.candidateBase' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Certificate.candidateBase

/-- info: 'STACS2027.Runtimes.BoundedCost.Certificate.variableCount' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Certificate.variableCount

/-- info: 'STACS2027.Runtimes.BoundedCost.Certificate.index' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Certificate.index

/-- info: 'STACS2027.Runtimes.BoundedCost.Certificate.offset' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Certificate.offset

/-- info: 'STACS2027.Runtimes.BoundedCost.Certificate.firstCode' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Certificate.firstCode

/-- info: 'STACS2027.Runtimes.BoundedCost.Certificate.secondCode' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Certificate.secondCode

/-- info: 'STACS2027.Runtimes.BoundedCost.Certificate.firstTruth' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Certificate.firstTruth

/-- info: 'STACS2027.Runtimes.BoundedCost.Certificate.secondTruth' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Certificate.secondTruth

/-- info: 'STACS2027.Runtimes.BoundedCost.Certificate.value' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Certificate.value

/-- info: 'STACS2027.Runtimes.BoundedCost.Certificate.deletedCount' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Certificate.deletedCount

/-- info: 'STACS2027.Runtimes.BoundedCost.Certificate.variableIndex' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Certificate.variableIndex

/-- info: 'STACS2027.Runtimes.BoundedCost.Certificate.positiveCode' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Certificate.positiveCode

/-- info: 'STACS2027.Runtimes.BoundedCost.Certificate.negativeCode' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Certificate.negativeCode

/-- info: 'STACS2027.Runtimes.BoundedCost.Certificate.literalIndex' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Certificate.literalIndex

/-- info: 'STACS2027.Runtimes.BoundedCost.Certificate.literalCount' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Certificate.literalCount

/-- info: 'STACS2027.Runtimes.BoundedCost.Certificate.literalValue' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Certificate.literalValue

/-- info: 'STACS2027.Runtimes.BoundedCost.Certificate.occurs' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Certificate.occurs

/-- info: 'STACS2027.Runtimes.BoundedCost.Certificate.scratch' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Certificate.scratch

/-- info: 'STACS2027.Runtimes.BoundedCost.Certificate.readClause' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Certificate.readClause

/-- info: 'STACS2027.Runtimes.BoundedCost.Certificate.countClause' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Certificate.countClause

/-- info: 'STACS2027.Runtimes.BoundedCost.Certificate.emitClause' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Certificate.emitClause

/-- info: 'STACS2027.Runtimes.BoundedCost.Certificate.occurrenceBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Certificate.occurrenceBody

/-- info: 'STACS2027.Runtimes.BoundedCost.Certificate.occurrenceScan' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Certificate.occurrenceScan

/-- info: 'STACS2027.Runtimes.BoundedCost.Certificate.prepareVariable' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Certificate.prepareVariable

/-- info: 'STACS2027.Runtimes.BoundedCost.Certificate.finishVariable' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Certificate.finishVariable

/-- info: 'STACS2027.Runtimes.BoundedCost.Certificate.emitVariable' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Certificate.emitVariable

/-- info: 'STACS2027.Runtimes.BoundedCost.Certificate.init' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Certificate.init

/-- info: 'STACS2027.Runtimes.BoundedCost.Certificate.header' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Certificate.header

/-- info: 'STACS2027.Runtimes.BoundedCost.Certificate.outputCertificate' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Certificate.outputCertificate

/-- info: 'STACS2027.Runtimes.BoundedCost.Certificate.Globals' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Certificate.Globals

/-- info: 'STACS2027.Runtimes.BoundedCost.Certificate.ClauseMemory' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Certificate.ClauseMemory

/-- info: 'STACS2027.Runtimes.BoundedCost.Certificate.globals_indep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Certificate.globals_indep

/-- info: 'STACS2027.Runtimes.BoundedCost.Certificate.readClause_loopFree' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Certificate.readClause_loopFree

/-- info: 'STACS2027.Runtimes.BoundedCost.Certificate.readClause_stores' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Certificate.readClause_stores

/-- info: 'STACS2027.Runtimes.BoundedCost.Certificate.readClause_writes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Certificate.readClause_writes

/-- info: 'STACS2027.Runtimes.BoundedCost.Certificate.readClause_wregs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Certificate.readClause_wregs

/-- info: 'STACS2027.Runtimes.BoundedCost.Certificate.readClause_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Certificate.readClause_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.Certificate.readClause_checked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Certificate.readClause_checked

/-- info: 'STACS2027.Runtimes.BoundedCost.Certificate.CountInv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Certificate.CountInv

/-- info: 'STACS2027.Runtimes.BoundedCost.Certificate.countInv_indep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Certificate.countInv_indep

/-- info: 'STACS2027.Runtimes.BoundedCost.Certificate.countClause_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Certificate.countClause_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.Certificate.countDeleted_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Certificate.countDeleted_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.Certificate.EmitInv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Certificate.EmitInv

/-- info: 'STACS2027.Runtimes.BoundedCost.Certificate.emitInv_indep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Certificate.emitInv_indep

/-- info: 'STACS2027.Runtimes.BoundedCost.Certificate.emitClause_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Certificate.emitClause_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.Certificate.emitDeleted_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Certificate.emitDeleted_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.Certificate.header_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Certificate.header_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.Certificate.seen' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Certificate.seen

/-- info: 'STACS2027.Runtimes.BoundedCost.Certificate.seen_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Certificate.seen_succ

/-- info: 'STACS2027.Runtimes.BoundedCost.Certificate.OccurrenceInv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Certificate.OccurrenceInv

/-- info: 'STACS2027.Runtimes.BoundedCost.Certificate.occurrenceBody_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Certificate.occurrenceBody_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.Certificate.occurrenceScan_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Certificate.occurrenceScan_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.Certificate.trueVariables_succ' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Certificate.trueVariables_succ

/-- info: 'STACS2027.Runtimes.BoundedCost.Certificate.finishVariable_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Certificate.finishVariable_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.Certificate.VariableInv' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Certificate.VariableInv

/-- info: 'STACS2027.Runtimes.BoundedCost.Certificate.emitVariable_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Certificate.emitVariable_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.Certificate.emitTrueVariables_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Certificate.emitTrueVariables_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.Certificate.InputGlobals' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Certificate.InputGlobals

/-- info: 'STACS2027.Runtimes.BoundedCost.Certificate.init_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Certificate.init_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.Certificate.outputCertificate_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Certificate.outputCertificate_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.Certificate.outputCertificate_assignmentAnswer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Certificate.outputCertificate_assignmentAnswer

/-- info: 'STACS2027.Runtimes.BoundedCost.compilerNodeTime' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.compilerNodeTime

/-- info: 'STACS2027.Runtimes.BoundedCost.compilerPathTime' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.compilerPathTime

/-- info: 'STACS2027.Runtimes.BoundedCost.compilerInnerTime' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.compilerInnerTime

/-- info: 'STACS2027.Runtimes.BoundedCost.compilerOuterTime' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.compilerOuterTime

/-- info: 'STACS2027.Runtimes.BoundedCost.compilerPrefixTime' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.compilerPrefixTime

/-- info: 'STACS2027.Runtimes.BoundedCost.compilerFinalTime' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.compilerFinalTime

/-- info: 'STACS2027.Runtimes.BoundedCost.compilerUniformConstant' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.compilerUniformConstant

/-- info: 'STACS2027.Runtimes.BoundedCost.compilerNodeTime_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.compilerNodeTime_le

/-- info: 'STACS2027.Runtimes.BoundedCost.compilerPathTime_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.compilerPathTime_le

/-- info: '_private.Runtimes.BoundedCost.CompilerBounds.0.STACS2027.Runtimes.BoundedCost.compilerInnerArithmetic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.compilerInnerArithmetic

/-- info: 'STACS2027.Runtimes.BoundedCost.compilerInnerTime_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.compilerInnerTime_le

/-- info: '_private.Runtimes.BoundedCost.CompilerBounds.0.STACS2027.Runtimes.BoundedCost.compilerOuterArithmetic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.compilerOuterArithmetic

/-- info: 'STACS2027.Runtimes.BoundedCost.compilerOuterTime_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.compilerOuterTime_le

/-- info: 'STACS2027.Runtimes.BoundedCost.compilerPrefixTime_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.compilerPrefixTime_le

/-- info: 'STACS2027.Runtimes.BoundedCost.compilerTotalTime_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.compilerTotalTime_le

/-- info: 'STACS2027.Runtimes.BoundedCost.compilerTotalSpace_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.compilerTotalSpace_le

/-- info: 'STACS2027.Runtimes.BoundedCost.actualInnerCost_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.actualInnerCost_le

/-- info: 'STACS2027.Runtimes.BoundedCost.outerCompleteCost_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.outerCompleteCost_le

/-- info: 'STACS2027.Runtimes.BoundedCost.compilerOuterTime_mono_special' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.compilerOuterTime_mono_special

/-- info: 'STACS2027.Runtimes.BoundedCost.Compiler.compilerExecutionCost' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Compiler.compilerExecutionCost

/-- info: 'STACS2027.Runtimes.BoundedCost.Compiler.compilerExecution_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Compiler.compilerExecution_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.Compiler.globalRegisters' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Compiler.globalRegisters

/-- info: 'STACS2027.Runtimes.BoundedCost.Compiler.globals_reg_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Compiler.globals_reg_frame

/-- info: 'STACS2027.Runtimes.BoundedCost.Compiler.globals_reg_indep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Compiler.globals_reg_indep

/-- info: 'STACS2027.Runtimes.BoundedCost.Compiler.StageZero' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Compiler.StageZero

/-- info: 'STACS2027.Runtimes.BoundedCost.Compiler.stageZero_reg_indep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Compiler.stageZero_reg_indep

/-- info: 'STACS2027.Runtimes.BoundedCost.Compiler.StageZero.caller_exec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Compiler.StageZero.caller_exec

/-- info: 'STACS2027.Runtimes.BoundedCost.Compiler.globals_actualPath_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Compiler.globals_actualPath_frame

/-- info: 'STACS2027.Runtimes.BoundedCost.CompilerInit.copyReady' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CompilerInit.copyReady

/-- info: 'STACS2027.Runtimes.BoundedCost.CompilerInit.program' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CompilerInit.program

/-- info: 'STACS2027.Runtimes.BoundedCost.CompilerInit.Globals' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CompilerInit.Globals

/-- info: 'STACS2027.Runtimes.BoundedCost.CompilerInit.initializedMemory' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CompilerInit.initializedMemory

/-- info: 'STACS2027.Runtimes.BoundedCost.CompilerInit.program_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CompilerInit.program_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.CompilerLayout' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CompilerLayout

/-- info: 'STACS2027.Runtimes.BoundedCost.compilerLayout' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.compilerLayout

/-- info: 'STACS2027.Runtimes.BoundedCost.compilerLayout_regions' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.compilerLayout_regions

/-- info: 'STACS2027.Runtimes.BoundedCost.compilerLayout_input_copy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.compilerLayout_input_copy

/-- info: 'STACS2027.Runtimes.BoundedCost.compilerLayout_space_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.compilerLayout_space_bound

/-- info: 'STACS2027.Runtimes.BoundedCost.Compiler.initialized_tables' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Compiler.initialized_tables

/-- info: 'STACS2027.Runtimes.BoundedCost.Compiler.positiveOutput_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Compiler.positiveOutput_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.Compiler.negativeOutput_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Compiler.negativeOutput_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.Compiler.positiveOutput_answer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Compiler.positiveOutput_answer

/-- info: 'STACS2027.Runtimes.BoundedCost.Compiler.negativeOutput_answer' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Compiler.negativeOutput_answer

/-- info: 'STACS2027.Runtimes.BoundedCost.Compiler.alive' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Compiler.alive

/-- info: 'STACS2027.Runtimes.BoundedCost.Compiler.prefixIndex' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Compiler.prefixIndex

/-- info: 'STACS2027.Runtimes.BoundedCost.Compiler.negativeValue' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Compiler.negativeValue

/-- info: 'STACS2027.Runtimes.BoundedCost.Compiler.branchExcess' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Compiler.branchExcess

/-- info: 'STACS2027.Runtimes.BoundedCost.Compiler.prefixExcess' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Compiler.prefixExcess

/-- info: 'STACS2027.Runtimes.BoundedCost.Compiler.trivialExcess' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Compiler.trivialExcess

/-- info: 'STACS2027.Runtimes.BoundedCost.Compiler.processed' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Compiler.processed

/-- info: 'STACS2027.Runtimes.BoundedCost.Compiler.budget' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Compiler.budget

/-- info: 'STACS2027.Runtimes.BoundedCost.Compiler.pathBody' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Compiler.pathBody

/-- info: 'STACS2027.Runtimes.BoundedCost.Compiler.innerScan' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Compiler.innerScan

/-- info: 'STACS2027.Runtimes.BoundedCost.Compiler.outerBody' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Compiler.outerBody

/-- info: 'STACS2027.Runtimes.BoundedCost.Compiler.compression' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Compiler.compression

/-- info: 'STACS2027.Runtimes.BoundedCost.Compiler.prefixBody' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Compiler.prefixBody

/-- info: 'STACS2027.Runtimes.BoundedCost.Compiler.prefixLoop' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Compiler.prefixLoop

/-- info: 'STACS2027.Runtimes.BoundedCost.Compiler.negativeOutput' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Compiler.negativeOutput

/-- info: 'STACS2027.Runtimes.BoundedCost.Compiler.positiveOutput' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Compiler.positiveOutput

/-- info: 'STACS2027.Runtimes.BoundedCost.Compiler.finish' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Compiler.finish

/-- info: 'STACS2027.Runtimes.BoundedCost.Compiler.properBudget' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Compiler.properBudget

/-- info: 'STACS2027.Runtimes.BoundedCost.Compiler.program' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Compiler.program

/-- info: '_private.Runtimes.BoundedCost.CompilerRegisterFrame.0.STACS2027.Runtimes.BoundedCost.Compiler.protected_compression_register' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Compiler.protected_compression_register

/-- info: 'STACS2027.Runtimes.BoundedCost.Compiler.not_mem_compression_global' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Compiler.not_mem_compression_global

/-- info: 'STACS2027.Runtimes.BoundedCost.Compiler.not_mem_compression_prefixIndex' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Compiler.not_mem_compression_prefixIndex

/-- info: 'STACS2027.Runtimes.BoundedCost.Compiler.not_mem_compression_processed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Compiler.not_mem_compression_processed

/-- info: 'STACS2027.Runtimes.BoundedCost.Compiler.innerProtectedRegisters' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Compiler.innerProtectedRegisters

/-- info: 'STACS2027.Runtimes.BoundedCost.Compiler.not_mem_innerScan_protected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Compiler.not_mem_innerScan_protected

/-- info: 'STACS2027.Runtimes.BoundedCost.Compiler.Globals' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Compiler.Globals

/-- info: 'STACS2027.Runtimes.BoundedCost.Compiler.globals_of_initialized' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Compiler.globals_of_initialized

/-- info: 'STACS2027.Runtimes.BoundedCost.Compiler.Globals.leastCut' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Compiler.Globals.leastCut

/-- info: 'STACS2027.Runtimes.BoundedCost.Compiler.prefixStep' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Compiler.prefixStep

/-- info: 'STACS2027.Runtimes.BoundedCost.Compiler.prefixFold' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Compiler.prefixFold

/-- info: 'STACS2027.Runtimes.BoundedCost.Compiler.PrefixCorrect' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Compiler.PrefixCorrect

/-- info: 'STACS2027.Runtimes.BoundedCost.Compiler.take_next' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Compiler.take_next

/-- info: 'STACS2027.Runtimes.BoundedCost.Compiler.prefixStep_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Compiler.prefixStep_correct

/-- info: 'STACS2027.Runtimes.BoundedCost.Compiler.prefixFold_zero' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Compiler.prefixFold_zero

/-- info: 'STACS2027.Runtimes.BoundedCost.Compiler.prefixFold_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Compiler.prefixFold_succ

/-- info: 'STACS2027.Runtimes.BoundedCost.Compiler.prefixFold_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Compiler.prefixFold_correct

/-- info: 'STACS2027.Runtimes.BoundedCost.Compiler.prefixFold_decides' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Compiler.prefixFold_decides

/-- info: 'STACS2027.Runtimes.BoundedCost.tryCompressionBranches' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.tryCompressionBranches

/-- info: 'STACS2027.Runtimes.BoundedCost.compressionSearch' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.compressionSearch

/-- info: 'STACS2027.Runtimes.BoundedCost.tryCompressionBranches_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.tryCompressionBranches_sound

/-- info: 'STACS2027.Runtimes.BoundedCost.tryCompressionBranches_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.tryCompressionBranches_complete

/-- info: 'STACS2027.Runtimes.BoundedCost.compressionSearch_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.compressionSearch_sound

/-- info: 'STACS2027.Runtimes.BoundedCost.compressionSearch_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.compressionSearch_correct

/-- info: 'STACS2027.Runtimes.BoundedCost.compressionVector_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.compressionVector_total

/-- info: 'STACS2027.Runtimes.BoundedCost.clauseCodePairs_codes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.clauseCodePairs_codes

/-- info: 'STACS2027.Runtimes.BoundedCost.seedRowsOf_getD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.seedRowsOf_getD

/-- info: 'STACS2027.Runtimes.BoundedCost.seedRowsOf_tables' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.seedRowsOf_tables

/-- info: 'STACS2027.Runtimes.BoundedCost.compressionSeedCaller_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.compressionSeedCaller_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.compressionVector' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.compressionVector

/-- info: 'STACS2027.Runtimes.BoundedCost.compressionVector_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.compressionVector_mem

/-- info: 'STACS2027.Runtimes.BoundedCost.compressionVector_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.compressionVector_complete

/-- info: 'STACS2027.Runtimes.BoundedCost.compressionBranches_iff_encoded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.compressionBranches_iff_encoded

/-- info: 'STACS2027.Runtimes.BoundedCost.encodedCompressionSearch' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.encodedCompressionSearch

/-- info: 'STACS2027.Runtimes.BoundedCost.encodedCompressionSearch_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.encodedCompressionSearch_sound

/-- info: 'STACS2027.Runtimes.BoundedCost.encodedCompressionSearch_correct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.encodedCompressionSearch_correct

/-- info: 'STACS2027.Runtimes.BoundedCost.CompressionSeedRow' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CompressionSeedRow

/-- info: 'STACS2027.Runtimes.BoundedCost.seedSelected' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.seedSelected

/-- info: 'STACS2027.Runtimes.BoundedCost.seedForcedValue' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.seedForcedValue

/-- info: 'STACS2027.Runtimes.BoundedCost.seedDeletedCount' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.seedDeletedCount

/-- info: 'STACS2027.Runtimes.BoundedCost.seedDeletedCount_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.seedDeletedCount_succ

/-- info: 'STACS2027.Runtimes.BoundedCost.seedForcedValue_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.seedForcedValue_succ

/-- info: 'STACS2027.Runtimes.BoundedCost.seedSpecialBase' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.seedSpecialBase

/-- info: 'STACS2027.Runtimes.BoundedCost.seedSpecialCount' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.seedSpecialCount

/-- info: 'STACS2027.Runtimes.BoundedCost.seedDeleted' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.seedDeleted

/-- info: 'STACS2027.Runtimes.BoundedCost.seedDigitsBase' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.seedDigitsBase

/-- info: 'STACS2027.Runtimes.BoundedCost.seedForcedBase' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.seedForcedBase

/-- info: 'STACS2027.Runtimes.BoundedCost.seedVariableCount' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.seedVariableCount

/-- info: 'STACS2027.Runtimes.BoundedCost.seedGlobalBudget' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.seedGlobalBudget

/-- info: 'STACS2027.Runtimes.BoundedCost.seedIndex' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.seedIndex

/-- info: 'STACS2027.Runtimes.BoundedCost.seedOffset' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.seedOffset

/-- info: 'STACS2027.Runtimes.BoundedCost.seedFirst' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.seedFirst

/-- info: 'STACS2027.Runtimes.BoundedCost.seedSecond' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.seedSecond

/-- info: 'STACS2027.Runtimes.BoundedCost.seedChoice' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.seedChoice

/-- info: 'STACS2027.Runtimes.BoundedCost.seedOne' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.seedOne

/-- info: 'STACS2027.Runtimes.BoundedCost.seedTemporary' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.seedTemporary

/-- info: 'STACS2027.Runtimes.BoundedCost.compressionSeedBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.compressionSeedBody

/-- info: 'STACS2027.Runtimes.BoundedCost.compressionSeedScan' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.compressionSeedScan

/-- info: 'STACS2027.Runtimes.BoundedCost.CompressionSeedGlobals' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CompressionSeedGlobals

/-- info: 'STACS2027.Runtimes.BoundedCost.CompressionSeedRowsMem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CompressionSeedRowsMem

/-- info: 'STACS2027.Runtimes.BoundedCost.SeedScanInv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.SeedScanInv

/-- info: '_private.Runtimes.BoundedCost.CompressionSeedRAM.0.STACS2027.Runtimes.BoundedCost.compressionSeedBody_run' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.compressionSeedBody_run

/-- info: 'STACS2027.Runtimes.BoundedCost.compressionSeedBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.compressionSeedBody_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.compressionSeedScan_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.compressionSeedScan_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.compressionSeedClearReady' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.compressionSeedClearReady

/-- info: 'STACS2027.Runtimes.BoundedCost.compressionSeedClear' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.compressionSeedClear

/-- info: 'STACS2027.Runtimes.BoundedCost.compressionSeedSetup' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.compressionSeedSetup

/-- info: 'STACS2027.Runtimes.BoundedCost.compressionSeedClear_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.compressionSeedClear_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.compressionSeedSetup_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.compressionSeedSetup_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.seedChosenCode' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.seedChosenCode

/-- info: 'STACS2027.Runtimes.BoundedCost.seedRequirementCodes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.seedRequirementCodes

/-- info: 'STACS2027.Runtimes.BoundedCost.seedRequirements' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.seedRequirements

/-- info: 'STACS2027.Runtimes.BoundedCost.seedSelected_iff_chosenCode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.seedSelected_iff_chosenCode

/-- info: 'STACS2027.Runtimes.BoundedCost.seedForcedValue_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.seedForcedValue_eq_one

/-- info: 'STACS2027.Runtimes.BoundedCost.requires_seedRequirements' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.requires_seedRequirements

/-- info: 'STACS2027.Runtimes.BoundedCost.seedRequirementCodes_bounded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.seedRequirementCodes_bounded

/-- info: 'STACS2027.Runtimes.BoundedCost.requires_dense_seed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.requires_dense_seed

/-- info: 'STACS2027.Runtimes.BoundedCost.seedRowsOf' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.seedRowsOf

/-- info: 'STACS2027.Runtimes.BoundedCost.seedRequirementCodes_all' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.seedRequirementCodes_all

/-- info: 'STACS2027.Runtimes.BoundedCost.seedDeletedCount_all' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.seedDeletedCount_all

/-- info: 'STACS2027.Runtimes.BoundedCost.seedRowsOf_vector' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.seedRowsOf_vector

/-- info: 'STACS2027.Runtimes.BoundedCost.seedRowsOf_bounded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.seedRowsOf_bounded

/-- info: 'STACS2027.Runtimes.BoundedCost.denseSeed_vector_requirements' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.denseSeed_vector_requirements

/-- info: 'STACS2027.Runtimes.BoundedCost.setupRowsOf_tables' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.setupRowsOf_tables

/-- info: 'STACS2027.Runtimes.BoundedCost.setupOccurrenceMask_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.setupOccurrenceMask_length

/-- info: 'STACS2027.Runtimes.BoundedCost.setupOccurrenceMask_clauses' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.setupOccurrenceMask_clauses

/-- info: 'STACS2027.Runtimes.BoundedCost.setupOccurrenceMask_getD' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.setupOccurrenceMask_getD

/-- info: 'STACS2027.Runtimes.BoundedCost.setupSnapshot_mask' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.setupSnapshot_mask

/-- info: 'STACS2027.Runtimes.BoundedCost.compressionSetupCaller_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.compressionSetupCaller_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.CompressionSetupRow' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CompressionSetupRow

/-- info: 'STACS2027.Runtimes.BoundedCost.setupRowTrue' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.setupRowTrue

/-- info: 'STACS2027.Runtimes.BoundedCost.setupActiveValue' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.setupActiveValue

/-- info: 'STACS2027.Runtimes.BoundedCost.setupSpecialPrefix' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.setupSpecialPrefix

/-- info: 'STACS2027.Runtimes.BoundedCost.setupSpecialPrefix_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.setupSpecialPrefix_succ

/-- info: 'STACS2027.Runtimes.BoundedCost.setupSpecialPrefix_length_le' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.setupSpecialPrefix_length_le

/-- info: 'STACS2027.Runtimes.BoundedCost.setupSpecialBase' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.setupSpecialBase

/-- info: 'STACS2027.Runtimes.BoundedCost.setupSpecialCount' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.setupSpecialCount

/-- info: 'STACS2027.Runtimes.BoundedCost.setupBaseSnapshot' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.setupBaseSnapshot

/-- info: 'STACS2027.Runtimes.BoundedCost.setupIndex' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.setupIndex

/-- info: 'STACS2027.Runtimes.BoundedCost.setupOffset' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.setupOffset

/-- info: 'STACS2027.Runtimes.BoundedCost.setupFirst' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.setupFirst

/-- info: 'STACS2027.Runtimes.BoundedCost.setupSecond' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.setupSecond

/-- info: 'STACS2027.Runtimes.BoundedCost.setupFirstTruth' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.setupFirstTruth

/-- info: 'STACS2027.Runtimes.BoundedCost.setupSecondTruth' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.setupSecondTruth

/-- info: 'STACS2027.Runtimes.BoundedCost.setupActive' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.setupActive

/-- info: 'STACS2027.Runtimes.BoundedCost.setupTemporary' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.setupTemporary

/-- info: 'STACS2027.Runtimes.BoundedCost.setupFormulaBase' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.setupFormulaBase

/-- info: 'STACS2027.Runtimes.BoundedCost.setupClauseCount' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.setupClauseCount

/-- info: 'STACS2027.Runtimes.BoundedCost.setupActiveBase' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.setupActiveBase

/-- info: 'STACS2027.Runtimes.BoundedCost.setupCandidateBase' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.setupCandidateBase

/-- info: 'STACS2027.Runtimes.BoundedCost.setupPrefixCount' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.setupPrefixCount

/-- info: 'STACS2027.Runtimes.BoundedCost.setupPackFalse' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.setupPackFalse

/-- info: 'STACS2027.Runtimes.BoundedCost.setupReadClause' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.setupReadClause

/-- info: 'STACS2027.Runtimes.BoundedCost.compressionSetupBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.compressionSetupBody

/-- info: 'STACS2027.Runtimes.BoundedCost.compressionSetupScan' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.compressionSetupScan

/-- info: 'STACS2027.Runtimes.BoundedCost.CompressionSetupGlobals' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CompressionSetupGlobals

/-- info: 'STACS2027.Runtimes.BoundedCost.CompressionSetupRowsMem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CompressionSetupRowsMem

/-- info: 'STACS2027.Runtimes.BoundedCost.setupOutside' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.setupOutside

/-- info: 'STACS2027.Runtimes.BoundedCost.SetupScanInv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.SetupScanInv

/-- info: '_private.Runtimes.BoundedCost.CompressionSetupRAM.0.STACS2027.Runtimes.BoundedCost.setupStepMemory' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.setupStepMemory

/-- info: '_private.Runtimes.BoundedCost.CompressionSetupRAM.0.STACS2027.Runtimes.BoundedCost.compressionSetupBody_run' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.compressionSetupBody_run

/-- info: '_private.Runtimes.BoundedCost.CompressionSetupRAM.0.STACS2027.Runtimes.BoundedCost.setupStepMemory_preserve' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.setupStepMemory_preserve

/-- info: '_private.Runtimes.BoundedCost.CompressionSetupRAM.0.STACS2027.Runtimes.BoundedCost.setupStepMemory_active' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.setupStepMemory_active

/-- info: '_private.Runtimes.BoundedCost.CompressionSetupRAM.0.STACS2027.Runtimes.BoundedCost.setupStepMemory_snapshot' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.setupStepMemory_snapshot

/-- info: 'STACS2027.Runtimes.BoundedCost.compressionSetupBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.compressionSetupBody_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.compressionSetupScan_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.compressionSetupScan_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.setupRowOf' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.setupRowOf

/-- info: 'STACS2027.Runtimes.BoundedCost.setupRowsOf' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.setupRowsOf

/-- info: 'STACS2027.Runtimes.BoundedCost.clauseCodePair' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.clauseCodePair

/-- info: 'STACS2027.Runtimes.BoundedCost.setupRowsOf_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.setupRowsOf_length

/-- info: 'STACS2027.Runtimes.BoundedCost.setupRowOf_true' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.setupRowOf_true

/-- info: 'STACS2027.Runtimes.BoundedCost.setupRowsOf_getD' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.setupRowsOf_getD

/-- info: 'STACS2027.Runtimes.BoundedCost.range_filterMap_cutoff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.range_filterMap_cutoff

/-- info: 'STACS2027.Runtimes.BoundedCost.map_getD_range_take' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.map_getD_range_take

/-- info: 'STACS2027.Runtimes.BoundedCost.setupSpecialPrefix_take' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.setupSpecialPrefix_take

/-- info: 'STACS2027.Runtimes.BoundedCost.setupRows_filterMap_semantic' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.setupRows_filterMap_semantic

/-- info: 'STACS2027.Runtimes.BoundedCost.setupSpecialPrefix_semantic' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.setupSpecialPrefix_semantic

/-- info: 'STACS2027.Runtimes.BoundedCost.setupSpecialPrefix_count' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.setupSpecialPrefix_count

/-- info: 'STACS2027.Runtimes.BoundedCost.compression_trigger_new_false' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.compression_trigger_new_false

/-- info: 'STACS2027.Runtimes.BoundedCost.compression_trigger_false_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.compression_trigger_false_count

/-- info: 'STACS2027.Runtimes.BoundedCost.setupSpecialPrefix_compression' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.setupSpecialPrefix_compression

/-- info: 'STACS2027.Runtimes.BoundedCost.activeOccurrences_map' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.activeOccurrences_map

/-- info: 'STACS2027.Runtimes.BoundedCost.setupOccurrenceMask' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.setupOccurrenceMask

/-- info: 'STACS2027.Runtimes.BoundedCost.setupOccurrenceMask_active' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.setupOccurrenceMask_active

/-- info: 'STACS2027.Runtimes.BoundedCost.setupActiveValue_semantic' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.setupActiveValue_semantic

/-- info: 'STACS2027.Runtimes.BoundedCost.setupOccurrenceMask_compressionBase' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.setupOccurrenceMask_compressionBase

/-- info: 'STACS2027.Runtimes.BoundedCost.compressionStart' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.compressionStart

/-- info: 'STACS2027.Runtimes.BoundedCost.compressionStart_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.compressionStart_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.sourceTerminal' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.sourceTerminal

/-- info: 'STACS2027.Runtimes.BoundedCost.sinkTerminal' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.sinkTerminal

/-- info: 'STACS2027.Runtimes.BoundedCost.sourceTerminal_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.sourceTerminal_iff

/-- info: 'STACS2027.Runtimes.BoundedCost.sinkTerminal_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.sinkTerminal_iff

/-- info: 'STACS2027.Runtimes.BoundedCost.TerminalConsistent' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.TerminalConsistent

/-- info: 'STACS2027.Runtimes.BoundedCost.terminalConsistent_of_requires' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.terminalConsistent_of_requires

/-- info: 'STACS2027.Runtimes.BoundedCost.contractVariable' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.contractVariable

/-- info: 'STACS2027.Runtimes.BoundedCost.liftContractRegion' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.liftContractRegion

/-- info: 'STACS2027.Runtimes.BoundedCost.projectContractRegion' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.projectContractRegion

/-- info: 'STACS2027.Runtimes.BoundedCost.projectContractRegion_valid' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.projectContractRegion_valid

/-- info: 'STACS2027.Runtimes.BoundedCost.lift_projectContractRegion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.lift_projectContractRegion

/-- info: 'STACS2027.Runtimes.BoundedCost.requires_assignmentOfContractRegion' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.requires_assignmentOfContractRegion

/-- info: 'STACS2027.Runtimes.BoundedCost.terminalConsistent_iff_requires' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.terminalConsistent_iff_requires

/-- info: 'STACS2027.Runtimes.BoundedCost.contractCutArc' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.contractCutArc

/-- info: 'STACS2027.Runtimes.BoundedCost.contractedCutArcs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.contractedCutArcs

/-- info: 'STACS2027.Runtimes.BoundedCost.contractCutArc_cost' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.contractCutArc_cost

/-- info: 'STACS2027.Runtimes.BoundedCost.contractedCutSize_eq_lift' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.contractedCutSize_eq_lift

/-- info: 'STACS2027.Runtimes.BoundedCost.cutCost_assignmentOfContractRegion' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.cutCost_assignmentOfContractRegion

/-- info: 'STACS2027.Runtimes.BoundedCost.cutCost_projectContractRegion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.cutCost_projectContractRegion

/-- info: 'STACS2027.Runtimes.BoundedCost.contractVariable_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.contractVariable_lt

/-- info: 'STACS2027.Runtimes.BoundedCost.contractedCutArcs_length_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.contractedCutArcs_length_le

/-- info: 'STACS2027.Runtimes.BoundedCost.contractedCutArcs_endpoints' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.contractedCutArcs_endpoints

/-- info: 'STACS2027.Runtimes.BoundedCost.IsMaximumSourceCut' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.IsMaximumSourceCut

/-- info: 'STACS2027.Runtimes.BoundedCost.leastCut_of_maximumSourceCut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.leastCut_of_maximumSourceCut

/-- info: 'STACS2027.Runtimes.BoundedCost.ContractionRowsMem.of_labelFrame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.ContractionRowsMem.of_labelFrame

/-- info: 'STACS2027.Runtimes.BoundedCost.ContractionResult' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.ContractionResult

/-- info: 'STACS2027.Runtimes.BoundedCost.contractionBuild_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.contractionBuild_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.TerminalRow' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.TerminalRow

/-- info: 'STACS2027.Runtimes.BoundedCost.terminalLabel' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.terminalLabel

/-- info: 'STACS2027.Runtimes.BoundedCost.terminalConflict' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.terminalConflict

/-- info: 'STACS2027.Runtimes.BoundedCost.terminalConflictPrefix' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.terminalConflictPrefix

/-- info: 'STACS2027.Runtimes.BoundedCost.terminalLabels' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.terminalLabels

/-- info: 'STACS2027.Runtimes.BoundedCost.ContractionRow' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.ContractionRow

/-- info: 'STACS2027.Runtimes.BoundedCost.retainContractedArc' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.retainContractedArc

/-- info: 'STACS2027.Runtimes.BoundedCost.contractionRowArc' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.contractionRowArc

/-- info: 'STACS2027.Runtimes.BoundedCost.contractionArcsPrefix' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.contractionArcsPrefix

/-- info: 'STACS2027.Runtimes.BoundedCost.contractionArcCodes' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.contractionArcCodes

/-- info: 'STACS2027.Runtimes.BoundedCost.contractionEdgeInput' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.contractionEdgeInput

/-- info: 'STACS2027.Runtimes.BoundedCost.TerminalLabelValue' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.TerminalLabelValue

/-- info: 'STACS2027.Runtimes.BoundedCost.terminalLabels_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.terminalLabels_length

/-- info: 'STACS2027.Runtimes.BoundedCost.terminalLabels_get' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.terminalLabels_get

/-- info: 'STACS2027.Runtimes.BoundedCost.terminalConflictPrefix_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.terminalConflictPrefix_succ

/-- info: 'STACS2027.Runtimes.BoundedCost.ContractionBuilt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.ContractionBuilt

/-- info: 'STACS2027.Runtimes.BoundedCost.contractionHeader_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.contractionHeader_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.contractionFooter_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.contractionFooter_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.contractionFormulaBase' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.contractionFormulaBase

/-- info: 'STACS2027.Runtimes.BoundedCost.contractionClauseCount' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.contractionClauseCount

/-- info: 'STACS2027.Runtimes.BoundedCost.contractionActiveBase' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.contractionActiveBase

/-- info: 'STACS2027.Runtimes.BoundedCost.contractionReferenceBase' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.contractionReferenceBase

/-- info: 'STACS2027.Runtimes.BoundedCost.contractionVariableCount' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.contractionVariableCount

/-- info: 'STACS2027.Runtimes.BoundedCost.contractionForcedBase' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.contractionForcedBase

/-- info: 'STACS2027.Runtimes.BoundedCost.contractionLabelsBase' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.contractionLabelsBase

/-- info: 'STACS2027.Runtimes.BoundedCost.contractionOutputBase' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.contractionOutputBase

/-- info: 'STACS2027.Runtimes.BoundedCost.contractionArcCount' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.contractionArcCount

/-- info: 'STACS2027.Runtimes.BoundedCost.contractionIncompatible' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.contractionIncompatible

/-- info: 'STACS2027.Runtimes.BoundedCost.contractionIndex' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.contractionIndex

/-- info: 'STACS2027.Runtimes.BoundedCost.contractionOffset' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.contractionOffset

/-- info: 'STACS2027.Runtimes.BoundedCost.contractionPositive' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.contractionPositive

/-- info: 'STACS2027.Runtimes.BoundedCost.contractionNegative' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.contractionNegative

/-- info: 'STACS2027.Runtimes.BoundedCost.contractionReference' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.contractionReference

/-- info: 'STACS2027.Runtimes.BoundedCost.contractionLabel' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.contractionLabel

/-- info: 'STACS2027.Runtimes.BoundedCost.contractionFirst' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.contractionFirst

/-- info: 'STACS2027.Runtimes.BoundedCost.contractionSecond' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.contractionSecond

/-- info: 'STACS2027.Runtimes.BoundedCost.contractionFirstTruth' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.contractionFirstTruth

/-- info: 'STACS2027.Runtimes.BoundedCost.contractionSecondTruth' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.contractionSecondTruth

/-- info: 'STACS2027.Runtimes.BoundedCost.contractionTail' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.contractionTail

/-- info: 'STACS2027.Runtimes.BoundedCost.contractionHead' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.contractionHead

/-- info: 'STACS2027.Runtimes.BoundedCost.contractionTemporary' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.contractionTemporary

/-- info: 'STACS2027.Runtimes.BoundedCost.contractionValue' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.contractionValue

/-- info: 'STACS2027.Runtimes.BoundedCost.contractionChooseLabel' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.contractionChooseLabel

/-- info: 'STACS2027.Runtimes.BoundedCost.contractionLabelBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.contractionLabelBody

/-- info: 'STACS2027.Runtimes.BoundedCost.contractionEmitArc' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.contractionEmitArc

/-- info: 'STACS2027.Runtimes.BoundedCost.contractionRetainArc' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.contractionRetainArc

/-- info: 'STACS2027.Runtimes.BoundedCost.contractionReadArc' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.contractionReadArc

/-- info: 'STACS2027.Runtimes.BoundedCost.contractionClauseBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.contractionClauseBody

/-- info: 'STACS2027.Runtimes.BoundedCost.contractionStoreOffset' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.contractionStoreOffset

/-- info: 'STACS2027.Runtimes.BoundedCost.contractionHeader' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.contractionHeader

/-- info: 'STACS2027.Runtimes.BoundedCost.contractionBuild' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.contractionBuild

/-- info: 'STACS2027.Runtimes.BoundedCost.ContractionGlobals' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.ContractionGlobals

/-- info: 'STACS2027.Runtimes.BoundedCost.TerminalRowsMem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.TerminalRowsMem

/-- info: 'STACS2027.Runtimes.BoundedCost.OutsideCells' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OutsideCells

/-- info: 'STACS2027.Runtimes.BoundedCost.DisjointCells' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.DisjointCells

/-- info: 'STACS2027.Runtimes.BoundedCost.DisjointCells.outside' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.DisjointCells.outside

/-- info: 'STACS2027.Runtimes.BoundedCost.LabelBuildInv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.LabelBuildInv

/-- info: '_private.Runtimes.BoundedCost.ContractionRAM.0.STACS2027.Runtimes.BoundedCost.contractionChooseLabel_run' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.contractionChooseLabel_run

/-- info: 'STACS2027.Runtimes.BoundedCost.contractionLabelBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.contractionLabelBody_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.contractionLabelScan' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.contractionLabelScan

/-- info: 'STACS2027.Runtimes.BoundedCost.contractionLabelScan_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.contractionLabelScan_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.ContractionRowsMem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.ContractionRowsMem

/-- info: 'STACS2027.Runtimes.BoundedCost.contractionArcsPrefix_succ' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.contractionArcsPrefix_succ

/-- info: 'STACS2027.Runtimes.BoundedCost.contractionArcsPrefix_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.contractionArcsPrefix_length

/-- info: 'STACS2027.Runtimes.BoundedCost.contractionArcCodes_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.contractionArcCodes_length

/-- info: 'STACS2027.Runtimes.BoundedCost.contractionArcCodes_append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.contractionArcCodes_append

/-- info: 'STACS2027.Runtimes.BoundedCost.contractionPrefixInput' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.contractionPrefixInput

/-- info: 'STACS2027.Runtimes.BoundedCost.contractionPrefixInput_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.contractionPrefixInput_length

/-- info: 'STACS2027.Runtimes.BoundedCost.ClauseBuildInv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.ClauseBuildInv

/-- info: '_private.Runtimes.BoundedCost.ContractionRAM.0.STACS2027.Runtimes.BoundedCost.storeContractionArc' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.storeContractionArc

/-- info: '_private.Runtimes.BoundedCost.ContractionRAM.0.STACS2027.Runtimes.BoundedCost.contractionRetainArc_run' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.contractionRetainArc_run

/-- info: '_private.Runtimes.BoundedCost.ContractionRAM.0.STACS2027.Runtimes.BoundedCost.contractionClauseBody_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.contractionClauseBody_run

/-- info: '_private.Runtimes.BoundedCost.ContractionRAM.0.STACS2027.Runtimes.BoundedCost.DisjointCells.outside_left' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.DisjointCells.outside_left

/-- info: 'STACS2027.Runtimes.BoundedCost.contractionClauseBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.contractionClauseBody_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.contractionClauseScan_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.contractionClauseScan_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.mem_denseRequirements' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.mem_denseRequirements

/-- info: 'STACS2027.Runtimes.BoundedCost.sourceTerminal_denseRequirements' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.sourceTerminal_denseRequirements

/-- info: 'STACS2027.Runtimes.BoundedCost.sinkTerminal_denseRequirements' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.sinkTerminal_denseRequirements

/-- info: 'STACS2027.Runtimes.BoundedCost.terminalRowsOf' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.terminalRowsOf

/-- info: 'STACS2027.Runtimes.BoundedCost.terminalRowsOf_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.terminalRowsOf_length

/-- info: 'STACS2027.Runtimes.BoundedCost.terminalRowsOf_getD' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.terminalRowsOf_getD

/-- info: 'STACS2027.Runtimes.BoundedCost.terminalLabel_contractVariable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.terminalLabel_contractVariable

/-- info: 'STACS2027.Runtimes.BoundedCost.terminalLabelValue_code' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.terminalLabelValue_code

/-- info: 'STACS2027.Runtimes.BoundedCost.terminalConflictPrefix_dense' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.terminalConflictPrefix_dense

/-- info: 'STACS2027.Runtimes.BoundedCost.terminalConsistent_dense' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.terminalConsistent_dense

/-- info: 'STACS2027.Runtimes.BoundedCost.terminalConflictPrefix_false_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.terminalConflictPrefix_false_iff

/-- info: 'STACS2027.Runtimes.BoundedCost.contractionRowOf' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.contractionRowOf

/-- info: 'STACS2027.Runtimes.BoundedCost.contractionRowsOf' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.contractionRowsOf

/-- info: 'STACS2027.Runtimes.BoundedCost.contractionRowOf_arc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.contractionRowOf_arc

/-- info: 'STACS2027.Runtimes.BoundedCost.map_getD_range' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.map_getD_range

/-- info: 'STACS2027.Runtimes.BoundedCost.contractionArcsPrefix_all' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.contractionArcsPrefix_all

/-- info: 'STACS2027.Runtimes.BoundedCost.contractionRowsOf_arcs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.contractionRowsOf_arcs

/-- info: 'STACS2027.Runtimes.BoundedCost.contractionArcsPrefix_semantic' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.contractionArcsPrefix_semantic

/-- info: 'STACS2027.Runtimes.BoundedCost.edgePairs_cutNetwork' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.edgePairs_cutNetwork

/-- info: 'STACS2027.Runtimes.BoundedCost.contractionEdgeInput_cutNetwork' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.contractionEdgeInput_cutNetwork

/-- info: 'STACS2027.Runtimes.BoundedCost.mem_activeOccurrences' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.mem_activeOccurrences

/-- info: 'STACS2027.Runtimes.BoundedCost.activeOccurrences_twoCNF' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.activeOccurrences_twoCNF

/-- info: 'STACS2027.Runtimes.BoundedCost.contractionEdgeInput_semantic' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.contractionEdgeInput_semantic

/-- info: 'STACS2027.Runtimes.BoundedCost.CoreRAM.coreBase' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CoreRAM.coreBase

/-- info: 'STACS2027.Runtimes.BoundedCost.CoreRAM.coreAddress' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CoreRAM.coreAddress

/-- info: 'STACS2027.Runtimes.BoundedCost.CoreRAM.coreTwo' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CoreRAM.coreTwo

/-- info: 'STACS2027.Runtimes.BoundedCost.CoreRAM.coreFour' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CoreRAM.coreFour

/-- info: 'STACS2027.Runtimes.BoundedCost.CoreRAM.coreLength' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CoreRAM.coreLength

/-- info: 'STACS2027.Runtimes.BoundedCost.CoreRAM.coreBudget' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CoreRAM.coreBudget

/-- info: 'STACS2027.Runtimes.BoundedCost.CoreRAM.copyIndex' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CoreRAM.copyIndex

/-- info: 'STACS2027.Runtimes.BoundedCost.CoreRAM.headerIndex' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CoreRAM.headerIndex

/-- info: 'STACS2027.Runtimes.BoundedCost.CoreRAM.storeWord' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CoreRAM.storeWord

/-- info: 'STACS2027.Runtimes.BoundedCost.CoreRAM.header' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CoreRAM.header

/-- info: 'STACS2027.Runtimes.BoundedCost.CoreRAM.headerMemory' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CoreRAM.headerMemory

/-- info: 'STACS2027.Runtimes.BoundedCost.CoreRAM.HeaderGlobals' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CoreRAM.HeaderGlobals

/-- info: 'STACS2027.Runtimes.BoundedCost.CoreRAM.header_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CoreRAM.header_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.CoreRAM.readEdge' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CoreRAM.readEdge

/-- info: 'STACS2027.Runtimes.BoundedCost.CoreRAM.readWrites' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CoreRAM.readWrites

/-- info: 'STACS2027.Runtimes.BoundedCost.CoreRAM.readEdge_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CoreRAM.readEdge_run

/-- info: 'STACS2027.Runtimes.BoundedCost.CoreRAM.putEdge' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CoreRAM.putEdge

/-- info: 'STACS2027.Runtimes.BoundedCost.CoreRAM.edgeBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CoreRAM.edgeBody

/-- info: 'STACS2027.Runtimes.BoundedCost.CoreRAM.edgeRow' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CoreRAM.edgeRow

/-- info: 'STACS2027.Runtimes.BoundedCost.CoreRAM.edgeLoop' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CoreRAM.edgeLoop

/-- info: 'STACS2027.Runtimes.BoundedCost.CoreRAM.edgeMemory' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CoreRAM.edgeMemory

/-- info: 'STACS2027.Runtimes.BoundedCost.CoreRAM.edgeMemory_zero' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CoreRAM.edgeMemory_zero

/-- info: 'STACS2027.Runtimes.BoundedCost.CoreRAM.edgeMemory_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CoreRAM.edgeMemory_succ

/-- info: 'STACS2027.Runtimes.BoundedCost.CoreRAM.edgeMemory_outside' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CoreRAM.edgeMemory_outside

/-- info: 'STACS2027.Runtimes.BoundedCost.CoreRAM.edgeMemory_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CoreRAM.edgeMemory_pair

/-- info: 'STACS2027.Runtimes.BoundedCost.CoreRAM.vertexPut' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CoreRAM.vertexPut

/-- info: 'STACS2027.Runtimes.BoundedCost.CoreRAM.vertexLoop' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CoreRAM.vertexLoop

/-- info: 'STACS2027.Runtimes.BoundedCost.CoreRAM.vertexMemory' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CoreRAM.vertexMemory

/-- info: 'STACS2027.Runtimes.BoundedCost.CoreRAM.vertexMemory_zero' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CoreRAM.vertexMemory_zero

/-- info: 'STACS2027.Runtimes.BoundedCost.CoreRAM.vertexMemory_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CoreRAM.vertexMemory_succ

/-- info: 'STACS2027.Runtimes.BoundedCost.CoreRAM.vertexMemory_outside' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CoreRAM.vertexMemory_outside

/-- info: 'STACS2027.Runtimes.BoundedCost.CoreRAM.vertexMemory_get' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CoreRAM.vertexMemory_get

/-- info: 'STACS2027.Runtimes.BoundedCost.CoreRAM.VertexGlobals' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CoreRAM.VertexGlobals

/-- info: 'STACS2027.Runtimes.BoundedCost.CoreRAM.VertexInv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CoreRAM.VertexInv

/-- info: 'STACS2027.Runtimes.BoundedCost.CoreRAM.vertexPut_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CoreRAM.vertexPut_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.CoreRAM.vertexLoop_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CoreRAM.vertexLoop_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.CoreRAM.EdgeGlobals' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CoreRAM.EdgeGlobals

/-- info: 'STACS2027.Runtimes.BoundedCost.CoreRAM.EdgeInv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CoreRAM.EdgeInv

/-- info: 'STACS2027.Runtimes.BoundedCost.CoreRAM.RowInv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CoreRAM.RowInv

/-- info: 'STACS2027.Runtimes.BoundedCost.CoreRAM.edgeBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CoreRAM.edgeBody_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.CoreRAM.edgeRow_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CoreRAM.edgeRow_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.CoreRAM.CycleInv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CoreRAM.CycleInv

/-- info: 'STACS2027.Runtimes.BoundedCost.CoreRAM.edgeLoop_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CoreRAM.edgeLoop_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.CoreRAM.headerMemory_outside' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CoreRAM.headerMemory_outside

/-- info: 'STACS2027.Runtimes.BoundedCost.CoreRAM.headerMemory_fields' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CoreRAM.headerMemory_fields

/-- info: 'STACS2027.Runtimes.BoundedCost.CoreRAM.coreMemory' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CoreRAM.coreMemory

/-- info: 'STACS2027.Runtimes.BoundedCost.CoreRAM.coreInput' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CoreRAM.coreInput

/-- info: 'STACS2027.Runtimes.BoundedCost.CoreRAM.coreInput_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CoreRAM.coreInput_length

/-- info: 'STACS2027.Runtimes.BoundedCost.CoreRAM.coreInput_semantic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CoreRAM.coreInput_semantic

/-- info: 'STACS2027.Runtimes.BoundedCost.CoreRAM.coreMemory_input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CoreRAM.coreMemory_input

/-- info: 'STACS2027.Runtimes.BoundedCost.CoreRAM.ready' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CoreRAM.ready

/-- info: 'STACS2027.Runtimes.BoundedCost.CoreRAM.CoreGlobals' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CoreRAM.CoreGlobals

/-- info: 'STACS2027.Runtimes.BoundedCost.CoreRAM.program' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CoreRAM.program

/-- info: 'STACS2027.Runtimes.BoundedCost.CoreRAM.coreSpace' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CoreRAM.coreSpace

/-- info: 'STACS2027.Runtimes.BoundedCost.CoreRAM.CoreGlobals.transfer' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CoreRAM.CoreGlobals.transfer

/-- info: 'STACS2027.Runtimes.BoundedCost.CoreRAM.ready_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CoreRAM.ready_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.CoreRAM.program_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CoreRAM.program_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.CoreRAM.callerProgram' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CoreRAM.callerProgram

/-- info: 'STACS2027.Runtimes.BoundedCost.CoreRAM.callerProgram_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CoreRAM.callerProgram_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.coreOccurrenceGraph' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.coreOccurrenceGraph

/-- info: 'STACS2027.Runtimes.BoundedCost.coreOccurrenceGraph_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.coreOccurrenceGraph_length

/-- info: 'STACS2027.Runtimes.BoundedCost.coreOccurrenceGraph_support' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.coreOccurrenceGraph_support

/-- info: 'STACS2027.Runtimes.BoundedCost.cycles_of_same_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.cycles_of_same_support

/-- info: 'STACS2027.Runtimes.BoundedCost.coreOccurrenceGraph_cycles' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.coreOccurrenceGraph_cycles

/-- info: 'STACS2027.Runtimes.BoundedCost.coreOccurrenceGraph_hasAssignment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.coreOccurrenceGraph_hasAssignment

/-- info: 'STACS2027.Runtimes.BoundedCost.literalBound' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.literalBound

/-- info: 'STACS2027.Runtimes.BoundedCost.literalBound_member' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.literalBound_member

/-- info: 'STACS2027.Runtimes.BoundedCost.formulaBound' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.formulaBound

/-- info: 'STACS2027.Runtimes.BoundedCost.formulaBound_twoCNF' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.formulaBound_twoCNF

/-- info: 'STACS2027.Runtimes.BoundedCost.exists_leastCut_of_citedFlow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.exists_leastCut_of_citedFlow

/-- info: 'STACS2027.Runtimes.BoundedCost.citedFlowLeastCutOperation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.citedFlowLeastCutOperation

/-- info: 'STACS2027.Runtimes.BoundedCost.citedFlowLeastCutOperation_correct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.citedFlowLeastCutOperation_correct

/-- info: 'STACS2027.Runtimes.BoundedCost.citedFlowLeastCutFactory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.citedFlowLeastCutFactory

/-- info: 'STACS2027.Runtimes.BoundedCost.citedFlowLeastCutFactory_correct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.citedFlowLeastCutFactory_correct

/-- info: 'STACS2027.Runtimes.BoundedCost.citedFlowLeastCutOperation_eq_some' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.citedFlowLeastCutOperation_eq_some

/-- info: 'STACS2027.Runtimes.BoundedCost.agreementRegion' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.agreementRegion

/-- info: 'STACS2027.Runtimes.BoundedCost.agreementRegion_literal' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.agreementRegion_literal

/-- info: 'STACS2027.Runtimes.BoundedCost.assignmentOfRegion' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.assignmentOfRegion

/-- info: 'STACS2027.Runtimes.BoundedCost.agreementRegion_assignmentOfRegion' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.agreementRegion_assignmentOfRegion

/-- info: 'STACS2027.Runtimes.BoundedCost.assignmentOfRegion_agreementRegion' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.assignmentOfRegion_agreementRegion

/-- info: 'STACS2027.Runtimes.BoundedCost.clauseCutArcs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.clauseCutArcs

/-- info: 'STACS2027.Runtimes.BoundedCost.variableCutArcs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.variableCutArcs

/-- info: 'STACS2027.Runtimes.BoundedCost.variableArcCut' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.variableArcCut

/-- info: 'STACS2027.Runtimes.BoundedCost.variableCutSize' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.variableCutSize

/-- info: 'STACS2027.Runtimes.BoundedCost.cutClause_eq_variableArcCut' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.cutClause_eq_variableArcCut

/-- info: 'STACS2027.Runtimes.BoundedCost.cutCost_eq_variableCutSize' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.cutCost_eq_variableCutSize

/-- info: 'STACS2027.Runtimes.BoundedCost.variableCutArcs_length_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.variableCutArcs_length_le

/-- info: 'STACS2027.Runtimes.BoundedCost.variableCutArcs_endpoints' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.variableCutArcs_endpoints

/-- info: 'STACS2027.Runtimes.BoundedCost.requires_iff_agreementRegion' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.requires_iff_agreementRegion

/-- info: 'STACS2027.Runtimes.BoundedCost.cutNetwork' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.cutNetwork

/-- info: 'STACS2027.Runtimes.BoundedCost.extendCutRegion' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.extendCutRegion

/-- info: 'STACS2027.Runtimes.BoundedCost.extendCutRegion_fin' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.extendCutRegion_fin

/-- info: 'STACS2027.Runtimes.BoundedCost.cutNetwork_cutSize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.cutNetwork_cutSize

/-- info: 'STACS2027.Runtimes.BoundedCost.cutNetwork_extended_cutSize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.cutNetwork_extended_cutSize

/-- info: 'STACS2027.Runtimes.BoundedCost.maximumSourceCut_of_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.maximumSourceCut_of_finite

/-- info: 'STACS2027.Runtimes.BoundedCost.contractedCutNetwork' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.contractedCutNetwork

/-- info: 'STACS2027.Runtimes.BoundedCost.contractedCutNetwork_head_ne_source' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.contractedCutNetwork_head_ne_source

/-- info: 'STACS2027.Runtimes.BoundedCost.contractedCutNetwork_tail_ne_sink' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.contractedCutNetwork_tail_ne_sink

/-- info: 'STACS2027.Runtimes.BoundedCost.leastCut_of_contractedFiniteCut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.leastCut_of_contractedFiniteCut

/-- info: 'STACS2027.Runtimes.BoundedCost.activeOccurrences' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.activeOccurrences

/-- info: 'STACS2027.Runtimes.BoundedCost.disableOccurrence' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.disableOccurrence

/-- info: 'STACS2027.Runtimes.BoundedCost.disableOccurrence_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.disableOccurrence_length

/-- info: 'STACS2027.Runtimes.BoundedCost.activeOccurrences_disable_first' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.activeOccurrences_disable_first

/-- info: 'STACS2027.Runtimes.BoundedCost.literalOfCode' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.literalOfCode

/-- info: 'STACS2027.Runtimes.BoundedCost.code_literalOfCode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.code_literalOfCode

/-- info: 'STACS2027.Runtimes.BoundedCost.literalOfCode_code' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.literalOfCode_code

/-- info: 'STACS2027.Runtimes.BoundedCost.evalLiteral_literalOfCode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.evalLiteral_literalOfCode

/-- info: 'STACS2027.Runtimes.BoundedCost.denseRequirements' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.denseRequirements

/-- info: 'STACS2027.Runtimes.BoundedCost.denseRequirements_bounded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.denseRequirements_bounded

/-- info: 'STACS2027.Runtimes.BoundedCost.requires_denseRequirements' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.requires_denseRequirements

/-- info: 'STACS2027.Runtimes.BoundedCost.requires_denseRequirements_force' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.requires_denseRequirements_force

/-- info: 'STACS2027.Runtimes.BoundedCost.requires_denseRequirements_force_literal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.requires_denseRequirements_force_literal

/-- info: 'STACS2027.Runtimes.BoundedCost.TruthTable' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.TruthTable

/-- info: 'STACS2027.Runtimes.BoundedCost.codes_clause_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.codes_clause_pair

/-- info: 'STACS2027.Runtimes.BoundedCost.clauseMemory_of_tables' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.clauseMemory_of_tables

/-- info: 'STACS2027.Runtimes.BoundedCost.truthTable_positive' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.truthTable_positive

/-- info: 'STACS2027.Runtimes.BoundedCost.truthTable_negative' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.truthTable_negative

/-- info: 'STACS2027.Runtimes.BoundedCost.requires_dense_force_equiv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.requires_dense_force_equiv

/-- info: 'STACS2027.Runtimes.BoundedCost.decodedBits_upd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.decodedBits_upd

/-- info: 'STACS2027.Runtimes.BoundedCost.disableOccurrence_clause_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.disableOccurrence_clause_mem

/-- info: 'STACS2027.Runtimes.BoundedCost.disableOccurrence_domain' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.disableOccurrence_domain

/-- info: 'STACS2027.Runtimes.BoundedCost.LiteralDomain' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.LiteralDomain

/-- info: 'STACS2027.Runtimes.BoundedCost.isLeastCut_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.isLeastCut_unique

/-- info: 'STACS2027.Runtimes.BoundedCost.twoCNF_sublist' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.twoCNF_sublist

/-- info: 'STACS2027.Runtimes.BoundedCost.twoCNF_erase' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.twoCNF_erase

/-- info: 'STACS2027.Runtimes.BoundedCost.literalDomain_cons' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.literalDomain_cons

/-- info: 'STACS2027.Runtimes.BoundedCost.compressionBranches_domain' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.compressionBranches_domain

/-- info: 'STACS2027.Runtimes.BoundedCost.compressionBase_twoCNF' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.compressionBase_twoCNF

/-- info: 'STACS2027.Runtimes.BoundedCost.compressionSpecial_twoCNF' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.compressionSpecial_twoCNF

/-- info: 'STACS2027.Runtimes.BoundedCost.encodedIterativeSearch' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.encodedIterativeSearch

/-- info: 'STACS2027.Runtimes.BoundedCost.almostTwoSatEncodedSearch' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.almostTwoSatEncodedSearch

/-- info: 'STACS2027.Runtimes.BoundedCost.encodedIterativeSearch_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.encodedIterativeSearch_sound

/-- info: 'STACS2027.Runtimes.BoundedCost.encodedIterativeSearch_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.encodedIterativeSearch_complete

/-- info: 'STACS2027.Runtimes.BoundedCost.almostTwoSatEncodedSearch_correct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.almostTwoSatEncodedSearch_correct

/-- info: 'STACS2027.Runtimes.BoundedCost.meetAssignment' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.meetAssignment

/-- info: 'STACS2027.Runtimes.BoundedCost.joinAssignment' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.joinAssignment

/-- info: 'STACS2027.Runtimes.BoundedCost.evalLiteral_meetAssignment' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.evalLiteral_meetAssignment

/-- info: 'STACS2027.Runtimes.BoundedCost.evalLiteral_joinAssignment' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.evalLiteral_joinAssignment

/-- info: 'STACS2027.Runtimes.BoundedCost.meet_join_preserve_required' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.meet_join_preserve_required

/-- info: 'STACS2027.Runtimes.BoundedCost.meet_preserve_reference' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.meet_preserve_reference

/-- info: 'STACS2027.Runtimes.BoundedCost.cutClause' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.cutClause

/-- info: 'STACS2027.Runtimes.BoundedCost.conflictClause' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.conflictClause

/-- info: 'STACS2027.Runtimes.BoundedCost.cutCost' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.cutCost

/-- info: 'STACS2027.Runtimes.BoundedCost.conflictCost' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.conflictCost

/-- info: 'STACS2027.Runtimes.BoundedCost.unsatisfiedCount_eq_cut_add_conflict' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.unsatisfiedCount_eq_cut_add_conflict

/-- info: 'STACS2027.Runtimes.BoundedCost.cutClause_submodular' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.cutClause_submodular

/-- info: 'STACS2027.Runtimes.BoundedCost.conflictClause_meet_le' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.conflictClause_meet_le

/-- info: 'STACS2027.Runtimes.BoundedCost.cutCost_submodular' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.cutCost_submodular

/-- info: 'STACS2027.Runtimes.BoundedCost.conflictCost_meet_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.conflictCost_meet_le

/-- info: 'STACS2027.Runtimes.BoundedCost.annotated_neutral_exchange' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.annotated_neutral_exchange

/-- info: 'STACS2027.Runtimes.BoundedCost.exhaustiveTwoCNF_sublist' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.exhaustiveTwoCNF_sublist

/-- info: 'STACS2027.Runtimes.BoundedCost.almostTwoSatExhaustive' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.almostTwoSatExhaustive

/-- info: 'STACS2027.Runtimes.BoundedCost.almostTwoSatExhaustive_correct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.almostTwoSatExhaustive_correct

/-- info: 'STACS2027.Runtimes.BoundedCost.RdInv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.RdInv

/-- info: 'STACS2027.Runtimes.BoundedCost.AnsMem' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.AnsMem

/-- info: 'STACS2027.Runtimes.BoundedCost.rdInv_indep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.rdInv_indep

/-- info: 'STACS2027.Runtimes.BoundedCost.readBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.readBody_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.FlagPost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.FlagPost

/-- info: 'STACS2027.Runtimes.BoundedCost.readFlag_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.readFlag_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.readPre_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.readPre_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.readCost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.readCost

/-- info: 'STACS2027.Runtimes.BoundedCost.readAns_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.readAns_some

/-- info: 'STACS2027.Runtimes.BoundedCost.extractCost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.extractCost

/-- info: 'STACS2027.Runtimes.BoundedCost.extractSpace' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.extractSpace

/-- info: 'STACS2027.Runtimes.BoundedCost.extract5_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.extract5_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.firstSuccess' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.firstSuccess

/-- info: 'STACS2027.Runtimes.BoundedCost.firstSuccess_has' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.firstSuccess_has

/-- info: 'STACS2027.Runtimes.BoundedCost.firstSuccess_some' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.firstSuccess_some

/-- info: 'STACS2027.Runtimes.BoundedCost.firstSuccess_foldl' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.firstSuccess_foldl

/-- info: 'STACS2027.Runtimes.BoundedCost.encodedPathSearch' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.encodedPathSearch

/-- info: 'STACS2027.Runtimes.BoundedCost.encodedPathSearch_has' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.encodedPathSearch_has

/-- info: 'STACS2027.Runtimes.BoundedCost.annotatedPath_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.annotatedPath_sound

/-- info: 'STACS2027.Runtimes.BoundedCost.encodedPathSearch_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.encodedPathSearch_sound

/-- info: 'STACS2027.Runtimes.BoundedCost.encodedPathSearch_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.encodedPathSearch_correct

/-- info: 'STACS2027.Runtimes.BoundedCost.almost_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.almost_two

/-- info: 'STACS2027.Runtimes.BoundedCost.length_codes_almost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.length_codes_almost

/-- info: 'STACS2027.Runtimes.BoundedCost.pathConstraints_nil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.pathConstraints_nil

/-- info: 'STACS2027.Runtimes.BoundedCost.pcs_nCopies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.pcs_nCopies

/-- info: 'STACS2027.Runtimes.BoundedCost.psiR_front' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.psiR_front

/-- info: 'STACS2027.Runtimes.BoundedCost.frontCost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.frontCost

/-- info: 'STACS2027.Runtimes.BoundedCost.front5_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.front5_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.allocSeen_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.allocSeen_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.formCost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.formCost

/-- info: 'STACS2027.Runtimes.BoundedCost.form5_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.form5_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.nCopies' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.nCopies

/-- info: 'STACS2027.Runtimes.BoundedCost.PsiR' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.PsiR

/-- info: 'STACS2027.Runtimes.BoundedCost.initReadZ_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.initReadZ_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.stepInitZ_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.stepInitZ_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.readPsi_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.readPsi_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.stepInit5_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.stepInit5_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.Compiler.initialCompilerRAM_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Compiler.initialCompilerRAM_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.Compiler.initialPrefixRep_alive' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Compiler.initialPrefixRep_alive

/-- info: 'STACS2027.Runtimes.BoundedCost.innerDigitWords' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.innerDigitWords

/-- info: 'STACS2027.Runtimes.BoundedCost.innerDigitWords_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.innerDigitWords_length

/-- info: 'STACS2027.Runtimes.BoundedCost.innerDigitWords_array' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.innerDigitWords_array

/-- info: 'STACS2027.Runtimes.BoundedCost.innerStart_of_globals' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.innerStart_of_globals

/-- info: 'STACS2027.Runtimes.BoundedCost.innerGeometry_compilerLayout' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.innerGeometry_compilerLayout

/-- info: 'STACS2027.Runtimes.BoundedCost.innerGeometry_readOnlyGap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.innerGeometry_readOnlyGap

/-- info: 'STACS2027.Runtimes.BoundedCost.Compiler.globals_actualInner_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Compiler.globals_actualInner_frame

/-- info: 'STACS2027.Runtimes.BoundedCost.innerRep_setDigit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.innerRep_setDigit

/-- info: 'STACS2027.Runtimes.BoundedCost.InnerStart' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.InnerStart

/-- info: 'STACS2027.Runtimes.BoundedCost.pathBasic_transport_newDigits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.pathBasic_transport_newDigits

/-- info: 'STACS2027.Runtimes.BoundedCost.innerHeader_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.innerHeader_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.innerControlWrites' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.innerControlWrites

/-- info: 'STACS2027.Runtimes.BoundedCost.innerCallerRegister_mod' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.innerCallerRegister_mod

/-- info: 'STACS2027.Runtimes.BoundedCost.innerControlWrites_mod' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.innerControlWrites_mod

/-- info: 'STACS2027.Runtimes.BoundedCost.innerRep_indep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.innerRep_indep

/-- info: 'STACS2027.Runtimes.BoundedCost.innerPathBodyCost' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.innerPathBodyCost

/-- info: 'STACS2027.Runtimes.BoundedCost.actualPathRep_answer' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.actualPathRep_answer

/-- info: 'STACS2027.Runtimes.BoundedCost.innerPathBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.innerPathBody_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.not_mem_actualInner_wregs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.not_mem_actualInner_wregs

/-- info: 'STACS2027.Runtimes.BoundedCost.actualInner_registerFrame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.actualInner_registerFrame

/-- info: 'STACS2027.Runtimes.BoundedCost.InnerGeometry' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.InnerGeometry

/-- info: 'STACS2027.Runtimes.BoundedCost.InnerMemoryFrame' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.InnerMemoryFrame

/-- info: 'STACS2027.Runtimes.BoundedCost.InnerAnswerRep' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.InnerAnswerRep

/-- info: 'STACS2027.Runtimes.BoundedCost.InnerBasic' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.InnerBasic

/-- info: 'STACS2027.Runtimes.BoundedCost.InnerRep' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.InnerRep

/-- info: 'STACS2027.Runtimes.BoundedCost.innerBasic_after_restore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.innerBasic_after_restore

/-- info: 'STACS2027.Runtimes.BoundedCost.innerSearchCost' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.innerSearchCost

/-- info: 'STACS2027.Runtimes.BoundedCost.innerSearchRAM_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.innerSearchRAM_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.pathBasicRegisters' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.pathBasicRegisters

/-- info: 'STACS2027.Runtimes.BoundedCost.pathBasic_transport' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.pathBasic_transport

/-- info: 'STACS2027.Runtimes.BoundedCost.innerGeometry_snapshot_frames' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.innerGeometry_snapshot_frames

/-- info: 'STACS2027.Runtimes.BoundedCost.innerBasic_of_path' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.innerBasic_of_path

/-- info: 'STACS2027.Runtimes.BoundedCost.compressionBase' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.compressionBase

/-- info: 'STACS2027.Runtimes.BoundedCost.compressionSpecial' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.compressionSpecial

/-- info: 'STACS2027.Runtimes.BoundedCost.compression_partition_perm' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.compression_partition_perm

/-- info: 'STACS2027.Runtimes.BoundedCost.compressionBase_satisfied' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.compressionBase_satisfied

/-- info: 'STACS2027.Runtimes.BoundedCost.compressionSpecial_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.compressionSpecial_length

/-- info: 'STACS2027.Runtimes.BoundedCost.compressionBase_clauses2' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.compressionBase_clauses2

/-- info: 'STACS2027.Runtimes.BoundedCost.compressionSpecial_clauses2' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.compressionSpecial_clauses2

/-- info: 'STACS2027.Runtimes.BoundedCost.LeastCutFactory' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.LeastCutFactory

/-- info: 'STACS2027.Runtimes.BoundedCost.LeastCutFactoryCorrect' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.LeastCutFactoryCorrect

/-- info: 'STACS2027.Runtimes.BoundedCost.iterativeSearch' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.iterativeSearch

/-- info: 'STACS2027.Runtimes.BoundedCost.almostTwoSatSearch' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.almostTwoSatSearch

/-- info: 'STACS2027.Runtimes.BoundedCost.iterativeSearch_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.iterativeSearch_sound

/-- info: 'STACS2027.Runtimes.BoundedCost.iterativeSearch_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.iterativeSearch_complete

/-- info: 'STACS2027.Runtimes.BoundedCost.almostTwoSatSearch_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.almostTwoSatSearch_correct

/-- info: 'STACS2027.Runtimes.BoundedCost.LayoutRAM.span' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.LayoutRAM.span

/-- info: 'STACS2027.Runtimes.BoundedCost.LayoutRAM.nodesPlus' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.LayoutRAM.nodesPlus

/-- info: 'STACS2027.Runtimes.BoundedCost.LayoutRAM.square' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.LayoutRAM.square

/-- info: 'STACS2027.Runtimes.BoundedCost.LayoutRAM.multiplyIndex' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.LayoutRAM.multiplyIndex

/-- info: 'STACS2027.Runtimes.BoundedCost.LayoutRAM.factor' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.LayoutRAM.factor

/-- info: 'STACS2027.Runtimes.BoundedCost.LayoutRAM.codeLength' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.LayoutRAM.codeLength

/-- info: 'STACS2027.Runtimes.BoundedCost.LayoutRAM.truthLength' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.LayoutRAM.truthLength

/-- info: 'STACS2027.Runtimes.BoundedCost.LayoutRAM.depth' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.LayoutRAM.depth

/-- info: 'STACS2027.Runtimes.BoundedCost.LayoutRAM.originalBase' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.LayoutRAM.originalBase

/-- info: 'STACS2027.Runtimes.BoundedCost.LayoutRAM.inputAddress' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.LayoutRAM.inputAddress

/-- info: 'STACS2027.Runtimes.BoundedCost.LayoutRAM.savedBase' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.LayoutRAM.savedBase

/-- info: 'STACS2027.Runtimes.BoundedCost.LayoutRAM.savedLength' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.LayoutRAM.savedLength

/-- info: 'STACS2027.Runtimes.BoundedCost.LayoutRAM.edgeLength' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.LayoutRAM.edgeLength

/-- info: 'STACS2027.Runtimes.BoundedCost.LayoutRAM.prepare' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.LayoutRAM.prepare

/-- info: 'STACS2027.Runtimes.BoundedCost.LayoutRAM.allocateTables' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.LayoutRAM.allocateTables

/-- info: 'STACS2027.Runtimes.BoundedCost.LayoutRAM.program' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.LayoutRAM.program

/-- info: 'STACS2027.Runtimes.BoundedCost.LayoutRAM.ArithmeticGlobals' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.LayoutRAM.ArithmeticGlobals

/-- info: 'STACS2027.Runtimes.BoundedCost.LayoutRAM.LayoutRep' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.LayoutRAM.LayoutRep

/-- info: 'STACS2027.Runtimes.BoundedCost.LayoutRAM.prepare_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.LayoutRAM.prepare_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.LayoutRAM.allocateTables_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.LayoutRAM.allocateTables_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.LayoutRAM.program_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.LayoutRAM.program_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.leastCutIncompatibleTime' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.leastCutIncompatibleTime

/-- info: 'STACS2027.Runtimes.BoundedCost.leastCutTotalTime' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.leastCutTotalTime

/-- info: 'STACS2027.Runtimes.BoundedCost.compilerLayout_leastCutGeometry' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.compilerLayout_leastCutGeometry

/-- info: 'STACS2027.Runtimes.BoundedCost.leastCutSpan' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.leastCutSpan

/-- info: 'STACS2027.Runtimes.BoundedCost.leastCutMetadata' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.leastCutMetadata

/-- info: 'STACS2027.Runtimes.BoundedCost.leastCutBackend' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.leastCutBackend

/-- info: 'STACS2027.Runtimes.BoundedCost.wregs_renameRegisters' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.wregs_renameRegisters

/-- info: 'STACS2027.Runtimes.BoundedCost.callerRegister_wregs_mod' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.callerRegister_wregs_mod

/-- info: 'STACS2027.Runtimes.BoundedCost.callerRegister_exec_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.callerRegister_exec_zero

/-- info: 'STACS2027.Runtimes.BoundedCost.leastCutMetadata_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.leastCutMetadata_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.LeastCutGeometry' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.LeastCutGeometry

/-- info: 'STACS2027.Runtimes.BoundedCost.LeastCutGlobals' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.LeastCutGlobals

/-- info: 'STACS2027.Runtimes.BoundedCost.LeastCutFrame' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.LeastCutFrame

/-- info: 'STACS2027.Runtimes.BoundedCost.LeastCutRegisterFrame' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.LeastCutRegisterFrame

/-- info: 'STACS2027.Runtimes.BoundedCost.LeastCutResult' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.LeastCutResult

/-- info: 'STACS2027.Runtimes.BoundedCost.candidateDecode_prefix_truth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.candidateDecode_prefix_truth

/-- info: 'STACS2027.Runtimes.BoundedCost.activeOccurrences_length_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.activeOccurrences_length_le

/-- info: 'STACS2027.Runtimes.BoundedCost.leastCutBackend_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.leastCutBackend_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.LoopHeaders.inputBase' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.LoopHeaders.inputBase

/-- info: 'STACS2027.Runtimes.BoundedCost.LoopHeaders.inputDepth' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.LoopHeaders.inputDepth

/-- info: 'STACS2027.Runtimes.BoundedCost.LoopHeaders.controlBase' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.LoopHeaders.controlBase

/-- info: 'STACS2027.Runtimes.BoundedCost.LoopHeaders.controlDepth' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.LoopHeaders.controlDepth

/-- info: 'STACS2027.Runtimes.BoundedCost.LoopHeaders.ready' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.LoopHeaders.ready

/-- info: 'STACS2027.Runtimes.BoundedCost.LoopHeaders.program' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.LoopHeaders.program

/-- info: 'STACS2027.Runtimes.BoundedCost.LoopHeaders.Globals' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.LoopHeaders.Globals

/-- info: 'STACS2027.Runtimes.BoundedCost.LoopHeaders.program_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.LoopHeaders.program_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.clog_le_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.clog_le_add

/-- info: 'STACS2027.Runtimes.BoundedCost.almost_len_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.almost_len_le

/-- info: 'STACS2027.Runtimes.BoundedCost.frontCost_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.frontCost_le

/-- info: 'STACS2027.Runtimes.BoundedCost.nCopies_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.nCopies_le

/-- info: 'STACS2027.Runtimes.BoundedCost.bnd5' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.bnd5

/-- info: 'STACS2027.Runtimes.BoundedCost.C5' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.C5

/-- info: 'STACS2027.Runtimes.BoundedCost.bnd5_facts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.bnd5_facts

/-- info: 'STACS2027.Runtimes.BoundedCost.formCost_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.formCost_le

/-- info: 'STACS2027.Runtimes.BoundedCost.buildCost_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.buildCost_le

/-- info: 'STACS2027.Runtimes.BoundedCost.formSpace_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.formSpace_le

/-- info: 'STACS2027.Runtimes.BoundedCost.extractCost_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.extractCost_le

/-- info: 'STACS2027.Runtimes.BoundedCost.extractSpace_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.extractSpace_le

/-- info: 'STACS2027.Runtimes.BoundedCost.zeroCost_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.zeroCost_le

/-- info: 'STACS2027.Runtimes.BoundedCost.zeroSpace_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.zeroSpace_le

/-- info: 'STACS2027.Runtimes.BoundedCost.zero5_ram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.zero5_ram

/-- info: 'STACS2027.Runtimes.BoundedCost.almostFormula_shift_solverDomain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.almostFormula_shift_solverDomain

/-- info: 'STACS2027.Runtimes.BoundedCost.pipeline5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.pipeline5

/-- info: 'STACS2027.Runtimes.BoundedCost.boundedCost_ram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.boundedCost_ram

/-- info: 'STACS2027.Runtimes.BoundedCost.NodeActionBounded' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.NodeActionBounded

/-- info: 'STACS2027.Runtimes.BoundedCost.nodeActionRows' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.nodeActionRows

/-- info: 'STACS2027.Runtimes.BoundedCost.nodeActionForced' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.nodeActionForced

/-- info: 'STACS2027.Runtimes.BoundedCost.nodeActionRows_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.nodeActionRows_length

/-- info: 'STACS2027.Runtimes.BoundedCost.nodeActionRows_clauses' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.nodeActionRows_clauses

/-- info: 'STACS2027.Runtimes.BoundedCost.nodeAction_bounded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.nodeAction_bounded

/-- info: 'STACS2027.Runtimes.BoundedCost.nodeAction_tables' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.nodeAction_tables

/-- info: 'STACS2027.Runtimes.BoundedCost.SearchNodeMemoryFrame' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.SearchNodeMemoryFrame

/-- info: 'STACS2027.Runtimes.BoundedCost.nodeActionMemory_outside' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.nodeActionMemory_outside

/-- info: 'STACS2027.Runtimes.BoundedCost.LeastCutGeometry.frame_input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.LeastCutGeometry.frame_input

/-- info: 'STACS2027.Runtimes.BoundedCost.Arr.leastCutFrame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Arr.leastCutFrame

/-- info: 'STACS2027.Runtimes.BoundedCost.MaskTable.leastCutFrame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.MaskTable.leastCutFrame

/-- info: 'STACS2027.Runtimes.BoundedCost.ForcedTable.leastCutFrame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.ForcedTable.leastCutFrame

/-- info: 'STACS2027.Runtimes.BoundedCost.TruthTable.leastCutFrame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.TruthTable.leastCutFrame

/-- info: 'STACS2027.Runtimes.BoundedCost.mem_activeOccurrences_true' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.mem_activeOccurrences_true

/-- info: 'STACS2027.Runtimes.BoundedCost.findCutConflict_none_of_summary_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.findCutConflict_none_of_summary_zero

/-- info: 'STACS2027.Runtimes.BoundedCost.nodeActionState' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.nodeActionState

/-- info: 'STACS2027.Runtimes.BoundedCost.nodeActionState_annotatedPathStep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.nodeActionState_annotatedPathStep

/-- info: 'STACS2027.Runtimes.BoundedCost.occursInBool' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.occursInBool

/-- info: 'STACS2027.Runtimes.BoundedCost.occursInBool_eq_true' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.occursInBool_eq_true

/-- info: 'STACS2027.Runtimes.BoundedCost.falseIndices' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.falseIndices

/-- info: 'STACS2027.Runtimes.BoundedCost.falseIndices_pairwise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.falseIndices_pairwise

/-- info: 'STACS2027.Runtimes.BoundedCost.mem_falseIndices' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.mem_falseIndices

/-- info: 'STACS2027.Runtimes.BoundedCost.falseIndices_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.falseIndices_bounded

/-- info: 'STACS2027.Runtimes.BoundedCost.falseIndices_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.falseIndices_length

/-- info: 'STACS2027.Runtimes.BoundedCost.falseIndices_as_filterRange' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.falseIndices_as_filterRange

/-- info: 'STACS2027.Runtimes.BoundedCost.falseIndicesPrefix' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.falseIndicesPrefix

/-- info: 'STACS2027.Runtimes.BoundedCost.falseIndicesPrefix_zero' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.falseIndicesPrefix_zero

/-- info: 'STACS2027.Runtimes.BoundedCost.falseIndicesPrefix_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.falseIndicesPrefix_succ

/-- info: 'STACS2027.Runtimes.BoundedCost.occursInBool_iff_codes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.occursInBool_iff_codes

/-- info: 'STACS2027.Runtimes.BoundedCost.trueVariables' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.trueVariables

/-- info: 'STACS2027.Runtimes.BoundedCost.trueVariables_pairwise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.trueVariables_pairwise

/-- info: 'STACS2027.Runtimes.BoundedCost.mem_trueVariables' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.mem_trueVariables

/-- info: 'STACS2027.Runtimes.BoundedCost.trueVariables_occurring' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.trueVariables_occurring

/-- info: 'STACS2027.Runtimes.BoundedCost.trueVariables_agree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.trueVariables_agree

/-- info: 'STACS2027.Runtimes.BoundedCost.evalClause_trueVariables' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.evalClause_trueVariables

/-- info: 'STACS2027.Runtimes.BoundedCost.assignmentAnswer' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.assignmentAnswer

/-- info: 'STACS2027.Runtimes.BoundedCost.assignmentAnswer_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.assignmentAnswer_correct

/-- info: 'STACS2027.Runtimes.BoundedCost.searchAnswer' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.searchAnswer

/-- info: 'STACS2027.Runtimes.BoundedCost.searchAnswer_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.searchAnswer_correct

/-- info: 'STACS2027.Runtimes.BoundedCost.MaskTable' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.MaskTable

/-- info: 'STACS2027.Runtimes.BoundedCost.contractionRowsMem_of_tables' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.contractionRowsMem_of_tables

/-- info: 'STACS2027.Runtimes.BoundedCost.disableOccurrence_getElem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.disableOccurrence_getElem

/-- info: 'STACS2027.Runtimes.BoundedCost.disableOccurrence_clauses' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.disableOccurrence_clauses

/-- info: 'STACS2027.Runtimes.BoundedCost.MaskTable.disable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.MaskTable.disable

/-- info: 'STACS2027.Runtimes.BoundedCost.ForcedTable.force' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.ForcedTable.force

/-- info: 'STACS2027.Runtimes.BoundedCost.requires_dense_force_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.requires_dense_force_congr

/-- info: 'STACS2027.Runtimes.BoundedCost.MaskTable.upd_outside' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.MaskTable.upd_outside

/-- info: 'STACS2027.Runtimes.BoundedCost.ForcedTable.upd_outside' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.ForcedTable.upd_outside

/-- info: 'STACS2027.Runtimes.BoundedCost.TruthTable.upd_outside' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.TruthTable.upd_outside

/-- info: 'STACS2027.Runtimes.BoundedCost.OptSpanRAM.Known' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptSpanRAM.Known

/-- info: 'STACS2027.Runtimes.BoundedCost.OptSpanRAM.Known.cons' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptSpanRAM.Known.cons

/-- info: 'STACS2027.Runtimes.BoundedCost.OptSpanRAM.known_indep' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptSpanRAM.known_indep

/-- info: 'STACS2027.Runtimes.BoundedCost.OptSpanRAM.const_known' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptSpanRAM.const_known

/-- info: 'STACS2027.Runtimes.BoundedCost.OptSpanRAM.add_known' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptSpanRAM.add_known

/-- info: 'STACS2027.Runtimes.BoundedCost.OptSpanRAM.addc_known' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptSpanRAM.addc_known

/-- info: 'STACS2027.Runtimes.BoundedCost.OptSpanRAM.mul_known' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptSpanRAM.mul_known

/-- info: 'STACS2027.Runtimes.BoundedCost.OptSpanRAM.pow_known' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptSpanRAM.pow_known

/-- info: 'STACS2027.Runtimes.BoundedCost.OptBounds.uniformConstant' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptBounds.uniformConstant

/-- info: 'STACS2027.Runtimes.BoundedCost.OptBounds.totalTime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptBounds.totalTime

/-- info: 'STACS2027.Runtimes.BoundedCost.OptBounds.paper_positive' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptBounds.paper_positive

/-- info: 'STACS2027.Runtimes.BoundedCost.OptBounds.incidence_le_paper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptBounds.incidence_le_paper

/-- info: 'STACS2027.Runtimes.BoundedCost.OptBounds.bound_succ_le_paper' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptBounds.bound_succ_le_paper

/-- info: 'STACS2027.Runtimes.BoundedCost.OptBounds.totalTime_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptBounds.totalTime_le

/-- info: 'STACS2027.Runtimes.BoundedCost.OptBounds.callSpace_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptBounds.callSpace_le

/-- info: 'STACS2027.Runtimes.BoundedCost.OptBounds.constant_lower' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptBounds.constant_lower

/-- info: 'STACS2027.Runtimes.BoundedCost.OptBounds.coreSpace_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptBounds.coreSpace_le

/-- info: 'STACS2027.Runtimes.BoundedCost.OptBounds.emptyTime_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptBounds.emptyTime_le

/-- info: 'STACS2027.Runtimes.BoundedCost.OptCall.BoundedProgram' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptCall.BoundedProgram

/-- info: 'STACS2027.Runtimes.BoundedCost.OptCall.bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptCall.bound

/-- info: 'STACS2027.Runtimes.BoundedCost.OptCall.callSpace' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptCall.callSpace

/-- info: 'STACS2027.Runtimes.BoundedCost.OptCall.State' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptCall.State

/-- info: 'STACS2027.Runtimes.BoundedCost.OptCall.Result' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptCall.Result

/-- info: 'STACS2027.Runtimes.BoundedCost.OptCall.program' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptCall.program

/-- info: 'STACS2027.Runtimes.BoundedCost.OptCall.paper_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptCall.paper_core

/-- info: 'STACS2027.Runtimes.BoundedCost.OptCall.bound_input' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptCall.bound_input

/-- info: 'STACS2027.Runtimes.BoundedCost.OptCall.callReady_classZero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptCall.callReady_classZero

/-- info: 'STACS2027.Runtimes.BoundedCost.OptCall.call_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptCall.call_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.OptControl.inputK' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptControl.inputK

/-- info: 'STACS2027.Runtimes.BoundedCost.OptControl.inputT' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptControl.inputT

/-- info: 'STACS2027.Runtimes.BoundedCost.OptControl.budget' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptControl.budget

/-- info: 'STACS2027.Runtimes.BoundedCost.OptControl.span' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptControl.span

/-- info: 'STACS2027.Runtimes.BoundedCost.OptControl.alive' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptControl.alive

/-- info: 'STACS2027.Runtimes.BoundedCost.OptControl.address' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptControl.address

/-- info: 'STACS2027.Runtimes.BoundedCost.OptControl.answerBit' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptControl.answerBit

/-- info: 'STACS2027.Runtimes.BoundedCost.OptControl.outputIndex' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptControl.outputIndex

/-- info: 'STACS2027.Runtimes.BoundedCost.OptControl.outputLength' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptControl.outputLength

/-- info: 'STACS2027.Runtimes.BoundedCost.OptControl.Fixed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptControl.Fixed

/-- info: 'STACS2027.Runtimes.BoundedCost.OptControl.Fixed.transfer' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptControl.Fixed.transfer

/-- info: 'STACS2027.Runtimes.BoundedCost.OptControl.startProgram' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptControl.startProgram

/-- info: 'STACS2027.Runtimes.BoundedCost.OptControl.startProgram_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptControl.startProgram_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.OptControl.callReady' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptControl.callReady

/-- info: 'STACS2027.Runtimes.BoundedCost.OptControl.callReady_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptControl.callReady_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.OptControl.readAnswer' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptControl.readAnswer

/-- info: 'STACS2027.Runtimes.BoundedCost.OptControl.reject' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptControl.reject

/-- info: 'STACS2027.Runtimes.BoundedCost.OptControl.decideAnswer' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptControl.decideAnswer

/-- info: 'STACS2027.Runtimes.BoundedCost.OptControl.DecisionGlobals' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptControl.DecisionGlobals

/-- info: 'STACS2027.Runtimes.BoundedCost.OptControl.decideAnswer_zero_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptControl.decideAnswer_zero_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.OptControl.decideAnswer_one_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptControl.decideAnswer_one_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.OptEmit.emitOne' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptEmit.emitOne

/-- info: 'STACS2027.Runtimes.BoundedCost.OptEmit.emitBlock' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptEmit.emitBlock

/-- info: 'STACS2027.Runtimes.BoundedCost.OptEmit.emitAnswer' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptEmit.emitAnswer

/-- info: 'STACS2027.Runtimes.BoundedCost.OptEmit.OutputInv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptEmit.OutputInv

/-- info: 'STACS2027.Runtimes.BoundedCost.OptEmit.emitOne_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptEmit.emitOne_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.OptEmit.emitBlock_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptEmit.emitBlock_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.OptEmit.emitAnswer_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptEmit.emitAnswer_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.OptEmit.captureLength' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptEmit.captureLength

/-- info: 'STACS2027.Runtimes.BoundedCost.OptEmit.program' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptEmit.program

/-- info: 'STACS2027.Runtimes.BoundedCost.OptEmit.program_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptEmit.program_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.OptEmit.OptimumAnswer' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptEmit.OptimumAnswer

/-- info: 'STACS2027.Runtimes.BoundedCost.OptSpanRAM.Q_sum_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptSpanRAM.Q_sum_le

/-- info: 'STACS2027.Runtimes.BoundedCost.OptSpanRAM.span_sum_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptSpanRAM.span_sum_le

/-- info: 'STACS2027.Runtimes.BoundedCost.OptSpanRAM.Q_le_twice_paper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptSpanRAM.Q_le_twice_paper

/-- info: 'STACS2027.Runtimes.BoundedCost.OptSpanRAM.original_m_add_Q_le_twice_paper' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptSpanRAM.original_m_add_Q_le_twice_paper

/-- info: 'STACS2027.Runtimes.BoundedCost.OptSpanRAM.span_le_paper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptSpanRAM.span_le_paper

/-- info: 'STACS2027.Runtimes.BoundedCost.OptLoop.remaining' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptLoop.remaining

/-- info: 'STACS2027.Runtimes.BoundedCost.OptLoop.remaining_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptLoop.remaining_step

/-- info: 'STACS2027.Runtimes.BoundedCost.OptLoop.Inv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptLoop.Inv

/-- info: 'STACS2027.Runtimes.BoundedCost.OptLoop.potential' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptLoop.potential

/-- info: 'STACS2027.Runtimes.BoundedCost.OptLoop.program' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptLoop.program

/-- info: 'STACS2027.Runtimes.BoundedCost.OptLoop.program_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptLoop.program_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.OptLoop.searchAndEmit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptLoop.searchAndEmit

/-- info: 'STACS2027.Runtimes.BoundedCost.OptLoop.searchAndEmit_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptLoop.searchAndEmit_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.OptMain.emptyAnswer' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptMain.emptyAnswer

/-- info: 'STACS2027.Runtimes.BoundedCost.OptMain.program' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptMain.program

/-- info: 'STACS2027.Runtimes.BoundedCost.OptMain.emptyAnswer_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptMain.emptyAnswer_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.OptMain.emptyAnswer_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptMain.emptyAnswer_correct

/-- info: 'STACS2027.Runtimes.BoundedCost.OptMain.program_computes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptMain.program_computes

/-- info: 'STACS2027.Runtimes.BoundedCost.optimalCost_ram_fpt_from_citedFlow' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.optimalCost_ram_fpt_from_citedFlow

/-- info: 'STACS2027.Runtimes.BoundedCost.corePrefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.corePrefix

/-- info: 'STACS2027.Runtimes.BoundedCost.coreInput_eq_prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.coreInput_eq_prefix

/-- info: 'STACS2027.Runtimes.BoundedCost.corePrefix_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.corePrefix_length

/-- info: 'STACS2027.Runtimes.BoundedCost.offsetInput_update_last' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.offsetInput_update_last

/-- info: 'STACS2027.Runtimes.BoundedCost.coreInput_update_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.coreInput_update_budget

/-- info: 'STACS2027.Runtimes.BoundedCost.coreAnswer_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.coreAnswer_transfer

/-- info: 'STACS2027.Runtimes.BoundedCost.BoundedCostAnswer.negative' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.BoundedCostAnswer.negative

/-- info: 'STACS2027.Runtimes.BoundedCost.BoundedCostAnswer.positive' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.BoundedCostAnswer.positive

/-- info: 'STACS2027.Runtimes.BoundedCost.BoundedCostAnswer.head' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.BoundedCostAnswer.head

/-- info: 'STACS2027.Runtimes.BoundedCost.OptPowerRAM.budget' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptPowerRAM.budget

/-- info: 'STACS2027.Runtimes.BoundedCost.OptPowerRAM.value' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptPowerRAM.value

/-- info: 'STACS2027.Runtimes.BoundedCost.OptPowerRAM.counter' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptPowerRAM.counter

/-- info: 'STACS2027.Runtimes.BoundedCost.OptPowerRAM.temporary' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptPowerRAM.temporary

/-- info: 'STACS2027.Runtimes.BoundedCost.OptPowerRAM.body' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptPowerRAM.body

/-- info: 'STACS2027.Runtimes.BoundedCost.OptPowerRAM.program' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptPowerRAM.program

/-- info: 'STACS2027.Runtimes.BoundedCost.OptPowerRAM.body_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptPowerRAM.body_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.OptPowerRAM.program_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptPowerRAM.program_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.OptPowerRAM.program_registerFrame' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptPowerRAM.program_registerFrame

/-- info: 'STACS2027.Runtimes.BoundedCost.OptSpanRAM.z' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptSpanRAM.z

/-- info: 'STACS2027.Runtimes.BoundedCost.OptSpanRAM.Q' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptSpanRAM.Q

/-- info: 'STACS2027.Runtimes.BoundedCost.OptSpanRAM.span' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptSpanRAM.span

/-- info: 'STACS2027.Runtimes.BoundedCost.OptSpanRAM.Q_positive' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptSpanRAM.Q_positive

/-- info: 'STACS2027.Runtimes.BoundedCost.OptSpanRAM.span_positive' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptSpanRAM.span_positive

/-- info: 'STACS2027.Runtimes.BoundedCost.OptSpanRAM.Q_le_span' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptSpanRAM.Q_le_span

/-- info: 'STACS2027.Runtimes.BoundedCost.OptSpanRAM.span_scale_lower' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptSpanRAM.span_scale_lower

/-- info: 'STACS2027.Runtimes.BoundedCost.OptSpanRAM.base_components_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptSpanRAM.base_components_le

/-- info: 'STACS2027.Runtimes.BoundedCost.OptSpanRAM.z_positive' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptSpanRAM.z_positive

/-- info: 'STACS2027.Runtimes.BoundedCost.OptSpanRAM.positive_components_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptSpanRAM.positive_components_le

/-- info: 'STACS2027.Runtimes.BoundedCost.OptSpanRAM.Q_zero_exponent' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptSpanRAM.Q_zero_exponent

/-- info: 'STACS2027.Runtimes.BoundedCost.OptSpanRAM.span_zero_cycles' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptSpanRAM.span_zero_cycles

/-- info: 'STACS2027.Runtimes.BoundedCost.OptSpanRAM.z_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptSpanRAM.z_mono

/-- info: 'STACS2027.Runtimes.BoundedCost.OptSpanRAM.Q_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptSpanRAM.Q_mono

/-- info: 'STACS2027.Runtimes.BoundedCost.OptSpanRAM.span_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptSpanRAM.span_mono

/-- info: 'STACS2027.Runtimes.BoundedCost.OptSpanRAM.header_le_span' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptSpanRAM.header_le_span

/-- info: 'STACS2027.Runtimes.BoundedCost.OptSpanRAM.arithmetic_cost_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptSpanRAM.arithmetic_cost_bound

/-- info: 'STACS2027.Runtimes.BoundedCost.OptSpanRAM.baseProgram' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptSpanRAM.baseProgram

/-- info: 'STACS2027.Runtimes.BoundedCost.OptSpanRAM.baseTime' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptSpanRAM.baseTime

/-- info: 'STACS2027.Runtimes.BoundedCost.OptSpanRAM.positiveProgram' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptSpanRAM.positiveProgram

/-- info: 'STACS2027.Runtimes.BoundedCost.OptSpanRAM.positiveTime' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptSpanRAM.positiveTime

/-- info: 'STACS2027.Runtimes.BoundedCost.OptSpanRAM.inputValues' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptSpanRAM.inputValues

/-- info: 'STACS2027.Runtimes.BoundedCost.OptSpanRAM.baseValues' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptSpanRAM.baseValues

/-- info: 'STACS2027.Runtimes.BoundedCost.OptSpanRAM.positiveValues' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptSpanRAM.positiveValues

/-- info: 'STACS2027.Runtimes.BoundedCost.OptSpanRAM.base_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptSpanRAM.base_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.OptSpanRAM.positive_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptSpanRAM.positive_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.OptSpanRAM.zeroProgram' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptSpanRAM.zeroProgram

/-- info: 'STACS2027.Runtimes.BoundedCost.OptSpanRAM.rawProgram' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptSpanRAM.rawProgram

/-- info: 'STACS2027.Runtimes.BoundedCost.OptSpanRAM.program' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptSpanRAM.program

/-- info: 'STACS2027.Runtimes.BoundedCost.OptSpanRAM.baseTime_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptSpanRAM.baseTime_eq

/-- info: 'STACS2027.Runtimes.BoundedCost.OptSpanRAM.positiveTime_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptSpanRAM.positiveTime_eq

/-- info: 'STACS2027.Runtimes.BoundedCost.OptSpanRAM.baseTime_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptSpanRAM.baseTime_le

/-- info: 'STACS2027.Runtimes.BoundedCost.OptSpanRAM.positiveTime_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptSpanRAM.positiveTime_le

/-- info: 'STACS2027.Runtimes.BoundedCost.OptSpanRAM.positiveValues_output' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptSpanRAM.positiveValues_output

/-- info: 'STACS2027.Runtimes.BoundedCost.OptSpanRAM.rawProgram_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptSpanRAM.rawProgram_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.OptSpanRAM.program_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptSpanRAM.program_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.OptSpanRAM.rawProgram_registers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptSpanRAM.rawProgram_registers

/-- info: 'STACS2027.Runtimes.BoundedCost.OptSpanRAM.program_registerFrame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptSpanRAM.program_registerFrame

/-- info: 'STACS2027.Runtimes.BoundedCost.OptStep.Done' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptStep.Done

/-- info: 'STACS2027.Runtimes.BoundedCost.OptStep.program' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptStep.program

/-- info: 'STACS2027.Runtimes.BoundedCost.OptStep.cost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptStep.cost

/-- info: 'STACS2027.Runtimes.BoundedCost.OptStep.callSpace_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptStep.callSpace_mono

/-- info: 'STACS2027.Runtimes.BoundedCost.OptStep.decide_registerFrame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptStep.decide_registerFrame

/-- info: 'STACS2027.Runtimes.BoundedCost.OptStep.decide_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptStep.decide_fixed

/-- info: 'STACS2027.Runtimes.BoundedCost.OptStep.step_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptStep.step_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.OptSpanRAM.optimization_total_cost_le_paper' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OptSpanRAM.optimization_total_cost_le_paper

/-- info: 'STACS2027.Runtimes.BoundedCost.optimalBudgetCost' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.optimalBudgetCost

/-- info: 'STACS2027.Runtimes.BoundedCost.optimalBudgetCost_sum_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.optimalBudgetCost_sum_le

/-- info: 'STACS2027.Runtimes.BoundedCost.OutI' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OutI

/-- info: 'STACS2027.Runtimes.BoundedCost.outBody_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.outBody_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.stepOut_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.stepOut_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.buildCost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.buildCost

/-- info: 'STACS2027.Runtimes.BoundedCost.formSpace' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.formSpace

/-- info: 'STACS2027.Runtimes.BoundedCost.build5_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.build5_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.outerBodyCost' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.outerBodyCost

/-- info: 'STACS2027.Runtimes.BoundedCost.not_mem_outerBody_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.not_mem_outerBody_word

/-- info: 'STACS2027.Runtimes.BoundedCost.outerBodyRAM_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.outerBodyRAM_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.OuterStart' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OuterStart

/-- info: 'STACS2027.Runtimes.BoundedCost.outerHeader_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.outerHeader_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.outerControlWrites' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.outerControlWrites

/-- info: 'STACS2027.Runtimes.BoundedCost.outerReadRegisters' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.outerReadRegisters

/-- info: 'STACS2027.Runtimes.BoundedCost.outerControlWrites_mod' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.outerControlWrites_mod

/-- info: 'STACS2027.Runtimes.BoundedCost.outerRep_indep_of_protected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.outerRep_indep_of_protected

/-- info: 'STACS2027.Runtimes.BoundedCost.outerRep_indep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.outerRep_indep

/-- info: 'STACS2027.Runtimes.BoundedCost.outerRep_excess_indep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.outerRep_excess_indep

/-- info: 'STACS2027.Runtimes.BoundedCost.outerGeometry_compilerLayout' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.outerGeometry_compilerLayout

/-- info: 'STACS2027.Runtimes.BoundedCost.OuterGeometry' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OuterGeometry

/-- info: 'STACS2027.Runtimes.BoundedCost.OuterBasic' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OuterBasic

/-- info: 'STACS2027.Runtimes.BoundedCost.OuterRep' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OuterRep

/-- info: 'STACS2027.Runtimes.BoundedCost.outerAnswerStep' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.outerAnswerStep

/-- info: 'STACS2027.Runtimes.BoundedCost.outerAnswerStep_fold' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.outerAnswerStep_fold

/-- info: 'STACS2027.Runtimes.BoundedCost.outerRep_setDigit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.outerRep_setDigit

/-- info: 'STACS2027.Runtimes.BoundedCost.globals_seed_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.globals_seed_frame

/-- info: 'STACS2027.Runtimes.BoundedCost.outerBasic_seed_transport' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.outerBasic_seed_transport

/-- info: 'STACS2027.Runtimes.BoundedCost.seedForced_snapshot' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.seedForced_snapshot

/-- info: 'STACS2027.Runtimes.BoundedCost.outerSeed_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.outerSeed_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.outerGeometry_special_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.outerGeometry_special_frame

/-- info: 'STACS2027.Runtimes.BoundedCost.outerGeometry_digits_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.outerGeometry_digits_frame

/-- info: 'STACS2027.Runtimes.BoundedCost.outerBasic_after_inner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.outerBasic_after_inner

/-- info: 'STACS2027.Runtimes.BoundedCost.outerRep_after_inner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.outerRep_after_inner

/-- info: 'STACS2027.Runtimes.BoundedCost.length_codes_ovS_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.length_codes_ovS_le

/-- info: 'STACS2027.Runtimes.BoundedCost.length_codes_ovJ_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.length_codes_ovJ_le

/-- info: 'STACS2027.Runtimes.BoundedCost.length_codes_ovI_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.length_codes_ovI_le

/-- info: 'STACS2027.Runtimes.BoundedCost.MarkI' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.MarkI

/-- info: 'STACS2027.Runtimes.BoundedCost.markBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.markBody_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.ScanI' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.ScanI

/-- info: 'STACS2027.Runtimes.BoundedCost.emitOv_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.emitOv_run

/-- info: 'STACS2027.Runtimes.BoundedCost.scanBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.scanBody_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.ClearI' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.ClearI

/-- info: 'STACS2027.Runtimes.BoundedCost.clearBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.clearBody_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.ovPair_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.ovPair_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.PairI' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.PairI

/-- info: 'STACS2027.Runtimes.BoundedCost.ovPairT_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.ovPairT_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.RowI' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.RowI

/-- info: 'STACS2027.Runtimes.BoundedCost.ovRow_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.ovRow_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.stepOv_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.stepOv_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.activeOccurrences_disable_sublist' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.activeOccurrences_disable_sublist

/-- info: 'STACS2027.Runtimes.BoundedCost.nodeAction_force_bound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.nodeAction_force_bound

/-- info: 'STACS2027.Runtimes.BoundedCost.pathStateRep_of_nodeUpdated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.pathStateRep_of_nodeUpdated

/-- info: 'STACS2027.Runtimes.BoundedCost.pathBasic_of_searchNodeResult' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.pathBasic_of_searchNodeResult

/-- info: 'STACS2027.Runtimes.BoundedCost.pathDigitsBase' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.pathDigitsBase

/-- info: 'STACS2027.Runtimes.BoundedCost.pathDepth' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.pathDepth

/-- info: 'STACS2027.Runtimes.BoundedCost.pathIndex' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.pathIndex

/-- info: 'STACS2027.Runtimes.BoundedCost.pathControlStep' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.pathControlStep

/-- info: 'STACS2027.Runtimes.BoundedCost.pathControl' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.pathControl

/-- info: 'STACS2027.Runtimes.BoundedCost.livePathStep' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.livePathStep

/-- info: 'STACS2027.Runtimes.BoundedCost.pathPrefix' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.pathPrefix

/-- info: 'STACS2027.Runtimes.BoundedCost.pathPrefix_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.pathPrefix_succ

/-- info: 'STACS2027.Runtimes.BoundedCost.pathControl_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.pathControl_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.renamedPathControlStep' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.renamedPathControlStep

/-- info: 'STACS2027.Runtimes.BoundedCost.renamedPathControl' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.renamedPathControl

/-- info: 'STACS2027.Runtimes.BoundedCost.renamedPathControl_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.renamedPathControl_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.renamedLivePathControl_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.renamedLivePathControl_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.flowReset_wregs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.flowReset_wregs

/-- info: 'STACS2027.Runtimes.BoundedCost.flowRelocated_wregs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.flowRelocated_wregs

/-- info: 'STACS2027.Runtimes.BoundedCost.not_mem_reusableCall_wregs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.not_mem_reusableCall_wregs

/-- info: 'STACS2027.Runtimes.BoundedCost.not_mem_searchNode_wregs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.not_mem_searchNode_wregs

/-- info: 'STACS2027.Runtimes.BoundedCost.not_mem_actualPath_wregs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.not_mem_actualPath_wregs

/-- info: 'STACS2027.Runtimes.BoundedCost.actualPath_registerFrame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.actualPath_registerFrame

/-- info: 'STACS2027.Runtimes.BoundedCost.PathBasic' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.PathBasic

/-- info: 'STACS2027.Runtimes.BoundedCost.PathStateRep' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.PathStateRep

/-- info: 'STACS2027.Runtimes.BoundedCost.ActualPathRep' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.ActualPathRep

/-- info: 'STACS2027.Runtimes.BoundedCost.actualPathRep_live' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.actualPathRep_live

/-- info: 'STACS2027.Runtimes.BoundedCost.actualPathRep_control' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.actualPathRep_control

/-- info: 'STACS2027.Runtimes.BoundedCost.actualPathRep_indep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.actualPathRep_indep

/-- info: 'STACS2027.Runtimes.BoundedCost.PathRestore.activeSnapshot' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.PathRestore.activeSnapshot

/-- info: 'STACS2027.Runtimes.BoundedCost.PathRestore.forcedSnapshot' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.PathRestore.forcedSnapshot

/-- info: 'STACS2027.Runtimes.BoundedCost.PathRestore.globalBudget' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.PathRestore.globalBudget

/-- info: 'STACS2027.Runtimes.BoundedCost.PathRestore.specialDeleted' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.PathRestore.specialDeleted

/-- info: 'STACS2027.Runtimes.BoundedCost.PathRestore.truthLength' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.PathRestore.truthLength

/-- info: 'STACS2027.Runtimes.BoundedCost.PathRestore.activeReady' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.PathRestore.activeReady

/-- info: 'STACS2027.Runtimes.BoundedCost.PathRestore.forcedReady' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.PathRestore.forcedReady

/-- info: 'STACS2027.Runtimes.BoundedCost.PathRestore.finish' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.PathRestore.finish

/-- info: 'STACS2027.Runtimes.BoundedCost.PathRestore.program' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.PathRestore.program

/-- info: 'STACS2027.Runtimes.BoundedCost.PathRestore.Globals' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.PathRestore.Globals

/-- info: 'STACS2027.Runtimes.BoundedCost.PathRestore.restoredMemory' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.PathRestore.restoredMemory

/-- info: 'STACS2027.Runtimes.BoundedCost.PathRestore.program_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.PathRestore.program_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.maskWords' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.maskWords

/-- info: 'STACS2027.Runtimes.BoundedCost.forcedWords' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.forcedWords

/-- info: 'STACS2027.Runtimes.BoundedCost.maskWords_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.maskWords_length

/-- info: 'STACS2027.Runtimes.BoundedCost.forcedWords_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.forcedWords_length

/-- info: 'STACS2027.Runtimes.BoundedCost.MaskTable.array' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.MaskTable.array

/-- info: 'STACS2027.Runtimes.BoundedCost.ForcedTable.array' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.ForcedTable.array

/-- info: 'STACS2027.Runtimes.BoundedCost.PathRestoreMemoryFrame' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.PathRestoreMemoryFrame

/-- info: 'STACS2027.Runtimes.BoundedCost.pathRestore_tables' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.pathRestore_tables

/-- info: 'STACS2027.Runtimes.BoundedCost.pathRestore_array' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.pathRestore_array

/-- info: 'STACS2027.Runtimes.BoundedCost.pathRestore_truth' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.pathRestore_truth

/-- info: 'STACS2027.Runtimes.BoundedCost.SearchPathState' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.SearchPathState

/-- info: 'STACS2027.Runtimes.BoundedCost.SearchPathState.live' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.SearchPathState.live

/-- info: 'STACS2027.Runtimes.BoundedCost.SearchPathState.answer' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.SearchPathState.answer

/-- info: 'STACS2027.Runtimes.BoundedCost.annotatedPathStep' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.annotatedPathStep

/-- info: 'STACS2027.Runtimes.BoundedCost.annotatedPathStep_live' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.annotatedPathStep_live

/-- info: 'STACS2027.Runtimes.BoundedCost.foldPath_failed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.foldPath_failed

/-- info: 'STACS2027.Runtimes.BoundedCost.foldPath_answered' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.foldPath_answered

/-- info: 'STACS2027.Runtimes.BoundedCost.foldPath_answer' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.foldPath_answer

/-- info: 'STACS2027.Runtimes.BoundedCost.range_map_getD' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.range_map_getD

/-- info: 'STACS2027.Runtimes.BoundedCost.pathPrefix_answer' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.pathPrefix_answer

/-- info: 'STACS2027.Runtimes.BoundedCost.pcEmit_run5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.pcEmit_run5

/-- info: 'STACS2027.Runtimes.BoundedCost.PcInv5' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.PcInv5

/-- info: 'STACS2027.Runtimes.BoundedCost.PcInv5.indep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.PcInv5.indep

/-- info: 'STACS2027.Runtimes.BoundedCost.pcBody_spec5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.pcBody_spec5

/-- info: 'STACS2027.Runtimes.BoundedCost.MInv5' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.MInv5

/-- info: 'STACS2027.Runtimes.BoundedCost.OInv5' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OInv5

/-- info: 'STACS2027.Runtimes.BoundedCost.pcRowA_spec5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.pcRowA_spec5

/-- info: 'STACS2027.Runtimes.BoundedCost.pcRow_spec5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.pcRow_spec5

/-- info: 'STACS2027.Runtimes.BoundedCost.pcCopy_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.pcCopy_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.length_codes_pcs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.length_codes_pcs

/-- info: 'STACS2027.Runtimes.BoundedCost.SeenPost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.SeenPost

/-- info: 'STACS2027.Runtimes.BoundedCost.stepPcs_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.stepPcs_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.prefixCheck' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.prefixCheck

/-- info: 'STACS2027.Runtimes.BoundedCost.PrefixCheckGlobals' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.PrefixCheckGlobals

/-- info: 'STACS2027.Runtimes.BoundedCost.PrefixCheckFrame' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.PrefixCheckFrame

/-- info: 'STACS2027.Runtimes.BoundedCost.PrefixCheckResult' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.PrefixCheckResult

/-- info: 'STACS2027.Runtimes.BoundedCost.prefixCheckGlobals_indep_copy' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.prefixCheckGlobals_indep_copy

/-- info: 'STACS2027.Runtimes.BoundedCost.prefixCheckGlobals_indep_mask' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.prefixCheckGlobals_indep_mask

/-- info: 'STACS2027.Runtimes.BoundedCost.prefixCheckGlobals_indep_scan' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.prefixCheckGlobals_indep_scan

/-- info: 'STACS2027.Runtimes.BoundedCost.prefixCheck_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.prefixCheck_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.prefixCheckCaller' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.prefixCheckCaller

/-- info: 'STACS2027.Runtimes.BoundedCost.prefixCheckCaller_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.prefixCheckCaller_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.Compiler.prefixLoop_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Compiler.prefixLoop_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.Compiler.finish_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Compiler.finish_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.prefixMaskIndex' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.prefixMaskIndex

/-- info: 'STACS2027.Runtimes.BoundedCost.prefixMaskTemporary' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.prefixMaskTemporary

/-- info: 'STACS2027.Runtimes.BoundedCost.prefixMaskValue' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.prefixMaskValue

/-- info: 'STACS2027.Runtimes.BoundedCost.prefixMaskActiveBase' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.prefixMaskActiveBase

/-- info: 'STACS2027.Runtimes.BoundedCost.prefixMaskClauseCount' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.prefixMaskClauseCount

/-- info: 'STACS2027.Runtimes.BoundedCost.prefixMaskProcessed' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.prefixMaskProcessed

/-- info: 'STACS2027.Runtimes.BoundedCost.prefixMaskBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.prefixMaskBody

/-- info: 'STACS2027.Runtimes.BoundedCost.prefixMaskProgram' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.prefixMaskProgram

/-- info: 'STACS2027.Runtimes.BoundedCost.PrefixMaskGlobals' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.PrefixMaskGlobals

/-- info: 'STACS2027.Runtimes.BoundedCost.PrefixMaskInv' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.PrefixMaskInv

/-- info: 'STACS2027.Runtimes.BoundedCost.prefixMaskBody_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.prefixMaskBody_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.prefixMaskProgram_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.prefixMaskProgram_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.prefixOccurrences' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.prefixOccurrences

/-- info: 'STACS2027.Runtimes.BoundedCost.prefixOccurrences_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.prefixOccurrences_length

/-- info: 'STACS2027.Runtimes.BoundedCost.prefixMask_table' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.prefixMask_table

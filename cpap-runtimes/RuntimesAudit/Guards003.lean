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

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.vBlk' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.vBlk

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.vBlk_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.vBlk_spec

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.MemB2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.MemB2

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.rSet' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.rSet

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.cnSet' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.cnSet

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.rnSet' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.rnSet

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.cornBlk' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.cornBlk

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.bordBlk' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.bordBlk

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.bordBlk_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.bordBlk_spec

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.MemB3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.MemB3

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.znSet' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.znSet

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.znBlk' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.znBlk

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.znBlk_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.znBlk_spec

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.qBlk' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.qBlk

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.RQ' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.RQ

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.RQ_regIndep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.RQ_regIndep

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.qBlk_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.qBlk_spec

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.finBlk' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.finBlk

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.finBlk_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.finBlk_spec

/-- info: 'STACS2027.Runtimes.QPRam.relaxSolverProg' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.relaxSolverProg

/-- info: 'STACS2027.Runtimes.QPRam.Top.tk_le_input' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Top.tk_le_input

/-- info: 'STACS2027.Runtimes.QPRam.Top.solveExact_nil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Top.solveExact_nil

/-- info: 'STACS2027.Runtimes.QPRam.Top.solveExact_cons' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Top.solveExact_cons

/-- info: 'STACS2027.Runtimes.QPRam.Top.relaxSolver_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Top.relaxSolver_exec

/-- info: 'STACS2027.Runtimes.QPRam.Top.solveExact_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Top.solveExact_shape

/-- info: 'STACS2027.Runtimes.QPRam.relaxSolver_ram_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.relaxSolver_ram_of

/-- info: 'STACS2027.Runtimes.QPRam.relaxSolver_ram_optimal_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.relaxSolver_ram_optimal_of

/-- info: 'STACS2027.Runtimes.QPRam.Parse.cost1' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.cost1

/-- info: 'STACS2027.Runtimes.QPRam.Parse.cost2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.cost2

/-- info: 'STACS2027.Runtimes.QPRam.Parse.cost3' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.cost3

/-- info: 'STACS2027.Runtimes.QPRam.Parse.cost4' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.cost4

/-- info: 'STACS2027.Runtimes.QPRam.Parse.cost5' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.cost5

/-- info: 'STACS2027.Runtimes.QPRam.Parse.cost6' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.cost6

/-- info: 'STACS2027.Runtimes.QPRam.Parse.st1_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.st1_spec

/-- info: 'STACS2027.Runtimes.QPRam.Parse.st2_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.st2_spec

/-- info: 'STACS2027.Runtimes.QPRam.Parse.st3_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.st3_spec

/-- info: 'STACS2027.Runtimes.QPRam.Parse.st4_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.st4_spec

/-- info: 'STACS2027.Runtimes.QPRam.Parse.st5_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.st5_spec

/-- info: 'STACS2027.Runtimes.QPRam.Parse.st6_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.st6_spec

/-- info: 'STACS2027.Runtimes.QPRam.Parse.CRegs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.CRegs

/-- info: 'STACS2027.Runtimes.QPRam.Parse.constCost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.constCost

/-- info: 'STACS2027.Runtimes.QPRam.Parse.stepConsts_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.stepConsts_spec

/-- info: 'STACS2027.Runtimes.QPRam.Parse.size_le_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.size_le_self

/-- info: 'STACS2027.Runtimes.QPRam.Parse.mulCost_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.mulCost_le

/-- info: 'STACS2027.Runtimes.QPRam.Parse.mulCost_le_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.mulCost_le_of

/-- info: 'STACS2027.Runtimes.QPRam.Parse.bigE_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.bigE_lt

/-- info: 'STACS2027.Runtimes.QPRam.Parse.clog_le_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.clog_le_self

/-- info: 'STACS2027.Runtimes.QPRam.Parse.constCost_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.constCost_le

/-- info: 'STACS2027.Runtimes.QPRam.Parse.hMK' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.hMK

/-- info: 'STACS2027.Runtimes.QPRam.Parse.hK2' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.hK2

/-- info: 'STACS2027.Runtimes.QPRam.Parse.hB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.hB

/-- info: 'STACS2027.Runtimes.QPRam.Parse.hJB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.hJB

/-- info: 'STACS2027.Runtimes.QPRam.Parse.hCB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.hCB

/-- info: 'STACS2027.Runtimes.QPRam.Parse.hCol' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.hCol

/-- info: 'STACS2027.Runtimes.QPRam.Parse.hA' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.hA

/-- info: 'STACS2027.Runtimes.QPRam.Parse.hJA' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.hJA

/-- info: 'STACS2027.Runtimes.QPRam.Parse.hCA' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.hCA

/-- info: 'STACS2027.Runtimes.QPRam.Parse.hRow' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.hRow

/-- info: 'STACS2027.Runtimes.QPRam.Parse.hS' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.hS

/-- info: 'STACS2027.Runtimes.QPRam.Parse.hP' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.hP

/-- info: 'STACS2027.Runtimes.QPRam.Parse.hQ' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.hQ

/-- info: 'STACS2027.Runtimes.QPRam.Parse.hId' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.hId

/-- info: 'STACS2027.Runtimes.QPRam.Parse.hX' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.hX

/-- info: 'STACS2027.Runtimes.QPRam.Parse.hCnt' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.hCnt

/-- info: 'STACS2027.Runtimes.QPRam.Parse.hV' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.hV

/-- info: 'STACS2027.Runtimes.QPRam.Parse.hSz' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.hSz

/-- info: 'STACS2027.Runtimes.QPRam.Parse.nN' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.nN

/-- info: 'STACS2027.Runtimes.QPRam.Parse.nE' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.nE

/-- info: 'STACS2027.Runtimes.QPRam.Parse.bEI' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.bEI

/-- info: 'STACS2027.Runtimes.QPRam.Parse.bMK' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.bMK

/-- info: 'STACS2027.Runtimes.QPRam.Parse.bH' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.bH

/-- info: 'STACS2027.Runtimes.QPRam.Parse.bEnd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.bEnd

/-- info: 'STACS2027.Runtimes.QPRam.Parse.hlayout' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.hlayout

/-- info: 'STACS2027.Runtimes.QPRam.Parse.hfits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.hfits

/-- info: 'STACS2027.Runtimes.QPRam.Parse.hcell_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.hcell_lt

/-- info: 'STACS2027.Runtimes.QPRam.Parse.hcell_inj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.hcell_inj

/-- info: 'STACS2027.Runtimes.QPRam.Parse.HPart' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.HPart

/-- info: 'STACS2027.Runtimes.QPRam.Parse.HPart.congr' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.HPart.congr

/-- info: 'STACS2027.Runtimes.QPRam.Parse.HPart.upd_of_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.HPart.upd_of_lt

/-- info: 'STACS2027.Runtimes.QPRam.Parse.HPart.set' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.HPart.set

/-- info: 'STACS2027.Runtimes.QPRam.Parse.HM' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.HM

/-- info: 'STACS2027.Runtimes.QPRam.Parse.HM.mark' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.HM.mark

/-- info: 'STACS2027.Runtimes.QPRam.Parse.HM.hset' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.HM.hset

/-- info: 'STACS2027.Runtimes.QPRam.Parse.HM.congrH' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.HM.congrH

/-- info: 'STACS2027.Runtimes.QPRam.Parse.HM.congrM' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.HM.congrM

/-- info: 'STACS2027.Runtimes.QPRam.Parse.nextP' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.nextP

/-- info: 'STACS2027.Runtimes.QPRam.Parse.startP' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.startP

/-- info: 'STACS2027.Runtimes.QPRam.Parse.markBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.markBody

/-- info: 'STACS2027.Runtimes.QPRam.Parse.markWalk' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.markWalk

/-- info: 'STACS2027.Runtimes.QPRam.Parse.cntBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.cntBody

/-- info: 'STACS2027.Runtimes.QPRam.Parse.cntWalk' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.cntWalk

/-- info: 'STACS2027.Runtimes.QPRam.Parse.advA' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.advA

/-- info: 'STACS2027.Runtimes.QPRam.Parse.innerBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.innerBody

/-- info: 'STACS2027.Runtimes.QPRam.Parse.innerInit' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.innerInit

/-- info: 'STACS2027.Runtimes.QPRam.Parse.advB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.advB

/-- info: 'STACS2027.Runtimes.QPRam.Parse.outerBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.outerBody

/-- info: 'STACS2027.Runtimes.QPRam.Parse.hAlloc' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.hAlloc

/-- info: 'STACS2027.Runtimes.QPRam.Parse.hRegs' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.hRegs

/-- info: 'STACS2027.Runtimes.QPRam.Parse.stepH' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.stepH

/-- info: 'STACS2027.Runtimes.QPRam.Parse.HG' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.HG

/-- info: 'STACS2027.Runtimes.QPRam.Parse.WH' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.WH

/-- info: 'STACS2027.Runtimes.QPRam.Parse.HG.regIndep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.HG.regIndep

/-- info: 'STACS2027.Runtimes.QPRam.Parse.BR' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.BR

/-- info: 'STACS2027.Runtimes.QPRam.Parse.AR' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.AR

/-- info: 'STACS2027.Runtimes.QPRam.Parse.hv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.hv

/-- info: 'STACS2027.Runtimes.QPRam.Parse.WInv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.WInv

/-- info: 'STACS2027.Runtimes.QPRam.Parse.IInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.IInv

/-- info: 'STACS2027.Runtimes.QPRam.Parse.CInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.CInv

/-- info: 'STACS2027.Runtimes.QPRam.Parse.OInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.OInv

/-- info: 'STACS2027.Runtimes.QPRam.Parse.config_ext' depends on axioms: [Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.config_ext

/-- info: 'STACS2027.Runtimes.QPRam.Parse.run_nextP' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.run_nextP

/-- info: 'STACS2027.Runtimes.QPRam.Parse.run_startP' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.run_startP

/-- info: 'STACS2027.Runtimes.QPRam.Parse.idx_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.idx_succ

/-- info: 'STACS2027.Runtimes.QPRam.Parse.markBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.markBody_spec

/-- info: 'STACS2027.Runtimes.QPRam.Parse.Tmw' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.Tmw

/-- info: 'STACS2027.Runtimes.QPRam.Parse.markWalk_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.markWalk_spec

/-- info: 'STACS2027.Runtimes.QPRam.Parse.cntBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.cntBody_spec

/-- info: 'STACS2027.Runtimes.QPRam.Parse.Tcw' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.Tcw

/-- info: 'STACS2027.Runtimes.QPRam.Parse.cntWalk_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.cntWalk_spec

/-- info: 'STACS2027.Runtimes.QPRam.Parse.hv_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.hv_succ

/-- info: 'STACS2027.Runtimes.QPRam.Parse.advA_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.advA_spec

/-- info: 'STACS2027.Runtimes.QPRam.Parse.Tin' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.Tin

/-- info: 'STACS2027.Runtimes.QPRam.Parse.innerLoop_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.innerLoop_spec

/-- info: 'STACS2027.Runtimes.QPRam.Parse.hv_last' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.hv_last

/-- info: 'STACS2027.Runtimes.QPRam.Parse.advB_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.advB_spec

/-- info: 'STACS2027.Runtimes.QPRam.Parse.innerInit_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.innerInit_spec

/-- info: 'STACS2027.Runtimes.QPRam.Parse.Tout' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.Tout

/-- info: 'STACS2027.Runtimes.QPRam.Parse.outerBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.outerBody_spec

/-- info: 'STACS2027.Runtimes.QPRam.Parse.outerLoop_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.outerLoop_spec

/-- info: 'STACS2027.Runtimes.QPRam.Parse.HA0' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.HA0

/-- info: 'STACS2027.Runtimes.QPRam.Parse.HA1' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.HA1

/-- info: 'STACS2027.Runtimes.QPRam.Parse.FP' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.FP

/-- info: 'STACS2027.Runtimes.QPRam.Parse.hAlloc_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.hAlloc_spec

/-- info: 'STACS2027.Runtimes.QPRam.Parse.hRegs_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.hRegs_spec

/-- info: 'STACS2027.Runtimes.QPRam.Parse.Th' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.Th

/-- info: 'STACS2027.Runtimes.QPRam.Parse.stepH_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.stepH_spec

/-- info: 'STACS2027.Runtimes.QPRam.Parse.hv_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.hv_full

/-- info: 'STACS2027.Runtimes.QPRam.Parse.hMem_of_HM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.hMem_of_HM

/-- info: 'STACS2027.Runtimes.QPRam.Parse.HTF' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.HTF

/-- info: 'STACS2027.Runtimes.QPRam.Parse.HTF.of_HT' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.HTF.of_HT

/-- info: 'STACS2027.Runtimes.QPRam.Parse.HTF.mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.HTF.mono

/-- info: 'STACS2027.Runtimes.QPRam.Parse.HTF.seq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.HTF.seq

/-- info: 'STACS2027.Runtimes.QPRam.Parse.HTF.frameReg' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.HTF.frameReg

/-- info: 'STACS2027.Runtimes.QPRam.Parse.HTF.forUpC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.HTF.forUpC

/-- info: 'STACS2027.Runtimes.QPRam.Parse.KS' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.KS

/-- info: 'STACS2027.Runtimes.QPRam.Parse.KS.get' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.KS.get

/-- info: 'STACS2027.Runtimes.QPRam.Parse.KS.sub' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.KS.sub

/-- info: 'STACS2027.Runtimes.QPRam.Parse.KS.indep' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.KS.indep

/-- info: 'STACS2027.Runtimes.QPRam.Parse.KS.update' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.KS.update

/-- info: 'STACS2027.Runtimes.QPRam.Parse.KS.add' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.KS.add

/-- info: 'STACS2027.Runtimes.QPRam.Parse.KS.addc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.KS.addc

/-- info: 'STACS2027.Runtimes.QPRam.Parse.KS.subc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.KS.subc

/-- info: 'STACS2027.Runtimes.QPRam.Parse.KS.mov' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.KS.mov

/-- info: 'STACS2027.Runtimes.QPRam.Parse.KS.const' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.KS.const

/-- info: 'STACS2027.Runtimes.QPRam.Parse.KS.mulN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.KS.mulN

/-- info: 'STACS2027.Runtimes.QPRam.Parse.clogLoop' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.clogLoop

/-- info: 'STACS2027.Runtimes.QPRam.Parse.clogCost' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.clogCost

/-- info: 'STACS2027.Runtimes.QPRam.Parse.ClogInv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.ClogInv

/-- info: 'STACS2027.Runtimes.QPRam.Parse.clogLoop_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.clogLoop_spec

/-- info: 'STACS2027.Runtimes.QPRam.Parse.KS.clog' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.KS.clog

/-- info: 'STACS2027.Runtimes.QPRam.Parse.tZero' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.tZero

/-- info: 'STACS2027.Runtimes.QPRam.Parse.parseRest' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.parseRest

/-- info: 'STACS2027.Runtimes.QPRam.Parse.ParsePost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.ParsePost

/-- info: 'STACS2027.Runtimes.QPRam.Parse.frontCost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.frontCost

/-- info: 'STACS2027.Runtimes.QPRam.Parse.restCost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.restCost

/-- info: 'STACS2027.Runtimes.QPRam.Parse.consts_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.consts_spec

/-- info: 'STACS2027.Runtimes.QPRam.Parse.front_parse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.front_parse

/-- info: 'STACS2027.Runtimes.QPRam.Parse.rest_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.rest_spec

/-- info: 'STACS2027.Runtimes.QPRam.Parse.tZero_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.tZero_spec

/-- info: 'STACS2027.Runtimes.QPRam.Parse.branchCost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.branchCost

/-- info: 'STACS2027.Runtimes.QPRam.Parse.branchEnd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.branchEnd

/-- info: 'STACS2027.Runtimes.QPRam.Parse.parseProg_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.parseProg_spec

/-- info: 'STACS2027.Runtimes.QPRam.Parse.Th_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.Th_le

/-- info: 'STACS2027.Runtimes.QPRam.Parse.input_len' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.input_len

/-- info: 'STACS2027.Runtimes.QPRam.parseProg' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.parseProg

/-- info: 'STACS2027.Runtimes.QPRam.parse_ramB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.parse_ramB

/-- info: 'STACS2027.Runtimes.QPRam.Parse.opos' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.opos

/-- info: 'STACS2027.Runtimes.QPRam.Parse.occ' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.occ

/-- info: 'STACS2027.Runtimes.QPRam.Parse.opos_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.opos_eq

/-- info: 'STACS2027.Runtimes.QPRam.Parse.opos_lt' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.opos_lt

/-- info: 'STACS2027.Runtimes.QPRam.Parse.opos_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.opos_zero

/-- info: 'STACS2027.Runtimes.QPRam.Parse.opos_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.opos_succ

/-- info: 'STACS2027.Runtimes.QPRam.Parse.opos_inj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.opos_inj

/-- info: 'STACS2027.Runtimes.QPRam.Parse.div_mul_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.div_mul_lt

/-- info: 'STACS2027.Runtimes.QPRam.Parse.occ_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.occ_lt

/-- info: 'STACS2027.Runtimes.QPRam.Parse.mem_selected_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.mem_selected_iff

/-- info: 'STACS2027.Runtimes.QPRam.Parse.mk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.mk

/-- info: 'STACS2027.Runtimes.QPRam.Parse.mark' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.mark

/-- info: 'STACS2027.Runtimes.QPRam.Parse.hc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.hc

/-- info: 'STACS2027.Runtimes.QPRam.Parse.mk_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.mk_zero

/-- info: 'STACS2027.Runtimes.QPRam.Parse.mk_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.mk_succ

/-- info: 'STACS2027.Runtimes.QPRam.Parse.mk_unmark' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.mk_unmark

/-- info: 'STACS2027.Runtimes.QPRam.Parse.hc_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.hc_zero

/-- info: 'STACS2027.Runtimes.QPRam.Parse.hc_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.hc_succ

/-- info: 'STACS2027.Runtimes.QPRam.Parse.path_cycles' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.path_cycles

/-- info: 'STACS2027.Runtimes.QPRam.Parse.cnt_instOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.cnt_instOf

/-- info: 'STACS2027.Runtimes.QPRam.Parse.H_instOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.H_instOf

/-- info: 'STACS2027.Runtimes.QPRam.Parse.mark_occ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.mark_occ

/-- info: 'STACS2027.Runtimes.QPRam.Parse.Hflat_instOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.Hflat_instOf

/-- info: 'STACS2027.Runtimes.QPRam.qT' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.qT

/-- info: 'STACS2027.Runtimes.QPRam.qK' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.qK

/-- info: 'STACS2027.Runtimes.QPRam.qKT' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.qKT

/-- info: 'STACS2027.Runtimes.QPRam.qN' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.qN

/-- info: 'STACS2027.Runtimes.QPRam.qD' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.qD

/-- info: 'STACS2027.Runtimes.QPRam.qM' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.qM

/-- info: 'STACS2027.Runtimes.QPRam.qIt' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.qIt

/-- info: 'STACS2027.Runtimes.QPRam.qP' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.qP

/-- info: 'STACS2027.Runtimes.QPRam.qE' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.qE

/-- info: 'STACS2027.Runtimes.QPRam.qCN' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.qCN

/-- info: 'STACS2027.Runtimes.QPRam.qCD' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.qCD

/-- info: 'STACS2027.Runtimes.QPRam.qBH' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.qBH

/-- info: 'STACS2027.Runtimes.QPRam.qBX' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.qBX

/-- info: 'STACS2027.Runtimes.QPRam.div_lt_of_lt_tk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.div_lt_of_lt_tk

/-- info: 'STACS2027.Runtimes.QPRam.mod_lt_of_lt_tk' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.mod_lt_of_lt_tk

/-- info: 'STACS2027.Runtimes.QPRam.flat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.flat

/-- info: 'STACS2027.Runtimes.QPRam.Hflat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Hflat

/-- info: 'STACS2027.Runtimes.QPRam.HMem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.HMem

/-- info: 'STACS2027.Runtimes.QPRam.hCells' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.hCells

/-- info: 'STACS2027.Runtimes.QPRam.flat_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.flat_apply

/-- info: 'STACS2027.Runtimes.QPRam.Hflat_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Hflat_apply

/-- info: 'STACS2027.Runtimes.QPRam.sum_range_flat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.sum_range_flat

/-- info: 'STACS2027.Runtimes.QPRam.mulVec_Hflat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.mulVec_Hflat

/-- info: 'STACS2027.Runtimes.QPRam.QRegs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.QRegs

/-- info: 'STACS2027.Runtimes.QPRam.QIn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.QIn

/-- info: 'STACS2027.Runtimes.QPRam.QMid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.QMid

/-- info: 'STACS2027.Runtimes.QPRam.outList' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.outList

/-- info: 'STACS2027.Runtimes.QPRam.instOf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.instOf

/-- info: 'STACS2027.Runtimes.QPRam.ParseSpecRamB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.ParseSpecRamB

/-- info: 'STACS2027.Runtimes.QPRam.PhaseERamB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.PhaseERamB

/-- info: 'STACS2027.Runtimes.QPRam.PhaseKMORamB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.PhaseKMORamB

/-- info: 'STACS2027.Runtimes.QPRam.relaxSolverMachine' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.relaxSolverMachine

/-- info: 'STACS2027.Runtimes.QPRam.relaxSolver_ram_space_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.relaxSolver_ram_space_of

/-- info: 'STACS2027.Runtimes.QPRam.relaxSolver_ram_optimal_space_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.relaxSolver_ram_optimal_space_of

/-- info: 'STACS2027.Runtimes.QPRam.relaxSolver_ram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.relaxSolver_ram

/-- info: 'STACS2027.Runtimes.QPRam.relaxSolver_ram_optimal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.relaxSolver_ram_optimal

/-- info: 'STACS2027.Runtimes.Arith.SArr' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.SArr

/-- info: 'STACS2027.Runtimes.Arith.sw' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.sw

/-- info: 'STACS2027.Runtimes.Arith.wrArr' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.wrArr

/-- info: 'STACS2027.Runtimes.Arith.sw_apply_of_ne' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.sw_apply_of_ne

/-- info: 'STACS2027.Runtimes.Arith.smem_sw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.smem_sw

/-- info: 'STACS2027.Runtimes.Arith.wrArr_of_out' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.wrArr_of_out

/-- info: 'STACS2027.Runtimes.Arith.sarr_wrArr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.sarr_wrArr

/-- info: 'STACS2027.Runtimes.Arith.sameOn_wrArr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.sameOn_wrArr

/-- info: 'STACS2027.Runtimes.Arith.zeroFrom_wrArr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.zeroFrom_wrArr

/-- info: 'STACS2027.Runtimes.Arith.wrArr_succ' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.wrArr_succ

/-- info: 'STACS2027.Runtimes.Arith.addr_lt_of_stride' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.addr_lt_of_stride

/-- info: 'STACS2027.Runtimes.Arith.addr_lt_rows' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.addr_lt_rows

/-- info: 'STACS2027.Runtimes.Arith.addr_lt_cols' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.addr_lt_cols

/-- info: 'STACS2027.Runtimes.Arith.vK' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.vK

/-- info: 'STACS2027.Runtimes.Arith.vN' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.vN

/-- info: 'STACS2027.Runtimes.Arith.vPA' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.vPA

/-- info: 'STACS2027.Runtimes.Arith.vSA' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.vSA

/-- info: 'STACS2027.Runtimes.Arith.vPX' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.vPX

/-- info: 'STACS2027.Runtimes.Arith.vSX' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.vSX

/-- info: 'STACS2027.Runtimes.Arith.vAcc' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.vAcc

/-- info: 'STACS2027.Runtimes.Arith.vR' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.vR

/-- info: 'STACS2027.Runtimes.Arith.vRow' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.vRow

/-- info: 'STACS2027.Runtimes.Arith.vSI' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.vSI

/-- info: 'STACS2027.Runtimes.Arith.vPU' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.vPU

/-- info: 'STACS2027.Runtimes.Arith.vX0' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.vX0

/-- info: 'STACS2027.Runtimes.Arith.coreW' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.coreW

/-- info: 'STACS2027.Runtimes.Arith.dotW' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.dotW

/-- info: 'STACS2027.Runtimes.Arith.dotBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.dotBody

/-- info: 'STACS2027.Runtimes.Arith.dotCore' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.dotCore

/-- info: 'STACS2027.Runtimes.Arith.DF' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.DF

/-- info: 'STACS2027.Runtimes.Arith.DF_indep' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.DF_indep

/-- info: 'STACS2027.Runtimes.Arith.DG' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.DG

/-- info: 'STACS2027.Runtimes.Arith.DG_indep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.DG_indep

/-- info: 'STACS2027.Runtimes.Arith.dotBody_specB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.dotBody_specB

/-- info: 'STACS2027.Runtimes.Arith.DotInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.DotInv

/-- info: 'STACS2027.Runtimes.Arith.dotCore_specB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.dotCore_specB

/-- info: 'STACS2027.Runtimes.Arith.mvBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.mvBody

/-- info: 'STACS2027.Runtimes.Arith.mvCore' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.mvCore

/-- info: 'STACS2027.Runtimes.Arith.mvW' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.mvW

/-- info: 'STACS2027.Runtimes.Arith.mulVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.mulVec

/-- info: 'STACS2027.Runtimes.Arith.MvInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.MvInv

/-- info: 'STACS2027.Runtimes.Arith.mvCore_specB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.mvCore_specB

/-- info: 'STACS2027.Runtimes.Arith.rnd' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.rnd

/-- info: 'STACS2027.Runtimes.Arith.GoodDiv' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.GoodDiv

/-- info: 'STACS2027.Runtimes.Arith.vAl' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.vAl

/-- info: 'STACS2027.Runtimes.Arith.vBe' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.vBe

/-- info: 'STACS2027.Runtimes.Arith.vGa' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.vGa

/-- info: 'STACS2027.Runtimes.Arith.vB0' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.vB0

/-- info: 'STACS2027.Runtimes.Arith.divStep' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.divStep

/-- info: 'STACS2027.Runtimes.Arith.divStep_specB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.divStep_specB

/-- info: 'STACS2027.Runtimes.Arith.size_lin_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.size_lin_le

/-- info: 'STACS2027.Runtimes.Arith.size_mul_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.size_mul_le

/-- info: 'STACS2027.Runtimes.Arith.linW' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.linW

/-- info: 'STACS2027.Runtimes.Arith.linBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.linBody

/-- info: 'STACS2027.Runtimes.Arith.linCore' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.linCore

/-- info: 'STACS2027.Runtimes.Arith.LR' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.LR

/-- info: 'STACS2027.Runtimes.Arith.LF' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.LF

/-- info: 'STACS2027.Runtimes.Arith.LR_regIndep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.LR_regIndep

/-- info: 'STACS2027.Runtimes.Arith.LF_indep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.LF_indep

/-- info: 'STACS2027.Runtimes.Arith.linBody_specB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.linBody_specB

/-- info: 'STACS2027.Runtimes.Arith.linNew' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.linNew

/-- info: 'STACS2027.Runtimes.Arith.LInv' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.LInv

/-- info: 'STACS2027.Runtimes.Arith.linCore_specB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.linCore_specB

/-- info: 'STACS2027.Runtimes.Arith.wrRows' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.wrRows

/-- info: 'STACS2027.Runtimes.Arith.wrRows_of_out' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.wrRows_of_out

/-- info: 'STACS2027.Runtimes.Arith.sameOn_wrRows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.sameOn_wrRows

/-- info: 'STACS2027.Runtimes.Arith.zeroFrom_wrRows' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.zeroFrom_wrRows

/-- info: 'STACS2027.Runtimes.Arith.sarr_wrRows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.sarr_wrRows

/-- info: 'STACS2027.Runtimes.Arith.r1New' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.r1New

/-- info: 'STACS2027.Runtimes.Arith.r1Body' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.r1Body

/-- info: 'STACS2027.Runtimes.Arith.r1Core' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.r1Core

/-- info: 'STACS2027.Runtimes.Arith.r1W' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.r1W

/-- info: 'STACS2027.Runtimes.Arith.R1Inv' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.R1Inv

/-- info: 'STACS2027.Runtimes.Arith.r1Core_specB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.r1Core_specB

/-- info: 'STACS2027.Runtimes.Arith.vDe' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.vDe

/-- info: 'STACS2027.Runtimes.Arith.axW' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.axW

/-- info: 'STACS2027.Runtimes.Arith.axBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.axBody

/-- info: 'STACS2027.Runtimes.Arith.axCore' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.axCore

/-- info: 'STACS2027.Runtimes.Arith.AR' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.AR

/-- info: 'STACS2027.Runtimes.Arith.AR_regIndep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.AR_regIndep

/-- info: 'STACS2027.Runtimes.Arith.axBody_specB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.axBody_specB

/-- info: 'STACS2027.Runtimes.Arith.axNew' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.axNew

/-- info: 'STACS2027.Runtimes.Arith.AInv' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.AInv

/-- info: 'STACS2027.Runtimes.Arith.axCore_specB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.axCore_specB

/-- info: 'STACS2027.Runtimes.fourCycles_lister' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.fourCycles_lister

/-- info: 'STACS2027.Runtimes.cpap4_enum_ram_explicit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.cpap4_enum_ram_explicit

/-- info: 'STACS2027.Runtimes.cpap4_enum_ram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.cpap4_enum_ram

/-- info: 'STACS2027.Runtimes.cpap4_enum_ram_explicit_semantic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.cpap4_enum_ram_explicit_semantic

/-- info: 'STACS2027.Runtimes.cpap4_enum_ram_semantic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.cpap4_enum_ram_semantic

/-- info: 'STACS2027.Runtimes.cyclePayload' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.cyclePayload

/-- info: 'STACS2027.Runtimes.fourCycleAssignment_single_explicit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.fourCycleAssignment_single_explicit

/-- info: 'STACS2027.Runtimes.fourCycleAssignment_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.fourCycleAssignment_single

/-- info: 'STACS2027.Runtimes.CpapSingle.lenGraph' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.CpapSingle.lenGraph

/-- info: 'STACS2027.Runtimes.CpapSingle.lenGraph_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.CpapSingle.lenGraph_spec

/-- info: 'STACS2027.Runtimes.CpapSingle.emitHeader' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.CpapSingle.emitHeader

/-- info: 'STACS2027.Runtimes.CpapSingle.headerEnumerator' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.CpapSingle.headerEnumerator

/-- info: 'STACS2027.Runtimes.CpapSingle.headerEnumerator_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.CpapSingle.headerEnumerator_spec

/-- info: 'STACS2027.Runtimes.Flow.ResidualWalk' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.ResidualWalk

/-- info: '_private.Runtimes.Flow.Augment.0.STACS2027.Runtimes.Flow.residualWalk_suffix' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.residualWalk_suffix

/-- info: '_private.Runtimes.Flow.Augment.0.STACS2027.Runtimes.Flow.residualWalk_simplify' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.residualWalk_simplify

/-- info: 'STACS2027.Runtimes.Flow.residualReach_simple_walk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.residualReach_simple_walk

/-- info: 'STACS2027.Runtimes.Flow.augmentFlow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.augmentFlow

/-- info: '_private.Runtimes.Flow.Augment.0.STACS2027.Runtimes.Flow.sumOnList' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.sumOnList

/-- info: 'STACS2027.Runtimes.Flow.augmentFlow_balance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.augmentFlow_balance

/-- info: 'STACS2027.Runtimes.Flow.residualWalk_balance' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.residualWalk_balance

/-- info: 'STACS2027.Runtimes.Flow.residualReach_augments' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.residualReach_augments

/-- info: 'STACS2027.Runtimes.Flow.maximumFlow_no_residualReach' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.maximumFlow_no_residualReach

/-- info: 'STACS2027.Runtimes.Flow.cutSize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.cutSize

/-- info: 'STACS2027.Runtimes.Flow.cutDivergence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.cutDivergence

/-- info: 'STACS2027.Runtimes.Flow.ResidualClosed' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.ResidualClosed

/-- info: 'STACS2027.Runtimes.Flow.IsMinimumCut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.IsMinimumCut

/-- info: '_private.Runtimes.Flow.CutFacts.0.STACS2027.Runtimes.Flow.sumRegionBalance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.sumRegionBalance

/-- info: 'STACS2027.Runtimes.Flow.cutDivergence_eq_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.cutDivergence_eq_value

/-- info: 'STACS2027.Runtimes.Flow.value_le_cutSize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.value_le_cutSize

/-- info: 'STACS2027.Runtimes.Flow.cutDivergence_eq_cutSize_of_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.cutDivergence_eq_cutSize_of_closed

/-- info: 'STACS2027.Runtimes.Flow.minimumCut_of_flow_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.minimumCut_of_flow_closed

/-- info: 'STACS2027.Runtimes.Flow.residualClosed_of_value_eq_cutSize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.residualClosed_of_value_eq_cutSize

/-- info: 'STACS2027.Runtimes.Flow.length_flatten_uniform' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.length_flatten_uniform

/-- info: 'STACS2027.Runtimes.Flow.getD_flatten_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.getD_flatten_uniform

/-- info: 'STACS2027.Runtimes.Flow.occ_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.occ_lt

/-- info: 'STACS2027.Runtimes.Flow.verts' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.verts

/-- info: 'STACS2027.Runtimes.Flow.length_verts' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.length_verts

/-- info: 'STACS2027.Runtimes.Flow.verts_getD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.verts_getD

/-- info: 'STACS2027.Runtimes.Flow.occs_getD_cyc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.occs_getD_cyc

/-- info: 'STACS2027.Runtimes.Flow.occs_getD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.occs_getD

/-- info: 'STACS2027.Runtimes.Flow.occs_getD_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.occs_getD_mem

/-- info: 'STACS2027.Runtimes.Flow.pathEdges_mem'' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.pathEdges_mem'

/-- info: 'STACS2027.Runtimes.Flow.occs_mem_verts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.occs_mem_verts

/-- info: 'STACS2027.Runtimes.Flow.occs_ordered' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.occs_ordered

/-- info: 'STACS2027.Runtimes.Flow.maxV' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.maxV

/-- info: 'STACS2027.Runtimes.Flow.le_maxV' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.le_maxV

/-- info: 'STACS2027.Runtimes.Flow.occs_le_maxV' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.occs_le_maxV

/-- info: 'STACS2027.Runtimes.Flow.eid' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.eid

/-- info: 'STACS2027.Runtimes.Flow.cntF' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.cntF

/-- info: 'STACS2027.Runtimes.Flow.eid_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.eid_lt

/-- info: 'STACS2027.Runtimes.Flow.cntF_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.cntF_zero

/-- info: 'STACS2027.Runtimes.Flow.cntF_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.cntF_succ

/-- info: 'STACS2027.Runtimes.Flow.cntF_le' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.cntF_le

/-- info: 'STACS2027.Runtimes.Flow.cntF_final' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.cntF_final

/-- info: 'STACS2027.Runtimes.Flow.vprefix' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.vprefix

/-- info: 'STACS2027.Runtimes.Flow.vl' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.vl

/-- info: 'STACS2027.Runtimes.Flow.nV' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.nV

/-- info: 'STACS2027.Runtimes.Flow.idv' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.idv

/-- info: 'STACS2027.Runtimes.Flow.vprefix_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.vprefix_succ

/-- info: 'STACS2027.Runtimes.Flow.vprefix_full' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.vprefix_full

/-- info: 'STACS2027.Runtimes.Flow.length_vprefix_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.length_vprefix_le

/-- info: 'STACS2027.Runtimes.Flow.nV_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.nV_le

/-- info: 'STACS2027.Runtimes.Flow.mem_vl' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.mem_vl

/-- info: 'STACS2027.Runtimes.Flow.idv_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.idv_lt

/-- info: 'STACS2027.Runtimes.Flow.dictOf_vl' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.dictOf_vl

/-- info: 'STACS2027.Runtimes.Flow.idv_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.idv_inj

/-- info: 'STACS2027.Runtimes.Flow.verts_getD_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.verts_getD_mem

/-- info: 'STACS2027.Runtimes.Flow.occ_decomp' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.occ_decomp

/-- info: 'STACS2027.Runtimes.Flow.idPr' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.idPr

/-- info: 'STACS2027.Runtimes.Flow.prs' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.prs

/-- info: 'STACS2027.Runtimes.Flow.length_prs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.length_prs

/-- info: 'STACS2027.Runtimes.Flow.prs_below' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.prs_below

/-- info: 'STACS2027.Runtimes.Flow.idPr_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.idPr_inj

/-- info: 'STACS2027.Runtimes.Flow.eids_occs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.eids_occs

/-- info: 'STACS2027.Runtimes.Flow.eids_prs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.eids_prs

/-- info: 'STACS2027.Runtimes.Flow.count_eids_prs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.count_eids_prs

/-- info: 'STACS2027.Runtimes.Flow.length_eraseDups_prs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.length_eraseDups_prs

/-- info: 'STACS2027.Runtimes.Flow.map_fst_prs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.map_fst_prs

/-- info: 'STACS2027.Runtimes.Flow.map_snd_prs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.map_snd_prs

/-- info: 'STACS2027.Runtimes.Flow.occs_mem_graph' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.occs_mem_graph

/-- info: 'STACS2027.Runtimes.Flow.verts_le_maxLab' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.verts_le_maxLab

/-- info: 'STACS2027.Runtimes.Flow.maxV_lt_labelBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.maxV_lt_labelBound

/-- info: 'STACS2027.Runtimes.Flow.GE' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.GE

/-- info: 'STACS2027.Runtimes.Flow.GE.regIndep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.GE.regIndep

/-- info: 'STACS2027.Runtimes.Flow.EMem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.EMem

/-- info: 'STACS2027.Runtimes.Flow.EInv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.EInv

/-- info: 'STACS2027.Runtimes.Flow.EMem.put' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.EMem.put

/-- info: 'STACS2027.Runtimes.Flow.edgeRead_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.edgeRead_run

/-- info: 'STACS2027.Runtimes.Flow.JInv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.JInv

/-- info: 'STACS2027.Runtimes.Flow.edgeBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.edgeBody_spec

/-- info: 'STACS2027.Runtimes.Flow.edgeRow_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.edgeRow_spec

/-- info: 'STACS2027.Runtimes.Flow.EdgesPost' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.EdgesPost

/-- info: 'STACS2027.Runtimes.Flow.IdsPre' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.IdsPre

/-- info: 'STACS2027.Runtimes.Flow.IdsMid' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.IdsMid

/-- info: 'STACS2027.Runtimes.Flow.pairIds_flow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.pairIds_flow

/-- info: 'STACS2027.Runtimes.Flow.stepEdges_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.stepEdges_spec

/-- info: 'STACS2027.Runtimes.Flow.edgePhase_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.edgePhase_spec

/-- info: 'STACS2027.Runtimes.Flow.bOFF_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.bOFF_le

/-- info: 'STACS2027.Runtimes.Flow.num4' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.num4

/-- info: 'STACS2027.Runtimes.Flow.n4' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.n4

/-- info: 'STACS2027.Runtimes.Flow.netEnc4' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.netEnc4

/-- info: 'STACS2027.Runtimes.Flow.sourceLayer_succ' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.sourceLayer_succ

/-- info: 'STACS2027.Runtimes.Flow.pairLayer_succ' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.pairLayer_succ

/-- info: 'STACS2027.Runtimes.Flow.sinkLayer_take_succ' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.sinkLayer_take_succ

/-- info: 'STACS2027.Runtimes.Flow.pairChunk4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.pairChunk4

/-- info: 'STACS2027.Runtimes.Flow.num4_source' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.num4_source

/-- info: 'STACS2027.Runtimes.Flow.num4_sink' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.num4_sink

/-- info: 'STACS2027.Runtimes.Flow.num4_pair_false' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.num4_pair_false

/-- info: 'STACS2027.Runtimes.Flow.num4_pair_true' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.num4_pair_true

/-- info: 'STACS2027.Runtimes.Flow.encArcs_pairChunk4' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.encArcs_pairChunk4

/-- info: 'STACS2027.Runtimes.Flow.encArcs_srcChunk4' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.encArcs_srcChunk4

/-- info: 'STACS2027.Runtimes.Flow.num4_occ' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.num4_occ

/-- info: 'STACS2027.Runtimes.Flow.num4_eList' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.num4_eList

/-- info: 'STACS2027.Runtimes.Flow.nodeOf_net4' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.nodeOf_net4

/-- info: 'STACS2027.Runtimes.Flow.num4_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.num4_lt

/-- info: 'STACS2027.Runtimes.Flow.goodNet4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.goodNet4

/-- info: 'STACS2027.Runtimes.Flow.getD_append_right'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.getD_append_right'

/-- info: 'STACS2027.Runtimes.Flow.pairLayer_getD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.pairLayer_getD

/-- info: 'STACS2027.Runtimes.Flow.net4_getD_q0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.net4_getD_q0

/-- info: 'STACS2027.Runtimes.Flow.net4_getD_q1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.net4_getD_q1

/-- info: 'STACS2027.Runtimes.Flow.readOff4_select' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.readOff4_select

/-- info: 'STACS2027.Runtimes.Flow.buildEnumeratedSorted' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.buildEnumeratedSorted

/-- info: 'STACS2027.Runtimes.Flow.enumeratedBuildSpace' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.enumeratedBuildSpace

/-- info: 'STACS2027.Runtimes.Flow.enumeratedBuildConstant' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.enumeratedBuildConstant

/-- info: 'STACS2027.Runtimes.Flow.ob_of_enumeratedFront' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.ob_of_enumeratedFront

/-- info: 'STACS2027.Runtimes.Flow.enumeratedBuild_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.enumeratedBuild_spec

/-- info: 'STACS2027.Runtimes.Flow.enumeratedBuild_memory' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.enumeratedBuild_memory

/-- info: 'STACS2027.Runtimes.Flow.sortedNetworkConstruction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.sortedNetworkConstruction

/-- info: 'STACS2027.Runtimes.Flow.mem_answer' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.mem_answer

/-- info: 'STACS2027.Runtimes.Flow.pos4' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.pos4

/-- info: 'STACS2027.Runtimes.Flow.ExInv4' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.ExInv4

/-- info: 'STACS2027.Runtimes.Flow.exInit4_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.exInit4_spec

/-- info: 'STACS2027.Runtimes.Flow.exBody4_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.exBody4_spec

/-- info: 'STACS2027.Runtimes.Flow.extract4_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.extract4_spec

/-- info: 'STACS2027.Runtimes.Flow.pos3b' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.pos3b

/-- info: 'STACS2027.Runtimes.Flow.ExInv3' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.ExInv3

/-- info: 'STACS2027.Runtimes.Flow.exInit3_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.exInit3_spec

/-- info: 'STACS2027.Runtimes.Flow.exBody3_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.exBody3_spec

/-- info: 'STACS2027.Runtimes.Flow.extract3_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.extract3_spec

/-- info: 'STACS2027.Runtimes.Flow.cyc' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.cyc

/-- info: 'STACS2027.Runtimes.Flow.occs' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.occs

/-- info: 'STACS2027.Runtimes.Flow.eList' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.eList

/-- info: 'STACS2027.Runtimes.Flow.wcount' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.wcount

/-- info: 'STACS2027.Runtimes.Flow.cyc_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.cyc_mem

/-- info: 'STACS2027.Runtimes.Flow.eList_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.eList_nodup

/-- info: 'STACS2027.Runtimes.Flow.mem_eList' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.mem_eList

/-- info: 'STACS2027.Runtimes.Flow.mem_eList_occs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.mem_eList_occs

/-- info: 'STACS2027.Runtimes.Flow.wcount_eq_countP' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.wcount_eq_countP

/-- info: 'STACS2027.Runtimes.Flow.wcount_eq_sum' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.wcount_eq_sum

/-- info: 'STACS2027.Runtimes.Flow.wcount_le' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.wcount_le

/-- info: 'STACS2027.Runtimes.Flow.wcount_eq_count' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.wcount_eq_count

/-- info: 'STACS2027.Runtimes.Flow.sum_wcount' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.sum_wcount

/-- info: 'STACS2027.Runtimes.Flow.length_eList_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.length_eList_le

/-- info: 'STACS2027.Runtimes.Flow.length_occs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.length_occs

/-- info: 'STACS2027.Runtimes.Flow.eraseDups_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.eraseDups_perm

/-- info: 'STACS2027.Runtimes.Flow.validChoices_nil_left' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.validChoices_nil_left

/-- info: 'STACS2027.Runtimes.Flow.validChoices_cons' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.validChoices_cons

/-- info: 'STACS2027.Runtimes.Flow.validChoices_perm' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.validChoices_perm

/-- info: 'STACS2027.Runtimes.Flow.hasAssignment_iff_perm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.hasAssignment_iff_perm

/-- info: 'STACS2027.Runtimes.Flow.OptCost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.OptCost

/-- info: 'STACS2027.Runtimes.Flow.optCost_of_optimal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.optCost_of_optimal

/-- info: 'STACS2027.Runtimes.Flow.zipWith_selected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.zipWith_selected

/-- info: 'STACS2027.Runtimes.Flow.net4' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.net4

/-- info: 'STACS2027.Runtimes.Flow.net4_cycles' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.net4_cycles

/-- info: 'STACS2027.Runtimes.Flow.cyc_isCycle' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.cyc_isCycle

/-- info: 'STACS2027.Runtimes.Flow.opp_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.opp_nodup

/-- info: 'STACS2027.Runtimes.Flow.net4_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.net4_nodup

/-- info: 'STACS2027.Runtimes.Flow.length_net4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.length_net4

/-- info: 'STACS2027.Runtimes.Flow.length_eList4' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.length_eList4

/-- info: 'STACS2027.Runtimes.Flow.flowOf4' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.flowOf4

/-- info: 'STACS2027.Runtimes.Flow.inflow_flowOf4' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.inflow_flowOf4

/-- info: 'STACS2027.Runtimes.Flow.outflow_flowOf4' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.outflow_flowOf4

/-- info: 'STACS2027.Runtimes.Flow.flowCost_flowOf4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.flowCost_flowOf4

/-- info: 'STACS2027.Runtimes.Flow.flowValue_flowOf4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.flowValue_flowOf4

/-- info: 'STACS2027.Runtimes.Flow.inflow_flowOf4_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.inflow_flowOf4_pair

/-- info: 'STACS2027.Runtimes.Flow.outflow_flowOf4_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.outflow_flowOf4_pair

/-- info: 'STACS2027.Runtimes.Flow.inflow_flowOf4_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.inflow_flowOf4_edge

/-- info: 'STACS2027.Runtimes.Flow.outflow_flowOf4_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.outflow_flowOf4_edge

/-- info: 'STACS2027.Runtimes.Flow.inflow_flowOf4_triangle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.inflow_flowOf4_triangle

/-- info: 'STACS2027.Runtimes.Flow.outflow_flowOf4_triangle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.outflow_flowOf4_triangle

/-- info: 'STACS2027.Runtimes.Flow.inflow4_edge_eq_load' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.inflow4_edge_eq_load

/-- info: 'STACS2027.Runtimes.Flow.path_mem_eList4' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.path_mem_eList4

/-- info: 'STACS2027.Runtimes.Flow.load_le_wcount4' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.load_le_wcount4

/-- info: 'STACS2027.Runtimes.Flow.load_eq_zero4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.load_eq_zero4

/-- info: 'STACS2027.Runtimes.Flow.cost_eq_load_sum4' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.cost_eq_load_sum4

/-- info: 'STACS2027.Runtimes.Flow.flow_of_assignment4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.flow_of_assignment4

/-- info: 'STACS2027.Runtimes.Flow.q0' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.q0

/-- info: 'STACS2027.Runtimes.Flow.q1' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.q1

/-- info: 'STACS2027.Runtimes.Flow.readOff4' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.readOff4

/-- info: 'STACS2027.Runtimes.Flow.assignment_of_flow4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.assignment_of_flow4

/-- info: 'STACS2027.Runtimes.Flow.optimal_of_minFlow4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.optimal_of_minFlow4

/-- info: 'STACS2027.Runtimes.Flow.length_flowInput' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.length_flowInput

/-- info: 'STACS2027.Runtimes.Flow.input_facts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.input_facts

/-- info: 'STACS2027.Runtimes.Flow.zeroFrom_flowInput' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.zeroFrom_flowInput

/-- info: 'STACS2027.Runtimes.Flow.GA' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.GA

/-- info: 'STACS2027.Runtimes.Flow.InitPost' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.InitPost

/-- info: 'STACS2027.Runtimes.Flow.initRead_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.initRead_spec

/-- info: 'STACS2027.Runtimes.Flow.stepInit_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.stepInit_spec

/-- info: 'STACS2027.Runtimes.Flow.MaxInv' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.MaxInv

/-- info: 'STACS2027.Runtimes.Flow.maxBody_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.maxBody_spec

/-- info: 'STACS2027.Runtimes.Flow.stepMax_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.stepMax_spec

/-- info: 'STACS2027.Runtimes.Flow.DictInv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.DictInv

/-- info: 'STACS2027.Runtimes.Flow.dictInit_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.dictInit_spec

/-- info: 'STACS2027.Runtimes.Flow.dictOf_vprefix_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.dictOf_vprefix_succ

/-- info: 'STACS2027.Runtimes.Flow.dictBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.dictBody_spec

/-- info: 'STACS2027.Runtimes.Flow.DictPost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.DictPost

/-- info: 'STACS2027.Runtimes.Flow.stepDict_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.stepDict_spec

/-- info: 'STACS2027.Runtimes.Flow.hornQuery' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.hornQuery

/-- info: 'STACS2027.Runtimes.Flow.hornQuery_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.hornQuery_length

/-- info: 'STACS2027.Runtimes.Flow.hornQuery_isTwoCNF' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.hornQuery_isTwoCNF

/-- info: '_private.Runtimes.Flow.HornQuery.0.STACS2027.Runtimes.Flow.implication_true' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.implication_true

/-- info: 'STACS2027.Runtimes.Flow.hornQuery_semantics' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.hornQuery_semantics

/-- info: 'STACS2027.Runtimes.Flow.regionAssignment' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.regionAssignment

/-- info: 'STACS2027.Runtimes.Flow.regionAssignment_fin' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.regionAssignment_fin

/-- info: 'STACS2027.Runtimes.Flow.hornQuery_satisfiable_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.hornQuery_satisfiable_iff

/-- info: 'STACS2027.Runtimes.Flow.hornQuery_decision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.hornQuery_decision

/-- info: 'STACS2027.Runtimes.Flow.originalFlowBits' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.originalFlowBits

/-- info: 'STACS2027.Runtimes.Flow.hornInput' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.hornInput

/-- info: 'STACS2027.Runtimes.Flow.maximalRegionBits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.maximalRegionBits

/-- info: 'STACS2027.Runtimes.Flow.originalFlowBits_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.originalFlowBits_length

/-- info: 'STACS2027.Runtimes.Flow.hornInput_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.hornInput_length

/-- info: 'STACS2027.Runtimes.Flow.maximalRegionBits_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.maximalRegionBits_length

/-- info: 'STACS2027.Runtimes.Flow.residualCodes' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.residualCodes

/-- info: 'STACS2027.Runtimes.Flow.residualCodes_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.residualCodes_length

/-- info: 'STACS2027.Runtimes.Flow.residualCodes_succ' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.residualCodes_succ

/-- info: 'STACS2027.Runtimes.Flow.hornQuery_codes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.hornQuery_codes

/-- info: 'STACS2027.Runtimes.Flow.hNodes' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.hNodes

/-- info: 'STACS2027.Runtimes.Flow.hArcs' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.hArcs

/-- info: 'STACS2027.Runtimes.Flow.hSink' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.hSink

/-- info: 'STACS2027.Runtimes.Flow.hBits' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.hBits

/-- info: 'STACS2027.Runtimes.Flow.hLength' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.hLength

/-- info: 'STACS2027.Runtimes.Flow.hVertex' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.hVertex

/-- info: 'STACS2027.Runtimes.Flow.hArc' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.hArc

/-- info: 'STACS2027.Runtimes.Flow.hAddr' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.hAddr

/-- info: 'STACS2027.Runtimes.Flow.hTail' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.hTail

/-- info: 'STACS2027.Runtimes.Flow.hHead' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.hHead

/-- info: 'STACS2027.Runtimes.Flow.hBit' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.hBit

/-- info: 'STACS2027.Runtimes.Flow.hNeg' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.hNeg

/-- info: 'STACS2027.Runtimes.Flow.hPos' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.hPos

/-- info: 'STACS2027.Runtimes.Flow.hBase' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.hBase

/-- info: 'STACS2027.Runtimes.Flow.hValue' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.hValue

/-- info: 'STACS2027.Runtimes.Flow.hZero' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.hZero

/-- info: 'STACS2027.Runtimes.Flow.hOne' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.hOne

/-- info: 'STACS2027.Runtimes.Flow.hPairs' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.hPairs

/-- info: 'STACS2027.Runtimes.Flow.hPadding' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.hPadding

/-- info: 'STACS2027.Runtimes.Flow.hornInit' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.hornInit

/-- info: 'STACS2027.Runtimes.Flow.hornPrepare' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.hornPrepare

/-- info: 'STACS2027.Runtimes.Flow.hornRead' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.hornRead

/-- info: 'STACS2027.Runtimes.Flow.hornCodes' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.hornCodes

/-- info: 'STACS2027.Runtimes.Flow.hornStore' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.hornStore

/-- info: 'STACS2027.Runtimes.Flow.hornArcBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.hornArcBody

/-- info: 'STACS2027.Runtimes.Flow.hornUnits' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.hornUnits

/-- info: 'STACS2027.Runtimes.Flow.hornVertexBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.hornVertexBody

/-- info: 'STACS2027.Runtimes.Flow.hornRAM' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.hornRAM

/-- info: 'STACS2027.Runtimes.Flow.HornRegs' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.HornRegs

/-- info: '_private.Runtimes.Flow.HornRAM.0.STACS2027.Runtimes.Flow.HornRegs.run' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.HornRegs.run

/-- info: '_private.Runtimes.Flow.HornRAM.0.STACS2027.Runtimes.Flow.inputEndpoints' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.inputEndpoints

/-- info: 'STACS2027.Runtimes.Flow.hornInit_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.hornInit_spec

/-- info: 'STACS2027.Runtimes.Flow.HornBuildRegs' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.HornBuildRegs

/-- info: '_private.Runtimes.Flow.HornRAM.0.STACS2027.Runtimes.Flow.HornBuildRegs.run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.HornBuildRegs.run

/-- info: 'STACS2027.Runtimes.Flow.HornBuildInv' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.HornBuildInv

/-- info: 'STACS2027.Runtimes.Flow.hornArcBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.hornArcBody_spec

/-- info: 'STACS2027.Runtimes.Flow.hornPrepare_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.hornPrepare_spec

/-- info: 'STACS2027.Runtimes.Flow.HornReady' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.HornReady

/-- info: 'STACS2027.Runtimes.Flow.hornUnits_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.hornUnits_spec

/-- info: 'STACS2027.Runtimes.Flow.hornDecision_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.hornDecision_spec

/-- info: 'STACS2027.Runtimes.Flow.HornOuterInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.HornOuterInv

/-- info: '_private.Runtimes.Flow.HornRAM.0.STACS2027.Runtimes.Flow.maximalRegionBits_succ' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.maximalRegionBits_succ

/-- info: 'STACS2027.Runtimes.Flow.hornVertexBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.hornVertexBody_spec

/-- info: 'STACS2027.Runtimes.Flow.hornRAM_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.hornRAM_spec

/-- info: 'STACS2027.Runtimes.Flow.hornRAM_computes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.hornRAM_computes

/-- info: 'STACS2027.Runtimes.Flow.hornSeparator' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.hornSeparator

/-- info: 'STACS2027.Runtimes.Flow.maximalRegionBits_get' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.maximalRegionBits_get

/-- info: 'STACS2027.Runtimes.Flow.originalFlowBits_projection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.originalFlowBits_projection

/-- info: 'STACS2027.Runtimes.Flow.hornInput_projection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.hornInput_projection

/-- info: '_private.Runtimes.Flow.HornSeparator.0.STACS2027.Runtimes.Flow.hornResourceBounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.hornResourceBounds

/-- info: 'STACS2027.Runtimes.Flow.hornSeparator_computes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.hornSeparator_computes

/-- info: 'STACS2027.Runtimes.Flow.IndexedNetwork' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.IndexedNetwork

/-- info: 'STACS2027.Runtimes.Flow.IndexedFlow' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.IndexedFlow

/-- info: 'STACS2027.Runtimes.Flow.indexedBalance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.indexedBalance

/-- info: 'STACS2027.Runtimes.Flow.indexedCost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.indexedCost

/-- info: 'STACS2027.Runtimes.Flow.IsIndexedFlow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.IsIndexedFlow

/-- info: 'STACS2027.Runtimes.Flow.ResidualEdge' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.ResidualEdge

/-- info: 'STACS2027.Runtimes.Flow.residualAvailable' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.residualAvailable

/-- info: 'STACS2027.Runtimes.Flow.residualTail' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.residualTail

/-- info: 'STACS2027.Runtimes.Flow.residualHead' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.residualHead

/-- info: 'STACS2027.Runtimes.Flow.residualEdgeCost' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.residualEdgeCost

/-- info: 'STACS2027.Runtimes.Flow.residualCost' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.residualCost

/-- info: 'STACS2027.Runtimes.Flow.residualBalance' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.residualBalance

/-- info: 'STACS2027.Runtimes.Flow.IsResidualCycle' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.IsResidualCycle

/-- info: 'STACS2027.Runtimes.Flow.residualDifference' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.residualDifference

/-- info: '_private.Runtimes.Flow.IndexedFacts.0.STACS2027.Runtimes.Flow.differenceIndexes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.differenceIndexes

/-- info: 'STACS2027.Runtimes.Flow.residualDifference_index_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.residualDifference_index_nodup

/-- info: 'STACS2027.Runtimes.Flow.residualDifference_available' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.residualDifference_available

/-- info: '_private.Runtimes.Flow.IndexedFacts.0.STACS2027.Runtimes.Flow.differenceCostList' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.differenceCostList

/-- info: '_private.Runtimes.Flow.IndexedFacts.0.STACS2027.Runtimes.Flow.differenceBalanceList' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.differenceBalanceList

/-- info: '_private.Runtimes.Flow.IndexedFacts.0.STACS2027.Runtimes.Flow.sumFinRange' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.sumFinRange

/-- info: 'STACS2027.Runtimes.Flow.residualDifference_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.residualDifference_cost

/-- info: 'STACS2027.Runtimes.Flow.residualDifference_balance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.residualDifference_balance

/-- info: 'STACS2027.Runtimes.Flow.residualDifference_balanced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.residualDifference_balanced

/-- info: 'STACS2027.Runtimes.Flow.indexedCost_le_square' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.indexedCost_le_square

/-- info: 'STACS2027.Runtimes.Flow.isCycle_of_perm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.isCycle_of_perm

/-- info: 'STACS2027.Runtimes.Flow.validChoices_first' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.validChoices_first

/-- info: 'STACS2027.Runtimes.Flow.build4_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.build4_spec

/-- info: 'STACS2027.Runtimes.Flow.build3_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.build3_spec

/-- info: 'STACS2027.Runtimes.Flow.bOFF_le_flow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.bOFF_le_flow

/-- info: 'STACS2027.Runtimes.Flow.cpap4_flow_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.cpap4_flow_core

/-- info: 'STACS2027.Runtimes.Flow.triangle_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.triangle_core

/-- info: 'STACS2027.Runtimes.Flow.cpap4_flow_ram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.cpap4_flow_ram

/-- info: 'STACS2027.Runtimes.Flow.triangle_ram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.triangle_ram

/-- info: 'STACS2027.Runtimes.Flow.rpow_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.rpow_bound

/-- info: 'STACS2027.Runtimes.Flow.le_rpow_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.le_rpow_self

/-- info: 'STACS2027.Runtimes.Flow.almostLinear_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.almostLinear_const

/-- info: 'STACS2027.Runtimes.Flow.solver_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.solver_le

/-- info: 'STACS2027.Runtimes.Flow.split_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.split_bound

/-- info: 'STACS2027.Runtimes.Flow.cpap4_flow_ram_almostLinear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.cpap4_flow_ram_almostLinear

/-- info: 'STACS2027.Runtimes.Flow.triangle_ram_almostLinear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.triangle_ram_almostLinear

/-- info: 'STACS2027.Runtimes.Flow.cpap4_enum_of_lister' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.cpap4_enum_of_lister

/-- info: 'STACS2027.Runtimes.Flow.cpap4_enum_of_fourCycles' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.cpap4_enum_of_fourCycles

/-- info: 'STACS2027.Runtimes.Flow.numberedNode' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.numberedNode

/-- info: 'STACS2027.Runtimes.Flow.numberedNodeNumber' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.numberedNodeNumber

/-- info: 'STACS2027.Runtimes.Flow.numberedNodeNumber_numberedNode' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.numberedNodeNumber_numberedNode

/-- info: 'STACS2027.Runtimes.Flow.numberedNode_source' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.numberedNode_source

/-- info: 'STACS2027.Runtimes.Flow.numberedNode_sink' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.numberedNode_sink

/-- info: 'STACS2027.Runtimes.Flow.numberedNode_injective' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.numberedNode_injective

/-- info: 'STACS2027.Runtimes.Flow.numberedArc' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.numberedArc

/-- info: 'STACS2027.Runtimes.Flow.numberedArcs' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.numberedArcs

/-- info: 'STACS2027.Runtimes.Flow.bypassArc' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.bypassArc

/-- info: 'STACS2027.Runtimes.Flow.maxFlowNetwork' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.maxFlowNetwork

/-- info: 'STACS2027.Runtimes.Flow.numberedArcs_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.numberedArcs_length

/-- info: 'STACS2027.Runtimes.Flow.maxFlowNetwork_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.maxFlowNetwork_length

/-- info: '_private.Runtimes.Flow.MaxFlowNetwork.0.STACS2027.Runtimes.Flow.nodeOf_maxFlowNetwork' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.nodeOf_maxFlowNetwork

/-- info: 'STACS2027.Runtimes.Flow.maxFlowNetwork_good' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.maxFlowNetwork_good

/-- info: 'STACS2027.Runtimes.Flow.maxFlowNetwork_feasible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.maxFlowNetwork_feasible

/-- info: 'STACS2027.Runtimes.Flow.maxFlowProjection' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.maxFlowProjection

/-- info: 'STACS2027.Runtimes.Flow.listBalance' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.listBalance

/-- info: 'STACS2027.Runtimes.Flow.listBalance_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.listBalance_eq

/-- info: 'STACS2027.Runtimes.Flow.sum_select_ofFn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.sum_select_ofFn

/-- info: 'STACS2027.Runtimes.Flow.select_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.select_append

/-- info: 'STACS2027.Runtimes.Flow.select_replicate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.select_replicate

/-- info: 'STACS2027.Runtimes.Flow.maxFlow_selected_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.maxFlow_selected_split

/-- info: 'STACS2027.Runtimes.Flow.projection_balance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.projection_balance

/-- info: 'STACS2027.Runtimes.Flow.numbered_selected_cost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.numbered_selected_cost

/-- info: 'STACS2027.Runtimes.Flow.listBalance_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.listBalance_append

/-- info: 'STACS2027.Runtimes.Flow.bypass_balance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.bypass_balance

/-- info: 'STACS2027.Runtimes.Flow.numbered_selected_source_inflow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.numbered_selected_source_inflow

/-- info: 'STACS2027.Runtimes.Flow.indexedBalance_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.indexedBalance_sum

/-- info: 'STACS2027.Runtimes.Flow.isIndexedFlow_of_conservation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.isIndexedFlow_of_conservation

/-- info: 'STACS2027.Runtimes.Flow.maxFlow_projection_feasible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.maxFlow_projection_feasible

/-- info: 'STACS2027.Runtimes.Flow.indexedBits' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.indexedBits

/-- info: 'STACS2027.Runtimes.Flow.projection_indexedBits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.projection_indexedBits

/-- info: 'STACS2027.Runtimes.Flow.indexed_flow_reified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.indexed_flow_reified

/-- info: 'STACS2027.Runtimes.Flow.indexed_flow_value_le_arcs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.indexed_flow_value_le_arcs

/-- info: 'STACS2027.Runtimes.Flow.indexed_flow_fixedDemand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.indexed_flow_fixedDemand

/-- info: 'STACS2027.Runtimes.Flow.maxFlow_projection_optimal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.maxFlow_projection_optimal

/-- info: 'STACS2027.Runtimes.Flow.offsetIndex' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.offsetIndex

/-- info: 'STACS2027.Runtimes.Flow.offsetAddress' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.offsetAddress

/-- info: 'STACS2027.Runtimes.Flow.offsetValue' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.offsetValue

/-- info: 'STACS2027.Runtimes.Flow.offsetTwo' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.offsetTwo

/-- info: 'STACS2027.Runtimes.Flow.offsetFour' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.offsetFour

/-- info: 'STACS2027.Runtimes.Flow.offsetZero' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.offsetZero

/-- info: 'STACS2027.Runtimes.Flow.offsetBase' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.offsetBase

/-- info: 'STACS2027.Runtimes.Flow.OffsetInput' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.OffsetInput

/-- info: 'STACS2027.Runtimes.Flow.offsetReady' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.offsetReady

/-- info: 'STACS2027.Runtimes.Flow.offsetCopyBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.offsetCopyBody

/-- info: 'STACS2027.Runtimes.Flow.offsetCopy' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.offsetCopy

/-- info: 'STACS2027.Runtimes.Flow.offsetCall' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.offsetCall

/-- info: 'STACS2027.Runtimes.Flow.OffsetGlobals' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.OffsetGlobals

/-- info: 'STACS2027.Runtimes.Flow.OffsetCopyInv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.OffsetCopyInv

/-- info: 'STACS2027.Runtimes.Flow.offsetReady_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.offsetReady_spec

/-- info: 'STACS2027.Runtimes.Flow.offsetCopyBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.offsetCopyBody_spec

/-- info: 'STACS2027.Runtimes.Flow.offsetCopy_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.offsetCopy_spec

/-- info: 'STACS2027.Runtimes.Flow.OffsetCallResult' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.OffsetCallResult

/-- info: 'STACS2027.Runtimes.Flow.offsetCall_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.offsetCall_spec

/-- info: 'STACS2027.Runtimes.Flow.OffsetCallResult.input' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.OffsetCallResult.input

/-- info: 'STACS2027.Runtimes.Flow.OB' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.OB

/-- info: 'STACS2027.Runtimes.Flow.fits_out' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.fits_out

/-- info: 'STACS2027.Runtimes.Flow.OB.of_post' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.OB.of_post

/-- info: 'STACS2027.Runtimes.Flow.OB.run' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.OB.run

/-- info: 'STACS2027.Runtimes.Flow.sum_countP_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.sum_countP_eq

/-- info: 'STACS2027.Runtimes.Flow.sum_cntF_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.sum_cntF_le

/-- info: 'STACS2027.Runtimes.Flow.InnerInv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.InnerInv

/-- info: 'STACS2027.Runtimes.Flow.SinkInv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.SinkInv

/-- info: 'STACS2027.Runtimes.Flow.sinkInner_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.sinkInner_spec

/-- info: 'STACS2027.Runtimes.Flow.sinkBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.sinkBody_spec

/-- info: 'STACS2027.Runtimes.Flow.outSink_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.outSink_spec

/-- info: 'STACS2027.Runtimes.Flow.hdr4L' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.hdr4L

/-- info: 'STACS2027.Runtimes.Flow.HInv4' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.HInv4

/-- info: 'STACS2027.Runtimes.Flow.hdr4_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.hdr4_spec

/-- info: 'STACS2027.Runtimes.Flow.SrcInv4' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.SrcInv4

/-- info: 'STACS2027.Runtimes.Flow.srcBody4_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.srcBody4_spec

/-- info: 'STACS2027.Runtimes.Flow.src4_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.src4_spec

/-- info: 'STACS2027.Runtimes.Flow.PairInv4' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.PairInv4

/-- info: 'STACS2027.Runtimes.Flow.pairBody4_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.pairBody4_spec

/-- info: 'STACS2027.Runtimes.Flow.pair4_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.pair4_spec

/-- info: 'STACS2027.Runtimes.Flow.out4_specA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.out4_specA

/-- info: 'STACS2027.Runtimes.Flow.out4_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.out4_spec

/-- info: 'STACS2027.Runtimes.Flow.hdr3L' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.hdr3L

/-- info: 'STACS2027.Runtimes.Flow.HInv3' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.HInv3

/-- info: 'STACS2027.Runtimes.Flow.hdr3_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.hdr3_spec

/-- info: 'STACS2027.Runtimes.Flow.SrcInv3' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.SrcInv3

/-- info: 'STACS2027.Runtimes.Flow.srcBody3_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.srcBody3_spec

/-- info: 'STACS2027.Runtimes.Flow.src3_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.src3_spec

/-- info: 'STACS2027.Runtimes.Flow.TriInv3' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.TriInv3

/-- info: 'STACS2027.Runtimes.Flow.triBody3_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.triBody3_spec

/-- info: 'STACS2027.Runtimes.Flow.tri3_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.tri3_spec

/-- info: 'STACS2027.Runtimes.Flow.out3_specA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.out3_specA

/-- info: 'STACS2027.Runtimes.Flow.out3_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.out3_spec

/-- info: 'STACS2027.Runtimes.Flow.edgePairs' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.edgePairs

/-- info: 'STACS2027.Runtimes.Flow.edgeInput' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.edgeInput

/-- info: 'STACS2027.Runtimes.Flow.edgePairs_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.edgePairs_length

/-- info: 'STACS2027.Runtimes.Flow.edgeInput_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.edgeInput_length

/-- info: 'STACS2027.Runtimes.Flow.edgePairs_get' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.edgePairs_get

/-- info: 'STACS2027.Runtimes.Flow.cNodes' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.cNodes

/-- info: 'STACS2027.Runtimes.Flow.cArcs' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.cArcs

/-- info: 'STACS2027.Runtimes.Flow.cSource' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.cSource

/-- info: 'STACS2027.Runtimes.Flow.cSink' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.cSink

/-- info: 'STACS2027.Runtimes.Flow.cPadding' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.cPadding

/-- info: 'STACS2027.Runtimes.Flow.cIndex' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.cIndex

/-- info: 'STACS2027.Runtimes.Flow.cAddr' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.cAddr

/-- info: 'STACS2027.Runtimes.Flow.cValue' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.cValue

/-- info: 'STACS2027.Runtimes.Flow.cStart' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.cStart

/-- info: 'STACS2027.Runtimes.Flow.cZero' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.cZero

/-- info: 'STACS2027.Runtimes.Flow.cOne' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.cOne

/-- info: 'STACS2027.Runtimes.Flow.cTotal' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.cTotal

/-- info: 'STACS2027.Runtimes.Flow.paddedEncodeInit' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.paddedEncodeInit

/-- info: 'STACS2027.Runtimes.Flow.paddedOriginalBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.paddedOriginalBody

/-- info: 'STACS2027.Runtimes.Flow.paddedBypassBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.paddedBypassBody

/-- info: 'STACS2027.Runtimes.Flow.paddedEncode' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.paddedEncode

/-- info: 'STACS2027.Runtimes.Flow.PaddedBuildBase' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.PaddedBuildBase

/-- info: 'STACS2027.Runtimes.Flow.paddedHeader' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.paddedHeader

/-- info: 'STACS2027.Runtimes.Flow.originalCodes' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.originalCodes

/-- info: '_private.Runtimes.Flow.PaddedEncoding.0.STACS2027.Runtimes.Flow.initial_edgeInput_endpoints' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.initial_edgeInput_endpoints

/-- info: 'STACS2027.Runtimes.Flow.paddedEncodeInit_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.paddedEncodeInit_spec

/-- info: 'STACS2027.Runtimes.Flow.PaddedOriginalInv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.PaddedOriginalInv

/-- info: 'STACS2027.Runtimes.Flow.PaddedBypassInv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.PaddedBypassInv

/-- info: '_private.Runtimes.Flow.PaddedEncoding.0.STACS2027.Runtimes.Flow.PaddedBuildBase.run' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.PaddedBuildBase.run

/-- info: '_private.Runtimes.Flow.PaddedEncoding.0.STACS2027.Runtimes.Flow.originalCodes_succ' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.originalCodes_succ

/-- info: 'STACS2027.Runtimes.Flow.paddedOriginalBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.paddedOriginalBody_spec

/-- info: 'STACS2027.Runtimes.Flow.paddedBypassBody_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.paddedBypassBody_spec

/-- info: 'STACS2027.Runtimes.Flow.originalCodes_all' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.originalCodes_all

/-- info: 'STACS2027.Runtimes.Flow.paddedEncode_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.paddedEncode_spec

/-- info: 'STACS2027.Runtimes.Flow.paddedEncode_computes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.paddedEncode_computes

/-- info: 'STACS2027.Runtimes.Flow.paddedInputLength' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.paddedInputLength

/-- info: 'STACS2027.Runtimes.Flow.paddedInputLength_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.paddedInputLength_spec

/-- info: 'STACS2027.Runtimes.Flow.paddedMaxFlowNetwork' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.paddedMaxFlowNetwork

/-- info: 'STACS2027.Runtimes.Flow.paddedMaxFlowNetwork_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.paddedMaxFlowNetwork_length

/-- info: '_private.Runtimes.Flow.PaddedNetwork.0.STACS2027.Runtimes.Flow.nodeOf_paddedMaxFlowNetwork' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.nodeOf_paddedMaxFlowNetwork

/-- info: 'STACS2027.Runtimes.Flow.paddedMaxFlowNetwork_good' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.paddedMaxFlowNetwork_good

/-- info: 'STACS2027.Runtimes.Flow.paddedMaxFlowNetwork_feasible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.paddedMaxFlowNetwork_feasible

/-- info: 'STACS2027.Runtimes.Flow.paddedMaxFlow_selected_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.paddedMaxFlow_selected_split

/-- info: 'STACS2027.Runtimes.Flow.paddedMaxFlow_projection_feasible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.paddedMaxFlow_projection_feasible

/-- info: 'STACS2027.Runtimes.Flow.indexed_flow_paddedDemand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.indexed_flow_paddedDemand

/-- info: 'STACS2027.Runtimes.Flow.paddedMaxFlow_projection_optimal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.paddedMaxFlow_projection_optimal

/-- info: 'STACS2027.Runtimes.Flow.paddedMaxFlow_answer_optimal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.paddedMaxFlow_answer_optimal

/-- info: 'STACS2027.Runtimes.Flow.xI' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.xI

/-- info: 'STACS2027.Runtimes.Flow.xV' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.xV

/-- info: 'STACS2027.Runtimes.Flow.xA' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.xA

/-- info: 'STACS2027.Runtimes.Flow.xZ' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.xZ

/-- info: 'STACS2027.Runtimes.Flow.xOne' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.xOne

/-- info: 'STACS2027.Runtimes.Flow.xL' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.xL

/-- info: 'STACS2027.Runtimes.Flow.sp' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.sp

/-- info: 'STACS2027.Runtimes.Flow.spreadBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.spreadBody

/-- info: 'STACS2027.Runtimes.Flow.spread' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.spread

/-- info: 'STACS2027.Runtimes.Flow.SpInv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.SpInv

/-- info: 'STACS2027.Runtimes.Flow.spreadBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.spreadBody_spec

/-- info: 'STACS2027.Runtimes.Flow.spread_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.spread_spec

/-- info: 'STACS2027.Runtimes.Flow.ne_of_mod' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.ne_of_mod

/-- info: 'STACS2027.Runtimes.Flow.setConsts' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.setConsts

/-- info: 'STACS2027.Runtimes.Flow.ptr2' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.ptr2

/-- info: 'STACS2027.Runtimes.Flow.pipe3' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.pipe3

/-- info: 'STACS2027.Runtimes.Flow.LenPost' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.LenPost

/-- info: 'STACS2027.Runtimes.Flow.exec_loopFree' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.exec_loopFree

/-- info: 'STACS2027.Runtimes.Flow.getD_append_left'' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.getD_append_left'

/-- info: 'STACS2027.Runtimes.Flow.getD_append_right''' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.getD_append_right''

/-- info: 'STACS2027.Runtimes.Flow.pipe3_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.pipe3_spec

/-- info: 'STACS2027.Runtimes.Flow.pipe3_spec_time' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.pipe3_spec_time

/-- info: 'STACS2027.Runtimes.Flow.AlmostLinear.polynomialBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.AlmostLinear.polynomialBound

/-- info: 'STACS2027.Runtimes.Flow.polynomialMinCostFlowSolver_of_almostLinear' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.polynomialMinCostFlowSolver_of_almostLinear

/-- info: 'STACS2027.Runtimes.Flow.polynomialMinCostFlowSolverExists_of_almostLinear' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.polynomialMinCostFlowSolverExists_of_almostLinear

/-- info: 'STACS2027.Runtimes.Flow.flowInput' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.flowInput

/-- info: 'STACS2027.Runtimes.Flow.gK' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.gK

/-- info: 'STACS2027.Runtimes.Flow.gT' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.gT

/-- info: 'STACS2027.Runtimes.Flow.gV' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.gV

/-- info: 'STACS2027.Runtimes.Flow.gKT' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.gKT

/-- info: 'STACS2027.Runtimes.Flow.gNV' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.gNV

/-- info: 'STACS2027.Runtimes.Flow.gMX' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.gMX

/-- info: 'STACS2027.Runtimes.Flow.gD' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.gD

/-- info: 'STACS2027.Runtimes.Flow.gN' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.gN

/-- info: 'STACS2027.Runtimes.Flow.gPU' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.gPU

/-- info: 'STACS2027.Runtimes.Flow.gPV' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.gPV

/-- info: 'STACS2027.Runtimes.Flow.gEID' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.gEID

/-- info: 'STACS2027.Runtimes.Flow.gCNT' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.gCNT

/-- info: 'STACS2027.Runtimes.Flow.gNE' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.gNE

/-- info: 'STACS2027.Runtimes.Flow.gEB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.gEB

/-- info: 'STACS2027.Runtimes.Flow.sQ' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.sQ

/-- info: 'STACS2027.Runtimes.Flow.sI' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.sI

/-- info: 'STACS2027.Runtimes.Flow.sJ' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.sJ

/-- info: 'STACS2027.Runtimes.Flow.sX' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.sX

/-- info: 'STACS2027.Runtimes.Flow.sY' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.sY

/-- info: 'STACS2027.Runtimes.Flow.sP' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.sP

/-- info: 'STACS2027.Runtimes.Flow.sZ' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.sZ

/-- info: 'STACS2027.Runtimes.Flow.sC' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.sC

/-- info: 'STACS2027.Runtimes.Flow.sBase' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.sBase

/-- info: 'STACS2027.Runtimes.Flow.sA' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.sA

/-- info: 'STACS2027.Runtimes.Flow.sE' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.sE

/-- info: 'STACS2027.Runtimes.Flow.sR' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.sR

/-- info: 'STACS2027.Runtimes.Flow.sOne' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.sOne

/-- info: 'STACS2027.Runtimes.Flow.sZ0' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.sZ0

/-- info: 'STACS2027.Runtimes.Flow.sB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.sB

/-- info: 'STACS2027.Runtimes.Flow.sThree' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.sThree

/-- info: 'STACS2027.Runtimes.Flow.bV' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.bV

/-- info: 'STACS2027.Runtimes.Flow.bD' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.bD

/-- info: 'STACS2027.Runtimes.Flow.bPU' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.bPU

/-- info: 'STACS2027.Runtimes.Flow.bPV' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.bPV

/-- info: 'STACS2027.Runtimes.Flow.bPI' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.bPI

/-- info: 'STACS2027.Runtimes.Flow.bEID' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.bEID

/-- info: 'STACS2027.Runtimes.Flow.bCNT' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.bCNT

/-- info: 'STACS2027.Runtimes.Flow.bOFF' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.bOFF

/-- info: 'STACS2027.Runtimes.Flow.bEID_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.bEID_eq

/-- info: 'STACS2027.Runtimes.Flow.layout_eqs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.layout_eqs

/-- info: 'STACS2027.Runtimes.Flow.idsEnd_eq' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.idsEnd_eq

/-- info: 'STACS2027.Runtimes.Flow.edgePhase' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.edgePhase

/-- info: 'STACS2027.Runtimes.Flow.pairArc' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.pairArc

/-- info: 'STACS2027.Runtimes.Flow.sinkInner' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.sinkInner

/-- info: 'STACS2027.Runtimes.Flow.sinkBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.sinkBody

/-- info: 'STACS2027.Runtimes.Flow.outSink' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.outSink

/-- info: 'STACS2027.Runtimes.Flow.hdr4' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.hdr4

/-- info: 'STACS2027.Runtimes.Flow.srcBody4' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.srcBody4

/-- info: 'STACS2027.Runtimes.Flow.src4' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.src4

/-- info: 'STACS2027.Runtimes.Flow.pairBody4' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.pairBody4

/-- info: 'STACS2027.Runtimes.Flow.pair4' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.pair4

/-- info: 'STACS2027.Runtimes.Flow.out4' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.out4

/-- info: 'STACS2027.Runtimes.Flow.build4' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.build4

/-- info: 'STACS2027.Runtimes.Flow.hdr3' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.hdr3

/-- info: 'STACS2027.Runtimes.Flow.srcBody3' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.srcBody3

/-- info: 'STACS2027.Runtimes.Flow.src3' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.src3

/-- info: 'STACS2027.Runtimes.Flow.triBody3' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.triBody3

/-- info: 'STACS2027.Runtimes.Flow.tri3' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.tri3

/-- info: 'STACS2027.Runtimes.Flow.out3' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.out3

/-- info: 'STACS2027.Runtimes.Flow.build3' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.build3

/-- info: 'STACS2027.Runtimes.Flow.exInit4' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.exInit4

/-- info: 'STACS2027.Runtimes.Flow.exBody4' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.exBody4

/-- info: 'STACS2027.Runtimes.Flow.extract4' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.extract4

/-- info: 'STACS2027.Runtimes.Flow.exInit3' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.exInit3

/-- info: 'STACS2027.Runtimes.Flow.exBody3' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.exBody3

/-- info: 'STACS2027.Runtimes.Flow.extract3' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.extract3

/-- info: 'STACS2027.Runtimes.Flow.rl' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.rl

/-- info: 'STACS2027.Runtimes.Flow.xT' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.xT

/-- info: 'STACS2027.Runtimes.Flow.xP' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.xP

/-- info: 'STACS2027.Runtimes.Flow.xFour' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.xFour

/-- info: 'STACS2027.Runtimes.Flow.xJ' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.xJ

/-- info: 'STACS2027.Runtimes.Flow.addrOf' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.addrOf

/-- info: 'STACS2027.Runtimes.Flow.tr' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.tr

/-- info: 'STACS2027.Runtimes.Flow.Sim' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.Sim

/-- info: 'STACS2027.Runtimes.Flow.OutRel' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.OutRel

/-- info: 'STACS2027.Runtimes.Flow.rl_mod' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.rl_mod

/-- info: 'STACS2027.Runtimes.Flow.rl_inj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.rl_inj

/-- info: 'STACS2027.Runtimes.Flow.xJ_mod' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.xJ_mod

/-- info: 'STACS2027.Runtimes.Flow.rl_ne' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.rl_ne

/-- info: 'STACS2027.Runtimes.Flow.xJ_ne_xT' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.xJ_ne_xT

/-- info: 'STACS2027.Runtimes.Flow.xJ_ne_xP' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.xJ_ne_xP

/-- info: 'STACS2027.Runtimes.Flow.ExecB.out_length_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.ExecB.out_length_le

/-- info: 'STACS2027.Runtimes.Flow.Exec.exists_execB' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.Exec.exists_execB

/-- info: 'STACS2027.Runtimes.Flow.Computes.exists_computesIn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.Computes.exists_computesIn

/-- info: 'STACS2027.Runtimes.Flow.SimPost' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.SimPost

/-- info: 'STACS2027.Runtimes.Flow.sim_setReg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.sim_setReg

/-- info: 'STACS2027.Runtimes.Flow.frame_setReg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.frame_setReg

/-- info: 'STACS2027.Runtimes.Flow.addrOf_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.addrOf_run

/-- info: 'STACS2027.Runtimes.Flow.addrOf_exec' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.addrOf_exec

/-- info: 'STACS2027.Runtimes.Flow.sim_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.sim_step

/-- info: 'STACS2027.Runtimes.Flow.callIndex' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.callIndex

/-- info: 'STACS2027.Runtimes.Flow.callSpan' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.callSpan

/-- info: 'STACS2027.Runtimes.Flow.callInput' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.callInput

/-- info: 'STACS2027.Runtimes.Flow.callLength' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.callLength

/-- info: 'STACS2027.Runtimes.Flow.callOutput' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.callOutput

/-- info: 'STACS2027.Runtimes.Flow.callAddress' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.callAddress

/-- info: 'STACS2027.Runtimes.Flow.callValue' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.callValue

/-- info: 'STACS2027.Runtimes.Flow.callZero' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.callZero

/-- info: 'STACS2027.Runtimes.Flow.callCount' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.callCount

/-- info: 'STACS2027.Runtimes.Flow.callRemaining' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.callRemaining

/-- info: 'STACS2027.Runtimes.Flow.callBegin' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.callBegin

/-- info: 'STACS2027.Runtimes.Flow.callOne' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.callOne

/-- info: 'STACS2027.Runtimes.Flow.resetCallRegisters' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.resetCallRegisters

/-- info: '_private.Runtimes.Flow.ReusableCall.0.STACS2027.Runtimes.Flow.resetCallRegisters_loopFree' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.resetCallRegisters_loopFree

/-- info: '_private.Runtimes.Flow.ReusableCall.0.STACS2027.Runtimes.Flow.resetCallRegisters_size' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.resetCallRegisters_size

/-- info: '_private.Runtimes.Flow.ReusableCall.0.STACS2027.Runtimes.Flow.resetCallRegisters_run' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.resetCallRegisters_run

/-- info: 'STACS2027.Runtimes.Flow.resetCallRegisters_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.resetCallRegisters_spec

/-- info: 'STACS2027.Runtimes.Flow.ExecB.memory_above' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.ExecB.memory_above

/-- info: 'STACS2027.Runtimes.Flow.ExecB.output_length_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.ExecB.output_length_bound

/-- info: 'STACS2027.Runtimes.Flow.clearCallBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.clearCallBody

/-- info: 'STACS2027.Runtimes.Flow.copyCallBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.copyCallBody

/-- info: 'STACS2027.Runtimes.Flow.initializeCall' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.initializeCall

/-- info: 'STACS2027.Runtimes.Flow.countCallBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.countCallBody

/-- info: 'STACS2027.Runtimes.Flow.countCallOutput' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.countCallOutput

/-- info: 'STACS2027.Runtimes.Flow.reusableCall' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.reusableCall

/-- info: 'STACS2027.Runtimes.Flow.CallMeta' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.CallMeta

/-- info: '_private.Runtimes.Flow.ReusableCall.0.STACS2027.Runtimes.Flow.CallMeta.kept' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.CallMeta.kept

/-- info: '_private.Runtimes.Flow.ReusableCall.0.STACS2027.Runtimes.Flow.classZeroReg_kept' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.classZeroReg_kept

/-- info: 'STACS2027.Runtimes.Flow.clearedCallMemory' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.clearedCallMemory

/-- info: 'STACS2027.Runtimes.Flow.copiedCallMemory' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.copiedCallMemory

/-- info: 'STACS2027.Runtimes.Flow.CallClearInv' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.CallClearInv

/-- info: 'STACS2027.Runtimes.Flow.CallCopyInv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.CallCopyInv

/-- info: 'STACS2027.Runtimes.Flow.clearCallBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.clearCallBody_spec

/-- info: 'STACS2027.Runtimes.Flow.copyCallBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.copyCallBody_spec

/-- info: '_private.Runtimes.Flow.ReusableCall.0.STACS2027.Runtimes.Flow.CallClearInv.independent' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.CallClearInv.independent

/-- info: '_private.Runtimes.Flow.ReusableCall.0.STACS2027.Runtimes.Flow.CallCopyInv.independent' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.CallCopyInv.independent

/-- info: 'STACS2027.Runtimes.Flow.initializeCall_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.initializeCall_spec

/-- info: '_private.Runtimes.Flow.ReusableCall.0.STACS2027.Runtimes.Flow.clearCall_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.clearCall_spec

/-- info: '_private.Runtimes.Flow.ReusableCall.0.STACS2027.Runtimes.Flow.copyCall_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.copyCall_spec

/-- info: '_private.Runtimes.Flow.ReusableCall.0.STACS2027.Runtimes.Flow.CallCountInv' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.CallCountInv

/-- info: '_private.Runtimes.Flow.ReusableCall.0.STACS2027.Runtimes.Flow.countCallBody_spec' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.countCallBody_spec

/-- info: 'STACS2027.Runtimes.Flow.countCallOutput_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.countCallOutput_spec

/-- info: '_private.Runtimes.Flow.ReusableCall.0.STACS2027.Runtimes.Flow.CallMeta.transfer' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.CallMeta.transfer

/-- info: 'STACS2027.Runtimes.Flow.CallResult' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.CallResult

/-- info: 'STACS2027.Runtimes.Flow.reusableCall_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.reusableCall_spec

/-- info: 'STACS2027.Runtimes.Flow.CallResult.memory_high' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.CallResult.memory_high

/-- info: 'STACS2027.Runtimes.Flow.CallResult.array_high' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.CallResult.array_high

/-- info: 'STACS2027.Runtimes.Flow.availableEdge' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.availableEdge

/-- info: 'STACS2027.Runtimes.Flow.ResidualStep' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.ResidualStep

/-- info: 'STACS2027.Runtimes.Flow.ResidualReach' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.ResidualReach

/-- info: 'STACS2027.Runtimes.Flow.reverseStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.reverseStep

/-- info: 'STACS2027.Runtimes.Flow.reverseReachSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.reverseReachSet

/-- info: '_private.Runtimes.Flow.ReverseReach.0.STACS2027.Runtimes.Flow.subset_reverseStep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.subset_reverseStep

/-- info: '_private.Runtimes.Flow.ReverseReach.0.STACS2027.Runtimes.Flow.reverseReachSet_stays_fixed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.reverseReachSet_stays_fixed

/-- info: 'STACS2027.Runtimes.Flow.reverseReachSet_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.reverseReachSet_fixed

/-- info: 'STACS2027.Runtimes.Flow.reverseReachSet_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.reverseReachSet_sound

/-- info: 'STACS2027.Runtimes.Flow.reverseReachSet_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.reverseReachSet_complete

/-- info: 'STACS2027.Runtimes.Flow.maximalCutRegion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.maximalCutRegion

/-- info: 'STACS2027.Runtimes.Flow.maximalCutRegion_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.maximalCutRegion_closed

/-- info: 'STACS2027.Runtimes.Flow.residualClosed_subset_maximalCutRegion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.residualClosed_subset_maximalCutRegion

/-- info: 'STACS2027.Runtimes.Flow.maximalCutRegion_minimum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.maximalCutRegion_minimum

/-- info: 'STACS2027.Runtimes.Flow.reverseEdgeStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.reverseEdgeStep

/-- info: 'STACS2027.Runtimes.Flow.reverseScan' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.reverseScan

/-- info: 'STACS2027.Runtimes.Flow.reverseScanSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.reverseScanSet

/-- info: '_private.Runtimes.Flow.ReverseScan.0.STACS2027.Runtimes.Flow.subset_edgeStep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.subset_edgeStep

/-- info: '_private.Runtimes.Flow.ReverseScan.0.STACS2027.Runtimes.Flow.subset_scanList' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.subset_scanList

/-- info: '_private.Runtimes.Flow.ReverseScan.0.STACS2027.Runtimes.Flow.predecessor_scanList' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.predecessor_scanList

/-- info: 'STACS2027.Runtimes.Flow.reverseStep_subset_reverseScan' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.reverseStep_subset_reverseScan

/-- info: '_private.Runtimes.Flow.ReverseScan.0.STACS2027.Runtimes.Flow.reverseStep_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.reverseStep_mono

/-- info: 'STACS2027.Runtimes.Flow.reverseReachSet_subset_reverseScanSet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.reverseReachSet_subset_reverseScanSet

/-- info: '_private.Runtimes.Flow.ReverseScan.0.STACS2027.Runtimes.Flow.scanList_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.scanList_sound

/-- info: 'STACS2027.Runtimes.Flow.reverseScanSet_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.reverseScanSet_sound

/-- info: 'STACS2027.Runtimes.Flow.reverseScanSet_eq_reverseReachSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.reverseScanSet_eq_reverseReachSet

/-- info: 'STACS2027.Runtimes.Flow.paddedMaxFlow_cut_optimal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.paddedMaxFlow_cut_optimal

/-- info: 'STACS2027.Runtimes.Flow.paddedMaxFlow_oracle_quadratic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.paddedMaxFlow_oracle_quadratic

/-- info: 'STACS2027.Runtimes.Flow.paddedMaxFlow_oracle_cut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.paddedMaxFlow_oracle_cut

/-- info: 'STACS2027.Runtimes.Flow.yM' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.yM

/-- info: 'STACS2027.Runtimes.Flow.yV' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.yV

/-- info: 'STACS2027.Runtimes.Flow.yC' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.yC

/-- info: 'STACS2027.Runtimes.Flow.yA' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.yA

/-- info: 'STACS2027.Runtimes.Flow.yK' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.yK

/-- info: 'STACS2027.Runtimes.Flow.yT' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.yT

/-- info: 'STACS2027.Runtimes.Flow.yKT' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.yKT

/-- info: 'STACS2027.Runtimes.Flow.yQ' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.yQ

/-- info: 'STACS2027.Runtimes.Flow.lenRead' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.lenRead

/-- info: 'STACS2027.Runtimes.Flow.lenFlow' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.lenFlow

/-- info: 'STACS2027.Runtimes.Flow.lenFlow_value_app' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.lenFlow_value_app

/-- info: 'STACS2027.Runtimes.Flow.lenFlow_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.lenFlow_value

/-- info: 'STACS2027.Runtimes.Flow.lenFlow_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.lenFlow_spec

/-- info: 'STACS2027.Runtimes.Flow.cpap4_flow_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.cpap4_flow_single

/-- info: 'STACS2027.Runtimes.Flow.triangle_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.triangle_single

/-- info: 'STACS2027.Runtimes.Flow.cpap4_flow_single_almostLinear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.cpap4_flow_single_almostLinear

/-- info: 'STACS2027.Runtimes.Flow.triangle_single_almostLinear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.triangle_single_almostLinear

/-- info: 'STACS2027.Runtimes.Flow.select' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.select

/-- info: 'STACS2027.Runtimes.Flow.encArcs' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.encArcs

/-- info: 'STACS2027.Runtimes.Flow.netInput' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.netInput

/-- info: 'STACS2027.Runtimes.Flow.NodeOf' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.NodeOf

/-- info: 'STACS2027.Runtimes.Flow.GoodNet' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.GoodNet

/-- info: 'STACS2027.Runtimes.Flow.IsMinFlow' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.IsMinFlow

/-- info: 'STACS2027.Runtimes.Flow.FlowAnswer' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.FlowAnswer

/-- info: 'STACS2027.Runtimes.Flow.MinCostFlowSolver' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.MinCostFlowSolver

/-- info: 'STACS2027.Runtimes.Flow.AlmostLinear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.AlmostLinear

/-- info: 'STACS2027.Runtimes.Flow.length_encArcs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.length_encArcs

/-- info: 'STACS2027.Runtimes.Flow.length_netInput' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.length_netInput

/-- info: 'STACS2027.Runtimes.Flow.encArcs_append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.encArcs_append

/-- info: 'STACS2027.Runtimes.Flow.select_sublist' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.select_sublist

/-- info: 'STACS2027.Runtimes.Flow.getD_mem_select' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.getD_mem_select

/-- info: 'STACS2027.Runtimes.Flow.flowInput_cycles' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.flowInput_cycles

/-- info: 'STACS2027.Runtimes.Flow.eList_cycles' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.eList_cycles

/-- info: 'STACS2027.Runtimes.Flow.eid_cycles' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.eid_cycles

/-- info: 'STACS2027.Runtimes.Flow.cntF_cycles' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.cntF_cycles

/-- info: 'STACS2027.Runtimes.Flow.ob_of_front' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.ob_of_front

/-- info: 'STACS2027.Runtimes.Flow.build3s' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.build3s

/-- info: 'STACS2027.Runtimes.Flow.CB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.CB

/-- info: 'STACS2027.Runtimes.Flow.sB3' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.sB3

/-- info: 'STACS2027.Runtimes.Flow.isCycle_cycles' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.isCycle_cycles

/-- info: 'STACS2027.Runtimes.Flow.frontCost3_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.frontCost3_le

/-- info: 'STACS2027.Runtimes.Flow.build3s_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.build3s_spec

/-- info: 'STACS2027.Runtimes.Flow.sB3_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.sB3_le

/-- info: 'STACS2027.Runtimes.Flow.triangle_sort_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.triangle_sort_core

/-- info: 'STACS2027.Runtimes.Flow.triangle_sort_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.triangle_sort_single

/-- info: 'STACS2027.Runtimes.Flow.triangle_sort_single_almostLinear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.triangle_sort_single_almostLinear

/-- info: 'STACS2027.Runtimes.Flow.buildSorted' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.buildSorted

/-- info: 'STACS2027.Runtimes.Flow.sortedBuildSpace' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.sortedBuildSpace

/-- info: 'STACS2027.Runtimes.Flow.sortedBuildConstant' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.sortedBuildConstant

/-- info: 'STACS2027.Runtimes.Flow.sortedBuildTime' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.sortedBuildTime

/-- info: 'STACS2027.Runtimes.Flow.sortedBuild_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.sortedBuild_spec

/-- info: 'STACS2027.Runtimes.Flow.sortedBuild_memory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.sortedBuild_memory

/-- info: 'STACS2027.Runtimes.Flow.sortedBuild_logarithm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.sortedBuild_logarithm

/-- info: 'STACS2027.Runtimes.Flow.sortedBuildTime_paper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.sortedBuildTime_paper

/-- info: 'STACS2027.Runtimes.Flow.sortedBuild_computes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.sortedBuild_computes

/-- info: 'STACS2027.Runtimes.Flow.sortedNetwork_construction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.sortedNetwork_construction

/-- info: 'STACS2027.Runtimes.Flow.sortedNetwork_pipeline' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.sortedNetwork_pipeline

/-- info: 'STACS2027.Runtimes.Flow.net4_hasAssignment_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.net4_hasAssignment_iff

/-- info: 'STACS2027.Runtimes.Flow.net3_hasAssignment_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.net3_hasAssignment_iff

/-- info: 'STACS2027.Runtimes.Flow.cpap4_flow_ram_semantic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.cpap4_flow_ram_semantic

/-- info: 'STACS2027.Runtimes.Flow.triangle_ram_semantic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.triangle_ram_semantic

/-- info: 'STACS2027.Runtimes.Flow.strideIndex' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.strideIndex

/-- info: 'STACS2027.Runtimes.Flow.strideAddress' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.strideAddress

/-- info: 'STACS2027.Runtimes.Flow.strideValue' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.strideValue

/-- info: 'STACS2027.Runtimes.Flow.strideTwo' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.strideTwo

/-- info: 'STACS2027.Runtimes.Flow.strideFour' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.strideFour

/-- info: 'STACS2027.Runtimes.Flow.strideZero' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.strideZero

/-- info: 'STACS2027.Runtimes.Flow.StridedInput' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.StridedInput

/-- info: 'STACS2027.Runtimes.Flow.strideReady' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.strideReady

/-- info: 'STACS2027.Runtimes.Flow.strideCopyBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.strideCopyBody

/-- info: 'STACS2027.Runtimes.Flow.strideCopy' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.strideCopy

/-- info: 'STACS2027.Runtimes.Flow.stridedCall' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.stridedCall

/-- info: 'STACS2027.Runtimes.Flow.StrideGlobals' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.StrideGlobals

/-- info: 'STACS2027.Runtimes.Flow.StrideCopyInv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.StrideCopyInv

/-- info: 'STACS2027.Runtimes.Flow.strideReady_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.strideReady_spec

/-- info: 'STACS2027.Runtimes.Flow.strideCopyBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.strideCopyBody_spec

/-- info: 'STACS2027.Runtimes.Flow.strideCopy_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.strideCopy_spec

/-- info: 'STACS2027.Runtimes.Flow.StridedCallResult' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.StridedCallResult

/-- info: 'STACS2027.Runtimes.Flow.stridedCall_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.stridedCall_spec

/-- info: 'STACS2027.Runtimes.Flow.StridedCallResult.input' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.StridedCallResult.input

/-- info: 'STACS2027.Runtimes.Flow.net3' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.net3

/-- info: 'STACS2027.Runtimes.Flow.net3_cycles' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.net3_cycles

/-- info: 'STACS2027.Runtimes.Flow.selected_three' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.selected_three

/-- info: 'STACS2027.Runtimes.Flow.tri_isCycle' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.tri_isCycle

/-- info: 'STACS2027.Runtimes.Flow.net3_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.net3_nodup

/-- info: 'STACS2027.Runtimes.Flow.tri_edges_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.tri_edges_length

/-- info: 'STACS2027.Runtimes.Flow.length_net3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.length_net3

/-- info: 'STACS2027.Runtimes.Flow.length_eList3' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.length_eList3

/-- info: 'STACS2027.Runtimes.Flow.flowOf3' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.flowOf3

/-- info: 'STACS2027.Runtimes.Flow.inflow_flowOf3' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.inflow_flowOf3

/-- info: 'STACS2027.Runtimes.Flow.outflow_flowOf3' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.outflow_flowOf3

/-- info: 'STACS2027.Runtimes.Flow.flowCost_flowOf3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.flowCost_flowOf3

/-- info: 'STACS2027.Runtimes.Flow.flowValue_flowOf3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.flowValue_flowOf3

/-- info: 'STACS2027.Runtimes.Flow.inflow_flowOf3_triangle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.inflow_flowOf3_triangle

/-- info: 'STACS2027.Runtimes.Flow.outflow_flowOf3_triangle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.outflow_flowOf3_triangle

/-- info: 'STACS2027.Runtimes.Flow.inflow_flowOf3_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.inflow_flowOf3_edge

/-- info: 'STACS2027.Runtimes.Flow.outflow_flowOf3_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.outflow_flowOf3_edge

/-- info: 'STACS2027.Runtimes.Flow.inflow_flowOf3_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.inflow_flowOf3_pair

/-- info: 'STACS2027.Runtimes.Flow.outflow_flowOf3_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.outflow_flowOf3_pair

/-- info: 'STACS2027.Runtimes.Flow.tri_path_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.tri_path_edge

/-- info: 'STACS2027.Runtimes.Flow.inflow3_edge_eq_load' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.inflow3_edge_eq_load

/-- info: 'STACS2027.Runtimes.Flow.tri_edge_mem_eList' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.tri_edge_mem_eList

/-- info: 'STACS2027.Runtimes.Flow.load_le_wcount3' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.load_le_wcount3

/-- info: 'STACS2027.Runtimes.Flow.load_eq_zero3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.load_eq_zero3

/-- info: 'STACS2027.Runtimes.Flow.cost_eq_load_sum3' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.cost_eq_load_sum3

/-- info: 'STACS2027.Runtimes.Flow.flow_of_assignment3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.flow_of_assignment3

/-- info: 'STACS2027.Runtimes.Flow.pos3' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.pos3

/-- info: 'STACS2027.Runtimes.Flow.readOff3' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.readOff3

/-- info: 'STACS2027.Runtimes.Flow.assignment_of_flow3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.assignment_of_flow3

/-- info: 'STACS2027.Runtimes.Flow.optimal_of_minFlow3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.optimal_of_minFlow3

/-- info: 'STACS2027.Runtimes.Flow.num3' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.num3

/-- info: 'STACS2027.Runtimes.Flow.n3' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.n3

/-- info: 'STACS2027.Runtimes.Flow.netEnc3' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.netEnc3

/-- info: 'STACS2027.Runtimes.Flow.triangleSourceLayer_succ' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.triangleSourceLayer_succ

/-- info: 'STACS2027.Runtimes.Flow.triangleLayer_succ' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.triangleLayer_succ

/-- info: 'STACS2027.Runtimes.Flow.triChunk3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.triChunk3

/-- info: 'STACS2027.Runtimes.Flow.num3_source' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.num3_source

/-- info: 'STACS2027.Runtimes.Flow.num3_sink' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.num3_sink

/-- info: 'STACS2027.Runtimes.Flow.num3_triangle' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.num3_triangle

/-- info: 'STACS2027.Runtimes.Flow.encArcs_triChunk3' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.encArcs_triChunk3

/-- info: 'STACS2027.Runtimes.Flow.encArcs_srcChunk3' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.encArcs_srcChunk3

/-- info: 'STACS2027.Runtimes.Flow.num3_occ' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.num3_occ

/-- info: 'STACS2027.Runtimes.Flow.num3_eList' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.num3_eList

/-- info: 'STACS2027.Runtimes.Flow.nodeOf_net3' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.nodeOf_net3

/-- info: 'STACS2027.Runtimes.Flow.goodNet3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.goodNet3

/-- info: 'STACS2027.Runtimes.Flow.triangleLayer_getD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.triangleLayer_getD

/-- info: 'STACS2027.Runtimes.Flow.net3_getD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.net3_getD

/-- info: 'STACS2027.Runtimes.Flow.readOff3_select' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Flow.readOff3_select

/-- info: 'STACS2027.Runtimes.GeneralCycles.representativeBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.representativeBody_spec

/-- info: 'STACS2027.Runtimes.GeneralCycles.outerScan_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.outerScan_spec

/-- info: 'STACS2027.Runtimes.GeneralCycles.initCounts_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.initCounts_spec

/-- info: 'STACS2027.Runtimes.GeneralCycles.enumerateProgram_computes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.enumerateProgram_computes

/-- info: 'STACS2027.Runtimes.GeneralCycles.tupleTime_double_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.tupleTime_double_bound

/-- info: 'STACS2027.Runtimes.GeneralCycles.graph_polynomial_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.graph_polynomial_bound

/-- info: 'STACS2027.Runtimes.GeneralCycles.callbackCost' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.callbackCost

/-- info: 'STACS2027.Runtimes.GeneralCycles.rejectionScan_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.rejectionScan_spec

/-- info: 'STACS2027.Runtimes.GeneralCycles.emitAccepted_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.emitAccepted_spec

/-- info: 'STACS2027.Runtimes.GeneralCycles.acceptanceFlag' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.acceptanceFlag

/-- info: 'STACS2027.Runtimes.GeneralCycles.innerValidFlag' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.innerValidFlag

/-- info: 'STACS2027.Runtimes.GeneralCycles.outerIndices' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.outerIndices

/-- info: 'STACS2027.Runtimes.GeneralCycles.outerValues' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.outerValues

/-- info: 'STACS2027.Runtimes.GeneralCycles.innerIndices' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.innerIndices

/-- info: 'STACS2027.Runtimes.GeneralCycles.innerValues' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.innerValues

/-- info: 'STACS2027.Runtimes.GeneralCycles.bit' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.bit

/-- info: 'STACS2027.Runtimes.GeneralCycles.registers' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.registers

/-- info: 'STACS2027.Runtimes.GeneralCycles.comparisonTest' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.comparisonTest

/-- info: 'STACS2027.Runtimes.GeneralCycles.clearCounter' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.clearCounter

/-- info: 'STACS2027.Runtimes.GeneralCycles.regValues_registers' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.regValues_registers

/-- info: 'STACS2027.Runtimes.GeneralCycles.registers_safe' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.registers_safe

/-- info: 'STACS2027.Runtimes.GeneralCycles.Placed.index_labels' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.Placed.index_labels

/-- info: 'STACS2027.Runtimes.GeneralCycles.comparisonTest_safe' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.comparisonTest_safe

/-- info: 'STACS2027.Runtimes.GeneralCycles.comparisonTest_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.comparisonTest_eval

/-- info: 'STACS2027.Runtimes.GeneralCycles.clearCounter_loopFree' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.clearCounter_loopFree

/-- info: 'STACS2027.Runtimes.GeneralCycles.clearCounter_memFree' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.clearCounter_memFree

/-- info: 'STACS2027.Runtimes.GeneralCycles.clearCounter_stores' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.clearCounter_stores

/-- info: 'STACS2027.Runtimes.GeneralCycles.clearCounter_writes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.clearCounter_writes

/-- info: 'STACS2027.Runtimes.GeneralCycles.clearCounter_wregs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.clearCounter_wregs

/-- info: 'STACS2027.Runtimes.GeneralCycles.clearCounter_agree' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.clearCounter_agree

/-- info: 'STACS2027.Runtimes.GeneralCycles.clearCounter_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.clearCounter_value

/-- info: 'STACS2027.Runtimes.GeneralCycles.endpoints' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.endpoints

/-- info: 'STACS2027.Runtimes.GeneralCycles.tuples' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.tuples

/-- info: 'STACS2027.Runtimes.GeneralCycles.tupleLabels' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.tupleLabels

/-- info: 'STACS2027.Runtimes.GeneralCycles.Valid' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.Valid

/-- info: 'STACS2027.Runtimes.GeneralCycles.Earlier' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.Earlier

/-- info: 'STACS2027.Runtimes.GeneralCycles.Accepted' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.Accepted

/-- info: 'STACS2027.Runtimes.GeneralCycles.outputCycles' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.outputCycles

/-- info: 'STACS2027.Runtimes.GeneralCycles.edgeCount' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.edgeCount

/-- info: 'STACS2027.Runtimes.GeneralCycles.edgeCounter' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.edgeCounter

/-- info: 'STACS2027.Runtimes.GeneralCycles.edgeAddr' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.edgeAddr

/-- info: 'STACS2027.Runtimes.GeneralCycles.edgeFirst' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.edgeFirst

/-- info: 'STACS2027.Runtimes.GeneralCycles.edgeSecond' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.edgeSecond

/-- info: 'STACS2027.Runtimes.GeneralCycles.edgeFound' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.edgeFound

/-- info: 'STACS2027.Runtimes.GeneralCycles.edgeScratch' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.edgeScratch

/-- info: 'STACS2027.Runtimes.GeneralCycles.edgeWrites' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.edgeWrites

/-- info: 'STACS2027.Runtimes.GeneralCycles.readEdge' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.readEdge

/-- info: 'STACS2027.Runtimes.GeneralCycles.inputEdgeTest' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.inputEdgeTest

/-- info: 'STACS2027.Runtimes.GeneralCycles.markEdge' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.markEdge

/-- info: 'STACS2027.Runtimes.GeneralCycles.edgeBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.edgeBody

/-- info: 'STACS2027.Runtimes.GeneralCycles.scanEdge' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.scanEdge

/-- info: 'STACS2027.Runtimes.GeneralCycles.inputEdgeTest_eval' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.inputEdgeTest_eval

/-- info: 'STACS2027.Runtimes.GeneralCycles.inputEdgeTest_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.inputEdgeTest_safe

/-- info: 'STACS2027.Runtimes.GeneralCycles.readEdge_loopFree' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.readEdge_loopFree

/-- info: 'STACS2027.Runtimes.GeneralCycles.markEdge_loopFree' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.markEdge_loopFree

/-- info: 'STACS2027.Runtimes.GeneralCycles.edgeBody_loopFree' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.edgeBody_loopFree

/-- info: 'STACS2027.Runtimes.GeneralCycles.markEdge_memFree' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.markEdge_memFree

/-- info: 'STACS2027.Runtimes.GeneralCycles.edgeBody_stores' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.edgeBody_stores

/-- info: 'STACS2027.Runtimes.GeneralCycles.edgeBody_writes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.edgeBody_writes

/-- info: 'STACS2027.Runtimes.GeneralCycles.edgeBody_wregs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.edgeBody_wregs

/-- info: 'STACS2027.Runtimes.GeneralCycles.edgeBody_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.edgeBody_agree

/-- info: 'STACS2027.Runtimes.GeneralCycles.readEdge_values' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.readEdge_values

/-- info: 'STACS2027.Runtimes.GeneralCycles.readEdge_reg' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.readEdge_reg

/-- info: 'STACS2027.Runtimes.GeneralCycles.edgeBody_found' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.edgeBody_found

/-- info: 'STACS2027.Runtimes.GeneralCycles.GraphMemory' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.GraphMemory

/-- info: 'STACS2027.Runtimes.GeneralCycles.graphMemory_initial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.graphMemory_initial

/-- info: 'STACS2027.Runtimes.GeneralCycles.EdgeInv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.EdgeInv

/-- info: 'STACS2027.Runtimes.GeneralCycles.edgeInv_indep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.edgeInv_indep

/-- info: 'STACS2027.Runtimes.GeneralCycles.edgeBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.edgeBody_spec

/-- info: 'STACS2027.Runtimes.GeneralCycles.scanEdge_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.scanEdge_spec

/-- info: 'STACS2027.Runtimes.GeneralCycles.foldTuples_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.foldTuples_eq

/-- info: 'STACS2027.Runtimes.GeneralCycles.Counterexample' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.Counterexample

/-- info: 'STACS2027.Runtimes.GeneralCycles.rejectStep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.rejectStep

/-- info: 'STACS2027.Runtimes.GeneralCycles.reject_fold_true' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.reject_fold_true

/-- info: 'STACS2027.Runtimes.GeneralCycles.rejection_result' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.rejection_result

/-- info: 'STACS2027.Runtimes.GeneralCycles.outputStep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.outputStep

/-- info: 'STACS2027.Runtimes.GeneralCycles.output_fold' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.output_fold

/-- info: 'STACS2027.Runtimes.GeneralCycles.output_result' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.output_result

/-- info: 'STACS2027.Runtimes.GeneralCycles.validCheck_validitySpec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.validCheck_validitySpec

/-- info: 'STACS2027.Runtimes.GeneralCycles.validityBudget' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.validityBudget

/-- info: 'STACS2027.Runtimes.GeneralCycles.cycleEnumerator' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.cycleEnumerator

/-- info: 'STACS2027.Runtimes.GeneralCycles.cycleEnumeratorConstant' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.cycleEnumeratorConstant

/-- info: 'STACS2027.Runtimes.GeneralCycles.cycleEnumerator_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.cycleEnumerator_correct

/-- info: 'STACS2027.Runtimes.generalCycleEnumerationRam' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.generalCycleEnumerationRam

/-- info: 'STACS2027.Runtimes.GeneralCycles.valuesList' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.valuesList

/-- info: 'STACS2027.Runtimes.GeneralCycles.emitValues' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.emitValues

/-- info: 'STACS2027.Runtimes.GeneralCycles.emitValues_loopFree' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.emitValues_loopFree

/-- info: 'STACS2027.Runtimes.GeneralCycles.emitValues_size' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.emitValues_size

/-- info: 'STACS2027.Runtimes.GeneralCycles.emitValues_addrOK' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.emitValues_addrOK

/-- info: 'STACS2027.Runtimes.GeneralCycles.emitValues_wregs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.emitValues_wregs

/-- info: 'STACS2027.Runtimes.GeneralCycles.emitValues_stores' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.emitValues_stores

/-- info: 'STACS2027.Runtimes.GeneralCycles.valuesList_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.valuesList_succ

/-- info: 'STACS2027.Runtimes.GeneralCycles.emitValues_out' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.emitValues_out

/-- info: 'STACS2027.Runtimes.GeneralCycles.emitValues_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.emitValues_spec

/-- info: 'STACS2027.Runtimes.GeneralCycles.initial_endpoint' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.initial_endpoint

/-- info: 'STACS2027.Runtimes.GeneralCycles.Placed.emission_labels' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.Placed.emission_labels

/-- info: 'STACS2027.Runtimes.GeneralCycles.Held' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.Held

/-- info: 'STACS2027.Runtimes.GeneralCycles.allPairs' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.allPairs

/-- info: 'STACS2027.Runtimes.GeneralCycles.andFlag' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.andFlag

/-- info: 'STACS2027.Runtimes.GeneralCycles.scanPairs' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.scanPairs

/-- info: 'STACS2027.Runtimes.GeneralCycles.held_indep' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.held_indep

/-- info: 'STACS2027.Runtimes.GeneralCycles.andFlag_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.andFlag_spec

/-- info: 'STACS2027.Runtimes.GeneralCycles.edgeBody_size_le' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.edgeBody_size_le

/-- info: 'STACS2027.Runtimes.GeneralCycles.scanPairs_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.scanPairs_spec

/-- info: 'STACS2027.Runtimes.GeneralCycles.programConstant' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.GeneralCycles.programConstant

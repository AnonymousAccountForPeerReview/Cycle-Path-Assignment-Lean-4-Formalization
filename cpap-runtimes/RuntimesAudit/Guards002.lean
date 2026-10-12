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

/-- info: 'STACS2027.Runtimes.ConvexQP.rK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.rK

/-- info: 'STACS2027.Runtimes.ConvexQP.Phi0_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Phi0_pos

/-- info: 'STACS2027.Runtimes.ConvexQP.rK_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.rK_pos

/-- info: 'STACS2027.Runtimes.ConvexQP.div_rK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.div_rK

/-- info: 'STACS2027.Runtimes.ConvexQP.inY_convex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.inY_convex

/-- info: 'STACS2027.Runtimes.ConvexQP.ball_in_Kset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.ball_in_Kset

/-- info: 'STACS2027.Runtimes.ConvexQP.stOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.stOf

/-- info: 'STACS2027.Runtimes.ConvexQP.ellIter_inr_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.ellIter_inr_succ

/-- info: 'STACS2027.Runtimes.ConvexQP.ellIter_inr_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.ellIter_inr_le

/-- info: 'STACS2027.Runtimes.ConvexQP.ellIter_inl_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.ellIter_inl_le

/-- info: 'STACS2027.Runtimes.ConvexQP.ellIter_succ_inl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.ellIter_succ_inl

/-- info: 'STACS2027.Runtimes.ConvexQP.ellIter_inr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.ellIter_inr

/-- info: 'STACS2027.Runtimes.ConvexQP.ellIter_cut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.ellIter_cut

/-- info: 'STACS2027.Runtimes.ConvexQP.isSymm_of_QR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.isSymm_of_QR

/-- info: 'STACS2027.Runtimes.ConvexQP.prec_facts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.prec_facts

/-- info: 'STACS2027.Runtimes.ConvexQP.ellIter_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.ellIter_inv

/-- info: 'STACS2027.Runtimes.ConvexQP.ellRun_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.ellRun_success

/-- info: 'STACS2027.Runtimes.ConvexQP.phaseE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.phaseE

/-- info: 'STACS2027.Runtimes.ConvexQP.phaseE_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.phaseE_spec

/-- info: 'STACS2027.Runtimes.ConvexQP.solveExact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.solveExact

/-- info: 'STACS2027.Runtimes.ConvexQP.relaxation_exact_optimal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.relaxation_exact_optimal

/-- info: 'STACS2027.Runtimes.ConvexQP.solveExact_map_fst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.solveExact_map_fst

/-- info: 'STACS2027.Runtimes.ConvexQP.nRows' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.nRows

/-- info: 'STACS2027.Runtimes.ConvexQP.colEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.colEquiv

/-- info: 'STACS2027.Runtimes.ConvexQP.rowEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.rowEquiv

/-- info: 'STACS2027.Runtimes.ConvexQP.sgnS' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.sgnS

/-- info: 'STACS2027.Runtimes.ConvexQP.coefX' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.coefX

/-- info: 'STACS2027.Runtimes.ConvexQP.coefL' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.coefL

/-- info: 'STACS2027.Runtimes.ConvexQP.kktEntry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.kktEntry

/-- info: 'STACS2027.Runtimes.ConvexQP.kktRhs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.kktRhs

/-- info: 'STACS2027.Runtimes.ConvexQP.kktG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.kktG

/-- info: 'STACS2027.Runtimes.ConvexQP.kktH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.kktH

/-- info: 'STACS2027.Runtimes.ConvexQP.kktZ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.kktZ

/-- info: 'STACS2027.Runtimes.ConvexQP.kktZn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.kktZn

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.colX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.colX

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.colP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.colP

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.xOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.xOf

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.piOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.piOf

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.exactFrom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.exactFrom

/-- info: 'STACS2027.Runtimes.ConvexQP.rowVal_kkt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.rowVal_kkt

/-- info: 'STACS2027.Runtimes.ConvexQP.rowVal_S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.rowVal_S

/-- info: 'STACS2027.Runtimes.ConvexQP.sum_delta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.sum_delta

/-- info: 'STACS2027.Runtimes.ConvexQP.rowVal_X' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.rowVal_X

/-- info: 'STACS2027.Runtimes.ConvexQP.kktH_S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.kktH_S

/-- info: 'STACS2027.Runtimes.ConvexQP.kktH_X' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.kktH_X

/-- info: 'STACS2027.Runtimes.ConvexQP.forall_rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.forall_rows

/-- info: 'STACS2027.Runtimes.ConvexQP.vec_ext' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.vec_ext

/-- info: 'STACS2027.Runtimes.ConvexQP.coef_cases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.coef_cases

/-- info: 'STACS2027.Runtimes.ConvexQP.kktG_entry_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.kktG_entry_le

/-- info: 'STACS2027.Runtimes.ConvexQP.kkt_bdd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.kkt_bdd

/-- info: 'STACS2027.Runtimes.ConvexQP.xhat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.xhat

/-- info: 'STACS2027.Runtimes.ConvexQP.ptOf_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.ptOf_eq

/-- info: 'STACS2027.Runtimes.ConvexQP.xOf_ptZ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.xOf_ptZ

/-- info: 'STACS2027.Runtimes.ConvexQP.piOf_ptZ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.piOf_ptZ

/-- info: 'STACS2027.Runtimes.ConvexQP.kktZ_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.kktZ_iff

/-- info: 'STACS2027.Runtimes.ConvexQP.term_le_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.term_le_gap

/-- info: 'STACS2027.Runtimes.ConvexQP.le_of_sq_le_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.le_of_sq_le_sq

/-- info: 'STACS2027.Runtimes.ConvexQP.eps_lt_inv_k' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.eps_lt_inv_k

/-- info: 'STACS2027.Runtimes.ConvexQP.exists_not_Z' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.exists_not_Z

/-- info: 'STACS2027.Runtimes.ConvexQP.kkt_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.kkt_approx

/-- info: 'STACS2027.Runtimes.ConvexQP.kkt_optimal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.kkt_optimal

/-- info: 'STACS2027.Runtimes.ConvexQP.kkt_box' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.kkt_box

/-- info: 'STACS2027.Runtimes.ConvexQP.exactFrom_optimal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.exactFrom_optimal

/-- info: 'STACS2027.Runtimes.ConvexQP.exactFrom_magnitudes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.exactFrom_magnitudes

/-- info: 'STACS2027.Runtimes.ConvexQP.solveExactWith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.solveExactWith

/-- info: 'STACS2027.Runtimes.ConvexQP.solveExactWith_optimal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.solveExactWith_optimal

/-- info: 'STACS2027.Runtimes.ConvexQP.solveExactWith_map_fst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.solveExactWith_map_fst

/-- info: 'STACS2027.Runtimes.ConvexQP.rounding_solveExactWith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.rounding_solveExactWith

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.Valid' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.Valid

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.cnt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.cnt

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.H

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.lam' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.lam

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.L' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.L

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.inner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.inner

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.L_eq_H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.L_eq_H

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.lam_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.lam_map

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.L_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.L_map

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.lam_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.lam_add

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.lam_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.lam_smul

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.L_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.L_add

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.L_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.L_smul

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.lam_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.lam_sub

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.L_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.L_sub

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.pi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.pi

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.gap

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.pi_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.pi_le

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.exists_L_eq_pi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.exists_L_eq_pi

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.pi_eq_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.pi_eq_of

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.F' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.F

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.Phi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.Phi

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.InX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.InX

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.vtx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.vtx

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.L_intCast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.L_intCast

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.lam_intCast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.lam_intCast

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.L_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.L_div

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.lam_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.lam_div

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.pi_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.pi_div

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.gap_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.gap_div

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.sum_count_fin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.sum_count_fin

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.sum_cnt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.sum_cnt

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.cnt_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.cnt_le_one

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.sum_cnt_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.sum_cnt_valid

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.H_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.H_le

/-- info: 'STACS2027.Runtimes.ConvexQP.dimKKT' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.dimKKT

/-- info: 'STACS2027.Runtimes.ConvexQP.entryBound' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.entryBound

/-- info: 'STACS2027.Runtimes.ConvexQP.bigE' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.bigE

/-- info: 'STACS2027.Runtimes.ConvexQP.eps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.eps

/-- info: 'STACS2027.Runtimes.ConvexQP.curv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.curv

/-- info: 'STACS2027.Runtimes.ConvexQP.Phi0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Phi0

/-- info: 'STACS2027.Runtimes.ConvexQP.entryBound_pos' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.entryBound_pos

/-- info: 'STACS2027.Runtimes.ConvexQP.bigE_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.bigE_pos

/-- info: 'STACS2027.Runtimes.ConvexQP.eps_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.eps_pos

/-- info: 'STACS2027.Runtimes.ConvexQP.ptOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.ptOf

/-- info: 'STACS2027.Runtimes.ConvexQP.PhaseESpec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.PhaseESpec

/-- info: 'STACS2027.Runtimes.ConvexQP.path' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.path

/-- info: 'STACS2027.Runtimes.ConvexQP.ofOpts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.ofOpts

/-- info: 'STACS2027.Runtimes.ConvexQP.weightsOf' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.weightsOf

/-- info: 'STACS2027.Runtimes.ConvexQP.wlists' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.wlists

/-- info: 'STACS2027.Runtimes.ConvexQP.getD_of_lt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.getD_of_lt

/-- info: 'STACS2027.Runtimes.ConvexQP.weightedSum_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.weightedSum_eq_sum

/-- info: 'STACS2027.Runtimes.ConvexQP.sum_getD_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.sum_getD_eq_sum

/-- info: 'STACS2027.Runtimes.ConvexQP.fractionalLoad_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.fractionalLoad_eq_sum

/-- info: 'STACS2027.Runtimes.ConvexQP.path_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.path_mem

/-- info: 'STACS2027.Runtimes.ConvexQP.cnt_ofOpts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.cnt_ofOpts

/-- info: 'STACS2027.Runtimes.ConvexQP.fractionalLoad_get' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.fractionalLoad_get

/-- info: 'STACS2027.Runtimes.ConvexQP.relaxationObjective_eq_Phi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.relaxationObjective_eq_Phi

/-- info: 'STACS2027.Runtimes.ConvexQP.weightsOf_zip' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.weightsOf_zip

/-- info: 'STACS2027.Runtimes.ConvexQP.map_fst_zip_wlists' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.map_fst_zip_wlists

/-- info: 'STACS2027.Runtimes.ConvexQP.optimalFractional_of_min' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.optimalFractional_of_min

/-- info: 'STACS2027.Runtimes.ConvexQP.cycles_opts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.cycles_opts

/-- info: 'STACS2027.Runtimes.ConvexQP.length_filter_finRange_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.length_filter_finRange_mem

/-- info: 'STACS2027.Runtimes.ConvexQP.ofOpts_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.ofOpts_valid

/-- info: 'STACS2027.Runtimes.ConvexQP.ofOpts_valid_cycles' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.ofOpts_valid_cycles

/-- info: 'STACS2027.Runtimes.ConvexQP.qf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.qf

/-- info: 'STACS2027.Runtimes.ConvexQP.FormGe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.FormGe

/-- info: 'STACS2027.Runtimes.ConvexQP.FormLe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.FormLe

/-- info: 'STACS2027.Runtimes.ConvexQP.InEll' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.InEll

/-- info: 'STACS2027.Runtimes.ConvexQP.dot_self_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.dot_self_nonneg

/-- info: 'STACS2027.Runtimes.ConvexQP.dot_self_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.dot_self_pos

/-- info: 'STACS2027.Runtimes.ConvexQP.isHermitian_of_isSymm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.isHermitian_of_isSymm

/-- info: 'STACS2027.Runtimes.ConvexQP.dot_mulVec_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.dot_mulVec_comm

/-- info: 'STACS2027.Runtimes.ConvexQP.qf_add_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.qf_add_smul

/-- info: 'STACS2027.Runtimes.ConvexQP.qf_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.qf_smul

/-- info: 'STACS2027.Runtimes.ConvexQP.qf_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.qf_sub

/-- info: 'STACS2027.Runtimes.ConvexQP.qf_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.qf_add

/-- info: 'STACS2027.Runtimes.ConvexQP.qf_vecMulVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.qf_vecMulVec

/-- info: 'STACS2027.Runtimes.ConvexQP.qf_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.qf_one

/-- info: 'STACS2027.Runtimes.ConvexQP.qf_neg_smul_self_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.qf_neg_smul_self_le

/-- info: 'STACS2027.Runtimes.ConvexQP.sq_dot_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.sq_dot_le

/-- info: 'STACS2027.Runtimes.ConvexQP.inEll_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.inEll_mono

/-- info: 'STACS2027.Runtimes.ConvexQP.inEll_of_image' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.inEll_of_image

/-- info: 'STACS2027.Runtimes.ConvexQP.image_of_inEll' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.image_of_inEll

/-- info: 'STACS2027.Runtimes.ConvexQP.formGe_of_ball' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.formGe_of_ball

/-- info: 'STACS2027.Runtimes.ConvexQP.posSemidef_of_form' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.posSemidef_of_form

/-- info: 'STACS2027.Runtimes.ConvexQP.posDef_of_formGe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.posDef_of_formGe

/-- info: 'STACS2027.Runtimes.ConvexQP.formGe_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.formGe_nonneg

/-- info: 'STACS2027.Runtimes.ConvexQP.one_le_det_of_one_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.one_le_det_of_one_le

/-- info: 'STACS2027.Runtimes.ConvexQP.det_le_det_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.det_le_det_of_le

/-- info: 'STACS2027.Runtimes.ConvexQP.pow_le_det' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.pow_le_det

/-- info: 'STACS2027.Runtimes.ConvexQP.det_le_det_of_form' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.det_le_det_of_form

/-- info: 'STACS2027.Runtimes.ConvexQP.qf_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.qf_single

/-- info: 'STACS2027.Runtimes.ConvexQP.dot_single_mulVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.dot_single_mulVec

/-- info: 'STACS2027.Runtimes.ConvexQP.sq_mulVec_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.sq_mulVec_le

/-- info: 'STACS2027.Runtimes.ConvexQP.diag_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.diag_le

/-- info: 'STACS2027.Runtimes.ConvexQP.abs_entry_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.abs_entry_le

/-- info: 'STACS2027.Runtimes.ConvexQP.amStep' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.amStep

/-- info: 'STACS2027.Runtimes.ConvexQP.argMinRatio' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.argMinRatio

/-- info: 'STACS2027.Runtimes.ConvexQP.AmInv' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.AmInv

/-- info: 'STACS2027.Runtimes.ConvexQP.amStep_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.amStep_inv

/-- info: 'STACS2027.Runtimes.ConvexQP.foldl_amInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.foldl_amInv

/-- info: 'STACS2027.Runtimes.ConvexQP.argMinRatio_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.argMinRatio_some

/-- info: 'STACS2027.Runtimes.ConvexQP.argMinRatio_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.argMinRatio_spec

/-- info: 'STACS2027.Runtimes.ConvexQP.extend' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.extend

/-- info: 'STACS2027.Runtimes.ConvexQP.sum_mul_extend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.sum_mul_extend

/-- info: 'STACS2027.Runtimes.ConvexQP.subB' depends on axioms: [Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.subB

/-- info: 'STACS2027.Runtimes.ConvexQP.subB_snoc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.subB_snoc

/-- info: 'STACS2027.Runtimes.ConvexQP.MState' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.MState

/-- info: 'STACS2027.Runtimes.ConvexQP.MState.init' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.MState.init

/-- info: 'STACS2027.Runtimes.ConvexQP.mDir' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.mDir

/-- info: 'STACS2027.Runtimes.ConvexQP.mOmega' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.mOmega

/-- info: 'STACS2027.Runtimes.ConvexQP.mSigma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.mSigma

/-- info: 'STACS2027.Runtimes.ConvexQP.mNext' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.mNext

/-- info: 'STACS2027.Runtimes.ConvexQP.moveStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.moveStep

/-- info: 'STACS2027.Runtimes.ConvexQP.moveAux' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.moveAux

/-- info: 'STACS2027.Runtimes.ConvexQP.moveRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.moveRun

/-- info: 'STACS2027.Runtimes.ConvexQP.zNum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.zNum

/-- info: 'STACS2027.Runtimes.ConvexQP.ptZ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.ptZ

/-- info: 'STACS2027.Runtimes.ConvexQP.rowVal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.rowVal

/-- info: 'STACS2027.Runtimes.ConvexQP.zStar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.zStar

/-- info: 'STACS2027.Runtimes.ConvexQP.Bdd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Bdd

/-- info: 'STACS2027.Runtimes.ConvexQP.Inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inv

/-- info: 'STACS2027.Runtimes.ConvexQP.rowVal_ptZ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.rowVal_ptZ

/-- info: 'STACS2027.Runtimes.ConvexQP.mOmega_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.mOmega_apply

/-- info: 'STACS2027.Runtimes.ConvexQP.mDir_last' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.mDir_last

/-- info: 'STACS2027.Runtimes.ConvexQP.mOmega_T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.mOmega_T

/-- info: 'STACS2027.Runtimes.ConvexQP.exists_mOmega_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.exists_mOmega_pos

/-- info: 'STACS2027.Runtimes.ConvexQP.rowVal_mNext' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.rowVal_mNext

/-- info: 'STACS2027.Runtimes.ConvexQP.mSigma_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.mSigma_div

/-- info: 'STACS2027.Runtimes.ConvexQP.moveStep_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.moveStep_inv

/-- info: 'STACS2027.Runtimes.ConvexQP.moveStep_isSome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.moveStep_isSome

/-- info: 'STACS2027.Runtimes.ConvexQP.init_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.init_inv

/-- info: 'STACS2027.Runtimes.ConvexQP.moveAux_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.moveAux_inv

/-- info: 'STACS2027.Runtimes.ConvexQP.abs_det_subB_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.abs_det_subB_le

/-- info: 'STACS2027.Runtimes.ConvexQP.abs_adjugate_subB_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.abs_adjugate_subB_le

/-- info: 'STACS2027.Runtimes.ConvexQP.factorial_pow_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.factorial_pow_mono

/-- info: 'STACS2027.Runtimes.ConvexQP.moveAux_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.moveAux_bounds

/-- info: 'STACS2027.Runtimes.ConvexQP.Inv.Zn_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inv.Zn_bound

/-- info: 'STACS2027.Runtimes.ConvexQP.moveRun_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.moveRun_exact

/-- info: 'STACS2027.Runtimes.ConvexQP.roundDiv' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.roundDiv

/-- info: 'STACS2027.Runtimes.ConvexQP.roundDiv_err' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.roundDiv_err

/-- info: 'STACS2027.Runtimes.ConvexQP.isqrt_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.isqrt_approx

/-- info: 'STACS2027.Runtimes.ConvexQP.isqrt_err' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.isqrt_err

/-- info: 'STACS2027.Runtimes.ConvexQP.etaOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.etaOf

/-- info: 'STACS2027.Runtimes.ConvexQP.ellOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.ellOf

/-- info: 'STACS2027.Runtimes.ConvexQP.thetaOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.thetaOf

/-- info: 'STACS2027.Runtimes.ConvexQP.growOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.growOf

/-- info: 'STACS2027.Runtimes.ConvexQP.etaOf_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.etaOf_pos

/-- info: 'STACS2027.Runtimes.ConvexQP.etaOf_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.etaOf_le

/-- info: 'STACS2027.Runtimes.ConvexQP.ellOf_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.ellOf_pos

/-- info: 'STACS2027.Runtimes.ConvexQP.ellOf_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.ellOf_succ

/-- info: 'STACS2027.Runtimes.ConvexQP.ellOf_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.ellOf_zero

/-- info: 'STACS2027.Runtimes.ConvexQP.ellOf_anti' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.ellOf_anti

/-- info: 'STACS2027.Runtimes.ConvexQP.ellOf_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.ellOf_le

/-- info: 'STACS2027.Runtimes.ConvexQP.thetaOf_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.thetaOf_pos

/-- info: 'STACS2027.Runtimes.ConvexQP.growOf_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.growOf_pos

/-- info: 'STACS2027.Runtimes.ConvexQP.one_add_le_exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.one_add_le_exp

/-- info: 'STACS2027.Runtimes.ConvexQP.pow_le_exp_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.pow_le_exp_mul

/-- info: 'STACS2027.Runtimes.ConvexQP.kap_part_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.kap_part_le

/-- info: 'STACS2027.Runtimes.ConvexQP.thetaOf_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.thetaOf_le

/-- info: 'STACS2027.Runtimes.ConvexQP.growOf_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.growOf_le

/-- info: 'STACS2027.Runtimes.ConvexQP.le_mul_ceil' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.le_mul_ceil

/-- info: 'STACS2027.Runtimes.ConvexQP.exp_one_le_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.exp_one_le_four

/-- info: 'STACS2027.Runtimes.ConvexQP.ratio_pow_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.ratio_pow_le

/-- info: 'STACS2027.Runtimes.ConvexQP.prec_main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.prec_main

/-- info: 'STACS2027.Runtimes.ConvexQP.prec_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.prec_bounds

/-- info: 'STACS2027.Runtimes.ConvexQP.final_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.final_lt

/-- info: 'STACS2027.Runtimes.ConvexQP.grow_pow_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.grow_pow_le

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.lam_add'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.lam_add'

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.lam_sub'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.lam_sub'

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.lam_smul'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.lam_smul'

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.L_sub'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.L_sub'

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.inner_L_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.inner_L_eq

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.inner_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.inner_add

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.inner_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.inner_sub

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.inner_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.inner_smul

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.F_nonneg'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.F_nonneg'

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.F_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.F_add

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.F_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.F_ge

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.F_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.F_smul

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.F_add_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.F_add_smul

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.F_convex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.F_convex

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.lam_eq_sum_p' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.lam_eq_sum_p

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.p_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.p_nonneg

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.p_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.p_le_one

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.lam_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.lam_nonneg

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.lam_le_t' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.lam_le_t

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.sum_lam' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.sum_lam

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.Phi_eq_F' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.Phi_eq_F

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.F_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.F_nonneg

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.F_le_Phi0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.F_le_Phi0

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.two_F_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.two_F_sub_le

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.F_le_of_kkt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.F_le_of_kkt

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.Phi_le_of_kkt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.Phi_le_of_kkt

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.k_pos_of_inX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.k_pos_of_inX

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.vtx_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.vtx_eq

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.vtx_inX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.vtx_inX

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.sum_vtx_mul_L' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.sum_vtx_mul_L

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.inner_L_vtx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.inner_L_vtx

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.inner_L_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.inner_L_ge

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.gap_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.gap_eq

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.inner_L_sub_vtx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.inner_L_sub_vtx

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.gap_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.gap_nonneg

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.F_sub_le_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.F_sub_le_gap

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.fw_inX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.fw_inX

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.F_fw_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.F_fw_step

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.F_fw_step_decrease' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.F_fw_step_decrease

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.xiq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.xiq

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.red' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.red

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.lastL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.lastL

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.gradRed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.gradRed

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.xi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.xi

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.InY' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.InY

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.f' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.f

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.sum_fin_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.sum_fin_split

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.xiq_castLE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.xiq_castLE

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.xiq_last' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.xiq_last

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.sum_xiq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.sum_xiq

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.xi_inX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.xi_inX

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.sum_red' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.sum_red

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.red_inY' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.red_inY

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.xi_red' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.xi_red

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.red_xiq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.red_xiq

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.red_xi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.red_xi

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.xiq_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.xiq_div

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.gradRed_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.gradRed_div

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.inner_L_xi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.inner_L_xi

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.f_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.f_ge

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.xi_affine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.xi_affine

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.f_convex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.f_convex

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.f_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.f_nonneg

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.f_le_Phi0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.f_le_Phi0

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.InY_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.InY_le_one

/-- info: 'STACS2027.Runtimes.ConvexQP.Inst.ball_subset_Y' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Inst.ball_subset_Y

/-- info: 'STACS2027.Runtimes.Arith.gA0' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.gA0

/-- info: 'STACS2027.Runtimes.Arith.gB0' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.gB0

/-- info: 'STACS2027.Runtimes.Arith.gL' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.gL

/-- info: 'STACS2027.Runtimes.Arith.gP' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.gP

/-- info: 'STACS2027.Runtimes.Arith.gQ' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.gQ

/-- info: 'STACS2027.Runtimes.Arith.gK' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.gK

/-- info: 'STACS2027.Runtimes.Arith.gPtr' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.gPtr

/-- info: 'STACS2027.Runtimes.Arith.gPtr2' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.gPtr2

/-- info: 'STACS2027.Runtimes.Arith.gR' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.gR

/-- info: 'STACS2027.Runtimes.Arith.gAcc' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.gAcc

/-- info: 'STACS2027.Runtimes.Arith.pE' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.pE

/-- info: 'STACS2027.Runtimes.Arith.pR' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.pR

/-- info: 'STACS2027.Runtimes.Arith.arithW' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.arithW

/-- info: 'STACS2027.Runtimes.Arith.gW' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.gW

/-- info: 'STACS2027.Runtimes.Arith.mem_arithW_of_gW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.mem_arithW_of_gW

/-- info: 'STACS2027.Runtimes.Arith.pow_size_pred_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.pow_size_pred_le

/-- info: 'STACS2027.Runtimes.Arith.add_size_le_of_mul_pow_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.add_size_le_of_mul_pow_le

/-- info: 'STACS2027.Runtimes.Arith.mtab' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.mtab

/-- info: 'STACS2027.Runtimes.Arith.mtab_of_ge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.mtab_of_ge

/-- info: 'STACS2027.Runtimes.Arith.mtab_lo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.mtab_lo

/-- info: 'STACS2027.Runtimes.Arith.mtab_hi' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.mtab_hi

/-- info: 'STACS2027.Runtimes.Arith.mtab_clear' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.mtab_clear

/-- info: 'STACS2027.Runtimes.Arith.gCond' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.gCond

/-- info: 'STACS2027.Runtimes.Arith.gBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.gBody

/-- info: 'STACS2027.Runtimes.Arith.gDesc' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.gDesc

/-- info: 'STACS2027.Runtimes.Arith.gInit' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.gInit

/-- info: 'STACS2027.Runtimes.Arith.gMid' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.gMid

/-- info: 'STACS2027.Runtimes.Arith.gCore' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.gCore

/-- info: 'STACS2027.Runtimes.Arith.wregs_gCore_sub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.wregs_gCore_sub

/-- info: 'STACS2027.Runtimes.Arith.writes_gCore' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.writes_gCore

/-- info: 'STACS2027.Runtimes.Arith.entB' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.entB

/-- info: 'STACS2027.Runtimes.Arith.BInv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.BInv

/-- info: 'STACS2027.Runtimes.Arith.gInit_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.gInit_spec

/-- info: 'STACS2027.Runtimes.Arith.gCond_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.gCond_spec

/-- info: 'STACS2027.Runtimes.Arith.gStep_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.gStep_spec

/-- info: 'STACS2027.Runtimes.Arith.DInv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.DInv

/-- info: 'STACS2027.Runtimes.Arith.gDesc_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.gDesc_spec

/-- info: 'STACS2027.Runtimes.Arith.gCost' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.gCost

/-- info: 'STACS2027.Runtimes.Arith.gMid_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.gMid_spec

/-- info: 'STACS2027.Runtimes.Arith.gStep_specB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.gStep_specB

/-- info: 'STACS2027.Runtimes.Arith.gDesc_specB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.gDesc_specB

/-- info: 'STACS2027.Runtimes.Arith.gCore_specB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.gCore_specB

/-- info: 'STACS2027.Runtimes.Arith.gCore_frameB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.gCore_frameB

/-- info: 'STACS2027.Runtimes.Arith.pow2Core' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.pow2Core

/-- info: 'STACS2027.Runtimes.Arith.wregs_pow2Core' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.wregs_pow2Core

/-- info: 'STACS2027.Runtimes.Arith.pow2Core_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.pow2Core_spec

/-- info: 'STACS2027.Runtimes.Arith.pow2Core_specB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.pow2Core_specB

/-- info: 'STACS2027.Runtimes.Arith.ne_of_not_mem_arithW' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.ne_of_not_mem_arithW

/-- info: 'STACS2027.Runtimes.Arith.mulN' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.mulN

/-- info: 'STACS2027.Runtimes.Arith.mulCost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.mulCost

/-- info: 'STACS2027.Runtimes.Arith.indep_free' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.indep_free

/-- info: 'STACS2027.Runtimes.Arith.HTB.mulN_pre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.HTB.mulN_pre

/-- info: 'STACS2027.Runtimes.Arith.HTB.mulN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.HTB.mulN

/-- info: 'STACS2027.Runtimes.Arith.divmodN' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.divmodN

/-- info: 'STACS2027.Runtimes.Arith.divCost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.divCost

/-- info: 'STACS2027.Runtimes.Arith.HTB.divmodN_pre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.HTB.divmodN_pre

/-- info: 'STACS2027.Runtimes.Arith.HTB.divmodN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.HTB.divmodN

/-- info: 'STACS2027.Runtimes.Arith.pow2N' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.pow2N

/-- info: 'STACS2027.Runtimes.Arith.HT.pow2N' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.HT.pow2N

/-- info: 'STACS2027.Runtimes.Arith.HTB.pow2N' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.HTB.pow2N

/-- info: 'STACS2027.Runtimes.Arith.SArg' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.SArg

/-- info: 'STACS2027.Runtimes.Arith.SArg.indep' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.SArg.indep

/-- info: 'STACS2027.Runtimes.Arith.SArg.ne' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.SArg.ne

/-- info: 'STACS2027.Runtimes.Arith.indep_ofArith' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.indep_ofArith

/-- info: 'STACS2027.Runtimes.Arith.free_not_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.free_not_mem

/-- info: 'STACS2027.Runtimes.Arith.indep_and_free' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.indep_and_free

/-- info: 'STACS2027.Runtimes.Arith.smov' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.smov

/-- info: 'STACS2027.Runtimes.Arith.HT.smov' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.HT.smov

/-- info: 'STACS2027.Runtimes.Arith.HTB.smov' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.HTB.smov

/-- info: 'STACS2027.Runtimes.Arith.sconst' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.sconst

/-- info: 'STACS2027.Runtimes.Arith.HT.sconst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.HT.sconst

/-- info: 'STACS2027.Runtimes.Arith.HTB.sconst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.HTB.sconst

/-- info: 'STACS2027.Runtimes.Arith.sofNat' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.sofNat

/-- info: 'STACS2027.Runtimes.Arith.HT.sofNat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.HT.sofNat

/-- info: 'STACS2027.Runtimes.Arith.HTB.sofNat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.HTB.sofNat

/-- info: 'STACS2027.Runtimes.Arith.sadd' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.sadd

/-- info: 'STACS2027.Runtimes.Arith.HT.sadd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.HT.sadd

/-- info: 'STACS2027.Runtimes.Arith.HTB.sadd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.HTB.sadd

/-- info: 'STACS2027.Runtimes.Arith.mem_dW' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.mem_dW

/-- info: 'STACS2027.Runtimes.Arith.HT.smovOut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.HT.smovOut

/-- info: 'STACS2027.Runtimes.Arith.HTB.smovOut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.HTB.smovOut

/-- info: 'STACS2027.Runtimes.Arith.HT.smovIn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.HT.smovIn

/-- info: 'STACS2027.Runtimes.Arith.HTB.smovIn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.HTB.smovIn

/-- info: 'STACS2027.Runtimes.Arith.ssub' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.ssub

/-- info: 'STACS2027.Runtimes.Arith.HT.ssub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.HT.ssub

/-- info: 'STACS2027.Runtimes.Arith.HTB.ssub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.HTB.ssub

/-- info: 'STACS2027.Runtimes.Arith.sneg' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.sneg

/-- info: 'STACS2027.Runtimes.Arith.HT.sneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.HT.sneg

/-- info: 'STACS2027.Runtimes.Arith.HTB.sneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.HTB.sneg

/-- info: 'STACS2027.Runtimes.Arith.sle' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.sle

/-- info: 'STACS2027.Runtimes.Arith.HT.sle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.HT.sle

/-- info: 'STACS2027.Runtimes.Arith.HTB.sle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.HTB.sle

/-- info: 'STACS2027.Runtimes.Arith.slt' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.slt

/-- info: 'STACS2027.Runtimes.Arith.HT.slt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.HT.slt

/-- info: 'STACS2027.Runtimes.Arith.HTB.slt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.HTB.slt

/-- info: 'STACS2027.Runtimes.Arith.isz' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.isz

/-- info: 'STACS2027.Runtimes.Arith.HT.isz' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.HT.isz

/-- info: 'STACS2027.Runtimes.Arith.HTB.isz' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.HTB.isz

/-- info: 'STACS2027.Runtimes.Arith.smul' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.smul

/-- info: 'STACS2027.Runtimes.Arith.HTB.smul_pre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.HTB.smul_pre

/-- info: 'STACS2027.Runtimes.Arith.HTB.smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.HTB.smul

/-- info: 'STACS2027.Runtimes.Arith.sdivmod' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.sdivmod

/-- info: 'STACS2027.Runtimes.Arith.HTB.sdivmod_pre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.HTB.sdivmod_pre

/-- info: 'STACS2027.Runtimes.Arith.HTB.sdivmod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.HTB.sdivmod

/-- info: 'STACS2027.Runtimes.Arith.sround' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.sround

/-- info: 'STACS2027.Runtimes.Arith.HTB.sround_pre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.HTB.sround_pre

/-- info: 'STACS2027.Runtimes.Arith.HTB.sround' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.HTB.sround

/-- info: 'STACS2027.Runtimes.Arith.isqrtN' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.isqrtN

/-- info: 'STACS2027.Runtimes.Arith.HTB.isqrtN_pre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.HTB.isqrtN_pre

/-- info: 'STACS2027.Runtimes.Arith.HTB.isqrtN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.HTB.isqrtN

/-- info: 'STACS2027.Runtimes.Arith.sload' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.sload

/-- info: 'STACS2027.Runtimes.Arith.HT.sload' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.HT.sload

/-- info: 'STACS2027.Runtimes.Arith.HTB.sload' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.HTB.sload

/-- info: 'STACS2027.Runtimes.Arith.sstore' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.sstore

/-- info: 'STACS2027.Runtimes.Arith.HT.sstore' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.HT.sstore

/-- info: 'STACS2027.Runtimes.Arith.HTB.sstore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.HTB.sstore

/-- info: 'STACS2027.Runtimes.Arith.sgnBit' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.sgnBit

/-- info: 'STACS2027.Runtimes.Arith.SReg' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.SReg

/-- info: 'STACS2027.Runtimes.Arith.SMem' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.SMem

/-- info: 'STACS2027.Runtimes.Arith.indep_sreg' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.indep_sreg

/-- info: 'STACS2027.Runtimes.Arith.regIndep_sreg' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.regIndep_sreg

/-- info: 'STACS2027.Runtimes.Arith.SReg.eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.SReg.eq

/-- info: 'STACS2027.Runtimes.Arith.sreg_of' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.sreg_of

/-- info: 'STACS2027.Runtimes.Arith.sgnBit_le_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.sgnBit_le_one

/-- info: 'STACS2027.Runtimes.Arith.sgnBit_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.sgnBit_mul

/-- info: 'STACS2027.Runtimes.Arith.sX' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.sX

/-- info: 'STACS2027.Runtimes.Arith.sY' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.sY

/-- info: 'STACS2027.Runtimes.Arith.sZ' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.sZ

/-- info: 'STACS2027.Runtimes.Arith.sB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.sB

/-- info: 'STACS2027.Runtimes.Arith.mX' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.mX

/-- info: 'STACS2027.Runtimes.Arith.mY' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.mY

/-- info: 'STACS2027.Runtimes.Arith.mZ' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.mZ

/-- info: 'STACS2027.Runtimes.Arith.mRm' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.mRm

/-- info: 'STACS2027.Runtimes.Arith.mQ' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.mQ

/-- info: 'STACS2027.Runtimes.Arith.rU' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.rU

/-- info: 'STACS2027.Runtimes.Arith.rV' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.rV

/-- info: 'STACS2027.Runtimes.Arith.saddCore' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.saddCore

/-- info: 'STACS2027.Runtimes.Arith.wregs_saddCore_sub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.wregs_saddCore_sub

/-- info: 'STACS2027.Runtimes.Arith.saddCore_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.saddCore_spec

/-- info: 'STACS2027.Runtimes.Arith.saddCore_specB' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.saddCore_specB

/-- info: 'STACS2027.Runtimes.Arith.sflip' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.sflip

/-- info: 'STACS2027.Runtimes.Arith.run_sflip' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.run_sflip

/-- info: 'STACS2027.Runtimes.Arith.sflip_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.sflip_spec

/-- info: 'STACS2027.Runtimes.Arith.sflip_specB' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.sflip_specB

/-- info: 'STACS2027.Runtimes.Arith.sleCore' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.sleCore

/-- info: 'STACS2027.Runtimes.Arith.sleCore_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.sleCore_spec

/-- info: 'STACS2027.Runtimes.Arith.sleCore_specB' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.sleCore_specB

/-- info: 'STACS2027.Runtimes.Arith.smulCore' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.smulCore

/-- info: 'STACS2027.Runtimes.Arith.smW' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.smW

/-- info: 'STACS2027.Runtimes.Arith.smulCost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.smulCost

/-- info: 'STACS2027.Runtimes.Arith.smulCore_specB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.smulCore_specB

/-- info: 'STACS2027.Runtimes.Arith.qMag' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.qMag

/-- info: 'STACS2027.Runtimes.Arith.rNat' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.rNat

/-- info: 'STACS2027.Runtimes.Arith.ediv_pos_aux' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.ediv_pos_aux

/-- info: 'STACS2027.Runtimes.Arith.ediv_eq_natAbs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.ediv_eq_natAbs

/-- info: 'STACS2027.Runtimes.Arith.sdivPre' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.sdivPre

/-- info: 'STACS2027.Runtimes.Arith.sdivFix' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.sdivFix

/-- info: 'STACS2027.Runtimes.Arith.sdivCore' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.sdivCore

/-- info: 'STACS2027.Runtimes.Arith.sdW' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.sdW

/-- info: 'STACS2027.Runtimes.Arith.sdivCost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.sdivCost

/-- info: 'STACS2027.Runtimes.Arith.sdivFix_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.sdivFix_run

/-- info: 'STACS2027.Runtimes.Arith.sdivCore_specB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.sdivCore_specB

/-- info: 'STACS2027.Runtimes.Arith.size_round_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.size_round_le

/-- info: 'STACS2027.Runtimes.Arith.roundPre' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.roundPre

/-- info: 'STACS2027.Runtimes.Arith.roundCore' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.roundCore

/-- info: 'STACS2027.Runtimes.Arith.rdW' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.rdW

/-- info: 'STACS2027.Runtimes.Arith.roundCost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.roundCost

/-- info: 'STACS2027.Runtimes.Arith.roundPre_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.roundPre_run

/-- info: 'STACS2027.Runtimes.Arith.roundCore_specB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.roundCore_specB

/-- info: 'STACS2027.Runtimes.Arith.qN' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.qN

/-- info: 'STACS2027.Runtimes.Arith.qR' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.qR

/-- info: 'STACS2027.Runtimes.Arith.qJ' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.qJ

/-- info: 'STACS2027.Runtimes.Arith.qT' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.qT

/-- info: 'STACS2027.Runtimes.Arith.qH' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.qH

/-- info: 'STACS2027.Runtimes.Arith.sqW' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.sqW

/-- info: 'STACS2027.Runtimes.Arith.qCond' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.qCond

/-- info: 'STACS2027.Runtimes.Arith.qBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.qBody

/-- info: 'STACS2027.Runtimes.Arith.qStep' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.qStep

/-- info: 'STACS2027.Runtimes.Arith.isqrtCore' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.isqrtCore

/-- info: 'STACS2027.Runtimes.Arith.qStepCost' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.qStepCost

/-- info: 'STACS2027.Runtimes.Arith.isqrtCost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.isqrtCost

/-- info: 'STACS2027.Runtimes.Arith.isqrtCost_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.isqrtCost_le

/-- info: 'STACS2027.Runtimes.Arith.QF' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.QF

/-- info: 'STACS2027.Runtimes.Arith.qStep_specB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.qStep_specB

/-- info: 'STACS2027.Runtimes.Arith.QD' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.QD

/-- info: 'STACS2027.Runtimes.Arith.QI' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.QI

/-- info: 'STACS2027.Runtimes.Arith.isqrtCore_specB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.Arith.isqrtCore_specB

/-- info: 'STACS2027.Runtimes.QPRam.Parse.cI' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.cI

/-- info: 'STACS2027.Runtimes.QPRam.Parse.cJ' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.cJ

/-- info: 'STACS2027.Runtimes.QPRam.Parse.cA0' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.cA0

/-- info: 'STACS2027.Runtimes.QPRam.Parse.cK1' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.cK1

/-- info: 'STACS2027.Runtimes.QPRam.Parse.cX' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.cX

/-- info: 'STACS2027.Runtimes.QPRam.Parse.cR' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.cR

/-- info: 'STACS2027.Runtimes.QPRam.Parse.cL' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.cL

/-- info: 'STACS2027.Runtimes.QPRam.Parse.cY' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.cY

/-- info: 'STACS2027.Runtimes.QPRam.Parse.cW' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.cW

/-- info: 'STACS2027.Runtimes.QPRam.Parse.cZ' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.cZ

/-- info: 'STACS2027.Runtimes.QPRam.Parse.cU' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.cU

/-- info: 'STACS2027.Runtimes.QPRam.Parse.cV' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.cV

/-- info: 'STACS2027.Runtimes.QPRam.Parse.cB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.cB

/-- info: 'STACS2027.Runtimes.QPRam.Parse.cD1' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.cD1

/-- info: 'STACS2027.Runtimes.QPRam.Parse.cC' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.cC

/-- info: 'STACS2027.Runtimes.QPRam.Parse.cW2' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.cW2

/-- info: 'STACS2027.Runtimes.QPRam.Parse.cv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.cv

/-- info: 'STACS2027.Runtimes.QPRam.Parse.rs0' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.rs0

/-- info: 'STACS2027.Runtimes.QPRam.Parse.rs1' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.rs1

/-- info: 'STACS2027.Runtimes.QPRam.Parse.rs2' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.rs2

/-- info: 'STACS2027.Runtimes.QPRam.Parse.rs3' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.rs3

/-- info: 'STACS2027.Runtimes.QPRam.Parse.rs4' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.rs4

/-- info: 'STACS2027.Runtimes.QPRam.Parse.rs5' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.rs5

/-- info: 'STACS2027.Runtimes.QPRam.Parse.rs6' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.rs6

/-- info: 'STACS2027.Runtimes.QPRam.Parse.cA' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.cA

/-- info: 'STACS2027.Runtimes.QPRam.Parse.cND' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.cND

/-- info: 'STACS2027.Runtimes.QPRam.Parse.factBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.factBody

/-- info: 'STACS2027.Runtimes.QPRam.Parse.cFact' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.cFact

/-- info: 'STACS2027.Runtimes.QPRam.Parse.cPow' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.cPow

/-- info: 'STACS2027.Runtimes.QPRam.Parse.cE' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.cE

/-- info: 'STACS2027.Runtimes.QPRam.Parse.cRad' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.cRad

/-- info: 'STACS2027.Runtimes.QPRam.Parse.cIt' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.cIt

/-- info: 'STACS2027.Runtimes.QPRam.Parse.cPrec' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.cPrec

/-- info: 'STACS2027.Runtimes.QPRam.Parse.cCN' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.cCN

/-- info: 'STACS2027.Runtimes.QPRam.Parse.stepConsts' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.stepConsts

/-- info: 'STACS2027.Runtimes.QPRam.Parse.mulCost_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.mulCost_mono

/-- info: 'STACS2027.Runtimes.QPRam.Parse.KS.cons' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.KS.cons

/-- info: 'STACS2027.Runtimes.QPRam.Parse.KS.fact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.KS.fact

/-- info: 'STACS2027.Runtimes.QPRam.Parse.KS.pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Parse.KS.pow

/-- info: 'STACS2027.Runtimes.QPRam.clog_le_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.clog_le_self

/-- info: 'STACS2027.Runtimes.QPRam.nDim_le_tk' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.nDim_le_tk

/-- info: 'STACS2027.Runtimes.QPRam.logRad_le_X' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.logRad_le_X

/-- info: 'STACS2027.Runtimes.QPRam.iters_le_X' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.iters_le_X

/-- info: 'STACS2027.Runtimes.QPRam.prec_le_X' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.prec_le_X

/-- info: 'STACS2027.Runtimes.QPRam.iterPoly' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.iterPoly

/-- info: 'STACS2027.Runtimes.QPRam.iterCost_le_poly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.iterCost_le_poly

/-- info: 'STACS2027.Runtimes.QPRam.iterPoly_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.iterPoly_le

/-- info: 'STACS2027.Runtimes.QPRam.iterCost_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.iterCost_le

/-- info: 'STACS2027.Runtimes.QPRam.ellC' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.ellC

/-- info: 'STACS2027.Runtimes.QPRam.setupCost_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.setupCost_le

/-- info: 'STACS2027.Runtimes.QPRam.total_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.total_le

/-- info: 'STACS2027.Runtimes.QPRam.ellSpace_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.ellSpace_le

/-- info: 'STACS2027.Runtimes.QPRam.bitB' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.bitB

/-- info: 'STACS2027.Runtimes.QPRam.ellSc' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.ellSc

/-- info: 'STACS2027.Runtimes.QPRam.radInv_ge_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.radInv_ge_two

/-- info: 'STACS2027.Runtimes.QPRam.logRad_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.logRad_pos

/-- info: 'STACS2027.Runtimes.QPRam.prec_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.prec_ge

/-- info: 'STACS2027.Runtimes.QPRam.poly_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.poly_le

/-- info: 'STACS2027.Runtimes.QPRam.kt_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.kt_le

/-- info: 'STACS2027.Runtimes.QPRam.bigE_le_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.bigE_le_pow

/-- info: 'STACS2027.Runtimes.QPRam.abs_le_two_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.abs_le_two_pow

/-- info: 'STACS2027.Runtimes.QPRam.flatR_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.flatR_bits

/-- info: 'STACS2027.Runtimes.QPRam.flatM_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.flatM_bits

/-- info: 'STACS2027.Runtimes.QPRam.two_pow_mul_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.two_pow_mul_eq

/-- info: 'STACS2027.Runtimes.QPRam.four_pow' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.four_pow

/-- info: 'STACS2027.Runtimes.QPRam.eight_pow' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.eight_pow

/-- info: 'STACS2027.Runtimes.QPRam.sixteen_pow' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.sixteen_pow

/-- info: 'STACS2027.Runtimes.QPRam.updBits_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.updBits_of

/-- info: 'STACS2027.Runtimes.QPRam.flat_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.flat_bits

/-- info: 'STACS2027.Runtimes.QPRam.xs_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.xs_bits

/-- info: 'STACS2027.Runtimes.QPRam.bigE_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.bigE_bits

/-- info: 'STACS2027.Runtimes.QPRam.feasPt_flat_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.feasPt_flat_lt

/-- info: 'STACS2027.Runtimes.QPRam.feasPt_flat_last' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.feasPt_flat_last

/-- info: 'STACS2027.Runtimes.QPRam.fxIn' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.fxIn

/-- info: 'STACS2027.Runtimes.QPRam.fxOut' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.fxOut

/-- info: 'STACS2027.Runtimes.QPRam.feasXs' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.feasXs

/-- info: 'STACS2027.Runtimes.QPRam.FxIn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.FxIn

/-- info: 'STACS2027.Runtimes.QPRam.FxOut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.FxOut

/-- info: 'STACS2027.Runtimes.QPRam.fxIn_specB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.fxIn_specB

/-- info: 'STACS2027.Runtimes.QPRam.fxOut_specB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.fxOut_specB

/-- info: 'STACS2027.Runtimes.QPRam.feasXs_specB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.feasXs_specB

/-- info: 'STACS2027.Runtimes.QPRam.mvLSet' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.mvLSet

/-- info: 'STACS2027.Runtimes.QPRam.mvL' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.mvL

/-- info: 'STACS2027.Runtimes.QPRam.mvL_wregs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.mvL_wregs

/-- info: 'STACS2027.Runtimes.QPRam.mulVec_Hflat_flat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.mulVec_Hflat_flat

/-- info: 'STACS2027.Runtimes.QPRam.mvL_specB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.mvL_specB

/-- info: 'STACS2027.Runtimes.QPRam.pmin' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.pmin

/-- info: 'STACS2027.Runtimes.QPRam.pmin_le' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.pmin_le

/-- info: 'STACS2027.Runtimes.QPRam.pmin_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.pmin_mem

/-- info: 'STACS2027.Runtimes.QPRam.sxl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.sxl

/-- info: 'STACS2027.Runtimes.QPRam.spi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.spi

/-- info: 'STACS2027.Runtimes.QPRam.gapN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.gapN

/-- info: 'STACS2027.Runtimes.QPRam.pi_eq_pmin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.pi_eq_pmin

/-- info: 'STACS2027.Runtimes.QPRam.gapN_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.gapN_eq

/-- info: 'STACS2027.Runtimes.QPRam.gpIn' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.gpIn

/-- info: 'STACS2027.Runtimes.QPRam.gpOut' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.gpOut

/-- info: 'STACS2027.Runtimes.QPRam.gapB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.gapB

/-- info: 'STACS2027.Runtimes.QPRam.testB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.testB

/-- info: 'STACS2027.Runtimes.QPRam.GpB' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.GpB

/-- info: 'STACS2027.Runtimes.QPRam.GpIn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.GpIn

/-- info: 'STACS2027.Runtimes.QPRam.GpOut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.GpOut

/-- info: 'STACS2027.Runtimes.QPRam.GpB.indep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.GpB.indep

/-- info: 'STACS2027.Runtimes.QPRam.gpIn_specB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.gpIn_specB

/-- info: 'STACS2027.Runtimes.QPRam.gpOut_specB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.gpOut_specB

/-- info: 'STACS2027.Runtimes.QPRam.natAbs_two_pow' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.natAbs_two_pow

/-- info: 'STACS2027.Runtimes.QPRam.size_two_pow' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.size_two_pow

/-- info: 'STACS2027.Runtimes.QPRam.gapB_specB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.gapB_specB

/-- info: 'STACS2027.Runtimes.QPRam.testB_specB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.testB_specB

/-- info: 'STACS2027.Runtimes.QPRam.gMode' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.gMode

/-- info: 'STACS2027.Runtimes.QPRam.gVal' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.gVal

/-- info: 'STACS2027.Runtimes.QPRam.gIn' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.gIn

/-- info: 'STACS2027.Runtimes.QPRam.gOut' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.gOut

/-- info: 'STACS2027.Runtimes.QPRam.gLoop' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.gLoop

/-- info: 'STACS2027.Runtimes.QPRam.gLoop_wregs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.gLoop_wregs

/-- info: 'STACS2027.Runtimes.QPRam.GIn' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.GIn

/-- info: 'STACS2027.Runtimes.QPRam.GOut' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.GOut

/-- info: 'STACS2027.Runtimes.QPRam.GIn.indep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.GIn.indep

/-- info: 'STACS2027.Runtimes.QPRam.gVal_specB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.gVal_specB

/-- info: 'STACS2027.Runtimes.QPRam.gIn_specB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.gIn_specB

/-- info: 'STACS2027.Runtimes.QPRam.gOut_specB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.gOut_specB

/-- info: 'STACS2027.Runtimes.QPRam.gLoop_specB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.gLoop_specB

/-- info: 'STACS2027.Runtimes.QPRam.layOf' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.layOf

/-- info: 'STACS2027.Runtimes.QPRam.layOf_ok' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.layOf_ok

/-- info: 'STACS2027.Runtimes.QPRam.setA' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.setA

/-- info: 'STACS2027.Runtimes.QPRam.setB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.setB

/-- info: 'STACS2027.Runtimes.QPRam.setP' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.setP

/-- info: 'STACS2027.Runtimes.QPRam.aIn' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.aIn

/-- info: 'STACS2027.Runtimes.QPRam.initA' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.initA

/-- info: 'STACS2027.Runtimes.QPRam.qIn' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.qIn

/-- info: 'STACS2027.Runtimes.QPRam.initQ' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.initQ

/-- info: 'STACS2027.Runtimes.QPRam.setup' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.setup

/-- info: 'STACS2027.Runtimes.QPRam.setup_wregs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.setup_wregs

/-- info: 'STACS2027.Runtimes.QPRam.EGa' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.EGa

/-- info: 'STACS2027.Runtimes.QPRam.SR0' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.SR0

/-- info: 'STACS2027.Runtimes.QPRam.setAB_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.setAB_spec

/-- info: 'STACS2027.Runtimes.QPRam.setP_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.setP_spec

/-- info: 'STACS2027.Runtimes.QPRam.aIn_specB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.aIn_specB

/-- info: 'STACS2027.Runtimes.QPRam.initA_specB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.initA_specB

/-- info: 'STACS2027.Runtimes.QPRam.qInit' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.qInit

/-- info: 'STACS2027.Runtimes.QPRam.qInit_cell' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.qInit_cell

/-- info: 'STACS2027.Runtimes.QPRam.QI' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.QI

/-- info: 'STACS2027.Runtimes.QPRam.QO' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.QO

/-- info: 'STACS2027.Runtimes.QPRam.qIn_specB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.qIn_specB

/-- info: 'STACS2027.Runtimes.QPRam.qOut_specB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.qOut_specB

/-- info: 'STACS2027.Runtimes.QPRam.initQ_specB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.initQ_specB

/-- info: 'STACS2027.Runtimes.QPRam.setupCost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.setupCost

/-- info: 'STACS2027.Runtimes.QPRam.init_As' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.init_As

/-- info: 'STACS2027.Runtimes.QPRam.init_Qs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.init_Qs

/-- info: 'STACS2027.Runtimes.QPRam.setup_specB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.setup_specB

/-- info: 'STACS2027.Runtimes.QPRam.feas' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.feas

/-- info: 'STACS2027.Runtimes.QPRam.feasC' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.feasC

/-- info: 'STACS2027.Runtimes.QPRam.feasMem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.feasMem

/-- info: 'STACS2027.Runtimes.QPRam.feas_specB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.feas_specB

/-- info: 'STACS2027.Runtimes.QPRam.feasOpt' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.feasOpt

/-- info: 'STACS2027.Runtimes.QPRam.tailB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.tailB

/-- info: 'STACS2027.Runtimes.QPRam.iterB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.iterB

/-- info: 'STACS2027.Runtimes.QPRam.feasOpt_wregs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.feasOpt_wregs

/-- info: 'STACS2027.Runtimes.QPRam.iterB_wregs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.iterB_wregs

/-- info: 'STACS2027.Runtimes.QPRam.MSt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.MSt

/-- info: 'STACS2027.Runtimes.QPRam.negFind_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.negFind_some

/-- info: 'STACS2027.Runtimes.QPRam.negFind_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.negFind_none

/-- info: 'STACS2027.Runtimes.QPRam.overFind_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.overFind_some

/-- info: 'STACS2027.Runtimes.QPRam.overFind_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.overFind_none

/-- info: 'STACS2027.Runtimes.QPRam.gMode_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.gMode_neg

/-- info: 'STACS2027.Runtimes.QPRam.gMode_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.gMode_block

/-- info: 'STACS2027.Runtimes.QPRam.gMode_grad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.gMode_grad

/-- info: 'STACS2027.Runtimes.QPRam.scanC' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.scanC

/-- info: 'STACS2027.Runtimes.QPRam.gC' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.gC

/-- info: 'STACS2027.Runtimes.QPRam.iterCost' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.iterCost

/-- info: 'STACS2027.Runtimes.QPRam.HT.of_false' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.HT.of_false

/-- info: 'STACS2027.Runtimes.QPRam.cutUpd_specB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.cutUpd_specB

/-- info: 'STACS2027.Runtimes.QPRam.regIndep_cnt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.regIndep_cnt

/-- info: 'STACS2027.Runtimes.QPRam.feas_wregs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.feas_wregs

/-- info: 'STACS2027.Runtimes.QPRam.gu_wregs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.gu_wregs

/-- info: 'STACS2027.Runtimes.QPRam.IterPost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.IterPost

/-- info: 'STACS2027.Runtimes.QPRam.constDn_specB' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.constDn_specB

/-- info: 'STACS2027.Runtimes.QPRam.tail_cutB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.tail_cutB

/-- info: 'STACS2027.Runtimes.QPRam.feasMem_facts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.feasMem_facts

/-- info: 'STACS2027.Runtimes.QPRam.tail_feasB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.tail_feasB

/-- info: 'STACS2027.Runtimes.QPRam.iter_specB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.iter_specB

/-- info: 'STACS2027.Runtimes.QPRam.eA' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.eA

/-- info: 'STACS2027.Runtimes.QPRam.eQ' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.eQ

/-- info: 'STACS2027.Runtimes.QPRam.eL' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.eL

/-- info: 'STACS2027.Runtimes.QPRam.eG' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.eG

/-- info: 'STACS2027.Runtimes.QPRam.eU' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.eU

/-- info: 'STACS2027.Runtimes.QPRam.e2N' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.e2N

/-- info: 'STACS2027.Runtimes.QPRam.eK1' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.eK1

/-- info: 'STACS2027.Runtimes.QPRam.eCnt' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.eCnt

/-- info: 'STACS2027.Runtimes.QPRam.eP2' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.eP2

/-- info: 'STACS2027.Runtimes.QPRam.eC' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.eC

/-- info: 'STACS2027.Runtimes.QPRam.eJ' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.eJ

/-- info: 'STACS2027.Runtimes.QPRam.ePa' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.ePa

/-- info: 'STACS2027.Runtimes.QPRam.ePx' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.ePx

/-- info: 'STACS2027.Runtimes.QPRam.ePy' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.ePy

/-- info: 'STACS2027.Runtimes.QPRam.eF1' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.eF1

/-- info: 'STACS2027.Runtimes.QPRam.eF2' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.eF2

/-- info: 'STACS2027.Runtimes.QPRam.eDn' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.eDn

/-- info: 'STACS2027.Runtimes.QPRam.eV' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.eV

/-- info: 'STACS2027.Runtimes.QPRam.eW' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.eW

/-- info: 'STACS2027.Runtimes.QPRam.eS1' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.eS1

/-- info: 'STACS2027.Runtimes.QPRam.eS2' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.eS2

/-- info: 'STACS2027.Runtimes.QPRam.eS3' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.eS3

/-- info: 'STACS2027.Runtimes.QPRam.eT1' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.eT1

/-- info: 'STACS2027.Runtimes.QPRam.eT2' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.eT2

/-- info: 'STACS2027.Runtimes.QPRam.ellW' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.ellW

/-- info: 'STACS2027.Runtimes.QPRam.arithW_sub_ellW' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.arithW_sub_ellW

/-- info: 'STACS2027.Runtimes.QPRam.flatR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.flatR

/-- info: 'STACS2027.Runtimes.QPRam.flatM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.flatM

/-- info: 'STACS2027.Runtimes.QPRam.fIdx' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.fIdx

/-- info: 'STACS2027.Runtimes.QPRam.flatR_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.flatR_apply

/-- info: 'STACS2027.Runtimes.QPRam.flatR_fIdx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.flatR_fIdx

/-- info: 'STACS2027.Runtimes.QPRam.flatM_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.flatM_apply

/-- info: 'STACS2027.Runtimes.QPRam.flat_of_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.flat_of_ge

/-- info: 'STACS2027.Runtimes.QPRam.flat_decomp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.flat_decomp

/-- info: 'STACS2027.Runtimes.QPRam.fIdx_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.fIdx_lt

/-- info: 'STACS2027.Runtimes.QPRam.fIdx_inj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.fIdx_inj

/-- info: 'STACS2027.Runtimes.QPRam.fIdx_mk' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.fIdx_mk

/-- info: 'STACS2027.Runtimes.QPRam.fIdx_surj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.fIdx_surj

/-- info: 'STACS2027.Runtimes.QPRam.flatM_fIdx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.flatM_fIdx

/-- info: 'STACS2027.Runtimes.QPRam.flat_idx_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.flat_idx_lt

/-- info: 'STACS2027.Runtimes.QPRam.nDim_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.nDim_eq

/-- info: 'STACS2027.Runtimes.QPRam.flatR_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.flatR_mul

/-- info: 'STACS2027.Runtimes.QPRam.sum_flatR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.sum_flatR

/-- info: 'STACS2027.Runtimes.QPRam.mulVec_flatM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.mulVec_flatM

/-- info: 'STACS2027.Runtimes.QPRam.dot_flatR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.dot_flatR

/-- info: 'STACS2027.Runtimes.QPRam.bsum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.bsum

/-- info: 'STACS2027.Runtimes.QPRam.bsum_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.bsum_eq

/-- info: 'STACS2027.Runtimes.QPRam.range_mul_flatMap' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.range_mul_flatMap

/-- info: 'STACS2027.Runtimes.QPRam.map_val_finRange' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.map_val_finRange

/-- info: 'STACS2027.Runtimes.QPRam.idxList_map_fIdx' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.idxList_map_fIdx

/-- info: 'STACS2027.Runtimes.QPRam.negFind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.negFind

/-- info: 'STACS2027.Runtimes.QPRam.overFind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.overFind

/-- info: 'STACS2027.Runtimes.QPRam.negFind_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.negFind_eq

/-- info: 'STACS2027.Runtimes.QPRam.overFind_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.overFind_eq

/-- info: 'STACS2027.Runtimes.QPRam.enc' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.enc

/-- info: 'STACS2027.Runtimes.QPRam.find_range_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.find_range_succ

/-- info: 'STACS2027.Runtimes.QPRam.find_range_zero' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.find_range_zero

/-- info: 'STACS2027.Runtimes.QPRam.Lay' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Lay

/-- info: 'STACS2027.Runtimes.QPRam.Lay.Ok' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Lay.Ok

/-- info: 'STACS2027.Runtimes.QPRam.EG' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.EG

/-- info: 'STACS2027.Runtimes.QPRam.Lay.Ok.fits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Lay.Ok.fits

/-- info: 'STACS2027.Runtimes.QPRam.EG.regIndep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.EG.regIndep

/-- info: 'STACS2027.Runtimes.QPRam.EG.indep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.EG.indep

/-- info: 'STACS2027.Runtimes.QPRam.EG.p2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.EG.p2

/-- info: 'STACS2027.Runtimes.QPRam.EG.t' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.EG.t

/-- info: 'STACS2027.Runtimes.QPRam.EG.k' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.EG.k

/-- info: 'STACS2027.Runtimes.QPRam.EG.kt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.EG.kt

/-- info: 'STACS2027.Runtimes.QPRam.EG.n' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.EG.n

/-- info: 'STACS2027.Runtimes.QPRam.EG.it' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.EG.it

/-- info: 'STACS2027.Runtimes.QPRam.EG.p' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.EG.p

/-- info: 'STACS2027.Runtimes.QPRam.EG.e' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.EG.e

/-- info: 'STACS2027.Runtimes.QPRam.EG.cn' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.EG.cn

/-- info: 'STACS2027.Runtimes.QPRam.EG.cd' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.EG.cd

/-- info: 'STACS2027.Runtimes.QPRam.QsMem' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.QsMem

/-- info: 'STACS2027.Runtimes.QPRam.StMem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.StMem

/-- info: 'STACS2027.Runtimes.QPRam.cell_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.cell_le

/-- info: 'STACS2027.Runtimes.QPRam.SArr.out' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.SArr.out

/-- info: 'STACS2027.Runtimes.QPRam.row_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.row_le

/-- info: 'STACS2027.Runtimes.QPRam.QsMem.out' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.QsMem.out

/-- info: 'STACS2027.Runtimes.QPRam.hrow_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.hrow_le

/-- info: 'STACS2027.Runtimes.QPRam.HMem.out' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.HMem.out

/-- info: 'STACS2027.Runtimes.QPRam.StMem.out' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.StMem.out

/-- info: 'STACS2027.Runtimes.QPRam.SArr.get' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.SArr.get

/-- info: 'STACS2027.Runtimes.QPRam.SArr.congr_fun' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.SArr.congr_fun

/-- info: 'STACS2027.Runtimes.QPRam.size_le_of_abs_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.size_le_of_abs_le

/-- info: 'STACS2027.Runtimes.QPRam.size_le_of_le_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.size_le_of_le_pow

/-- info: 'STACS2027.Runtimes.QPRam.size_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.size_mono

/-- info: 'STACS2027.Runtimes.QPRam.smulCost_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.smulCost_le

/-- info: 'STACS2027.Runtimes.QPRam.MInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.MInv

/-- info: 'STACS2027.Runtimes.QPRam.loop_specB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.loop_specB

/-- info: 'STACS2027.Runtimes.QPRam.mid_of_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.mid_of_inv

/-- info: 'STACS2027.Runtimes.QPRam.ellProg' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.ellProg

/-- info: 'STACS2027.Runtimes.QPRam.ellProg_writes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.ellProg_writes

/-- info: 'STACS2027.Runtimes.QPRam.ellProg_wregs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.ellProg_wregs

/-- info: 'STACS2027.Runtimes.QPRam.phaseE_ramB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.phaseE_ramB

/-- info: 'STACS2027.Runtimes.QPRam.scanIn' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.scanIn

/-- info: 'STACS2027.Runtimes.QPRam.scanOut' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.scanOut

/-- info: 'STACS2027.Runtimes.QPRam.scan' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.scan

/-- info: 'STACS2027.Runtimes.QPRam.scan_wregs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.scan_wregs

/-- info: 'STACS2027.Runtimes.QPRam.scan_stores' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.scan_stores

/-- info: 'STACS2027.Runtimes.QPRam.ScR' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.ScR

/-- info: 'STACS2027.Runtimes.QPRam.qNeg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.qNeg

/-- info: 'STACS2027.Runtimes.QPRam.qOver' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.qOver

/-- info: 'STACS2027.Runtimes.QPRam.ScanIn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.ScanIn

/-- info: 'STACS2027.Runtimes.QPRam.ScanOut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.ScanOut

/-- info: 'STACS2027.Runtimes.QPRam.ScR.indep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.ScR.indep

/-- info: 'STACS2027.Runtimes.QPRam.scanIn_specB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.scanIn_specB

/-- info: 'STACS2027.Runtimes.QPRam.scanOut_specB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.scanOut_specB

/-- info: 'STACS2027.Runtimes.QPRam.scan_specB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.scan_specB

/-- info: 'STACS2027.Runtimes.QPRam.mulVec_flatM'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.mulVec_flatM'

/-- info: 'STACS2027.Runtimes.QPRam.uSet' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.uSet

/-- info: 'STACS2027.Runtimes.QPRam.uB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.uB

/-- info: 'STACS2027.Runtimes.QPRam.uB_specB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.uB_specB

/-- info: 'STACS2027.Runtimes.QPRam.dSet' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.dSet

/-- info: 'STACS2027.Runtimes.QPRam.dB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.dB

/-- info: 'STACS2027.Runtimes.QPRam.dB_specB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.dB_specB

/-- info: 'STACS2027.Runtimes.QPRam.sB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.sB

/-- info: 'STACS2027.Runtimes.QPRam.sB_specB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.sB_specB

/-- info: 'STACS2027.Runtimes.QPRam.aSet' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.aSet

/-- info: 'STACS2027.Runtimes.QPRam.aB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.aB

/-- info: 'STACS2027.Runtimes.QPRam.aB_specB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.aB_specB

/-- info: 'STACS2027.Runtimes.QPRam.mAl' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.mAl

/-- info: 'STACS2027.Runtimes.QPRam.mGa' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.mGa

/-- info: 'STACS2027.Runtimes.QPRam.mBe' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.mBe

/-- info: 'STACS2027.Runtimes.QPRam.mSet' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.mSet

/-- info: 'STACS2027.Runtimes.QPRam.mB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.mB

/-- info: 'STACS2027.Runtimes.QPRam.mB_specB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.mB_specB

/-- info: 'STACS2027.Runtimes.QPRam.upd' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.upd

/-- info: 'STACS2027.Runtimes.QPRam.upd_wregs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.upd_wregs

/-- info: 'STACS2027.Runtimes.QPRam.UpdBits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.UpdBits

/-- info: 'STACS2027.Runtimes.QPRam.updCost' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.updCost

/-- info: 'STACS2027.Runtimes.QPRam.updG_flat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.updG_flat

/-- info: 'STACS2027.Runtimes.QPRam.center_flat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.center_flat

/-- info: 'STACS2027.Runtimes.QPRam.matrix_flat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.matrix_flat

/-- info: 'STACS2027.Runtimes.QPRam.updCost_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.updCost_ge

/-- info: 'STACS2027.Runtimes.QPRam.upd_specB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.upd_specB

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.kY' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.kY

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.scanW' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.scanW

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.scrW_sub_scanW' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.scrW_sub_scanW

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.AccRep' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.AccRep

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.scSet' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.scSet

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.scCmp' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.scCmp

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.scPos' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.scPos

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.scBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.scBody

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.scan' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.scan

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.accAt' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.accAt

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.accAt_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.accAt_succ

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.accAt_M' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.accAt_M

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.ScQ' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.ScQ

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.scBW' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.scBW

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.scBW_sub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.scBW_sub

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.ScQ_indep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.ScQ_indep

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.AccRep_indep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.AccRep_indep

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.scSet_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.scSet_spec

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.ScZ' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.ScZ

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.ScS' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.ScS

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.scCmp_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.scCmp_spec

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.scPos_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.scPos_spec

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.scTest_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.scTest_spec

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.ScInv' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.ScInv

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.scBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.scBody_spec

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.scan_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.scan_spec

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.abs_mul_le_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.abs_mul_le_pow

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.abs_le_pow_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.abs_le_pow_mono

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.pow_add_pow_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.pow_add_pow_le

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.mulVec_abs_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.mulVec_abs_le

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.eD' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.eD

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.eQ' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.eQ

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.eZ' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.eZ

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.eU' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.eU

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.bitM' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.bitM

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.dd_le_pow' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.dd_le_pow

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.Ad_le' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.Ad_le

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.kz_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.kz_le

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.Gx_abs_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.Gx_abs_le

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.hf_abs_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.hf_abs_le

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.xs_bits_kmo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.xs_bits_kmo

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.stepBits_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.stepBits_of

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.kmo_sizes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.kmo_sizes

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.pow_le_pow_X' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.pow_le_pow_X

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.bitM_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.bitM_le

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.tstep_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.tstep_le

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.phaseM_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.phaseM_le

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.TK_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.TK_le

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.TO_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.TO_le

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.kmoC' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.kmoC

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.kmo_total_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.kmo_total_le

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.kmoSpace_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.kmoSpace_le

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.kScratch_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.kScratch_le

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.dd' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.dd

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.MM' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.MM

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.gsz' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.gsz

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.asz' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.asz

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.Lay' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.Lay

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.lay' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.lay

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.lay_eqs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.lay_eqs

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.Glob' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.Glob

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.qregs_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.qregs_iff

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.globFree' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.globFree

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.Glob.regIndep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.Glob.regIndep

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.Glob.regIndep'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.Glob.regIndep'

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.StRegs' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.StRegs

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.MemCore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.MemCore

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.WZero' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.WZero

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.KG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.KG

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.MInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.MInv

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.Out' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.Out

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.Out.refl' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.Out.refl

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.Out.trans' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.Out.trans

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.Out.mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.Out.mono

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.out_wrArr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.out_wrArr

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.out_sw' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.out_sw

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.out_wrRows' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.out_wrRows

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.out_upd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.out_upd

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.sarr_of_out' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.sarr_of_out

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.out_of_sameOn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.out_of_sameOn

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.Out.zeroFrom' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.Out.zeroFrom

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.kKL' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.kKL

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.kKO' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.kKO

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.kC' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.kC

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.kJJ' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.kJJ

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.kRP' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.kRP

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.kHP' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.kHP

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.kXP' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.kXP

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.kLP' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.kLP

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.kPP' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.kPP

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.kHR' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.kHR

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.kTK2' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.kTK2

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.kONE' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.kONE

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.kMONE' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.kMONE

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.kW' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.kW

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.KGl' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.KGl

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.KGl.regIndep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.KGl.regIndep

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.KGl.regIndep'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.KGl.regIndep'

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.kA1' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.kA1

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.kA2' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.kA2

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.kAlloc' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.kAlloc

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.kAlloc_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.kAlloc_spec

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.kOne' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.kOne

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.kCSet' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.kCSet

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.kLSet' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.kLSet

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.kPart1' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.kPart1

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.Lf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.Lf

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.ZeroOn' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.ZeroOn

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.KM1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.KM1

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.kPart1_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.kPart1_spec

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.minAcc' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.minAcc

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.minAcc_le' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.minAcc_le

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.minAcc_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.minAcc_mem

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.gL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.gL

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.minAcc_pi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.minAcc_pi

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.piInner' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.piInner

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.piOuter' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.piOuter

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.piInit' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.piInit

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.kPi' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.kPi

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.piV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.piV

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.PiQ' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.PiQ

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.PiQ_regs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.PiQ_regs

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.piInner_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.piInner_spec

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.PiO' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.PiO

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.piOuter_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.piOuter_spec

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.kPi_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.kPi_spec

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.RowsK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.RowsK

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.OutGH' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.OutGH

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.OutGH.refl' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.OutGH.refl

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.OutGH.trans' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.OutGH.trans

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.RowsK.step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.RowsK.step

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.rowS_content' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.rowS_content

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.rowA_content' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.rowA_content

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.rowB_content' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.rowB_content

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.rowSB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.rowSB

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.SG' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.SG

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.SG_regIndep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.SG_regIndep

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.rowSB_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.rowSB_spec

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.KM2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.KM2

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.piV_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.piV_eq

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.km2_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.km2_of

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.sInitB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.sInitB

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.sInit' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.sInit

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.sBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.sBody

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.kS' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.kS

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.SInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.SInv

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.SG_regIndep'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.SG_regIndep'

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.sBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.sBody_spec

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.sInit_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.sInit_spec

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.kS_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.kS_spec

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.coef_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.coef_values

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.rowA_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.rowA_of

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.rowB_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.rowB_of

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.XG' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.XG

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.XG_regIndep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.XG_regIndep

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.rowEnd' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.rowEnd

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.rowB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.rowB

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.rowASet' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.rowASet

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.rowA' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.rowA

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.rowEnd_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.rowEnd_spec

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.rowsK_after' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.rowsK_after

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.rowB_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.rowB_spec

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.rowA_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.rowA_spec

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.kZt' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.kZt

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.zf_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.zf_iff

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.zTest' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.zTest

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.rowsN' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.rowsN

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.rowsZ' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.rowsZ

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.xAdv' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.xAdv

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.xBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.xBody

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.xOuter' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.xOuter

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.xInit' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.xInit

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.kXR' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.kXR

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.zTest_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.zTest_spec

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.XInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.XInv

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.xinv_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.xinv_of

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.rowA_of'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.rowA_of'

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.rowB_of'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.rowB_of'

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.hpf_X'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.hpf_X'

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.rowsN_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.rowsN_spec

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.rowsZ_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.rowsZ_spec

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.xBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.xBody_spec

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.xBody_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.xBody_frame

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.xOuter_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.xOuter_spec

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.xInit_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.xInit_spec

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.kX_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.kX_spec

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.kFin' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.kFin

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.kProg' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.kProg

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.TK' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.TK

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.kFin_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.kFin_spec

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.memCore_init' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.memCore_init

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.kProg_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.kProg_spec

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.kPG' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.kPG

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.kGS' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.kGS

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.kPAJ' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.kPAJ

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.kAS' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.kAS

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.kPZN' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.kPZN

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.kPCOL' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.kPCOL

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.kPU' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.kPU

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.kPV' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.kPV

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.kPW' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.kPW

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.kPOM' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.kPOM

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.kPSG' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.kPSG

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.kPHP' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.kPHP

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.kPT' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.kPT

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.kE' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.kE

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.kR' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.kR

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.kDL' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.kDL

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.kQ' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.kQ

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.kROW' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.kROW

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.kOFF' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.kOFF

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.kSB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.kSB

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.kOB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.kOB

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.kBP' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.kBP

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.kFL' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.kFL

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.kP1' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.kP1

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.kP2' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.kP2

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.kJ' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.kJ

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.kN' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.kN

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.kPS' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.kPS

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.kSS' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.kSS

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.kPD' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.kPD

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.kSD' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.kSD

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.kNG' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.kNG

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.kX' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.kX

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.kA' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.kA

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.rowS_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.rowS_val

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.rowX_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.rowX_val

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.colX_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.colX_val

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.colP_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.colP_val

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.dimKKT_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.dimKKT_eq

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.nRows_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.nRows_eq

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.div_mul_add_mod'' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.div_mul_add_mod'

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.finRow_S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.finRow_S

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.finRow_X' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.finRow_X

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.finCol_X' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.finCol_X

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.finCol_P' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.finCol_P

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.Zf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.Zf

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.Gf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.Gf

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.hf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.hf

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.Gx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.Gx

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.hpf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.hpf

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.ZnF₀' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.ZnF₀

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.Gf_fin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.Gf_fin

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.hf_fin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.hf_fin

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.ZnF₀_fin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.ZnF₀_fin

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.sgnS_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.sgnS_val

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.Gx_S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.Gx_S

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.Gx_X' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.Gx_X

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.hpf_S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.hpf_S

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.hpf_X' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.hpf_X

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.ZnF₀_x' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.ZnF₀_x

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.ZnF₀_p' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.ZnF₀_p

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.smem_zero' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.smem_zero

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.sarr_of_eq' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.sarr_of_eq

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.entry_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.entry_lt

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.sarr_of_on' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.sarr_of_on

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.sarr_congr' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.sarr_congr

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.sarr_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.sarr_mono

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.sarr_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.sarr_zero

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.wrArr_of_ne' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.wrArr_of_ne

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.wrArr_of_out'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.wrArr_of_out'

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.sw_of_out' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.sw_of_out

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.succ_mul_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.succ_mul_le

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.TF' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.TF

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.AjF' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.AjF

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.ZnF' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.ZnF

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.TF_fin' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.TF_fin

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.AjF_fin' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.AjF_fin

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.ZnF_fin' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.ZnF_fin

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.TF_lt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.TF_lt

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.sum_fin_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.sum_fin_range

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.mulVec_eq_fin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.mulVec_eq_fin

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.sgnMul' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.sgnMul

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.HT.of_false' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.HT.of_false

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.cpBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.cpBody

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.cpLoop' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.cpLoop

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.cpW' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.cpW

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.wregs_cpLoop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.wregs_cpLoop

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.CG' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.CG

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.CG_regIndep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.CG_regIndep

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.cpBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.cpBody_spec

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.CInv' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.CInv

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.cpLoop_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.cpLoop_spec

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.gaBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.gaBody

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.gather' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.gather

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.gaW' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.gaW

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.wregs_gather' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.wregs_gather

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.GInv' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.GInv

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.gather_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.gather_spec

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.outVal_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.outVal_eq

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.hSet' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.hSet

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.zSet' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.zSet

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.outBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.outBody

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.oProg' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.oProg

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.ofFn_eq_range' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.ofFn_eq_range

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.hT_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.hT_eq

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.zNum_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.zNum_eq

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.outList_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.outList_eq

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.state_det_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.state_det_ne

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.rowEquiv_cases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.rowEquiv_cases

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.RO' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.RO

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.outF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.outF

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.outBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.outBody_spec

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.TO' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.TO

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.oProg_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.oProg_spec

/-- info: 'STACS2027.Runtimes.QPRam.kmoProg' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.kmoProg

/-- info: 'STACS2027.Runtimes.QPRam.kProg_writes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.kProg_writes

/-- info: 'STACS2027.Runtimes.QPRam.mLoop_writes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.mLoop_writes

/-- info: 'STACS2027.Runtimes.QPRam.kmoProg_wregs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.kmoProg_wregs

/-- info: 'STACS2027.Runtimes.QPRam.phaseKMO_ramB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.phaseKMO_ramB

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.colf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.colf

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.uf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.uf

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.wf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.wf

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.omf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.omf

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.gzf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.gzf

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.sgf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.sgf

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.vf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.vf

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.Gx_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.Gx_lt

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.castLE_last_val' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.castLE_last_val

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.colf_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.colf_eq

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.uf_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.uf_eq

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.wf_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.wf_eq

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.omf_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.omf_eq

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.gzf_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.gzf_eq

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.sgf_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.sgf_eq

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.vf_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.vf_eq

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.nxt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.nxt

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.Δ_next' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.Δ_next

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.q_next' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.q_next

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.TF_next_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.TF_next_lt

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.TF_next_r' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.TF_next_r

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.ZnF_next' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.ZnF_next

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.AjF_next_cc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.AjF_next_cc

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.AjF_next_cl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.AjF_next_cl

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.AjF_next_lc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.AjF_next_lc

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.AjF_next_ll' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.AjF_next_ll

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.kkt_start' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.kkt_start

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.step_math' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.step_math

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.StepBits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.StepBits

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.Tstep' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.Tstep

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.offBlk' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.offBlk

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.stepBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.stepBody

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.regIndep_stRegs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.regIndep_stRegs

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.RA_regIndep_scan' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.RA_regIndep_scan

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.memB3_next' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.memB3_next

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.step_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.step_spec

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.mLoop' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.mLoop

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.MInv_indep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.MInv_indep

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.mLoop_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.mLoop_spec

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.scrW' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.scrW

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.mvW_sub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.mvW_sub

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.linW_sub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.linW_sub

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.r1W_sub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.r1W_sub

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.axW_sub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.axW_sub

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.cpW_sub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.cpW_sub

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.gaW_sub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.gaW_sub

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.scrW_glob' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.scrW_glob

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.RA' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.RA

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.RA_regIndep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.RA_regIndep

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.MemA0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.MemA0

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.MemA1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.MemA1

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.MemA2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.MemA2

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.MemA3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.MemA3

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.MemA4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.MemA4

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.MemA5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.MemA5

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.MemA6' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.MemA6

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.MemCore.of_out' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.MemCore.of_out

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.colSet' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.colSet

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.colBlk' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.colBlk

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.colBlk_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.colBlk_spec

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.uSet' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.uSet

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.uBlk' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.uBlk

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.uBlk_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.uBlk_spec

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.wSet' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.wSet

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.wLast' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.wLast

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.wBlk' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.wBlk

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.wBlk_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.wBlk_spec

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.gRows_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.gRows_read

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.gSet' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.gSet

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.omBlk' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.omBlk

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.gzBlk' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.gzBlk

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.omBlk_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.omBlk_spec

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.gzBlk_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.gzBlk_spec

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.sgSet' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.sgSet

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.sgBlk' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.sgBlk

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.sgBlk_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.sgBlk_spec

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.cell_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.cell_eq

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.aj_border' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.aj_border

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.RB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.RB

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.RB_regIndep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.RB_regIndep

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.MemB1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.MemB1

/-- info: 'STACS2027.Runtimes.QPRam.Kmo.vSet' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.QPRam.Kmo.vSet

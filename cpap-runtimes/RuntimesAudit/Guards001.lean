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

/-- info: 'STACS2027.Runtimes.BoundedCost.prefixOccurrences_clauses' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.prefixOccurrences_clauses

/-- info: 'STACS2027.Runtimes.BoundedCost.activeOccurrences_prefixOccurrences' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.activeOccurrences_prefixOccurrences

/-- info: 'STACS2027.Runtimes.BoundedCost.Compiler.CompressionReady' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Compiler.CompressionReady

/-- info: 'STACS2027.Runtimes.BoundedCost.Compiler.prefixBasic_caller_exec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Compiler.prefixBasic_caller_exec

/-- info: '_private.Runtimes.BoundedCost.PrefixRAM.0.STACS2027.Runtimes.BoundedCost.Compiler.globals_not_inc' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Compiler.globals_not_inc

/-- info: '_private.Runtimes.BoundedCost.PrefixRAM.0.STACS2027.Runtimes.BoundedCost.Compiler.globals_not_excess' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Compiler.globals_not_excess

/-- info: 'STACS2027.Runtimes.BoundedCost.Compiler.prefixBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Compiler.prefixBody_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.Compiler.PrefixBasic' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Compiler.PrefixBasic

/-- info: 'STACS2027.Runtimes.BoundedCost.Compiler.PrefixAnswerRep' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Compiler.PrefixAnswerRep

/-- info: 'STACS2027.Runtimes.BoundedCost.Compiler.PrefixRep' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Compiler.PrefixRep

/-- info: 'STACS2027.Runtimes.BoundedCost.Compiler.prefixRep_indep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Compiler.prefixRep_indep

/-- info: 'STACS2027.Runtimes.BoundedCost.Compiler.globals_prefixCheck_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Compiler.globals_prefixCheck_frame

/-- info: 'STACS2027.Runtimes.BoundedCost.gPSI' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.gPSI

/-- info: 'STACS2027.Runtimes.BoundedCost.gPS1' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.gPS1

/-- info: 'STACS2027.Runtimes.BoundedCost.eP' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.eP

/-- info: 'STACS2027.Runtimes.BoundedCost.eD' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.eD

/-- info: 'STACS2027.Runtimes.BoundedCost.eOne' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.eOne

/-- info: 'STACS2027.Runtimes.BoundedCost.eY' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.eY

/-- info: 'STACS2027.Runtimes.BoundedCost.readPsi' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.readPsi

/-- info: 'STACS2027.Runtimes.BoundedCost.stepInit5' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.stepInit5

/-- info: 'STACS2027.Runtimes.BoundedCost.allocSeen' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.allocSeen

/-- info: 'STACS2027.Runtimes.BoundedCost.pcCopy' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.pcCopy

/-- info: 'STACS2027.Runtimes.BoundedCost.stepPcs' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.stepPcs

/-- info: 'STACS2027.Runtimes.BoundedCost.markBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.markBody

/-- info: 'STACS2027.Runtimes.BoundedCost.emitOv' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.emitOv

/-- info: 'STACS2027.Runtimes.BoundedCost.scanBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.scanBody

/-- info: 'STACS2027.Runtimes.BoundedCost.clearBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.clearBody

/-- info: 'STACS2027.Runtimes.BoundedCost.ovPair' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.ovPair

/-- info: 'STACS2027.Runtimes.BoundedCost.ovPairT' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.ovPairT

/-- info: 'STACS2027.Runtimes.BoundedCost.ovRow' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.ovRow

/-- info: 'STACS2027.Runtimes.BoundedCost.stepOv' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.stepOv

/-- info: 'STACS2027.Runtimes.BoundedCost.form5' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.form5

/-- info: 'STACS2027.Runtimes.BoundedCost.outBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.outBody

/-- info: 'STACS2027.Runtimes.BoundedCost.stepOut' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.stepOut

/-- info: 'STACS2027.Runtimes.BoundedCost.build5' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.build5

/-- info: 'STACS2027.Runtimes.BoundedCost.readBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.readBody

/-- info: 'STACS2027.Runtimes.BoundedCost.readPre' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.readPre

/-- info: 'STACS2027.Runtimes.BoundedCost.readT' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.readT

/-- info: 'STACS2027.Runtimes.BoundedCost.readAns' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.readAns

/-- info: 'STACS2027.Runtimes.BoundedCost.extract5' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.extract5

/-- info: 'STACS2027.Runtimes.BoundedCost.satMoves' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.satMoves

/-- info: 'STACS2027.Runtimes.BoundedCost.callSat5' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.callSat5

/-- info: 'STACS2027.Runtimes.BoundedCost.zero5' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.zero5

/-- info: 'STACS2027.Runtimes.BoundedCost.referenceCopyCandidate' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.referenceCopyCandidate

/-- info: 'STACS2027.Runtimes.BoundedCost.referenceCopyReference' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.referenceCopyReference

/-- info: 'STACS2027.Runtimes.BoundedCost.referenceCopyLength' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.referenceCopyLength

/-- info: 'STACS2027.Runtimes.BoundedCost.referenceCopyReady' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.referenceCopyReady

/-- info: 'STACS2027.Runtimes.BoundedCost.copyReference' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.copyReference

/-- info: 'STACS2027.Runtimes.BoundedCost.ReferenceCopyGlobals' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.ReferenceCopyGlobals

/-- info: 'STACS2027.Runtimes.BoundedCost.copyReference_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.copyReference_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.dualTruthValues' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.dualTruthValues

/-- info: 'STACS2027.Runtimes.BoundedCost.dualTruthValues_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.dualTruthValues_length

/-- info: 'STACS2027.Runtimes.BoundedCost.TruthTable.array' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.TruthTable.array

/-- info: 'STACS2027.Runtimes.BoundedCost.referenceCopy_truth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.referenceCopy_truth

/-- info: 'STACS2027.Runtimes.BoundedCost.IsLeastCut.requirements_congr' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.IsLeastCut.requirements_congr

/-- info: 'STACS2027.Runtimes.BoundedCost.isLeastCut_requirements_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.isLeastCut_requirements_iff

/-- info: 'STACS2027.Runtimes.BoundedCost.unsatisfiedCount_perm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.unsatisfiedCount_perm

/-- info: 'STACS2027.Runtimes.BoundedCost.cutCost_perm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.cutCost_perm

/-- info: 'STACS2027.Runtimes.BoundedCost.annotated_perm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.annotated_perm

/-- info: 'STACS2027.Runtimes.BoundedCost.annotated_member_branches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.annotated_member_branches

/-- info: 'STACS2027.Runtimes.BoundedCost.cutCost_erase_conflict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.cutCost_erase_conflict

/-- info: 'STACS2027.Runtimes.BoundedCost.leastCut_erase_conflict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.leastCut_erase_conflict

/-- info: 'STACS2027.Runtimes.BoundedCost.LeastCutOperation' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.LeastCutOperation

/-- info: 'STACS2027.Runtimes.BoundedCost.LeastCutOperationCorrect' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.LeastCutOperationCorrect

/-- info: 'STACS2027.Runtimes.BoundedCost.findCutConflict' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.findCutConflict

/-- info: 'STACS2027.Runtimes.BoundedCost.findCutConflict_some' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.findCutConflict_some

/-- info: 'STACS2027.Runtimes.BoundedCost.conflictCost_zero_of_findCutConflict_none' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.conflictCost_zero_of_findCutConflict_none

/-- info: 'STACS2027.Runtimes.BoundedCost.annotatedSearch' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.annotatedSearch

/-- info: 'STACS2027.Runtimes.BoundedCost.annotatedSearch_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.annotatedSearch_sound

/-- info: 'STACS2027.Runtimes.BoundedCost.orElse_exists_some_left' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.orElse_exists_some_left

/-- info: 'STACS2027.Runtimes.BoundedCost.orElse_exists_some_right' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.orElse_exists_some_right

/-- info: 'STACS2027.Runtimes.BoundedCost.annotatedSearch_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.annotatedSearch_complete

/-- info: 'STACS2027.Runtimes.BoundedCost.annotatedSearch_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.annotatedSearch_correct

/-- info: 'STACS2027.Runtimes.BoundedCost.sum_geometric_powers_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.sum_geometric_powers_le

/-- info: 'STACS2027.Runtimes.BoundedCost.sum_geometric_weight_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.sum_geometric_weight_le

/-- info: 'STACS2027.Runtimes.BoundedCost.fptBound_sum_of_constant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.fptBound_sum_of_constant

/-- info: 'STACS2027.Runtimes.BoundedCost.fptBound_accumulated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.fptBound_accumulated

/-- info: 'STACS2027.Runtimes.BoundedCost.almostFormula_solverInputLength_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.almostFormula_solverInputLength_mono

/-- info: 'STACS2027.Runtimes.BoundedCost.boundedCost_solverCalls_accumulated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.boundedCost_solverCalls_accumulated

/-- info: 'STACS2027.Runtimes.BoundedCost.ForcedTable' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.ForcedTable

/-- info: 'STACS2027.Runtimes.BoundedCost.terminalRowsMem_of_tables' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.terminalRowsMem_of_tables

/-- info: 'STACS2027.Runtimes.BoundedCost.searchRowsMem_of_contraction' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.searchRowsMem_of_contraction

/-- info: 'STACS2027.Runtimes.BoundedCost.searchNode' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.searchNode

/-- info: 'STACS2027.Runtimes.BoundedCost.LeastCutRegisterFrame.caller' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.LeastCutRegisterFrame.caller

/-- info: 'STACS2027.Runtimes.BoundedCost.LeastCutGeometry.read_cells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.LeastCutGeometry.read_cells

/-- info: 'STACS2027.Runtimes.BoundedCost.contractionRowsMem_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.contractionRowsMem_frame

/-- info: 'STACS2027.Runtimes.BoundedCost.nodeActionMemory_truth' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.nodeActionMemory_truth

/-- info: 'STACS2027.Runtimes.BoundedCost.SearchNodeRegisterFrame' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.SearchNodeRegisterFrame

/-- info: 'STACS2027.Runtimes.BoundedCost.SearchNodeResult' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.SearchNodeResult

/-- info: 'STACS2027.Runtimes.BoundedCost.summarizeRow_literal_bounds' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.summarizeRow_literal_bounds

/-- info: 'STACS2027.Runtimes.BoundedCost.summarizePrefix_literal_bounds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.summarizePrefix_literal_bounds

/-- info: 'STACS2027.Runtimes.BoundedCost.NodeControlGlobals' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.NodeControlGlobals

/-- info: 'STACS2027.Runtimes.BoundedCost.searchNode_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.searchNode_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.HasSearchAnswer' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.HasSearchAnswer

/-- info: 'STACS2027.Runtimes.BoundedCost.hasSearchAnswer_orElse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.hasSearchAnswer_orElse

/-- info: 'STACS2027.Runtimes.BoundedCost.exists_valid_choices_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.exists_valid_choices_succ

/-- info: 'STACS2027.Runtimes.BoundedCost.annotatedPath' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.annotatedPath

/-- info: 'STACS2027.Runtimes.BoundedCost.annotatedSearch_iff_path' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.annotatedSearch_iff_path

/-- info: 'STACS2027.Runtimes.BoundedCost.annotatedSearch_iff_encoded_path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.annotatedSearch_iff_encoded_path

/-- info: 'STACS2027.Runtimes.BoundedCost.rowUnsatisfied' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.rowUnsatisfied

/-- info: 'STACS2027.Runtimes.BoundedCost.rowCut' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.rowCut

/-- info: 'STACS2027.Runtimes.BoundedCost.rowConflict' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.rowConflict

/-- info: 'STACS2027.Runtimes.BoundedCost.summarizeRow_unsatisfied' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.summarizeRow_unsatisfied

/-- info: 'STACS2027.Runtimes.BoundedCost.summarizeRow_cut' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.summarizeRow_cut

/-- info: 'STACS2027.Runtimes.BoundedCost.summarizePrefix_unsatisfied' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.summarizePrefix_unsatisfied

/-- info: 'STACS2027.Runtimes.BoundedCost.summarizePrefix_cut' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.summarizePrefix_cut

/-- info: 'STACS2027.Runtimes.BoundedCost.summarizeRow_conflict' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.summarizeRow_conflict

/-- info: 'STACS2027.Runtimes.BoundedCost.summarizePrefix_conflict_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.summarizePrefix_conflict_zero

/-- info: 'STACS2027.Runtimes.BoundedCost.summarizePrefix_conflict_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.summarizePrefix_conflict_le

/-- info: 'STACS2027.Runtimes.BoundedCost.summarizePrefix_conflict_witness' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.summarizePrefix_conflict_witness

/-- info: 'STACS2027.Runtimes.BoundedCost.scanFormulaBase' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.scanFormulaBase

/-- info: 'STACS2027.Runtimes.BoundedCost.scanClauseCount' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.scanClauseCount

/-- info: 'STACS2027.Runtimes.BoundedCost.scanActiveBase' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.scanActiveBase

/-- info: 'STACS2027.Runtimes.BoundedCost.scanCandidateBase' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.scanCandidateBase

/-- info: 'STACS2027.Runtimes.BoundedCost.scanReferenceBase' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.scanReferenceBase

/-- info: 'STACS2027.Runtimes.BoundedCost.scanUnsatisfied' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.scanUnsatisfied

/-- info: 'STACS2027.Runtimes.BoundedCost.scanCut' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.scanCut

/-- info: 'STACS2027.Runtimes.BoundedCost.scanConflict' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.scanConflict

/-- info: 'STACS2027.Runtimes.BoundedCost.scanFirstLiteral' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.scanFirstLiteral

/-- info: 'STACS2027.Runtimes.BoundedCost.scanSecondLiteral' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.scanSecondLiteral

/-- info: 'STACS2027.Runtimes.BoundedCost.scanIndex' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.scanIndex

/-- info: 'STACS2027.Runtimes.BoundedCost.scanOffset' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.scanOffset

/-- info: 'STACS2027.Runtimes.BoundedCost.scanActive' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.scanActive

/-- info: 'STACS2027.Runtimes.BoundedCost.scanFirst' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.scanFirst

/-- info: 'STACS2027.Runtimes.BoundedCost.scanSecond' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.scanSecond

/-- info: 'STACS2027.Runtimes.BoundedCost.scanFirstTruth' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.scanFirstTruth

/-- info: 'STACS2027.Runtimes.BoundedCost.scanSecondTruth' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.scanSecondTruth

/-- info: 'STACS2027.Runtimes.BoundedCost.scanFirstReference' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.scanFirstReference

/-- info: 'STACS2027.Runtimes.BoundedCost.scanSecondReference' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.scanSecondReference

/-- info: 'STACS2027.Runtimes.BoundedCost.SearchRow' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.SearchRow

/-- info: 'STACS2027.Runtimes.BoundedCost.SearchSummary' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.SearchSummary

/-- info: 'STACS2027.Runtimes.BoundedCost.summarizeRow' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.summarizeRow

/-- info: 'STACS2027.Runtimes.BoundedCost.summarizePrefix' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.summarizePrefix

/-- info: 'STACS2027.Runtimes.BoundedCost.summarizePrefix_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.summarizePrefix_succ

/-- info: 'STACS2027.Runtimes.BoundedCost.SearchSummaryRep' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.SearchSummaryRep

/-- info: 'STACS2027.Runtimes.BoundedCost.searchScanRecordConflict' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.searchScanRecordConflict

/-- info: 'STACS2027.Runtimes.BoundedCost.searchScanUnsatisfied' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.searchScanUnsatisfied

/-- info: 'STACS2027.Runtimes.BoundedCost.searchScanBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.searchScanBody

/-- info: 'STACS2027.Runtimes.BoundedCost.searchScanInit' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.searchScanInit

/-- info: 'STACS2027.Runtimes.BoundedCost.searchScan' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.searchScan

/-- info: 'STACS2027.Runtimes.BoundedCost.SearchScanGlobals' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.SearchScanGlobals

/-- info: 'STACS2027.Runtimes.BoundedCost.SearchRowsMem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.SearchRowsMem

/-- info: 'STACS2027.Runtimes.BoundedCost.searchScanBody_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.searchScanBody_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.searchScan_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.searchScan_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.searchRowOf' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.searchRowOf

/-- info: 'STACS2027.Runtimes.BoundedCost.searchRowsOf' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.searchRowsOf

/-- info: 'STACS2027.Runtimes.BoundedCost.searchRowsOf_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.searchRowsOf_length

/-- info: 'STACS2027.Runtimes.BoundedCost.searchRowsOf_getD' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.searchRowsOf_getD

/-- info: 'STACS2027.Runtimes.BoundedCost.countP_getD_range' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.countP_getD_range

/-- info: 'STACS2027.Runtimes.BoundedCost.rowConflict_searchRow' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.rowConflict_searchRow

/-- info: 'STACS2027.Runtimes.BoundedCost.searchRows_unsatisfied' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.searchRows_unsatisfied

/-- info: 'STACS2027.Runtimes.BoundedCost.searchRows_cut' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.searchRows_cut

/-- info: 'STACS2027.Runtimes.BoundedCost.summarizePrefix_unsatisfied_semantic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.summarizePrefix_unsatisfied_semantic

/-- info: 'STACS2027.Runtimes.BoundedCost.summarizePrefix_cut_semantic' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.summarizePrefix_cut_semantic

/-- info: 'STACS2027.Runtimes.BoundedCost.find_activeOccurrence_first' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.find_activeOccurrence_first

/-- info: 'STACS2027.Runtimes.BoundedCost.summarizePrefix_conflict_semantic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.summarizePrefix_conflict_semantic

/-- info: 'STACS2027.Runtimes.BoundedCost.searchNodeBound' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.searchNodeBound

/-- info: 'STACS2027.Runtimes.BoundedCost.searchNodeBound_identity' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.searchNodeBound_identity

/-- info: 'STACS2027.Runtimes.BoundedCost.searchNodeBound_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.searchNodeBound_le

/-- info: 'STACS2027.Runtimes.BoundedCost.annotatedSearchCalls' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.annotatedSearchCalls

/-- info: 'STACS2027.Runtimes.BoundedCost.annotatedSearchCalls_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.annotatedSearchCalls_le

/-- info: 'STACS2027.Runtimes.BoundedCost.tryCompressionCalls' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.tryCompressionCalls

/-- info: 'STACS2027.Runtimes.BoundedCost.tryCompressionCalls_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.tryCompressionCalls_le

/-- info: 'STACS2027.Runtimes.BoundedCost.compressionSearchCalls' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.compressionSearchCalls

/-- info: 'STACS2027.Runtimes.BoundedCost.compressionSearchCalls_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.compressionSearchCalls_le

/-- info: 'STACS2027.Runtimes.BoundedCost.iterativeSearchCalls' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.iterativeSearchCalls

/-- info: 'STACS2027.Runtimes.BoundedCost.iterativeSearchCalls_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.iterativeSearchCalls_le

/-- info: 'STACS2027.Runtimes.BoundedCost.almostTwoSatSearchCalls' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.almostTwoSatSearchCalls

/-- info: 'STACS2027.Runtimes.BoundedCost.almostTwoSatSearchCalls_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.almostTwoSatSearchCalls_le

/-- info: 'STACS2027.Runtimes.BoundedCost.compressionPathWork_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.compressionPathWork_le

/-- info: 'STACS2027.Runtimes.BoundedCost.Clauses2' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Clauses2

/-- info: 'STACS2027.Runtimes.BoundedCost.SolverDomain' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.SolverDomain

/-- info: 'STACS2027.Runtimes.BoundedCost.solverDomain_clauses2' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.solverDomain_clauses2

/-- info: 'STACS2027.Runtimes.BoundedCost.OccursIn' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.OccursIn

/-- info: 'STACS2027.Runtimes.BoundedCost.a2In' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.a2In

/-- info: 'STACS2027.Runtimes.BoundedCost.A2Answer' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.A2Answer

/-- info: 'STACS2027.Runtimes.BoundedCost.Almost2SatSolver' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Almost2SatSolver

/-- info: 'STACS2027.Runtimes.BoundedCost.FPTBound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.FPTBound

/-- info: 'STACS2027.Runtimes.BoundedCost.shiftL' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.shiftL

/-- info: 'STACS2027.Runtimes.BoundedCost.shiftF' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.shiftF

/-- info: 'STACS2027.Runtimes.BoundedCost.length_shiftF' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.length_shiftF

/-- info: 'STACS2027.Runtimes.BoundedCost.code_shiftL' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.code_shiftL

/-- info: 'STACS2027.Runtimes.BoundedCost.codes_shiftF' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.codes_shiftF

/-- info: 'STACS2027.Runtimes.BoundedCost.evalClause_shiftL' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.evalClause_shiftL

/-- info: 'STACS2027.Runtimes.BoundedCost.evalCNF_shiftF' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.evalCNF_shiftF

/-- info: 'STACS2027.Runtimes.BoundedCost.clauses2_shiftF' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.clauses2_shiftF

/-- info: 'STACS2027.Runtimes.BoundedCost.occursIn_shiftF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.occursIn_shiftF

/-- info: 'STACS2027.Runtimes.BoundedCost.almostSatisfiable_shiftF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.almostSatisfiable_shiftF

/-- info: 'STACS2027.Runtimes.BoundedCost.keptOf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.keptOf

/-- info: 'STACS2027.Runtimes.BoundedCost.length_filter_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.length_filter_range

/-- info: 'STACS2027.Runtimes.BoundedCost.card_filter_mem_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.card_filter_mem_range

/-- info: 'STACS2027.Runtimes.BoundedCost.count_not_mem_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.count_not_mem_range

/-- info: 'STACS2027.Runtimes.BoundedCost.keptOf_sublist' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.keptOf_sublist

/-- info: 'STACS2027.Runtimes.BoundedCost.keptOf_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.keptOf_length

/-- info: 'STACS2027.Runtimes.BoundedCost.mem_keptOf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.mem_keptOf

/-- info: 'STACS2027.Runtimes.BoundedCost.evalCNF_keptOf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.evalCNF_keptOf

/-- info: 'STACS2027.Runtimes.BoundedCost.length_le_of_pairwise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.length_le_of_pairwise

/-- info: 'STACS2027.Runtimes.BoundedCost.noAssignment_of_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.noAssignment_of_shift

/-- info: 'STACS2027.Runtimes.BoundedCost.permitted_of_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.permitted_of_shift

/-- info: 'STACS2027.Runtimes.BoundedCost.boundedCostInput' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.boundedCostInput

/-- info: 'STACS2027.Runtimes.BoundedCost.length_boundedCostInput' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.length_boundedCostInput

/-- info: 'STACS2027.Runtimes.BoundedCost.input5z_facts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.input5z_facts

/-- info: 'STACS2027.Runtimes.BoundedCost.input5_facts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.input5_facts

/-- info: 'STACS2027.Runtimes.BoundedCost.updF' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.updF

/-- info: 'STACS2027.Runtimes.BoundedCost.updF_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.updF_succ

/-- info: 'STACS2027.Runtimes.BoundedCost.updF_of_ne' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.updF_of_ne

/-- info: 'STACS2027.Runtimes.BoundedCost.updF_at' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.updF_at

/-- info: 'STACS2027.Runtimes.BoundedCost.markF' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.markF

/-- info: 'STACS2027.Runtimes.BoundedCost.clearF' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.clearF

/-- info: 'STACS2027.Runtimes.BoundedCost.markF_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.markF_succ

/-- info: 'STACS2027.Runtimes.BoundedCost.clearF_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.clearF_succ

/-- info: 'STACS2027.Runtimes.BoundedCost.clearF_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.clearF_zero

/-- info: 'STACS2027.Runtimes.BoundedCost.markF_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.markF_zero

/-- info: 'STACS2027.Runtimes.BoundedCost.mark_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.mark_inj

/-- info: 'STACS2027.Runtimes.BoundedCost.markF_eid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.markF_eid

/-- info: 'STACS2027.Runtimes.BoundedCost.clearF_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.clearF_full

/-- info: 'STACS2027.Runtimes.BoundedCost.ovCl' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.ovCl

/-- info: 'STACS2027.Runtimes.BoundedCost.ovS' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.ovS

/-- info: 'STACS2027.Runtimes.BoundedCost.ovPairCl' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.ovPairCl

/-- info: 'STACS2027.Runtimes.BoundedCost.ovJ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.ovJ

/-- info: 'STACS2027.Runtimes.BoundedCost.ovI' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.ovI

/-- info: 'STACS2027.Runtimes.BoundedCost.pcs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.pcs

/-- info: 'STACS2027.Runtimes.BoundedCost.ovS_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.ovS_succ

/-- info: 'STACS2027.Runtimes.BoundedCost.ovJ_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.ovJ_succ

/-- info: 'STACS2027.Runtimes.BoundedCost.ovJ_start' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.ovJ_start

/-- info: 'STACS2027.Runtimes.BoundedCost.ovI_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.ovI_succ

/-- info: 'STACS2027.Runtimes.BoundedCost.pcs_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.pcs_succ

/-- info: 'STACS2027.Runtimes.BoundedCost.ovCl_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.ovCl_eq

/-- info: 'STACS2027.Runtimes.BoundedCost.flatMap_ite_singleton' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.flatMap_ite_singleton

/-- info: 'STACS2027.Runtimes.BoundedCost.ovI_full' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.ovI_full

/-- info: 'STACS2027.Runtimes.BoundedCost.almostFormula_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.almostFormula_eq

/-- info: 'STACS2027.Runtimes.BoundedCost.length_pcs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.length_pcs

/-- info: 'STACS2027.Runtimes.BoundedCost.bE5' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.bE5

/-- info: 'STACS2027.Runtimes.BoundedCost.bS5' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.bS5

/-- info: 'STACS2027.Runtimes.BoundedCost.bC5' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.bC5

/-- info: 'STACS2027.Runtimes.BoundedCost.lay5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.lay5

/-- info: 'STACS2027.Runtimes.BoundedCost.HG' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.HG

/-- info: 'STACS2027.Runtimes.BoundedCost.HMem' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.HMem

/-- info: 'STACS2027.Runtimes.BoundedCost.HS' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.HS

/-- info: 'STACS2027.Runtimes.BoundedCost.HMem.push2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.HMem.push2

/-- info: 'STACS2027.Runtimes.BoundedCost.HMem.seen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.HMem.seen

/-- info: 'STACS2027.Runtimes.BoundedCost.HG.regIndep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.HG.regIndep

/-- info: 'STACS2027.Runtimes.BoundedCost.WO' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.WO

/-- info: 'STACS2027.Runtimes.BoundedCost.HG.regIndepO' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.HG.regIndepO

/-- info: 'STACS2027.Runtimes.BoundedCost.HS.emit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.HS.emit

/-- info: 'STACS2027.Runtimes.BoundedCost.HS.room' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.HS.room

/-- info: 'STACS2027.Runtimes.BoundedCost.HS.seen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.HS.seen

/-- info: 'STACS2027.Runtimes.BoundedCost.length_codes_append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.length_codes_append

/-- info: 'STACS2027.Runtimes.BoundedCost.length_codes_flatMap_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.length_codes_flatMap_le

/-- info: 'STACS2027.Runtimes.BoundedCost.renamedTernaryLoop' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.renamedTernaryLoop

/-- info: 'STACS2027.Runtimes.BoundedCost.renamedTernaryScan' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.renamedTernaryScan

/-- info: 'STACS2027.Runtimes.BoundedCost.not_mem_renameRegisters_wregs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.not_mem_renameRegisters_wregs

/-- info: 'STACS2027.Runtimes.BoundedCost.renamedTernaryLoop_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.renamedTernaryLoop_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.renamedTernaryScan_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.renamedTernaryScan_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.wordIndex' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.wordIndex

/-- info: 'STACS2027.Runtimes.BoundedCost.wordCount' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.wordCount

/-- info: 'STACS2027.Runtimes.BoundedCost.ternaryLoop' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.ternaryLoop

/-- info: 'STACS2027.Runtimes.BoundedCost.ternaryScan' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.ternaryScan

/-- info: 'STACS2027.Runtimes.BoundedCost.ternaryFold' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.ternaryFold

/-- info: 'STACS2027.Runtimes.BoundedCost.ternaryFold_zero' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.ternaryFold_zero

/-- info: 'STACS2027.Runtimes.BoundedCost.ternaryFold_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.ternaryFold_succ

/-- info: 'STACS2027.Runtimes.BoundedCost.ternaryLoop_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.ternaryLoop_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.ternaryScan_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.ternaryScan_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.renamedOdo_state_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.renamedOdo_state_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.renamedTernaryLoop_state_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.renamedTernaryLoop_state_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.renamedTernaryScan_state_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.renamedTernaryScan_state_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.lenP5' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.lenP5

/-- info: 'STACS2027.Runtimes.BoundedCost.boundedCostInput_flow' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.boundedCostInput_flow

/-- info: 'STACS2027.Runtimes.BoundedCost.isCycle_all' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.isCycle_all

/-- info: 'STACS2027.Runtimes.BoundedCost.lenP5_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.lenP5_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.clearRegs' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.clearRegs

/-- info: 'STACS2027.Runtimes.BoundedCost.loopFree_clearRegs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.loopFree_clearRegs

/-- info: 'STACS2027.Runtimes.BoundedCost.memFree_clearRegs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.memFree_clearRegs

/-- info: 'STACS2027.Runtimes.BoundedCost.run_clearRegs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.run_clearRegs

/-- info: 'STACS2027.Runtimes.BoundedCost.topW' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.topW

/-- info: 'STACS2027.Runtimes.BoundedCost.TopPost' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.TopPost

/-- info: 'STACS2027.Runtimes.BoundedCost.clearTop_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.clearTop_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.readTop' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.readTop

/-- info: 'STACS2027.Runtimes.BoundedCost.readTop_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.readTop_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.boundedCostTop' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.boundedCostTop

/-- info: 'STACS2027.Runtimes.BoundedCost.htb_of_computesIn' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.htb_of_computesIn

/-- info: 'STACS2027.Runtimes.BoundedCost.lenA' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.lenA

/-- info: 'STACS2027.Runtimes.BoundedCost.CT5' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.CT5

/-- info: 'STACS2027.Runtimes.BoundedCost.boundedCostTop_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.boundedCostTop_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.boundedCost_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.boundedCost_single

/-- info: 'STACS2027.Runtimes.BoundedCost.paper5' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.paper5

/-- info: 'STACS2027.Runtimes.BoundedCost.bnd5_le_paper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.bnd5_le_paper

/-- info: 'STACS2027.Runtimes.BoundedCost.solver_le_paper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.solver_le_paper

/-- info: 'STACS2027.Runtimes.BoundedCost.boundedCost_ram_fpt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.boundedCost_ram_fpt

/-- info: 'STACS2027.Runtimes.BoundedCost.Tri.off1' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Tri.off1

/-- info: 'STACS2027.Runtimes.BoundedCost.Tri.off2' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Tri.off2

/-- info: 'STACS2027.Runtimes.BoundedCost.Tri.off1_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Tri.off1_lt

/-- info: 'STACS2027.Runtimes.BoundedCost.Tri.off2_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Tri.off2_lt

/-- info: 'STACS2027.Runtimes.BoundedCost.Tri.selected_tri' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Tri.selected_tri

/-- info: 'STACS2027.Runtimes.BoundedCost.Tri.triE' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Tri.triE

/-- info: 'STACS2027.Runtimes.BoundedCost.Tri.colc' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Tri.colc

/-- info: 'STACS2027.Runtimes.BoundedCost.Tri.allc' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Tri.allc

/-- info: 'STACS2027.Runtimes.BoundedCost.Tri.colc_zero' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Tri.colc_zero

/-- info: 'STACS2027.Runtimes.BoundedCost.Tri.colc_succ' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Tri.colc_succ

/-- info: 'STACS2027.Runtimes.BoundedCost.Tri.allc_zero' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Tri.allc_zero

/-- info: 'STACS2027.Runtimes.BoundedCost.Tri.allc_succ' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Tri.allc_succ

/-- info: 'STACS2027.Runtimes.BoundedCost.Tri.overlap_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Tri.overlap_single

/-- info: 'STACS2027.Runtimes.BoundedCost.Tri.sum_overlap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Tri.sum_overlap

/-- info: 'STACS2027.Runtimes.BoundedCost.Tri.cost_tri' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Tri.cost_tri

/-- info: 'STACS2027.Runtimes.BoundedCost.Tri.wM' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Tri.wM

/-- info: 'STACS2027.Runtimes.BoundedCost.Tri.wV' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Tri.wV

/-- info: 'STACS2027.Runtimes.BoundedCost.Tri.wT' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Tri.wT

/-- info: 'STACS2027.Runtimes.BoundedCost.Tri.wD' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Tri.wD

/-- info: 'STACS2027.Runtimes.BoundedCost.Tri.wS' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Tri.wS

/-- info: 'STACS2027.Runtimes.BoundedCost.Tri.wP' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Tri.wP

/-- info: 'STACS2027.Runtimes.BoundedCost.Tri.wJ' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Tri.wJ

/-- info: 'STACS2027.Runtimes.BoundedCost.Tri.wI' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Tri.wI

/-- info: 'STACS2027.Runtimes.BoundedCost.Tri.wN' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Tri.wN

/-- info: 'STACS2027.Runtimes.BoundedCost.Tri.wA' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Tri.wA

/-- info: 'STACS2027.Runtimes.BoundedCost.Tri.wB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Tri.wB

/-- info: 'STACS2027.Runtimes.BoundedCost.Tri.wX' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Tri.wX

/-- info: 'STACS2027.Runtimes.BoundedCost.Tri.wY' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Tri.wY

/-- info: 'STACS2027.Runtimes.BoundedCost.Tri.wQ' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Tri.wQ

/-- info: 'STACS2027.Runtimes.BoundedCost.Tri.wU' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Tri.wU

/-- info: 'STACS2027.Runtimes.BoundedCost.Tri.wO' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Tri.wO

/-- info: 'STACS2027.Runtimes.BoundedCost.Tri.wO'' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Tri.wO'

/-- info: 'STACS2027.Runtimes.BoundedCost.Tri.wW' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Tri.wW

/-- info: 'STACS2027.Runtimes.BoundedCost.Tri.wK' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Tri.wK

/-- info: 'STACS2027.Runtimes.BoundedCost.Tri.edgePre' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Tri.edgePre

/-- info: 'STACS2027.Runtimes.BoundedCost.Tri.edgeAt' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Tri.edgeAt

/-- info: 'STACS2027.Runtimes.BoundedCost.Tri.innerBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Tri.innerBody

/-- info: 'STACS2027.Runtimes.BoundedCost.Tri.outerPre' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Tri.outerPre

/-- info: 'STACS2027.Runtimes.BoundedCost.Tri.outerBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Tri.outerBody

/-- info: 'STACS2027.Runtimes.BoundedCost.Tri.checkInit' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Tri.checkInit

/-- info: 'STACS2027.Runtimes.BoundedCost.Tri.outBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Tri.outBody

/-- info: 'STACS2027.Runtimes.BoundedCost.Tri.ansYes' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Tri.ansYes

/-- info: 'STACS2027.Runtimes.BoundedCost.Tri.ansNo' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Tri.ansNo

/-- info: 'STACS2027.Runtimes.BoundedCost.Tri.answer' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Tri.answer

/-- info: 'STACS2027.Runtimes.BoundedCost.Tri.triCheck' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Tri.triCheck

/-- info: 'STACS2027.Runtimes.BoundedCost.Tri.edgePre_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Tri.edgePre_run

/-- info: 'STACS2027.Runtimes.BoundedCost.Tri.edgeAt_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Tri.edgeAt_run

/-- info: 'STACS2027.Runtimes.BoundedCost.Tri.edgeAt_addrOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Tri.edgeAt_addrOK

/-- info: 'STACS2027.Runtimes.BoundedCost.Tri.TG' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Tri.TG

/-- info: 'STACS2027.Runtimes.BoundedCost.Tri.Dat' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Tri.Dat

/-- info: 'STACS2027.Runtimes.BoundedCost.Tri.InnerI' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Tri.InnerI

/-- info: 'STACS2027.Runtimes.BoundedCost.Tri.OuterI' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Tri.OuterI

/-- info: 'STACS2027.Runtimes.BoundedCost.Tri.edgeAt_tg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Tri.edgeAt_tg

/-- info: 'STACS2027.Runtimes.BoundedCost.Tri.innerBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Tri.innerBody_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.Tri.outerPre_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Tri.outerPre_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.Tri.outerBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Tri.outerBody_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.Tri.checkInit_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Tri.checkInit_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.Tri.answer_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Tri.answer_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.Tri.triCheck_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.Tri.triCheck_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.boundedCostInput_three' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.boundedCostInput_three

/-- info: 'STACS2027.Runtimes.BoundedCost.isCycle_three' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.isCycle_three

/-- info: 'STACS2027.Runtimes.BoundedCost.length_flowInput_three' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.length_flowInput_three

/-- info: 'STACS2027.Runtimes.BoundedCost.dI' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.dI

/-- info: 'STACS2027.Runtimes.BoundedCost.dW' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.dW

/-- info: 'STACS2027.Runtimes.BoundedCost.dropBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.dropBody

/-- info: 'STACS2027.Runtimes.BoundedCost.dropPsi' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.dropPsi

/-- info: 'STACS2027.Runtimes.BoundedCost.dropPsi_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.dropPsi_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.triCheck_boundedCost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.triCheck_boundedCost

/-- info: 'STACS2027.Runtimes.BoundedCost.zipWith_selected_tri' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.zipWith_selected_tri

/-- info: 'STACS2027.Runtimes.BoundedCost.cost_selected_tri' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.cost_selected_tri

/-- info: 'STACS2027.Runtimes.BoundedCost.triDecide' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.triDecide

/-- info: 'STACS2027.Runtimes.BoundedCost.triDecide_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.triDecide_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.boundedCost_triangle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.boundedCost_triangle

/-- info: 'STACS2027.Runtimes.BoundedCost.boundedCost_triangle_almostLinear' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.boundedCost_triangle_almostLinear

/-- info: 'STACS2027.Runtimes.BoundedCost.readK' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.readK

/-- info: 'STACS2027.Runtimes.BoundedCost.boundedCostAll' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.boundedCostAll

/-- info: 'STACS2027.Runtimes.BoundedCost.boundedCostInput_getD_k' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.boundedCostInput_getD_k

/-- info: 'STACS2027.Runtimes.BoundedCost.boundedCostInput_getD_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.boundedCostInput_getD_zero

/-- info: 'STACS2027.Runtimes.BoundedCost.cfgK' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.cfgK

/-- info: 'STACS2027.Runtimes.BoundedCost.exec_readK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.exec_readK

/-- info: 'STACS2027.Runtimes.BoundedCost.execB_readK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.execB_readK

/-- info: 'STACS2027.Runtimes.BoundedCost.cfgK_init' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.cfgK_init

/-- info: 'STACS2027.Runtimes.BoundedCost.boundedCostAll_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.boundedCostAll_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.tri_le_all' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.tri_le_all

/-- info: 'STACS2027.Runtimes.BoundedCost.paper5_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.paper5_ge

/-- info: 'STACS2027.Runtimes.BoundedCost.tri_le_all'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.tri_le_all'

/-- info: 'STACS2027.Runtimes.BoundedCost.boundedCost_ram_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.boundedCost_ram_all

/-- info: 'STACS2027.Runtimes.BoundedCost.boundedCost_ram_all_almostLinear' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.boundedCost_ram_all_almostLinear

/-- info: 'STACS2027.Runtimes.BoundedCost.optCost_budget' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.optCost_budget

/-- info: 'STACS2027.Runtimes.BoundedCost.boundedCost_triangle_opt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.boundedCost_triangle_opt

/-- info: 'STACS2027.Runtimes.BoundedCost.real_bound_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.real_bound_le

/-- info: 'STACS2027.Runtimes.BoundedCost.boundedCost_triangle_opt_almostLinear' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.boundedCost_triangle_opt_almostLinear

/-- info: 'STACS2027.Runtimes.BoundedCost.TruthInit.candidateBase' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.TruthInit.candidateBase

/-- info: 'STACS2027.Runtimes.BoundedCost.TruthInit.variableCount' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.TruthInit.variableCount

/-- info: 'STACS2027.Runtimes.BoundedCost.TruthInit.index' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.TruthInit.index

/-- info: 'STACS2027.Runtimes.BoundedCost.TruthInit.codeIndex' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.TruthInit.codeIndex

/-- info: 'STACS2027.Runtimes.BoundedCost.TruthInit.value' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.TruthInit.value

/-- info: 'STACS2027.Runtimes.BoundedCost.TruthInit.body' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.TruthInit.body

/-- info: 'STACS2027.Runtimes.BoundedCost.TruthInit.program' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.TruthInit.program

/-- info: 'STACS2027.Runtimes.BoundedCost.TruthInit.Inv' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.TruthInit.Inv

/-- info: 'STACS2027.Runtimes.BoundedCost.TruthInit.body_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.TruthInit.body_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.TruthInit.program_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.TruthInit.program_spec

/-- info: 'STACS2027.Runtimes.BoundedCost.zeroSpace' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.zeroSpace

/-- info: 'STACS2027.Runtimes.BoundedCost.zeroCost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.zeroCost

/-- info: 'STACS2027.Runtimes.BoundedCost.zero5_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.BoundedCost.zero5_spec

/-- info: 'STACS2027.Runtimes.C4.pow43_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.pow43_mono

/-- info: 'STACS2027.Runtimes.C4.le_pow43' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.le_pow43

/-- info: 'STACS2027.Runtimes.C4.pow43_le_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.pow43_le_sq

/-- info: 'STACS2027.Runtimes.C4.numV_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.numV_le

/-- info: 'STACS2027.Runtimes.C4.length_idEdges_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.length_idEdges_le

/-- info: 'STACS2027.Runtimes.C4.length_le_sq_of_simple' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.length_le_sq_of_simple

/-- info: 'STACS2027.Runtimes.C4.sum_length_outL_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.sum_length_outL_le

/-- info: 'STACS2027.Runtimes.C4.length_outL_le_degen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.length_outL_le_degen

/-- info: 'STACS2027.Runtimes.C4.numPaths_le_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.numPaths_le_sq

/-- info: 'STACS2027.Runtimes.C4.numPaths_le_pow43' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.numPaths_le_pow43

/-- info: 'STACS2027.Runtimes.C4.numPaths_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.numPaths_le

/-- info: 'STACS2027.Runtimes.C4.numPaths_le'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.numPaths_le'

/-- info: 'STACS2027.Runtimes.C4.mem_bucket' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.mem_bucket

/-- info: 'STACS2027.Runtimes.C4.bucket_eq_nil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.bucket_eq_nil

/-- info: 'STACS2027.Runtimes.C4.length_reports_snoc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.length_reports_snoc

/-- info: 'STACS2027.Runtimes.C4.length_le_card_keys_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.length_le_card_keys_add

/-- info: 'STACS2027.Runtimes.C4.getElem?_snoc_lt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.getElem?_snoc_lt

/-- info: 'STACS2027.Runtimes.C4.getElem?_snoc_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.getElem?_snoc_length

/-- info: 'STACS2027.Runtimes.C4.mem_reports' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.mem_reports

/-- info: 'STACS2027.Runtimes.C4.mem_of_mem_reports' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.mem_of_mem_reports

/-- info: 'STACS2027.Runtimes.C4.nodup_bucket' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.nodup_bucket

/-- info: 'STACS2027.Runtimes.C4.nodup_reports' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.nodup_reports

/-- info: 'STACS2027.Runtimes.C4.reports_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.reports_prefix

/-- info: 'STACS2027.Runtimes.C4.length_reports_le_of_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.length_reports_le_of_prefix

/-- info: 'STACS2027.Runtimes.C4.cycleEdges4' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.cycleEdges4

/-- info: 'STACS2027.Runtimes.C4.mem_edges4' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.mem_edges4

/-- info: 'STACS2027.Runtimes.C4.nonedge4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.nonedge4

/-- info: 'STACS2027.Runtimes.C4.mem4_of_same' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.mem4_of_same

/-- info: 'STACS2027.Runtimes.C4.diagonals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.diagonals

/-- info: 'STACS2027.Runtimes.C4.sameCycle4' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.sameCycle4

/-- info: 'STACS2027.Runtimes.C4.canon4_same' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.canon4_same

/-- info: 'STACS2027.Runtimes.C4.mem_canon4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.mem_canon4

/-- info: 'STACS2027.Runtimes.C4.canon4_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.canon4_nodup

/-- info: 'STACS2027.Runtimes.C4.canon4_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.canon4_perm

/-- info: 'STACS2027.Runtimes.C4.canon4_isCanon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.canon4_isCanon

/-- info: 'STACS2027.Runtimes.C4.canon4_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.canon4_le

/-- info: 'STACS2027.Runtimes.C4.isCanon4_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.isCanon4_iff

/-- info: 'STACS2027.Runtimes.C4.canon4_eq_self' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.canon4_eq_self

/-- info: 'STACS2027.Runtimes.C4.canon4_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.canon4_unique

/-- info: 'STACS2027.Runtimes.C4.IsCycle.of_same' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.IsCycle.of_same

/-- info: 'STACS2027.Runtimes.C4.isCycle_canon4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.isCycle_canon4

/-- info: 'STACS2027.Runtimes.C4.vertices_sorted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.vertices_sorted

/-- info: 'STACS2027.Runtimes.C4.neighbors_sorted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.neighbors_sorted

/-- info: 'STACS2027.Runtimes.C4.walksFrom_zero' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.walksFrom_zero

/-- info: 'STACS2027.Runtimes.C4.walksFrom_succ' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.walksFrom_succ

/-- info: 'STACS2027.Runtimes.C4.head_walksFrom' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.head_walksFrom

/-- info: 'STACS2027.Runtimes.C4.walksFrom_sorted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.walksFrom_sorted

/-- info: 'STACS2027.Runtimes.C4.rawCycles_sorted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.rawCycles_sorted

/-- info: 'STACS2027.Runtimes.C4.cycleRepresentatives_min' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.cycleRepresentatives_min

/-- info: 'STACS2027.Runtimes.C4.eq4_of_isCycle' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.eq4_of_isCycle

/-- info: 'STACS2027.Runtimes.C4.isCanon4_of_mem_cycles' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.isCanon4_of_mem_cycles

/-- info: 'STACS2027.Runtimes.C4.mem_cycles4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.mem_cycles4

/-- info: 'STACS2027.Runtimes.C4.insStamp' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.insStamp

/-- info: 'STACS2027.Runtimes.C4.insCell' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.insCell

/-- info: 'STACS2027.Runtimes.C4.walkBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.walkBody

/-- info: 'STACS2027.Runtimes.C4.insWalk' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.insWalk

/-- info: 'STACS2027.Runtimes.C4.insNode' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.insNode

/-- info: 'STACS2027.Runtimes.C4.insertP' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.insertP

/-- info: 'STACS2027.Runtimes.C4.KW' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.KW

/-- info: 'STACS2027.Runtimes.C4.WInv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.WInv

/-- info: 'STACS2027.Runtimes.C4.mem_insS_of_bucket' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.mem_insS_of_bucket

/-- info: 'STACS2027.Runtimes.C4.length_reports_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.length_reports_le

/-- info: 'STACS2027.Runtimes.C4.walk_round' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.walk_round

/-- info: 'STACS2027.Runtimes.C4.KS' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.KS

/-- info: 'STACS2027.Runtimes.C4.insert_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.insert_spec

/-- info: 'STACS2027.Runtimes.C4.insPre' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.insPre

/-- info: 'STACS2027.Runtimes.C4.t1Pre' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.t1Pre

/-- info: 'STACS2027.Runtimes.C4.t1In' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.t1In

/-- info: 'STACS2027.Runtimes.C4.blk2' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.blk2

/-- info: 'STACS2027.Runtimes.C4.t2Pre' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.t2Pre

/-- info: 'STACS2027.Runtimes.C4.t2In' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.t2In

/-- info: 'STACS2027.Runtimes.C4.t1Pre_zero' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.t1Pre_zero

/-- info: 'STACS2027.Runtimes.C4.t2Pre_zero' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.t2Pre_zero

/-- info: 'STACS2027.Runtimes.C4.t1In_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.t1In_zero

/-- info: 'STACS2027.Runtimes.C4.t2In_start' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.t2In_start

/-- info: 'STACS2027.Runtimes.C4.insPre_zero' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.insPre_zero

/-- info: 'STACS2027.Runtimes.C4.insPre_numV' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.insPre_numV

/-- info: 'STACS2027.Runtimes.C4.t1In_succ' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.t1In_succ

/-- info: 'STACS2027.Runtimes.C4.t1In_full' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.t1In_full

/-- info: 'STACS2027.Runtimes.C4.t2In_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.t2In_succ

/-- info: 'STACS2027.Runtimes.C4.t2In_full' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.t2In_full

/-- info: 'STACS2027.Runtimes.C4.map_wedges1' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.map_wedges1

/-- info: 'STACS2027.Runtimes.C4.map_wedges2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.map_wedges2

/-- info: 'STACS2027.Runtimes.C4.insPre_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.insPre_succ

/-- info: 'STACS2027.Runtimes.C4.flatMap_prefix' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.flatMap_prefix

/-- info: 'STACS2027.Runtimes.C4.insPre_prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.insPre_prefix

/-- info: 'STACS2027.Runtimes.C4.t1Pre_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.t1Pre_prefix

/-- info: 'STACS2027.Runtimes.C4.t2Pre_prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.t2Pre_prefix

/-- info: 'STACS2027.Runtimes.C4.t1In_prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.t1In_prefix

/-- info: 'STACS2027.Runtimes.C4.t2In_prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.t2In_prefix

/-- info: 'STACS2027.Runtimes.C4.wt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.wt

/-- info: 'STACS2027.Runtimes.C4.wt_snoc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.wt_snoc

/-- info: 'STACS2027.Runtimes.C4.wt_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.wt_mono

/-- info: 'STACS2027.Runtimes.C4.insKey' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.insKey

/-- info: 'STACS2027.Runtimes.C4.writeP' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.writeP

/-- info: 'STACS2027.Runtimes.C4.pre1' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.pre1

/-- info: 'STACS2027.Runtimes.C4.body1' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.body1

/-- info: 'STACS2027.Runtimes.C4.midPre1' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.midPre1

/-- info: 'STACS2027.Runtimes.C4.mid1' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.mid1

/-- info: 'STACS2027.Runtimes.C4.pre2' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.pre2

/-- info: 'STACS2027.Runtimes.C4.body2' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.body2

/-- info: 'STACS2027.Runtimes.C4.midPre2' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.midPre2

/-- info: 'STACS2027.Runtimes.C4.mid2' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.mid2

/-- info: 'STACS2027.Runtimes.C4.outerPre' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.outerPre

/-- info: 'STACS2027.Runtimes.C4.outerB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.outerB

/-- info: 'STACS2027.Runtimes.C4.genAlloc' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.genAlloc

/-- info: 'STACS2027.Runtimes.C4.gen' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.gen

/-- info: 'STACS2027.Runtimes.C4.genEnd' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.genEnd

/-- info: 'STACS2027.Runtimes.C4.GGlob' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.GGlob

/-- info: 'STACS2027.Runtimes.C4.GMem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.GMem

/-- info: 'STACS2027.Runtimes.C4.GRep' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.GRep

/-- info: 'STACS2027.Runtimes.C4.WG' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.WG

/-- info: 'STACS2027.Runtimes.C4.GGlob.regIndep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.GGlob.regIndep

/-- info: 'STACS2027.Runtimes.C4.GRep.indep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.GRep.indep

/-- info: 'STACS2027.Runtimes.C4.GMem.write' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.GMem.write

/-- info: 'STACS2027.Runtimes.C4.WI' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.WI

/-- info: 'STACS2027.Runtimes.C4.writeP_wregs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.writeP_wregs

/-- info: 'STACS2027.Runtimes.C4.KG' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.KG

/-- info: 'STACS2027.Runtimes.C4.W' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.W

/-- info: 'STACS2027.Runtimes.C4.W_snoc' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.W_snoc

/-- info: 'STACS2027.Runtimes.C4.W_mono' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.W_mono

/-- info: 'STACS2027.Runtimes.C4.writeP_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.writeP_spec

/-- info: 'STACS2027.Runtimes.C4.gen_fits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.gen_fits

/-- info: 'STACS2027.Runtimes.C4.ps_out_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.ps_out_le

/-- info: 'STACS2027.Runtimes.C4.I1' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.I1

/-- info: 'STACS2027.Runtimes.C4.I1.indep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.I1.indep

/-- info: 'STACS2027.Runtimes.C4.t1_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.t1_prefix

/-- info: 'STACS2027.Runtimes.C4.body1_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.body1_spec

/-- info: 'STACS2027.Runtimes.C4.M1' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.M1

/-- info: 'STACS2027.Runtimes.C4.M1.indep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.M1.indep

/-- info: 'STACS2027.Runtimes.C4.f1' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.f1

/-- info: 'STACS2027.Runtimes.C4.W_t1In_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.W_t1In_step

/-- info: 'STACS2027.Runtimes.C4.mid1_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.mid1_spec

/-- info: 'STACS2027.Runtimes.C4.I2' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.I2

/-- info: 'STACS2027.Runtimes.C4.I2.indep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.I2.indep

/-- info: 'STACS2027.Runtimes.C4.t2_prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.t2_prefix

/-- info: 'STACS2027.Runtimes.C4.body2_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.body2_spec

/-- info: 'STACS2027.Runtimes.C4.M2' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.M2

/-- info: 'STACS2027.Runtimes.C4.M2.indep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.M2.indep

/-- info: 'STACS2027.Runtimes.C4.f2' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.f2

/-- info: 'STACS2027.Runtimes.C4.W_t2In_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.W_t2In_step

/-- info: 'STACS2027.Runtimes.C4.mid2_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.mid2_spec

/-- info: 'STACS2027.Runtimes.C4.fo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.fo

/-- info: 'STACS2027.Runtimes.C4.outerB_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.outerB_spec

/-- info: 'STACS2027.Runtimes.C4.genAlloc_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.genAlloc_spec

/-- info: 'STACS2027.Runtimes.C4.gen_wregs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.gen_wregs

/-- info: 'STACS2027.Runtimes.C4.gen_writes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.gen_writes

/-- info: 'STACS2027.Runtimes.C4.CG' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.CG

/-- info: 'STACS2027.Runtimes.C4.gen_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.gen_spec

/-- info: 'STACS2027.Runtimes.C4.keysX' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.keysX

/-- info: 'STACS2027.Runtimes.C4.srtIdx' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.srtIdx

/-- info: 'STACS2027.Runtimes.C4.keysX_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.keysX_lt

/-- info: 'STACS2027.Runtimes.C4.length_keysX' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.length_keysX

/-- info: 'STACS2027.Runtimes.C4.length_srtIdx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.length_srtIdx

/-- info: 'STACS2027.Runtimes.C4.read_srt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.read_srt

/-- info: 'STACS2027.Runtimes.C4.srtIdx_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.srtIdx_lt

/-- info: 'STACS2027.Runtimes.C4.ScanPre' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.ScanPre

/-- info: 'STACS2027.Runtimes.C4.bHDS' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.bHDS

/-- info: 'STACS2027.Runtimes.C4.bPOOL' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.bPOOL

/-- info: 'STACS2027.Runtimes.C4.bCYC' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.bCYC

/-- info: 'STACS2027.Runtimes.C4.scanEnd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.scanEnd

/-- info: 'STACS2027.Runtimes.C4.scan_layout' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.scan_layout

/-- info: 'STACS2027.Runtimes.C4.Rpt' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.Rpt

/-- info: 'STACS2027.Runtimes.C4.EGlob' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.EGlob

/-- info: 'STACS2027.Runtimes.C4.WE' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.WE

/-- info: 'STACS2027.Runtimes.C4.EGlob.regIndep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.EGlob.regIndep

/-- info: 'STACS2027.Runtimes.C4.EMem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.EMem

/-- info: 'STACS2027.Runtimes.C4.ERep' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.ERep

/-- info: 'STACS2027.Runtimes.C4.ERep.indep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.ERep.indep

/-- info: 'STACS2027.Runtimes.C4.length_flatten_phi' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.length_flatten_phi

/-- info: 'STACS2027.Runtimes.C4.EMem.advance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.EMem.advance

/-- info: 'STACS2027.Runtimes.C4.EMem.stamp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.EMem.stamp

/-- info: 'STACS2027.Runtimes.C4.EMem.node' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.EMem.node

/-- info: 'STACS2027.Runtimes.C4.EMem.emit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.EMem.emit

/-- info: 'STACS2027.Runtimes.C4.leaf' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.leaf

/-- info: 'STACS2027.Runtimes.C4.cA' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.cA

/-- info: 'STACS2027.Runtimes.C4.cB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.cB

/-- info: 'STACS2027.Runtimes.C4.cC' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.cC

/-- info: 'STACS2027.Runtimes.C4.cD' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.cD

/-- info: 'STACS2027.Runtimes.C4.c34' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.c34

/-- info: 'STACS2027.Runtimes.C4.c234' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.c234

/-- info: 'STACS2027.Runtimes.C4.canonP' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.canonP

/-- info: 'STACS2027.Runtimes.C4.canonP_loopFree' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.canonP_loopFree

/-- info: 'STACS2027.Runtimes.C4.canonP_wregs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.canonP_wregs

/-- info: 'STACS2027.Runtimes.C4.canonP_stores' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.canonP_stores

/-- info: 'STACS2027.Runtimes.C4.canonP_writes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.canonP_writes

/-- info: 'STACS2027.Runtimes.C4.outs' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.outs

/-- info: 'STACS2027.Runtimes.C4.leaf_outs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.leaf_outs

/-- info: 'STACS2027.Runtimes.C4.outs_ifLt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.outs_ifLt

/-- info: 'STACS2027.Runtimes.C4.cA_outs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.cA_outs

/-- info: 'STACS2027.Runtimes.C4.cB_outs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.cB_outs

/-- info: 'STACS2027.Runtimes.C4.cC_outs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.cC_outs

/-- info: 'STACS2027.Runtimes.C4.cD_outs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.cD_outs

/-- info: 'STACS2027.Runtimes.C4.c34_outs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.c34_outs

/-- info: 'STACS2027.Runtimes.C4.c234_outs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.c234_outs

/-- info: 'STACS2027.Runtimes.C4.canonP_outs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.canonP_outs

/-- info: 'STACS2027.Runtimes.C4.emit4' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.emit4

/-- info: 'STACS2027.Runtimes.C4.rload' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.rload

/-- info: 'STACS2027.Runtimes.C4.reportB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.reportB

/-- info: 'STACS2027.Runtimes.C4.emit4_run' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.emit4_run

/-- info: 'STACS2027.Runtimes.C4.reportB_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.reportB_run

/-- info: 'STACS2027.Runtimes.C4.srtArgs' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.srtArgs

/-- info: 'STACS2027.Runtimes.C4.srt' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.srt

/-- info: 'STACS2027.Runtimes.C4.scanAlloc' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.scanAlloc

/-- info: 'STACS2027.Runtimes.C4.readT' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.readT

/-- info: 'STACS2027.Runtimes.C4.scanBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.scanBody

/-- info: 'STACS2027.Runtimes.C4.scan' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.scan

/-- info: 'STACS2027.Runtimes.C4.enum' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.enum

/-- info: 'STACS2027.Runtimes.C4.WIS' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.WIS

/-- info: 'STACS2027.Runtimes.C4.insertP_wregs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.insertP_wregs

/-- info: 'STACS2027.Runtimes.C4.KI' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.KI

/-- info: 'STACS2027.Runtimes.C4.xprev' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.xprev

/-- info: 'STACS2027.Runtimes.C4.SInv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.SInv

/-- info: 'STACS2027.Runtimes.C4.ERep.advance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.ERep.advance

/-- info: 'STACS2027.Runtimes.C4.xprev_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.xprev_le

/-- info: 'STACS2027.Runtimes.C4.scanBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.scanBody_spec

/-- info: 'STACS2027.Runtimes.C4.scanAlloc_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.scanAlloc_spec

/-- info: 'STACS2027.Runtimes.C4.scan_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.scan_spec

/-- info: 'STACS2027.Runtimes.C4.sortEnd' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.sortEnd

/-- info: 'STACS2027.Runtimes.C4.enumEnd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.enumEnd

/-- info: 'STACS2027.Runtimes.C4.enumEnd_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.enumEnd_eq

/-- info: 'STACS2027.Runtimes.C4.srt_wregs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.srt_wregs

/-- info: 'STACS2027.Runtimes.C4.srt_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.srt_spec

/-- info: 'STACS2027.Runtimes.C4.enum_wregs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.enum_wregs

/-- info: 'STACS2027.Runtimes.C4.enum_writes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.enum_writes

/-- info: 'STACS2027.Runtimes.C4.scan_wregs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.scan_wregs

/-- info: 'STACS2027.Runtimes.C4.CE' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.CE

/-- info: 'STACS2027.Runtimes.C4.enum_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.enum_spec

/-- info: 'STACS2027.Runtimes.C4.sortX' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.sortX

/-- info: 'STACS2027.Runtimes.C4.sortX_succ' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.sortX_succ

/-- info: 'STACS2027.Runtimes.C4.filter_sortX_aux' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.filter_sortX_aux

/-- info: 'STACS2027.Runtimes.C4.filter_sortX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.filter_sortX

/-- info: 'STACS2027.Runtimes.C4.pairwise_sortX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.pairwise_sortX

/-- info: 'STACS2027.Runtimes.C4.sortX_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.sortX_mono

/-- info: 'STACS2027.Runtimes.C4.reports_filter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.reports_filter

/-- info: 'STACS2027.Runtimes.C4.reports_perm_of_filter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.reports_perm_of_filter

/-- info: 'STACS2027.Runtimes.C4.sortX_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.sortX_perm

/-- info: 'STACS2027.Runtimes.C4.insS' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.insS

/-- info: 'STACS2027.Runtimes.C4.enumOutS' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.enumOutS

/-- info: 'STACS2027.Runtimes.C4.lt_of_mem_ins'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.lt_of_mem_ins'

/-- info: 'STACS2027.Runtimes.C4.insS_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.insS_perm

/-- info: 'STACS2027.Runtimes.C4.length_insS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.length_insS

/-- info: 'STACS2027.Runtimes.C4.lt_of_mem_insS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.lt_of_mem_insS

/-- info: 'STACS2027.Runtimes.C4.reports_insS_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.reports_insS_perm

/-- info: 'STACS2027.Runtimes.C4.enumOutS_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.enumOutS_perm

/-- info: 'STACS2027.Runtimes.C4.length_enumOutS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.length_enumOutS

/-- info: 'STACS2027.Runtimes.C4.length_reports_insS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.length_reports_insS

/-- info: 'STACS2027.Runtimes.C4.length_flatten_enumOutS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.length_flatten_enumOutS

/-- info: 'STACS2027.Runtimes.C4.gCUR' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.gCUR

/-- info: 'STACS2027.Runtimes.C4.gDEL' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.gDEL

/-- info: 'STACS2027.Runtimes.C4.gBH' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.gBH

/-- info: 'STACS2027.Runtimes.C4.gPOS' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.gPOS

/-- info: 'STACS2027.Runtimes.C4.gODEG' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.gODEG

/-- info: 'STACS2027.Runtimes.C4.gOADJ' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.gOADJ

/-- info: 'STACS2027.Runtimes.C4.gP' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.gP

/-- info: 'STACS2027.Runtimes.C4.gTX' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.gTX

/-- info: 'STACS2027.Runtimes.C4.gTY' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.gTY

/-- info: 'STACS2027.Runtimes.C4.gPOOL' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.gPOOL

/-- info: 'STACS2027.Runtimes.C4.gCYC' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.gCYC

/-- info: 'STACS2027.Runtimes.C4.gT' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.gT

/-- info: 'STACS2027.Runtimes.C4.gNP' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.gNP

/-- info: 'STACS2027.Runtimes.C4.gTZ' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.gTZ

/-- info: 'STACS2027.Runtimes.C4.gSRT' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.gSRT

/-- info: 'STACS2027.Runtimes.C4.gSTP' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.gSTP

/-- info: 'STACS2027.Runtimes.C4.gHDS' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.gHDS

/-- info: 'STACS2027.Runtimes.C4.C4Base' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.C4Base

/-- info: 'STACS2027.Runtimes.C4.PeelPost' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.PeelPost

/-- info: 'STACS2027.Runtimes.C4.OrientPost' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.OrientPost

/-- info: 'STACS2027.Runtimes.C4.SizePost' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.SizePost

/-- info: 'STACS2027.Runtimes.C4.EnumPost' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.EnumPost

/-- info: 'STACS2027.Runtimes.C4.emit' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.emit

/-- info: 'STACS2027.Runtimes.C4.emit_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.emit_spec

/-- info: 'STACS2027.Runtimes.C4.c4Enum' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.c4Enum

/-- info: 'STACS2027.Runtimes.C4.c4Sub' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.c4Sub

/-- info: 'STACS2027.Runtimes.C4.fourCycles' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.fourCycles

/-- info: 'STACS2027.Runtimes.C4.c4Enum_wregs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.c4Enum_wregs

/-- info: 'STACS2027.Runtimes.C4.r1_wregs'' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.r1_wregs'

/-- info: 'STACS2027.Runtimes.C4.c4Sub_wregs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.c4Sub_wregs

/-- info: 'STACS2027.Runtimes.C4.c4Enum_writes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.c4Enum_writes

/-- info: 'STACS2027.Runtimes.C4.c4Size' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.c4Size

/-- info: 'STACS2027.Runtimes.C4.C4E' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.C4E

/-- info: 'STACS2027.Runtimes.C4.c4Enum_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.c4Enum_spec

/-- info: 'STACS2027.Runtimes.C4.CSub' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.CSub

/-- info: 'STACS2027.Runtimes.C4.c4Sub_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.c4Sub_spec

/-- info: 'STACS2027.Runtimes.C4.EnumPost.transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.EnumPost.transfer

/-- info: 'STACS2027.Runtimes.C4.emit_wregs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.emit_wregs

/-- info: 'STACS2027.Runtimes.C4.CF' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.CF

/-- info: 'STACS2027.Runtimes.C4.c4Space' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.c4Space

/-- info: 'STACS2027.Runtimes.C4.CS4' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.CS4

/-- info: 'STACS2027.Runtimes.C4.c4Space_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.c4Space_le

/-- info: 'STACS2027.Runtimes.C4.fourCycles_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.fourCycles_spec

/-- info: 'STACS2027.Runtimes.C4.fourCycles_ram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.fourCycles_ram

/-- info: 'STACS2027.Runtimes.C4.fourCycles_ram_paper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.fourCycles_ram_paper

/-- info: 'STACS2027.Runtimes.C4.fourCycles_ram_simple' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.fourCycles_ram_simple

/-- info: 'STACS2027.Runtimes.C4.orientAlloc' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.orientAlloc

/-- info: 'STACS2027.Runtimes.C4.orientInner' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.orientInner

/-- info: 'STACS2027.Runtimes.C4.orientPre' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.orientPre

/-- info: 'STACS2027.Runtimes.C4.orientBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.orientBody

/-- info: 'STACS2027.Runtimes.C4.orient' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.orient

/-- info: 'STACS2027.Runtimes.C4.OGlob' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.OGlob

/-- info: 'STACS2027.Runtimes.C4.orientEnd' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.orientEnd

/-- info: 'STACS2027.Runtimes.C4.OMem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.OMem

/-- info: 'STACS2027.Runtimes.C4.ORep' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.ORep

/-- info: 'STACS2027.Runtimes.C4.ORep.indep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.ORep.indep

/-- info: 'STACS2027.Runtimes.C4.outPre' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.outPre

/-- info: 'STACS2027.Runtimes.C4.outPre_full' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.outPre_full

/-- info: 'STACS2027.Runtimes.C4.outPre_succ' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.outPre_succ

/-- info: 'STACS2027.Runtimes.C4.length_outPre_le' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.length_outPre_le

/-- info: 'STACS2027.Runtimes.C4.IInv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.IInv

/-- info: 'STACS2027.Runtimes.C4.PeelPost.posR' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.PeelPost.posR

/-- info: 'STACS2027.Runtimes.C4.OMem.app' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.OMem.app

/-- info: 'STACS2027.Runtimes.C4.OGlob.regIndep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.OGlob.regIndep

/-- info: 'STACS2027.Runtimes.C4.orientInner_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.orientInner_run

/-- info: 'STACS2027.Runtimes.C4.IInv.indep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.IInv.indep

/-- info: 'STACS2027.Runtimes.C4.orientBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.orientBody_spec

/-- info: 'STACS2027.Runtimes.C4.orientAlloc_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.orientAlloc_spec

/-- info: 'STACS2027.Runtimes.C4.CO' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.CO

/-- info: 'STACS2027.Runtimes.C4.orient_wregs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.orient_wregs

/-- info: 'STACS2027.Runtimes.C4.orient_writes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.orient_writes

/-- info: 'STACS2027.Runtimes.C4.orient_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.orient_spec

/-- info: 'STACS2027.Runtimes.C4.idOf_labelOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.idOf_labelOf

/-- info: 'STACS2027.Runtimes.C4.edge_mem_of_nb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.edge_mem_of_nb

/-- info: 'STACS2027.Runtimes.C4.edge_mem_proper' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.edge_mem_proper

/-- info: 'STACS2027.Runtimes.C4.mem_labels_of_edge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.mem_labels_of_edge

/-- info: 'STACS2027.Runtimes.C4.nb_of_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.nb_of_edge

/-- info: 'STACS2027.Runtimes.C4.sameCycle_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.sameCycle_map

/-- info: 'STACS2027.Runtimes.C4.nodup_getElem?_inj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.nodup_getElem?_inj

/-- info: 'STACS2027.Runtimes.C4.report_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.report_shape

/-- info: 'STACS2027.Runtimes.C4.report_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.report_nodup

/-- info: 'STACS2027.Runtimes.C4.report_isCycle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.report_isCycle

/-- info: 'STACS2027.Runtimes.C4.phi_mem_cycles' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.phi_mem_cycles

/-- info: 'STACS2027.Runtimes.C4.report_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.report_inj

/-- info: 'STACS2027.Runtimes.C4.map_idOf_report' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.map_idOf_report

/-- info: 'STACS2027.Runtimes.C4.phi_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.phi_inj

/-- info: 'STACS2027.Runtimes.C4.eq4_of_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.eq4_of_length

/-- info: 'STACS2027.Runtimes.C4.sameCycle_diag' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.sameCycle_diag

/-- info: 'STACS2027.Runtimes.C4.sameCycle_rotate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.sameCycle_rotate

/-- info: 'STACS2027.Runtimes.C4.exists_report_diag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.exists_report_diag

/-- info: 'STACS2027.Runtimes.C4.key_cases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.key_cases

/-- info: 'STACS2027.Runtimes.C4.exists_report' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.exists_report

/-- info: 'STACS2027.Runtimes.C4.nodup_enumOutP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.nodup_enumOutP

/-- info: 'STACS2027.Runtimes.C4.enumOutP_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.enumOutP_perm

/-- info: 'STACS2027.Runtimes.C4.length_reports_ins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.length_reports_ins

/-- info: 'STACS2027.Runtimes.C4.enumOut_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.enumOut_perm

/-- info: 'STACS2027.Runtimes.C4.length_enumOut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.length_enumOut

/-- info: 'STACS2027.Runtimes.C4.length_flatten_enumOut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.length_flatten_enumOut

/-- info: 'STACS2027.Runtimes.C4.mem_outL' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.mem_outL

/-- info: 'STACS2027.Runtimes.C4.nodup_outL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.nodup_outL

/-- info: 'STACS2027.Runtimes.C4.lt_of_mem_outL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.lt_of_mem_outL

/-- info: 'STACS2027.Runtimes.C4.length_outL_le' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.length_outL_le

/-- info: 'STACS2027.Runtimes.C4.getD_eq_getElem'' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.getD_eq_getElem'

/-- info: 'STACS2027.Runtimes.C4.mem_pairsOf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.mem_pairsOf

/-- info: 'STACS2027.Runtimes.C4.getD_inj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.getD_inj

/-- info: 'STACS2027.Runtimes.C4.pairsOf_ne' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.pairsOf_ne

/-- info: 'STACS2027.Runtimes.C4.mem_of_mem_pairsOf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.mem_of_mem_pairsOf

/-- info: 'STACS2027.Runtimes.C4.pairsOf_asymm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.pairsOf_asymm

/-- info: 'STACS2027.Runtimes.C4.pairsOf_total' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.pairsOf_total

/-- info: 'STACS2027.Runtimes.C4.nodup_pairsOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.nodup_pairsOf

/-- info: 'STACS2027.Runtimes.C4.key_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.key_eq

/-- info: 'STACS2027.Runtimes.C4.key_comm' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.key_comm

/-- info: 'STACS2027.Runtimes.C4.key_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.key_lt

/-- info: 'STACS2027.Runtimes.C4.key_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.key_eq_iff

/-- info: 'STACS2027.Runtimes.C4.mem_wedges1' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.mem_wedges1

/-- info: 'STACS2027.Runtimes.C4.mem_wedges2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.mem_wedges2

/-- info: 'STACS2027.Runtimes.C4.mem_ins_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.mem_ins_iff

/-- info: 'STACS2027.Runtimes.C4.mem_ins_imp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.mem_ins_imp

/-- info: 'STACS2027.Runtimes.C4.lt_of_mem_ins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.lt_of_mem_ins

/-- info: 'STACS2027.Runtimes.C4.mem_ins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.mem_ins

/-- info: 'STACS2027.Runtimes.C4.Gen' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.Gen

/-- info: 'STACS2027.Runtimes.C4.gen_of_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.gen_of_mem

/-- info: 'STACS2027.Runtimes.C4.gen_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.gen_unique

/-- info: 'STACS2027.Runtimes.C4.nodup_wedges1_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.nodup_wedges1_map

/-- info: 'STACS2027.Runtimes.C4.nodup_wedges2_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.nodup_wedges2_map

/-- info: 'STACS2027.Runtimes.C4.nodup_wedges_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.nodup_wedges_map

/-- info: 'STACS2027.Runtimes.C4.nodup_ins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.nodup_ins

/-- info: 'STACS2027.Runtimes.C4.sum_map_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.sum_map_range

/-- info: 'STACS2027.Runtimes.C4.sum_map_eq_getD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.sum_map_eq_getD

/-- info: 'STACS2027.Runtimes.C4.length_pairsOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.length_pairsOf

/-- info: 'STACS2027.Runtimes.C4.length_wedges1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.length_wedges1

/-- info: 'STACS2027.Runtimes.C4.length_wedges2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.length_wedges2

/-- info: 'STACS2027.Runtimes.C4.numPaths_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.numPaths_eq_sum

/-- info: 'STACS2027.Runtimes.C4.numPaths_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.numPaths_eq

/-- info: 'STACS2027.Runtimes.C4.numPaths_le_degen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.numPaths_le_degen

/-- info: 'STACS2027.Runtimes.C4.NbOk' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.NbOk

/-- info: 'STACS2027.Runtimes.C4.NbOk.length_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.NbOk.length_lt

/-- info: 'STACS2027.Runtimes.C4.push_del' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.push_del

/-- info: 'STACS2027.Runtimes.C4.push_cur' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.push_cur

/-- info: 'STACS2027.Runtimes.C4.push_p' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.push_p

/-- info: 'STACS2027.Runtimes.C4.push_ord' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.push_ord

/-- info: 'STACS2027.Runtimes.C4.push_stk' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.push_stk

/-- info: 'STACS2027.Runtimes.C4.relax_del' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.relax_del

/-- info: 'STACS2027.Runtimes.C4.relax_p' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.relax_p

/-- info: 'STACS2027.Runtimes.C4.relax_ord' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.relax_ord

/-- info: 'STACS2027.Runtimes.C4.relax_cur' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.relax_cur

/-- info: 'STACS2027.Runtimes.C4.relax_stk' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.relax_stk

/-- info: 'STACS2027.Runtimes.C4.foldl_relax_del' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.foldl_relax_del

/-- info: 'STACS2027.Runtimes.C4.foldl_relax_p' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.foldl_relax_p

/-- info: 'STACS2027.Runtimes.C4.foldl_relax_ord' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.foldl_relax_ord

/-- info: 'STACS2027.Runtimes.C4.foldl_relax_cur' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.foldl_relax_cur

/-- info: 'STACS2027.Runtimes.C4.foldl_relax_stk_sub' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.foldl_relax_stk_sub

/-- info: 'STACS2027.Runtimes.C4.foldl_relax_stk_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.foldl_relax_stk_mem

/-- info: 'STACS2027.Runtimes.C4.foldl_relax_stk_cases' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.foldl_relax_stk_cases

/-- info: 'STACS2027.Runtimes.C4.stkSize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.stkSize

/-- info: 'STACS2027.Runtimes.C4.stkSize_push_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.stkSize_push_le

/-- info: 'STACS2027.Runtimes.C4.stkSize_relax_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.stkSize_relax_le

/-- info: 'STACS2027.Runtimes.C4.stkSize_foldl_relax_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.stkSize_foldl_relax_le

/-- info: 'STACS2027.Runtimes.C4.stkSize_pop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.stkSize_pop

/-- info: 'STACS2027.Runtimes.C4.remSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.remSum

/-- info: 'STACS2027.Runtimes.C4.pot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.pot

/-- info: 'STACS2027.Runtimes.C4.acost' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.acost

/-- info: 'STACS2027.Runtimes.C4.remove_del' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.remove_del

/-- info: 'STACS2027.Runtimes.C4.remove_ord' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.remove_ord

/-- info: 'STACS2027.Runtimes.C4.remove_p' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.remove_p

/-- info: 'STACS2027.Runtimes.C4.remove_cur' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.remove_cur

/-- info: 'STACS2027.Runtimes.C4.remove_stk_sub' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.remove_stk_sub

/-- info: 'STACS2027.Runtimes.C4.remove_stk_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.remove_stk_mem

/-- info: 'STACS2027.Runtimes.C4.remove_stk_cases' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.remove_stk_cases

/-- info: 'STACS2027.Runtimes.C4.stkSize_remove_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.stkSize_remove_le

/-- info: 'STACS2027.Runtimes.C4.deg' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.deg

/-- info: 'STACS2027.Runtimes.C4.length_filter_update' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.length_filter_update

/-- info: 'STACS2027.Runtimes.C4.PInv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.PInv

/-- info: 'STACS2027.Runtimes.C4.PInv.length_ord_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.PInv.length_ord_le

/-- info: 'STACS2027.Runtimes.C4.PInv.exists_rem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.PInv.exists_rem

/-- info: 'STACS2027.Runtimes.C4.PInv.del_eq_false_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.PInv.del_eq_false_iff

/-- info: 'STACS2027.Runtimes.C4.deg_le' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.deg_le

/-- info: 'STACS2027.Runtimes.C4.PInv.cur_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.PInv.cur_lt

/-- info: 'STACS2027.Runtimes.C4.PInv.p_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.PInv.p_lt

/-- info: 'STACS2027.Runtimes.C4.PInv.filter_not_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.PInv.filter_not_mem

/-- info: 'STACS2027.Runtimes.C4.pinitPre_fields' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.pinitPre_fields

/-- info: 'STACS2027.Runtimes.C4.stkSize_pinitPre_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.stkSize_pinitPre_le

/-- info: 'STACS2027.Runtimes.C4.pinv_pinit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.pinv_pinit

/-- info: 'STACS2027.Runtimes.C4.pot_pinit_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.pot_pinit_le

/-- info: 'STACS2027.Runtimes.C4.pinv_advance' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.pinv_advance

/-- info: 'STACS2027.Runtimes.C4.pinv_stale' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.pinv_stale

/-- info: 'STACS2027.Runtimes.C4.pinv_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.pinv_valid

/-- info: 'STACS2027.Runtimes.C4.pinv_pstep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.pinv_pstep

/-- info: 'STACS2027.Runtimes.C4.pinv_iterate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.pinv_iterate

/-- info: 'STACS2027.Runtimes.C4.pot_pstep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.pot_pstep

/-- info: 'STACS2027.Runtimes.C4.pstep_iterate_of_not_lt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.pstep_iterate_of_not_lt

/-- info: 'STACS2027.Runtimes.C4.length_ord_pstep_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.length_ord_pstep_ge

/-- info: 'STACS2027.Runtimes.C4.iterate_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.iterate_complete

/-- info: 'STACS2027.Runtimes.C4.iterate_eq_of_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.iterate_eq_of_complete

/-- info: 'STACS2027.Runtimes.C4.nodup_nb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.nodup_nb

/-- info: 'STACS2027.Runtimes.C4.nbOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.nbOk

/-- info: 'STACS2027.Runtimes.C4.sum_length_nb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.sum_length_nb

/-- info: 'STACS2027.Runtimes.C4.pot_pinit_graph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.pot_pinit_graph

/-- info: 'STACS2027.Runtimes.C4.pinv_peelState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.pinv_peelState

/-- info: 'STACS2027.Runtimes.C4.length_peelOrd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.length_peelOrd

/-- info: 'STACS2027.Runtimes.C4.iterate_eq_peelState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.iterate_eq_peelState

/-- info: 'STACS2027.Runtimes.C4.peelOrd_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.peelOrd_nodup

/-- info: 'STACS2027.Runtimes.C4.mem_peelOrd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.mem_peelOrd

/-- info: 'STACS2027.Runtimes.C4.peelOrd_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.peelOrd_perm

/-- info: 'STACS2027.Runtimes.C4.peelPos_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.peelPos_lt

/-- info: 'STACS2027.Runtimes.C4.getD_peelPos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.getD_peelPos

/-- info: 'STACS2027.Runtimes.C4.peelPos_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.peelPos_inj

/-- info: 'STACS2027.Runtimes.C4.peelPos_injOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.peelPos_injOn

/-- info: 'STACS2027.Runtimes.C4.mem_take_peelOrd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.mem_take_peelOrd

/-- info: 'STACS2027.Runtimes.C4.peel_minDeg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.peel_minDeg

/-- info: 'STACS2027.Runtimes.C4.peelAlloc' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.peelAlloc

/-- info: 'STACS2027.Runtimes.C4.pushB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.pushB

/-- info: 'STACS2027.Runtimes.C4.initPre' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.initPre

/-- info: 'STACS2027.Runtimes.C4.initBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.initBody

/-- info: 'STACS2027.Runtimes.C4.stepInit' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.stepInit

/-- info: 'STACS2027.Runtimes.C4.relaxDo' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.relaxDo

/-- info: 'STACS2027.Runtimes.C4.relaxBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.relaxBody

/-- info: 'STACS2027.Runtimes.C4.removeHead' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.removeHead

/-- info: 'STACS2027.Runtimes.C4.removeV' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.removeV

/-- info: 'STACS2027.Runtimes.C4.popRead' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.popRead

/-- info: 'STACS2027.Runtimes.C4.popStep' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.popStep

/-- info: 'STACS2027.Runtimes.C4.peelBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.peelBody

/-- info: 'STACS2027.Runtimes.C4.peelCond' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.peelCond

/-- info: 'STACS2027.Runtimes.C4.stepMain' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.stepMain

/-- info: 'STACS2027.Runtimes.C4.peel' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.peel

/-- info: 'STACS2027.Runtimes.C4.bDEL' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.bDEL

/-- info: 'STACS2027.Runtimes.C4.bBH' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.bBH

/-- info: 'STACS2027.Runtimes.C4.bPOS' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.bPOS

/-- info: 'STACS2027.Runtimes.C4.bNODE' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.bNODE

/-- info: 'STACS2027.Runtimes.C4.peelEnd' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.peelEnd

/-- info: 'STACS2027.Runtimes.C4.peel_layout' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.peel_layout

/-- info: 'STACS2027.Runtimes.C4.peel_fits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.peel_fits

/-- info: 'STACS2027.Runtimes.C4.PGlob' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.PGlob

/-- info: 'STACS2027.Runtimes.C4.WP' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.WP

/-- info: 'STACS2027.Runtimes.C4.PGlob.regIndep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.PGlob.regIndep

/-- info: 'STACS2027.Runtimes.C4.PMem' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.PMem

/-- info: 'STACS2027.Runtimes.C4.PRep' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.PRep

/-- info: 'STACS2027.Runtimes.C4.PRep.indep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.PRep.indep

/-- info: 'STACS2027.Runtimes.C4.PMem.push' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.PMem.push

/-- info: 'STACS2027.Runtimes.C4.PMem.extCur' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.PMem.extCur

/-- info: 'STACS2027.Runtimes.C4.PMem.setCur' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.PMem.setCur

/-- info: 'STACS2027.Runtimes.C4.PMem.pop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.PMem.pop

/-- info: 'STACS2027.Runtimes.C4.PMem.removeHead' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.PMem.removeHead

/-- info: 'STACS2027.Runtimes.C4.PMem.ofEq' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.PMem.ofEq

/-- info: 'STACS2027.Runtimes.C4.pushB_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.pushB_run

/-- info: 'STACS2027.Runtimes.C4.initBody_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.initBody_run

/-- info: 'STACS2027.Runtimes.C4.relaxBody_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.relaxBody_run

/-- info: 'STACS2027.Runtimes.C4.popRead_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.popRead_run

/-- info: 'STACS2027.Runtimes.C4.removeHead_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.removeHead_run

/-- info: 'STACS2027.Runtimes.C4.PMem.congrS' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.PMem.congrS

/-- info: 'STACS2027.Runtimes.C4.PRep.congrS' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.PRep.congrS

/-- info: 'STACS2027.Runtimes.C4.remSum_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.remSum_congr

/-- info: 'STACS2027.Runtimes.C4.remSum_of_del' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.remSum_of_del

/-- info: 'STACS2027.Runtimes.C4.remSum_pinit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.remSum_pinit

/-- info: 'STACS2027.Runtimes.C4.peelAlloc_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.peelAlloc_spec

/-- info: 'STACS2027.Runtimes.C4.PIInv' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.PIInv

/-- info: 'STACS2027.Runtimes.C4.stepInit_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.stepInit_spec

/-- info: 'STACS2027.Runtimes.C4.getElem_not_mem_take' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.getElem_not_mem_take

/-- info: 'STACS2027.Runtimes.C4.removeV_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.removeV_spec

/-- info: 'STACS2027.Runtimes.C4.MRep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.MRep

/-- info: 'STACS2027.Runtimes.C4.MRep.indep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.MRep.indep

/-- info: 'STACS2027.Runtimes.C4.KP' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.KP

/-- info: 'STACS2027.Runtimes.C4.PopRep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.PopRep

/-- info: 'STACS2027.Runtimes.C4.PopRep.indep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.PopRep.indep

/-- info: 'STACS2027.Runtimes.C4.body_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.body_spec

/-- info: 'STACS2027.Runtimes.C4.peelIt' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.peelIt

/-- info: 'STACS2027.Runtimes.C4.MInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.MInv

/-- info: 'STACS2027.Runtimes.C4.PhiP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.PhiP

/-- info: 'STACS2027.Runtimes.C4.cond_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.cond_spec

/-- info: 'STACS2027.Runtimes.C4.round_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.round_spec

/-- info: 'STACS2027.Runtimes.C4.stepMain_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.stepMain_spec

/-- info: 'STACS2027.Runtimes.C4.CP' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.CP

/-- info: 'STACS2027.Runtimes.C4.peel_wregs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.peel_wregs

/-- info: 'STACS2027.Runtimes.C4.peel_writes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.peel_writes

/-- info: 'STACS2027.Runtimes.C4.peel_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.peel_spec

/-- info: 'STACS2027.Runtimes.C4.xI' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.xI

/-- info: 'STACS2027.Runtimes.C4.xJ' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.xJ

/-- info: 'STACS2027.Runtimes.C4.xA' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.xA

/-- info: 'STACS2027.Runtimes.C4.xB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.xB

/-- info: 'STACS2027.Runtimes.C4.xV' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.xV

/-- info: 'STACS2027.Runtimes.C4.xW' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.xW

/-- info: 'STACS2027.Runtimes.C4.xX' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.xX

/-- info: 'STACS2027.Runtimes.C4.xY' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.xY

/-- info: 'STACS2027.Runtimes.C4.xZ' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.xZ

/-- info: 'STACS2027.Runtimes.C4.xH' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.xH

/-- info: 'STACS2027.Runtimes.C4.xQ' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.xQ

/-- info: 'STACS2027.Runtimes.C4.xD' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.xD

/-- info: 'STACS2027.Runtimes.C4.xS' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.xS

/-- info: 'STACS2027.Runtimes.C4.xP' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.xP

/-- info: 'STACS2027.Runtimes.C4.xK' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.xK

/-- info: 'STACS2027.Runtimes.C4.xOv' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.xOv

/-- info: 'STACS2027.Runtimes.C4.xDv' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.xDv

/-- info: 'STACS2027.Runtimes.C4.xOj' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.xOj

/-- info: 'STACS2027.Runtimes.C4.xDj' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.xDj

/-- info: 'STACS2027.Runtimes.C4.xC' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.xC

/-- info: 'STACS2027.Runtimes.C4.xA1' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.xA1

/-- info: 'STACS2027.Runtimes.C4.xLa' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.xLa

/-- info: 'STACS2027.Runtimes.C4.xLb' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.xLb

/-- info: 'STACS2027.Runtimes.C4.xLc' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.xLc

/-- info: 'STACS2027.Runtimes.C4.xLd' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.xLd

/-- info: 'STACS2027.Runtimes.C4.xO0' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.xO0

/-- info: 'STACS2027.Runtimes.C4.xO1' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.xO1

/-- info: 'STACS2027.Runtimes.C4.xO2' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.xO2

/-- info: 'STACS2027.Runtimes.C4.xO3' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.xO3

/-- info: 'STACS2027.Runtimes.C4.xT4' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.xT4

/-- info: 'STACS2027.Runtimes.C4.LL' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.LL

/-- info: 'STACS2027.Runtimes.C4.LL_nil' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.LL_nil

/-- info: 'STACS2027.Runtimes.C4.LL_cons' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.LL_cons

/-- info: 'STACS2027.Runtimes.C4.LL.congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.LL.congr

/-- info: 'STACS2027.Runtimes.C4.LL.mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.LL.mono

/-- info: 'STACS2027.Runtimes.C4.LL.upd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.LL.upd

/-- info: 'STACS2027.Runtimes.C4.LL.ne_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.LL.ne_zero

/-- info: 'STACS2027.Runtimes.C4.LL.push' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.LL.push

/-- info: 'STACS2027.Runtimes.C4.csrAdj_prefix' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.csrAdj_prefix

/-- info: 'STACS2027.Runtimes.C4.arr_seg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.arr_seg

/-- info: 'STACS2027.Runtimes.C4.C4Base.free_pos' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.C4Base.free_pos

/-- info: 'STACS2027.Runtimes.C4.C4Base.bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.C4Base.bounds

/-- info: 'STACS2027.Runtimes.C4.C4Base.offR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.C4Base.offR

/-- info: 'STACS2027.Runtimes.C4.C4Base.adjR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.C4Base.adjR

/-- info: 'STACS2027.Runtimes.C4.C4Base.labR' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.C4Base.labR

/-- info: 'STACS2027.Runtimes.C4.C4Base.transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.C4Base.transfer

/-- info: 'STACS2027.Runtimes.C4.PeelPost.transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.PeelPost.transfer

/-- info: 'STACS2027.Runtimes.C4.OrientPost.transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.OrientPost.transfer

/-- info: 'STACS2027.Runtimes.C4.le_of_steps' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.le_of_steps

/-- info: 'STACS2027.Runtimes.C4.sum_affine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.sum_affine

/-- info: 'STACS2027.Runtimes.C4.sum_tele' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.sum_tele

/-- info: 'STACS2027.Runtimes.C4.HTB.forUpTele' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.HTB.forUpTele

/-- info: 'STACS2027.Runtimes.C4.HTB.forRangeTele' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.HTB.forRangeTele

/-- info: 'STACS2027.Runtimes.C4.sizeInner' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.sizeInner

/-- info: 'STACS2027.Runtimes.C4.sizeOuter' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.sizeOuter

/-- info: 'STACS2027.Runtimes.C4.sizeP' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.sizeP

/-- info: 'STACS2027.Runtimes.C4.OrientPost.odegR' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.OrientPost.odegR

/-- info: 'STACS2027.Runtimes.C4.OrientPost.oadjR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.OrientPost.oadjR

/-- info: 'STACS2027.Runtimes.C4.term' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.term

/-- info: 'STACS2027.Runtimes.C4.rowSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.rowSum

/-- info: 'STACS2027.Runtimes.C4.numPaths_eq_rowSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.numPaths_eq_rowSum

/-- info: 'STACS2027.Runtimes.C4.SGlob' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.SGlob

/-- info: 'STACS2027.Runtimes.C4.SGlob.indep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.SGlob.indep

/-- info: 'STACS2027.Runtimes.C4.SOInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.SOInv

/-- info: 'STACS2027.Runtimes.C4.SIInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.SIInv

/-- info: 'STACS2027.Runtimes.C4.sizeInner_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.sizeInner_spec

/-- info: 'STACS2027.Runtimes.C4.sizeOuter_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.sizeOuter_spec

/-- info: 'STACS2027.Runtimes.C4.size_wregs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.size_wregs

/-- info: 'STACS2027.Runtimes.C4.size_stores' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.size_stores

/-- info: 'STACS2027.Runtimes.C4.size_writes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.size_writes

/-- info: 'STACS2027.Runtimes.C4.CS' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.CS

/-- info: 'STACS2027.Runtimes.C4.size_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.size_spec

/-- info: 'STACS2027.Runtimes.C4.nb' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.nb

/-- info: 'STACS2027.Runtimes.C4.PState' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.PState

/-- info: 'STACS2027.Runtimes.C4.push' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.push

/-- info: 'STACS2027.Runtimes.C4.relax' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.relax

/-- info: 'STACS2027.Runtimes.C4.remove' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.remove

/-- info: 'STACS2027.Runtimes.C4.pstep' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.pstep

/-- info: 'STACS2027.Runtimes.C4.pinit' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.pinit

/-- info: 'STACS2027.Runtimes.C4.peelFuel' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.peelFuel

/-- info: 'STACS2027.Runtimes.C4.peelState' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.peelState

/-- info: 'STACS2027.Runtimes.C4.peelOrd' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.peelOrd

/-- info: 'STACS2027.Runtimes.C4.peelPos' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.peelPos

/-- info: 'STACS2027.Runtimes.C4.outL' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.outL

/-- info: 'STACS2027.Runtimes.C4.pairsOf' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.pairsOf

/-- info: 'STACS2027.Runtimes.C4.wedges1' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.wedges1

/-- info: 'STACS2027.Runtimes.C4.wedges2' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.wedges2

/-- info: 'STACS2027.Runtimes.C4.wedges' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.wedges

/-- info: 'STACS2027.Runtimes.C4.key' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.key

/-- info: 'STACS2027.Runtimes.C4.Ins' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.Ins

/-- info: 'STACS2027.Runtimes.C4.entry' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.entry

/-- info: 'STACS2027.Runtimes.C4.ins' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.ins

/-- info: 'STACS2027.Runtimes.C4.numPaths' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.numPaths

/-- info: 'STACS2027.Runtimes.C4.Adm' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.Adm

/-- info: 'STACS2027.Runtimes.C4.bucket' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.bucket

/-- info: 'STACS2027.Runtimes.C4.reports' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.reports

/-- info: 'STACS2027.Runtimes.C4.IsCanon4' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.IsCanon4

/-- info: 'STACS2027.Runtimes.C4.canon4' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.canon4

/-- info: 'STACS2027.Runtimes.C4.phi' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.phi

/-- info: 'STACS2027.Runtimes.C4.enumOutP' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.enumOutP

/-- info: 'STACS2027.Runtimes.C4.enumOut' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.enumOut

/-- info: 'STACS2027.Runtimes.C4.degen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.degen

/-- info: 'STACS2027.Runtimes.C4.exists_pow43' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.exists_pow43

/-- info: 'STACS2027.Runtimes.C4.pow43' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.pow43

/-- info: 'STACS2027.Runtimes.C4.pstep_of_not_lt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.pstep_of_not_lt

/-- info: 'STACS2027.Runtimes.C4.pstep_advance' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.pstep_advance

/-- info: 'STACS2027.Runtimes.C4.pstep_valid' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.pstep_valid

/-- info: 'STACS2027.Runtimes.C4.pstep_stale' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.pstep_stale

/-- info: 'STACS2027.Runtimes.C4.pinitPre' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.pinitPre

/-- info: 'STACS2027.Runtimes.C4.pinitPre_zero' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.pinitPre_zero

/-- info: 'STACS2027.Runtimes.C4.pinitPre_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.pinitPre_succ

/-- info: 'STACS2027.Runtimes.C4.pinit_eq' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.pinit_eq

/-- info: 'STACS2027.Runtimes.C4.remove_eq' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.remove_eq

/-- info: 'STACS2027.Runtimes.C4.ins_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.ins_eq

/-- info: 'STACS2027.Runtimes.C4.bucket_nil' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.bucket_nil

/-- info: 'STACS2027.Runtimes.C4.bucket_snoc' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.bucket_snoc

/-- info: 'STACS2027.Runtimes.C4.reports_nil' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.reports_nil

/-- info: 'STACS2027.Runtimes.C4.reports_snoc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.reports_snoc

/-- info: 'STACS2027.Runtimes.C4.length_canon4' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.length_canon4

/-- info: 'STACS2027.Runtimes.C4.length_phi' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.length_phi

/-- info: 'STACS2027.Runtimes.C4.length_flatten_enumOutP' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.length_flatten_enumOutP

/-- info: 'STACS2027.Runtimes.C4.pow43_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.pow43_spec

/-- info: 'STACS2027.Runtimes.C4.pow43_min' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.pow43_min

/-- info: 'STACS2027.Runtimes.C4.min_pow43_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.min_pow43_le

/-- info: 'STACS2027.Runtimes.C4.fourCycles_ram_semantic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.fourCycles_ram_semantic

/-- info: 'STACS2027.Runtimes.C4.fourCycles_ram_paper_semantic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.fourCycles_ram_paper_semantic

/-- info: 'STACS2027.Runtimes.C4.fourCycles_ram_simple_semantic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.fourCycles_ram_simple_semantic

/-- info: 'STACS2027.Runtimes.C4.caseB'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.caseB'

/-- info: 'STACS2027.Runtimes.C4.final_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.final_bound

/-- info: 'STACS2027.Runtimes.C4.nbW' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.nbW

/-- info: 'STACS2027.Runtimes.C4.codW' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.codW

/-- info: 'STACS2027.Runtimes.C4.cherries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.cherries

/-- info: 'STACS2027.Runtimes.C4.sum_codW_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.sum_codW_ge

/-- info: 'STACS2027.Runtimes.C4.sum_codW_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.sum_codW_sq

/-- info: 'STACS2027.Runtimes.C4.isCycle_of_nb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.isCycle_of_nb

/-- info: 'STACS2027.Runtimes.C4.adjR' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.adjR

/-- info: 'STACS2027.Runtimes.C4.cfg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.cfg

/-- info: 'STACS2027.Runtimes.C4.cfgCycle' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.cfgCycle

/-- info: 'STACS2027.Runtimes.C4.mem_cfg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.mem_cfg

/-- info: 'STACS2027.Runtimes.C4.cfg_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.cfg_nodup

/-- info: 'STACS2027.Runtimes.C4.cfg_isCycle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.cfg_isCycle

/-- info: 'STACS2027.Runtimes.C4.cfgCycle_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.cfgCycle_mem

/-- info: 'STACS2027.Runtimes.C4.card_cfg_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.card_cfg_le

/-- info: 'STACS2027.Runtimes.C4.symm_adjR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.symm_adjR

/-- info: 'STACS2027.Runtimes.C4.card_nbW_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.card_nbW_core

/-- info: 'STACS2027.Runtimes.C4.card_nbW_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.card_nbW_le

/-- info: 'STACS2027.Runtimes.C4.supersat_caseB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.supersat_caseB

/-- info: 'STACS2027.Runtimes.C4.degen_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.C4.degen_bound

/-- info: 'STACS2027.Runtimes.ConvexQP.border' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.border

/-- info: 'STACS2027.Runtimes.ConvexQP.border_cc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.border_cc

/-- info: 'STACS2027.Runtimes.ConvexQP.border_cl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.border_cl

/-- info: 'STACS2027.Runtimes.ConvexQP.border_lc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.border_lc

/-- info: 'STACS2027.Runtimes.ConvexQP.border_ll' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.border_ll

/-- info: 'STACS2027.Runtimes.ConvexQP.border_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.border_map

/-- info: 'STACS2027.Runtimes.ConvexQP.border_eq_reindex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.border_eq_reindex

/-- info: 'STACS2027.Runtimes.ConvexQP.border_mul_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.border_mul_apply

/-- info: 'STACS2027.Runtimes.ConvexQP.det_border_field' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.det_border_field

/-- info: 'STACS2027.Runtimes.ConvexQP.adjugate_border_field' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.adjugate_border_field

/-- info: 'STACS2027.Runtimes.ConvexQP.det_border' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.det_border

/-- info: 'STACS2027.Runtimes.ConvexQP.adjugate_border' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.adjugate_border

/-- info: 'STACS2027.Runtimes.ConvexQP.kap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.kap

/-- info: 'STACS2027.Runtimes.ConvexQP.cutMat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.cutMat

/-- info: 'STACS2027.Runtimes.ConvexQP.cutCenter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.cutCenter

/-- info: 'STACS2027.Runtimes.ConvexQP.RoundOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.RoundOf

/-- info: 'STACS2027.Runtimes.ConvexQP.kap_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.kap_pos

/-- info: 'STACS2027.Runtimes.ConvexQP.vecMulVec_mulVec'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.vecMulVec_mulVec'

/-- info: 'STACS2027.Runtimes.ConvexQP.cutMat_symm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.cutMat_symm

/-- info: 'STACS2027.Runtimes.ConvexQP.qf_cutMat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.qf_cutMat

/-- info: 'STACS2027.Runtimes.ConvexQP.cutMat_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.cutMat_ge

/-- info: 'STACS2027.Runtimes.ConvexQP.cutMat_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.cutMat_le

/-- info: 'STACS2027.Runtimes.ConvexQP.det_cutMat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.det_cutMat

/-- info: 'STACS2027.Runtimes.ConvexQP.cut_scalar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.cut_scalar

/-- info: 'STACS2027.Runtimes.ConvexQP.inEll_cut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.inEll_cut

/-- info: 'STACS2027.Runtimes.ConvexQP.abs_le_mul_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.abs_le_mul_sqrt

/-- info: 'STACS2027.Runtimes.ConvexQP.sum_abs_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.sum_abs_sq_le

/-- info: 'STACS2027.Runtimes.ConvexQP.abs_qf_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.abs_qf_le

/-- info: 'STACS2027.Runtimes.ConvexQP.sq_dot_le_of_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.sq_dot_le_of_abs

/-- info: 'STACS2027.Runtimes.ConvexQP.scalar_d' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.scalar_d

/-- info: 'STACS2027.Runtimes.ConvexQP.scalar_qv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.scalar_qv

/-- info: 'STACS2027.Runtimes.ConvexQP.qf_pos_of_formGe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.qf_pos_of_formGe

/-- info: 'STACS2027.Runtimes.ConvexQP.rounded_form_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.rounded_form_bounds

/-- info: 'STACS2027.Runtimes.ConvexQP.rounded_formGe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.rounded_formGe

/-- info: 'STACS2027.Runtimes.ConvexQP.rounded_formLe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.rounded_formLe

/-- info: 'STACS2027.Runtimes.ConvexQP.rounded_det' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.rounded_det

/-- info: 'STACS2027.Runtimes.ConvexQP.rounded_inEll' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.rounded_inEll

/-- info: 'STACS2027.Runtimes.ConvexQP.abs_cutCenter_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.abs_cutCenter_sub_le

/-- info: 'STACS2027.Runtimes.ConvexQP.upperOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.upperOf

/-- info: 'STACS2027.Runtimes.ConvexQP.EllInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.EllInv

/-- info: 'STACS2027.Runtimes.ConvexQP.CutStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.CutStep

/-- info: 'STACS2027.Runtimes.ConvexQP.one_le_growOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.one_le_growOf

/-- info: 'STACS2027.Runtimes.ConvexQP.upperOf_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.upperOf_mono

/-- info: 'STACS2027.Runtimes.ConvexQP.ellInv_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.ellInv_zero

/-- info: 'STACS2027.Runtimes.ConvexQP.ellInv_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.ellInv_succ

/-- info: 'STACS2027.Runtimes.ConvexQP.ell_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.ell_invariant

/-- info: 'STACS2027.Runtimes.ConvexQP.ell_contradiction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.ell_contradiction

/-- info: 'STACS2027.Runtimes.ConvexQP.L_nonneg_of_inX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.L_nonneg_of_inX

/-- info: 'STACS2027.Runtimes.ConvexQP.L_le_of_inX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.L_le_of_inX

/-- info: 'STACS2027.Runtimes.ConvexQP.gap_le_of_inX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.gap_le_of_inX

/-- info: 'STACS2027.Runtimes.ConvexQP.feas_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.feas_bounds

/-- info: 'STACS2027.Runtimes.ConvexQP.ellCut_inr_feas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.ellCut_inr_feas

/-- info: 'STACS2027.Runtimes.ConvexQP.ellRun_output_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.ellRun_output_bounds

/-- info: 'STACS2027.Runtimes.ConvexQP.cut_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.cut_bound

/-- info: 'STACS2027.Runtimes.ConvexQP.sqrt_le_add_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.sqrt_le_add_one

/-- info: 'STACS2027.Runtimes.ConvexQP.ellIter_state_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.ellIter_state_bounds

/-- info: 'STACS2027.Runtimes.ConvexQP.update_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.update_bounds

/-- info: 'STACS2027.Runtimes.ConvexQP.k_le_dimKKT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.k_le_dimKKT

/-- info: 'STACS2027.Runtimes.ConvexQP.bigE_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.bigE_le

/-- info: 'STACS2027.Runtimes.ConvexQP.radInv_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.radInv_le

/-- info: 'STACS2027.Runtimes.ConvexQP.logRad_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.logRad_le

/-- info: 'STACS2027.Runtimes.ConvexQP.iters_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.iters_eq

/-- info: 'STACS2027.Runtimes.ConvexQP.prec_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.prec_eq

/-- info: 'STACS2027.Runtimes.ConvexQP.nDim' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.nDim

/-- info: 'STACS2027.Runtimes.ConvexQP.radInv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.radInv

/-- info: 'STACS2027.Runtimes.ConvexQP.logRad' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.logRad

/-- info: 'STACS2027.Runtimes.ConvexQP.iters' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.iters

/-- info: 'STACS2027.Runtimes.ConvexQP.prec' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.prec

/-- info: 'STACS2027.Runtimes.ConvexQP.cNum' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.cNum

/-- info: 'STACS2027.Runtimes.ConvexQP.cDen' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.cDen

/-- info: 'STACS2027.Runtimes.ConvexQP.Consts' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Consts

/-- info: 'STACS2027.Runtimes.ConvexQP.consts' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.consts

/-- info: 'STACS2027.Runtimes.ConvexQP.Idx' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Idx

/-- info: 'STACS2027.Runtimes.ConvexQP.EllState' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.EllState

/-- info: 'STACS2027.Runtimes.ConvexQP.idxList' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.idxList

/-- info: 'STACS2027.Runtimes.ConvexQP.firstNeg' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.firstNeg

/-- info: 'STACS2027.Runtimes.ConvexQP.blockSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.blockSum

/-- info: 'STACS2027.Runtimes.ConvexQP.firstOver' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.firstOver

/-- info: 'STACS2027.Runtimes.ConvexQP.feasPt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.feasPt

/-- info: 'STACS2027.Runtimes.ConvexQP.negCut' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.negCut

/-- info: 'STACS2027.Runtimes.ConvexQP.blockCut' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.blockCut

/-- info: 'STACS2027.Runtimes.ConvexQP.gradCut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.gradCut

/-- info: 'STACS2027.Runtimes.ConvexQP.ellCut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.ellCut

/-- info: 'STACS2027.Runtimes.ConvexQP.updU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.updU

/-- info: 'STACS2027.Runtimes.ConvexQP.updG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.updG

/-- info: 'STACS2027.Runtimes.ConvexQP.updS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.updS

/-- info: 'STACS2027.Runtimes.ConvexQP.ellUpdate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.ellUpdate

/-- info: 'STACS2027.Runtimes.ConvexQP.ellStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.ellStep

/-- info: 'STACS2027.Runtimes.ConvexQP.ellInit' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.ellInit

/-- info: 'STACS2027.Runtimes.ConvexQP.ellIter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.ellIter

/-- info: 'STACS2027.Runtimes.ConvexQP.ellRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.ellRun

/-- info: 'STACS2027.Runtimes.ConvexQP.card_idx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.card_idx

/-- info: 'STACS2027.Runtimes.ConvexQP.nDim_ge_two' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.nDim_ge_two

/-- info: 'STACS2027.Runtimes.ConvexQP.cNum_div_cDen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.cNum_div_cDen

/-- info: 'STACS2027.Runtimes.ConvexQP.cDen_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.cDen_pos

/-- info: 'STACS2027.Runtimes.ConvexQP.prec_ge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.prec_ge

/-- info: 'STACS2027.Runtimes.ConvexQP.prec_ge_two' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.prec_ge_two

/-- info: 'STACS2027.Runtimes.ConvexQP.mem_idxList' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.mem_idxList

/-- info: 'STACS2027.Runtimes.ConvexQP.firstNeg_some' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.firstNeg_some

/-- info: 'STACS2027.Runtimes.ConvexQP.firstNeg_none' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.firstNeg_none

/-- info: 'STACS2027.Runtimes.ConvexQP.firstOver_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.firstOver_some

/-- info: 'STACS2027.Runtimes.ConvexQP.firstOver_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.firstOver_none

/-- info: 'STACS2027.Runtimes.ConvexQP.QR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.QR

/-- info: 'STACS2027.Runtimes.ConvexQP.aR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.aR

/-- info: 'STACS2027.Runtimes.ConvexQP.gR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.gR

/-- info: 'STACS2027.Runtimes.ConvexQP.cur' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.cur

/-- info: 'STACS2027.Runtimes.ConvexQP.mulVec_QR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.mulVec_QR

/-- info: 'STACS2027.Runtimes.ConvexQP.qf_QR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.qf_QR

/-- info: 'STACS2027.Runtimes.ConvexQP.dot_gR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.dot_gR

/-- info: 'STACS2027.Runtimes.ConvexQP.one_le_dot_gR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.one_le_dot_gR

/-- info: 'STACS2027.Runtimes.ConvexQP.abs_div_pow_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.abs_div_pow_le

/-- info: 'STACS2027.Runtimes.ConvexQP.ellUpdate_round' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.ellUpdate_round

/-- info: 'STACS2027.Runtimes.ConvexQP.fstar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.fstar

/-- info: 'STACS2027.Runtimes.ConvexQP.delta0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.delta0

/-- info: 'STACS2027.Runtimes.ConvexQP.Kset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Kset

/-- info: 'STACS2027.Runtimes.ConvexQP.fstar_bdd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.fstar_bdd

/-- info: 'STACS2027.Runtimes.ConvexQP.fstar_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.fstar_le

/-- info: 'STACS2027.Runtimes.ConvexQP.inY_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.inY_zero

/-- info: 'STACS2027.Runtimes.ConvexQP.exists_near_fstar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.exists_near_fstar

/-- info: 'STACS2027.Runtimes.ConvexQP.curv_ge_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.curv_ge_one

/-- info: 'STACS2027.Runtimes.ConvexQP.eps_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.eps_le_one

/-- info: 'STACS2027.Runtimes.ConvexQP.delta0_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.delta0_pos

/-- info: 'STACS2027.Runtimes.ConvexQP.dot_negCut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.dot_negCut

/-- info: 'STACS2027.Runtimes.ConvexQP.dot_blockCut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.dot_blockCut

/-- info: 'STACS2027.Runtimes.ConvexQP.dot_gradCut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.dot_gradCut

/-- info: 'STACS2027.Runtimes.ConvexQP.cur_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.cur_sub

/-- info: 'STACS2027.Runtimes.ConvexQP.feas_inY' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.feas_inY

/-- info: 'STACS2027.Runtimes.ConvexQP.ptOf_feasPt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.ptOf_feasPt

/-- info: 'STACS2027.Runtimes.ConvexQP.gap_ptOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.gap_ptOf

/-- info: 'STACS2027.Runtimes.ConvexQP.f_gt_of_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.f_gt_of_gap

/-- info: 'STACS2027.Runtimes.ConvexQP.ellCut_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.ellCut_valid

/-- info: 'STACS2027.Runtimes.ConvexQP.ellCut_inr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.ellCut_inr

/-- info: 'STACS2027.Runtimes.ConvexQP.QR_init' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.QR_init

/-- info: 'STACS2027.Runtimes.ConvexQP.aR_init' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.aR_init

/-- info: 'STACS2027.Runtimes.ConvexQP.Kset_init' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Runtimes.ConvexQP.Kset_init

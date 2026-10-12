module

public import Runtimes.Flow.HornQuery
public import Runtimes.Flow.PaddedEncoding
public import Runtimes.TwoSatPhase
import Mathlib.Tactic

set_option maxRecDepth 4096

/-! # A uniform RAM driver for residual cut membership -/

@[expose] public section

namespace STACS2027.Runtimes.Flow

open STACS2027 STACS2027.RAM Complexity.SAT

/-- Selected original occurrence bits, in occurrence order. -/
def originalFlowBits {arcs : ℕ} (flow : IndexedFlow arcs) : List ℕ :=
  (List.finRange arcs).map fun i => if flow i then 1 else 0

/-- The flow-oracle flag and its selected bits follow the original edge input. -/
def hornInput {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs) (padding : ℕ)
    (flow : IndexedFlow arcs) (extraBits : List ℕ) : List ℕ :=
  edgeInput net padding ++ (1 :: originalFlowBits flow ++ extraBits)

/-- The maximum residual-closed source side, as one bit per original vertex. -/
def maximalRegionBits {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    (flow : IndexedFlow arcs) : List ℕ :=
  (List.finRange nodes).map fun v => if maximalCutRegion net flow v then 1 else 0

@[simp] theorem originalFlowBits_length {arcs : ℕ} (flow : IndexedFlow arcs) :
    (originalFlowBits flow).length = arcs := by simp [originalFlowBits]

@[simp] theorem hornInput_length {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    (padding : ℕ) (flow : IndexedFlow arcs) (extraBits : List ℕ) :
    (hornInput net padding flow extraBits).length = 3 * arcs + extraBits.length + 6 := by
  simp [hornInput]; omega

@[simp] theorem maximalRegionBits_length {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    (flow : IndexedFlow arcs) : (maximalRegionBits net flow).length = nodes := by
  simp [maximalRegionBits]

/-- A residual implication compiled as its two literal codes. -/
def residualCodes {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    (flow : IndexedFlow arcs) (count : ℕ) : List ℕ :=
  ((List.finRange arcs).take count).flatMap fun i =>
    if flow i then [2 * (net.head i).val + 1, 2 * (net.tail i).val]
    else [2 * (net.tail i).val + 1, 2 * (net.head i).val]

@[simp] theorem residualCodes_length {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    (flow : IndexedFlow arcs) (count : ℕ) :
    (residualCodes net flow count).length = 2 * min count arcs := by
  have hlen (i : Fin arcs) :
      (if flow i then [2 * (net.head i).val + 1, 2 * (net.tail i).val]
       else [2 * (net.tail i).val + 1, 2 * (net.head i).val]).length = 2 := by
    split_ifs <;> rfl
  simp [residualCodes, List.length_flatMap, hlen, Nat.mul_comm]

theorem residualCodes_succ {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    (flow : IndexedFlow arcs) (i : Fin arcs) :
    residualCodes net flow (i.val + 1) = residualCodes net flow i.val ++
      (if flow i then [2 * (net.head i).val + 1, 2 * (net.tail i).val]
       else [2 * (net.tail i).val + 1, 2 * (net.head i).val]) := by
  have ht : (List.finRange arcs).take (i.val + 1) =
      (List.finRange arcs).take i.val ++ [i] := by
    rw [List.take_add_one, List.getElem?_eq_getElem (by simpa using i.isLt)]
    simp
  simp [residualCodes, ht]

theorem hornQuery_codes {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    (flow : IndexedFlow arcs) (v : Fin nodes) :
    TwoSat.codes (hornQuery net flow v) = residualCodes net flow arcs ++
      [2 * v.val, 2 * v.val, 2 * net.sink.val + 1, 2 * net.sink.val + 1] := by
  have ht : (List.finRange arcs).take arcs = List.finRange arcs := by simp
  simp only [TwoSat.codes, hornQuery, List.flatMap_append, List.flatMap_map,
    List.flatMap_cons, List.flatMap_nil, List.append_nil]
  congr 1
  · rw [residualCodes, ht]
    apply List.flatMap_congr
    intro i hi
    cases h : flow i <;>
      simp [TwoSat.code, availableEdge, residualTail, residualHead, h]

abbrev hNodes : ℕ := 1000
abbrev hArcs : ℕ := 1001
abbrev hSink : ℕ := 1002
abbrev hBits : ℕ := 1003
abbrev hLength : ℕ := 1004
abbrev hVertex : ℕ := 1005
abbrev hArc : ℕ := 1006
abbrev hAddr : ℕ := 1007
abbrev hTail : ℕ := 1008
abbrev hHead : ℕ := 1009
abbrev hBit : ℕ := 1010
abbrev hNeg : ℕ := 1011
abbrev hPos : ℕ := 1012
abbrev hBase : ℕ := 1013
abbrev hValue : ℕ := 1014
abbrev hZero : ℕ := 1015
abbrev hOne : ℕ := 1016
abbrev hPairs : ℕ := 1017
abbrev hPadding : ℕ := 1018

def hornInit : Stmt :=
  .seq (.const hAddr 0) (.seq (.load hNodes hAddr) (.seq (.const hAddr 1)
  (.seq (.load hArcs hAddr) (.seq (.const hAddr 3) (.seq (.load hSink hAddr)
  (.seq (.const hAddr 4) (.seq (.load hPadding hAddr) (.seq (.add hBits hArcs hArcs)
  (.seq (addc hBits hBits 6) (.seq (.add hLength hBits hArcs)
  (.seq (.add hLength hLength hPadding) (.seq (mov rFREE hLength)
  (.seq (.const hZero 0) (.seq (.const hOne 1) (.const hPairs 5)))))))))))))))

def hornPrepare : Stmt :=
  .seq (mov TwoSat.tN hNodes) (.seq (addc TwoSat.tM hArcs 2)
    (.seq (mov hBase rFREE) (mov TwoSat.tCL rFREE)))

def hornRead : Stmt :=
  .seq (.add hAddr hArc hArc) (.seq (.add hAddr hAddr hPairs)
  (.seq (.load hTail hAddr) (.seq (inc hAddr) (.seq (.load hHead hAddr)
  (.seq (.add hAddr hBits hArc) (.load hBit hAddr))))))

def hornCodes : Stmt := ifEq hBit hZero
  (.seq (.add hNeg hTail hTail) (.seq (inc hNeg) (.add hPos hHead hHead)))
  (.seq (.add hNeg hHead hHead) (.seq (inc hNeg) (.add hPos hTail hTail)))

def hornStore : Stmt :=
  .seq (.add hAddr hArc hArc) (.seq (.add hAddr hAddr hBase)
  (.seq (.store hAddr hNeg) (.seq (inc hAddr) (.store hAddr hPos))))

def hornArcBody : Stmt := .seq hornRead (.seq hornCodes hornStore)

def hornUnits : Stmt :=
  .seq (.add hAddr hArcs hArcs) (.seq (.add hAddr hAddr hBase)
  (.seq (.add hValue hVertex hVertex) (.seq (.store hAddr hValue)
  (.seq (inc hAddr) (.seq (.store hAddr hValue) (.seq (inc hAddr)
  (.seq (.add hValue hSink hSink) (.seq (inc hValue) (.seq (.store hAddr hValue)
  (.seq (inc hAddr) (.seq (.store hAddr hValue) (addc rFREE hAddr 1))))))))))))

def hornVertexBody : Stmt := .seq hornPrepare
  (.seq (forUp hArc hArcs hornArcBody) (.seq hornUnits
    (.seq TwoSat.twoSat (.write TwoSat.tOK))))

/-- A fixed program, using the already verified linear 2-SAT phase once per vertex. -/
def hornRAM : Stmt := .seq hornInit (forUp hVertex hNodes hornVertexBody)


@[mk_iff] structure HornRegs {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    (padding : ℕ) (c : Config) : Prop where
  rn : c.reg hNodes = nodes
  rm : c.reg hArcs = arcs
  sink : c.reg hSink = net.sink.val
  bits : c.reg hBits = 2 * arcs + 6
  length : c.reg hLength = 3 * arcs + padding + 6
  zero : c.reg hZero = 0
  one : c.reg hOne = 1
  pairs : c.reg hPairs = 5

private theorem HornRegs.run {nodes arcs : ℕ} {net : IndexedNetwork nodes arcs}
    {padding : ℕ} {c : Config} {program : Stmt} (hs : LoopFree program)
    (hw : ∀ r ∈ wregs program,
      r ∉ [hNodes, hArcs, hSink, hBits, hLength, hZero, hOne, hPairs])
    (h : HornRegs net padding c) : HornRegs net padding (RAM.run program c) := by
  have hr : ∀ r ∈ [hNodes, hArcs, hSink, hBits, hLength, hZero, hOne, hPairs],
      (RAM.run program c).reg r = c.reg r := by
    intro r hr
    exact run_reg_of_not_mem hs (fun hm => hw r hm hr) c
  constructor
  · rw [hr hNodes (by simp)]; exact h.rn
  · rw [hr hArcs (by simp)]; exact h.rm
  · rw [hr hSink (by simp)]; exact h.sink
  · rw [hr hBits (by simp)]; exact h.bits
  · rw [hr hLength (by simp)]; exact h.length
  · rw [hr hZero (by simp)]; exact h.zero
  · rw [hr hOne (by simp)]; exact h.one
  · rw [hr hPairs (by simp)]; exact h.pairs

private theorem inputEndpoints {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    (padding : ℕ) (flow : IndexedFlow arcs) (extraBits : List ℕ) (mm : ℕ → ℕ)
    (h : Arr mm 0 (hornInput net padding flow extraBits)) (i : Fin arcs) :
    mm (5 + 2 * i.val) = (net.tail i).val ∧
      mm (5 + (2 * i.val + 1)) = (net.head i).val ∧
      mm (2 * arcs + 6 + i.val) = if flow i then 1 else 0 := by
  have he := (arr_append.mp h).1
  have hb := (arr_append.mp h).2
  simp only [edgeInput, arr_cons] at he
  have hp : Arr mm 5 (edgePairs net) := he.2.2.2.2.2
  have hb' : Arr mm (2 * arcs + 6) (originalFlowBits flow ++ extraBits) := by
    simpa [edgeInput_length, Nat.add_assoc] using (arr_cons.mp hb).2
  have hf := (arr_append.mp hb').1
  refine ⟨?_, ?_, ?_⟩
  · rw [hp.getD (by simp only [edgePairs_length]; omega)]; exact (edgePairs_get net i).1
  · rw [hp.getD (by simp only [edgePairs_length]; omega)]; exact (edgePairs_get net i).2
  · rw [hf.getD (by simpa using i.isLt)]
    simp [originalFlowBits]

/-- Initialization reads the encoded dimensions and starts fresh allocation after the input. -/
theorem hornInit_spec {nodes arcs S : ℕ} (net : IndexedNetwork nodes arcs) (padding : ℕ)
    (flow : IndexedFlow arcs) (extraBits : List ℕ) (he : extraBits.length = padding)
    (hS : 5 ≤ S) :
    HTB S hornInit (fun c => c = initial (hornInput net padding flow extraBits))
      (fun c => HornRegs net padding c ∧
        Arr c.mem 0 (hornInput net padding flow extraBits) ∧
        c.reg rFREE = 3 * arcs + padding + 6 ∧
        ZeroFrom c.mem (c.reg rFREE) ∧ c.out = []) 20 := by
  refine HTB.run_le (by decide) (by decide) fun c hc => ?_
  subst c
  have hmem := run_mem_of_stores (s := hornInit) (by decide) rfl
    (initial (hornInput net padding flow extraBits))
  have hfree : (run hornInit (initial (hornInput net padding flow extraBits))).reg rFREE =
      3 * arcs + padding + 6 := by
    simp +decide [hornInit, run_addc, run_mov, initial_mem, hornInput, edgeInput]
    omega
  refine ⟨by addr_ok [hornInit], ?_, ?_, hfree, ?_, ?_⟩
  · constructor
    all_goals simp +decide [hornInit, run_addc, run_mov, initial_mem, hornInput, edgeInput]
    all_goals omega
  · rw [hmem]; exact arr_initial _
  · rw [hmem, hfree]
    simpa [hornInput_length, he] using zeroFrom_initial (hornInput net padding flow extraBits)
  · exact run_out_of_writes (by decide) rfl _

@[mk_iff] structure HornBuildRegs {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    (padding base vertex : ℕ) (c : Config) : Prop where
  header : HornRegs net padding c
  rb : c.reg hBase = base
  rv : c.reg hVertex = vertex
  tn : c.reg TwoSat.tN = nodes
  tm : c.reg TwoSat.tM = arcs + 2
  tcl : c.reg TwoSat.tCL = base
  free : c.reg rFREE = base

private theorem HornBuildRegs.run {nodes arcs : ℕ} {net : IndexedNetwork nodes arcs}
    {padding base vertex : ℕ} {c : Config} {program : Stmt} (hs : LoopFree program)
    (hw : ∀ r ∈ wregs program, r ∉ [hNodes, hArcs, hSink, hBits, hLength, hZero, hOne,
      hPairs, hBase, hVertex, TwoSat.tN, TwoSat.tM, TwoSat.tCL, rFREE])
    (h : HornBuildRegs net padding base vertex c) :
    HornBuildRegs net padding base vertex (RAM.run program c) := by
  have hr : ∀ r ∈ [hBase, hVertex, TwoSat.tN, TwoSat.tM, TwoSat.tCL, rFREE],
      (RAM.run program c).reg r = c.reg r := by
    intro r hr; exact run_reg_of_not_mem hs (fun hm => hw r hm (by simp_all)) c
  constructor
  · exact HornRegs.run hs (by intro r hr; have := hw r hr; simp_all) h.header
  · rw [hr hBase (by simp)]; exact h.rb
  · rw [hr hVertex (by simp)]; exact h.rv
  · rw [hr TwoSat.tN (by simp)]; exact h.tn
  · rw [hr TwoSat.tM (by simp)]; exact h.tm
  · rw [hr TwoSat.tCL (by simp)]; exact h.tcl
  · rw [hr rFREE (by simp)]; exact h.free

/-- The growing residual implication table, allocated above the original input. -/
def HornBuildInv {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs) (padding : ℕ)
    (flow : IndexedFlow arcs) (extraBits : List ℕ) (base vertex j : ℕ) (out : List ℕ)
    (c : Config) : Prop :=
  HornBuildRegs net padding base vertex c ∧
    Arr c.mem 0 (hornInput net padding flow extraBits) ∧
    Arr c.mem base (residualCodes net flow j) ∧
    ZeroFrom c.mem (base + 2 * j) ∧ c.out = out


/-- Compile and append one residual implication without changing the original input. -/
theorem hornArcBody_spec {nodes arcs S : ℕ} (net : IndexedNetwork nodes arcs)
    (padding : ℕ) (flow : IndexedFlow arcs) (extraBits : List ℕ)
    (he : extraBits.length = padding) (base vertex j : ℕ) (hj : j < arcs)
    (hbase : 3 * arcs + padding + 6 ≤ base) (hS : base + 2 * arcs + 4 ≤ S)
    (out : List ℕ) :
    HTB S hornArcBody
      (fun c => HornBuildInv net padding flow extraBits base vertex j out c ∧
        c.reg hArc = j ∧ c.reg hArcs = arcs)
      (fun c => HornBuildInv net padding flow extraBits base vertex (j + 1) out c ∧
        c.reg hArc = j ∧ c.reg hArcs = arcs) 30 := by
  refine HTB.run_le (by decide) (by decide) fun c ⟨⟨hr, hinput, hcodes, hzero, hout⟩, hi, hm⟩ => ?_
  let i : Fin arcs := ⟨j, hj⟩
  have hends := inputEndpoints net padding flow extraBits c.mem hinput i
  have ht : c.mem (j + j + 5) = (net.tail i).val := by
    rw [show j + j + 5 = 5 + 2 * i.val by dsimp [i]; omega]; exact hends.1
  have hh : c.mem (j + j + 5 + 1) = (net.head i).val := by
    rw [show j + j + 5 + 1 = 5 + (2 * i.val + 1) by dsimp [i]; omega]; exact hends.2.1
  have hb : c.mem (2 * arcs + 6 + j) = if flow i then 1 else 0 := hends.2.2
  let neg := if flow i then 2 * (net.head i).val + 1 else 2 * (net.tail i).val + 1
  let pos := if flow i then 2 * (net.tail i).val else 2 * (net.head i).val
  have hmem : (run hornArcBody c).mem =
      upd (upd c.mem (base + 2 * j) neg) (base + 2 * j + 1) pos := by
    cases hf : flow i <;>
      simp +decide [hornArcBody, hornRead, hornCodes, hornStore, run_ifEq, run_inc,
        hi, hr.header.pairs, hr.header.bits, hr.header.zero, hr.rb, ht, hh, hb, hf, neg, pos,
        show j + j + base = base + 2 * j by omega]
    all_goals simp only [two_mul]
  have hl : (residualCodes net flow j).length = 2 * j := by simp; omega
  have hcode' : Arr (run hornArcBody c).mem base (residualCodes net flow (j + 1)) := by
    rw [hmem]
    have hp := (hcodes.upd_snoc (a := base + 2 * j) (x := neg) (by rw [hl])).upd_snoc
      (a := base + 2 * j + 1) (x := pos) (by simp only [List.length_append, List.length_singleton, hl]; omega)
    have hs := residualCodes_succ net flow i
    simp only [i, Fin.val_mk] at hs
    rw [hs]
    cases hf : flow i <;> simpa [neg, pos, hf, List.append_assoc] using hp
  have hr' := HornBuildRegs.run (program := hornArcBody) (by decide) (by decide) hr
  refine ⟨?_, ⟨hr', ?_, hcode', ?_, ?_⟩, ?_, ?_⟩
  · cases hf : flow i <;>
      addr_ok [hornArcBody, hornRead, hornCodes, hornStore, hi, hr.header.pairs,
        hr.header.bits, hr.header.zero, hr.rb, ht, hh, hb, hf]
  · rw [hmem]
    exact (hinput.upd_of_disjoint (by simp [hornInput_length, he]; omega)).upd_of_disjoint
      (by simp [hornInput_length, he]; omega)
  · rw [hmem]
    exact ((hzero.mono (by omega)).upd (by omega)).upd (by omega)
  · rw [run_out_of_writes (by decide) rfl]; exact hout
  · rw [run_reg_of_not_mem (by decide) (by decide)]; exact hi
  · exact hr'.header.rm


/-- Start the next vertex query in the current free region. -/
theorem hornPrepare_spec {nodes arcs S : ℕ} (net : IndexedNetwork nodes arcs)
    (padding : ℕ) (flow : IndexedFlow arcs) (extraBits : List ℕ)
    (base vertex : ℕ) (out : List ℕ) :
    HTB S hornPrepare
      (fun c => HornRegs net padding c ∧ Arr c.mem 0 (hornInput net padding flow extraBits) ∧
        c.reg rFREE = base ∧ c.reg hVertex = vertex ∧ ZeroFrom c.mem base ∧ c.out = out)
      (fun c => HornBuildInv net padding flow extraBits base vertex 0 out c ∧
        c.reg hArcs = arcs) 10 := by
  refine HTB.of_HT rfl <| HT.run_le (by decide) (by decide)
    fun c ⟨hr, hinput, hf, hv, hz, ho⟩ => ?_
  have hm := run_mem_of_stores (s := hornPrepare) (by decide) rfl c
  have hr' := HornRegs.run (program := hornPrepare) (by decide) (by decide) hr
  refine ⟨⟨⟨hr', ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩, hr'.rm⟩
  all_goals first
    | simpa [hm] using hinput
    | simpa [hm] using hz
    | simp +decide [hornPrepare, run_mov, run_addc, hf, hv, hr.rn, hr.rm, hm, ho,
        residualCodes]

/-- State just before a verified decision call. -/
def HornReady {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs) (padding : ℕ)
    (flow : IndexedFlow arcs) (extraBits : List ℕ) (base : ℕ) (v : Fin nodes)
    (out : List ℕ) (c : Config) : Prop :=
  HornRegs net padding c ∧ Arr c.mem 0 (hornInput net padding flow extraBits) ∧
    c.reg hVertex = v.val ∧ c.reg TwoSat.tN = nodes ∧ c.reg TwoSat.tM = arcs + 2 ∧
    c.reg TwoSat.tCL = base ∧ c.reg rFREE = base + 2 * arcs + 4 ∧
    Arr c.mem base (TwoSat.codes (hornQuery net flow v)) ∧
    ZeroFrom c.mem (base + 2 * arcs + 4) ∧ c.out = out

/-- Append the two unit clauses that force this vertex in and the sink out. -/
theorem hornUnits_spec {nodes arcs S : ℕ} (net : IndexedNetwork nodes arcs)
    (padding : ℕ) (flow : IndexedFlow arcs) (extraBits : List ℕ)
    (he : extraBits.length = padding) (base : ℕ) (v : Fin nodes)
    (hbase : 3 * arcs + padding + 6 ≤ base) (hS : base + 2 * arcs + 4 ≤ S)
    (out : List ℕ) :
    HTB S hornUnits (HornBuildInv net padding flow extraBits base v.val arcs out)
      (HornReady net padding flow extraBits base v out) 20 := by
  refine HTB.run_le (by decide) (by decide) fun c ⟨hr, hinput, hcodes, hzero, hout⟩ => ?_
  have hmem : (run hornUnits c).mem =
      upd (upd (upd (upd c.mem (base + 2 * arcs) (2 * v.val))
        (base + 2 * arcs + 1) (2 * v.val))
        (base + 2 * arcs + 2) (2 * net.sink.val + 1))
        (base + 2 * arcs + 3) (2 * net.sink.val + 1) := by
    simp +decide [hornUnits, run_inc, run_addc, hr.header.rm, hr.rb, hr.rv, hr.header.sink,
      show arcs + arcs + base = base + 2 * arcs by omega, Nat.add_assoc, two_mul]
  have hr' := HornRegs.run (program := hornUnits) (by decide) (by decide) hr.header
  have hcode' : Arr (run hornUnits c).mem base (TwoSat.codes (hornQuery net flow v)) := by
    rw [hornQuery_codes, arr_append]
    refine ⟨?_, ?_⟩
    · rw [hmem]
      exact (((hcodes.upd_of_disjoint (by simp)).upd_of_disjoint
        (by simp)).upd_of_disjoint (by simp)).upd_of_disjoint (by simp)
    · rw [hmem]
      simp only [residualCodes_length, min_self, arr_cons, arr_nil, and_true]
      simp [upd_apply, Nat.add_assoc]
  refine ⟨by addr_ok [hornUnits, hr.header.rm, hr.rb], hr', ?_, ?_, ?_, ?_, ?_, ?_, hcode', ?_, ?_⟩
  · rw [hmem]
    exact (((hinput.upd_of_disjoint (by simp [hornInput_length, he]; omega)).upd_of_disjoint
      (by simp [hornInput_length, he]; omega)).upd_of_disjoint
      (by simp [hornInput_length, he]; omega)).upd_of_disjoint
      (by simp [hornInput_length, he]; omega)
  · rw [run_reg_of_not_mem (by decide) (by decide)]; exact hr.rv
  · rw [run_reg_of_not_mem (by decide) (by decide)]; exact hr.tn
  · rw [run_reg_of_not_mem (by decide) (by decide)]; exact hr.tm
  · rw [run_reg_of_not_mem (by decide) (by decide)]; exact hr.tcl
  · simp +decide [hornUnits, run_inc, run_addc, hr.header.rm, hr.rb]; omega
  · rw [hmem]
    exact ((((hzero.mono (by omega)).upd (by omega)).upd (by omega)).upd (by omega)).upd (by omega)
  · rw [run_out_of_writes (by decide) rfl]; exact hout


/-- The call returns exactly one residual cut-membership bit. -/
theorem hornDecision_spec {nodes arcs S : ℕ} (net : IndexedNetwork nodes arcs)
    (padding : ℕ) (flow : IndexedFlow arcs) (extraBits : List ℕ)
    (he : extraBits.length = padding) (base : ℕ) (v : Fin nodes)
    (hbase : 3 * arcs + padding + 6 ≤ base)
    (hS : base + 21 * (nodes + arcs + 3) ≤ S) (out : List ℕ) :
    HTB S (.seq TwoSat.twoSat (.write TwoSat.tOK))
      (HornReady net padding flow extraBits base v out)
      (fun c => HornRegs net padding c ∧ Arr c.mem 0 (hornInput net padding flow extraBits) ∧
        c.reg hVertex = v.val ∧ 3 * arcs + padding + 6 ≤ c.reg rFREE ∧
        c.reg rFREE ≤ base + 21 * (nodes + arcs + 3) ∧ ZeroFrom c.mem (c.reg rFREE) ∧
        c.out = out ++ [if maximalCutRegion net flow v then 1 else 0])
      (TwoSat.CT * (nodes + arcs + 3) + 1) := by
  intro c ⟨hr, hinput, hv, hn, hm, hcl, hf, hcodes, hz, ho⟩
  have hlen : (TwoSat.codes (hornQuery net flow v)).length = 2 * (arcs + 2) := by
    rw [hornQuery_codes]; simp; omega
  have hB : TwoSat.TwoSatIn nodes (arcs + 2) (TwoSat.codes (hornQuery net flow v)) c := by
    refine ⟨hn, hm, ?_, ?_, ?_⟩
    · simpa [hcl] using hcodes
    · simpa [hf] using hz
    · rw [hcl, hf, hlen]; omega
  have hSp : TwoSat.endL nodes (arcs + 2) (c.reg rFREE) ≤ S := by
    have h := TwoSat.endL_le nodes (arcs + 2) (c.reg rFREE)
    rw [hf] at h ⊢; omega
  obtain ⟨c', steps, hex, hout, ht⟩ := TwoSat.twoSat_spec nodes (arcs + 2)
    (TwoSat.codes (hornQuery net flow v)) c hlen
    (TwoSat.codes_ok (hornQuery_isTwoCNF net flow v)) hSp c ⟨hB, rfl⟩
  have hr' : HornRegs net padding c' := by
    constructor
    all_goals first
      | rw [hout.frame _ (by decide) (by decide) (by decide)]; exact hr.rn
      | rw [hout.frame _ (by decide) (by decide) (by decide)]; exact hr.rm
      | rw [hout.frame _ (by decide) (by decide) (by decide)]; exact hr.sink
      | rw [hout.frame _ (by decide) (by decide) (by decide)]; exact hr.bits
      | rw [hout.frame _ (by decide) (by decide) (by decide)]; exact hr.length
      | rw [hout.frame _ (by decide) (by decide) (by decide)]; exact hr.zero
      | rw [hout.frame _ (by decide) (by decide) (by decide)]; exact hr.one
      | rw [hout.frame _ (by decide) (by decide) (by decide)]; exact hr.pairs
  have hinput' := hinput.of_below hout.same (by simp [hornInput_length, he, hf]; omega)
  have hlo : 3 * arcs + padding + 6 ≤ c'.reg rFREE := by
    have := hout.fresh; rw [hf] at this; omega
  have hhi : c'.reg rFREE ≤ base + 21 * (nodes + arcs + 3) := by
    rw [hout.rfree]
    have h := TwoSat.endL_le nodes (arcs + 2) (c.reg rFREE)
    rw [hf] at h ⊢; omega
  have hvertex : c'.reg hVertex = v.val := by
    rw [hout.frame _ (by decide) (by decide) (by decide)]; exact hv
  have hwrite : ExecB S (.write TwoSat.tOK) c' 1 (run (.write TwoSat.tOK) c') :=
    Exec.toExecB_of_memFree rfl (exec_run _ (by decide) _)
  refine ⟨run (.write TwoSat.tOK) c', steps + 1, ExecB.seq hex hwrite, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact HornRegs.run (by decide) (by decide) hr'
    · simpa using hinput'
    · simpa using hvertex
    · simpa using hlo
    · simpa using hhi
    · simpa using hout.free
    · simp only [run_write, emit_out, hout.ok, hornQuery_decision, hout.out, ho]
  · simpa only [Nat.add_assoc] using Nat.add_le_add_right ht 1

/-- Loop invariant after deciding the first `j` original vertices. -/
def HornOuterInv {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs) (padding : ℕ)
    (flow : IndexedFlow arcs) (extraBits : List ℕ) (j : ℕ) (c : Config) : Prop :=
  HornRegs net padding c ∧ Arr c.mem 0 (hornInput net padding flow extraBits) ∧
    3 * arcs + padding + 6 ≤ c.reg rFREE ∧
    c.reg rFREE ≤ 3 * arcs + padding + 6 + j * (21 * (nodes + arcs + 3)) ∧
    ZeroFrom c.mem (c.reg rFREE) ∧ c.out = (maximalRegionBits net flow).take j

private theorem maximalRegionBits_succ {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    (flow : IndexedFlow arcs) (v : Fin nodes) :
    (maximalRegionBits net flow).take (v.val + 1) =
      (maximalRegionBits net flow).take v.val ++ [if maximalCutRegion net flow v then 1 else 0] := by
  rw [List.take_add_one, List.getElem?_eq_getElem (by simpa using v.isLt)]
  simp [maximalRegionBits]

/-- One complete query preserves the original input and advances a fresh memory frontier. -/
theorem hornVertexBody_spec {nodes arcs S : ℕ} (net : IndexedNetwork nodes arcs)
    (padding : ℕ) (flow : IndexedFlow arcs) (extraBits : List ℕ)
    (he : extraBits.length = padding)
    (hS : 3 * arcs + padding + 6 + nodes * (21 * (nodes + arcs + 3)) ≤ S)
    (j : ℕ) (hj : j < nodes) :
    HTB S hornVertexBody
      (fun c => HornOuterInv net padding flow extraBits j c ∧
        c.reg hVertex = j ∧ c.reg hNodes = nodes)
      (fun c => HornOuterInv net padding flow extraBits (j + 1) c ∧
        c.reg hVertex = j ∧ c.reg hNodes = nodes) (1000 * (nodes + arcs + 3)) := by
  intro c hc
  rcases hc with ⟨⟨hr, hinput, hlo, hhi, hz, ho⟩, hv, hn⟩
  let base := c.reg rFREE
  let v : Fin nodes := ⟨j, hj⟩
  have hstep : base + 21 * (nodes + arcs + 3) ≤ S := by
    have hmul := Nat.mul_le_mul_right (21 * (nodes + arcs + 3)) (show j + 1 ≤ nodes by omega)
    simp only [Nat.add_mul, Nat.one_mul] at hmul
    dsimp [base]; omega
  have htime : 10 + (arcs * (30 + 4) + 3 + (20 +
      (TwoSat.CT * (nodes + arcs + 3) + 1))) ≤ 1000 * (nodes + arcs + 3) := by
    rw [TwoSat.CT]; omega
  have hbuild := HTB.forUpC (S := S) (i := hArc) (n := hArcs) (N := arcs)
    (body := hornArcBody) (HornBuildInv net padding flow extraBits base j  ·
      ((maximalRegionBits net flow).take j)) 30 (by decide) (by decide) (by decide)
    (fun k => by indep [HornBuildInv, hornBuildRegs_iff, hornRegs_iff])
    (fun k hk => hornArcBody_spec net padding flow extraBits he base j k hk hlo
      (by omega) _)
  have hunit := (hornUnits_spec (S := S) net padding flow extraBits he base v hlo (by omega)
      ((maximalRegionBits net flow).take j)).pre
    (P' := fun c => HornBuildInv net padding flow extraBits base j arcs
      ((maximalRegionBits net flow).take j) c ∧ c.reg hArc = arcs ∧ c.reg hArcs = arcs)
    (fun _ h => h.1)
  have hphase := hornDecision_spec net padding flow extraBits he base v hlo hstep
    ((maximalRegionBits net flow).take j)
  have hall := (hornPrepare_spec net padding flow extraBits base j
    ((maximalRegionBits net flow).take j)).seq (hbuild.seq (hunit.seq hphase))
  obtain ⟨c', steps, hex, ⟨hr', hi', hv', hlo', hhi', hz', ho'⟩, ht⟩ :=
    hall c ⟨hr, hinput, rfl, hv, hz, ho⟩
  refine ⟨c', steps, hex, ⟨⟨hr', hi', hlo', ?_, hz', ?_⟩, hv', hr'.rn⟩, ?_⟩
  · dsimp [base] at hhi'; simp only [Nat.add_mul, Nat.one_mul]; omega
  · rw [maximalRegionBits_succ net flow v]; exact ho'
  · exact ht.trans htime

/-- The single uniform extractor has quadratic time and space when dimensions are bounded. -/
theorem hornRAM_spec {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs) (padding : ℕ)
    (flow : IndexedFlow arcs) (extraBits : List ℕ) (he : extraBits.length = padding) :
    HTB (3 * arcs + padding + 6 + nodes * (21 * (nodes + arcs + 3))) hornRAM
      (fun c => c = initial (hornInput net padding flow extraBits))
      (fun c => c.out = maximalRegionBits net flow)
      (1010 * (nodes + 1) * (nodes + arcs + 3)) := by
  let S := 3 * arcs + padding + 6 + nodes * (21 * (nodes + arcs + 3))
  have hloop := HTB.forUpC (S := S) (i := hVertex) (n := hNodes) (N := nodes)
    (body := hornVertexBody) (HornOuterInv net padding flow extraBits)
    (1000 * (nodes + arcs + 3)) (by decide) (by decide) (by decide)
    (fun j => by indep [HornOuterInv, hornRegs_iff])
    (fun j hj => hornVertexBody_spec net padding flow extraBits he (by rfl) j hj)
  have hinit := (hornInit_spec net padding flow extraBits he (S := S) (by dsimp [S]; omega)).post
    (Q' := fun c => HornOuterInv net padding flow extraBits 0 c ∧ c.reg hNodes = nodes)
    fun c ⟨hr, hi, hf, hz, ho⟩ => by
      refine ⟨⟨hr, hi, by omega, by simp [hf], hz, by simpa using ho⟩, hr.rn⟩
  refine (hinit.seq hloop).mono (fun _ h => h) (fun c h => ?_) ?_
  · simpa [List.take_of_length_le (by simp :
      (maximalRegionBits net flow).length ≤ nodes)] using h.1.2.2.2.2.2
  · nlinarith

/-- Concrete execution of the extractor, with its polynomial resource bound. -/
theorem hornRAM_computes {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs) (padding : ℕ)
    (flow : IndexedFlow arcs) (extraBits : List ℕ) (he : extraBits.length = padding) :
    ∃ steps, ComputesIn hornRAM (hornInput net padding flow extraBits)
      (maximalRegionBits net flow) steps
      (3 * arcs + padding + 6 + nodes * (21 * (nodes + arcs + 3))) ∧
      steps ≤ 1010 * (nodes + 1) * (nodes + arcs + 3) := by
  obtain ⟨steps, ht, hc⟩ := (hornRAM_spec net padding flow extraBits he).computesIn
  exact ⟨steps, hc, ht⟩

end STACS2027.Runtimes.Flow





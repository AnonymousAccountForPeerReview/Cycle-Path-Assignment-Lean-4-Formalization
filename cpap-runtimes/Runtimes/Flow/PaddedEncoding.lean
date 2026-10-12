module

public import Runtimes.Flow.PaddedNetwork
public import Runtimes.Flow.Pipe
public import Outerplanar.RAM.BoundedLib
public import Outerplanar.RAM.Layout
import Mathlib.Tactic

/-! # A linear RAM encoder for the padded minimum-cut network -/

@[expose] public section

namespace STACS2027.Runtimes.Flow

open STACS2027 STACS2027.RAM

/-- Original endpoint occurrences in their unchanged order. -/
def edgePairs {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs) : List ℕ :=
  ((List.finRange arcs).map fun i => (net.tail i |>.val, net.head i |>.val)).flatMap
    fun ends => [ends.1, ends.2]

/-- Input shared by the separator stages: vertex count, arc count, terminals, padding,
then two endpoint numbers for every original occurrence. -/
def edgeInput {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs) (padding : ℕ) : List ℕ :=
  nodes :: arcs :: net.source.val :: net.sink.val :: padding :: edgePairs net

@[simp] theorem edgePairs_length {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs) :
    (edgePairs net).length = 2 * arcs := by
  simp [edgePairs, List.length_flatMap, Function.comp_def, Nat.mul_comm]

@[simp] theorem edgeInput_length {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs) (padding : ℕ) :
    (edgeInput net padding).length = 2 * arcs + 5 := by simp [edgeInput]

theorem edgePairs_get {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs) (i : Fin arcs) :
    (edgePairs net).getD (2 * i.val) 0 = (net.tail i).val ∧
      (edgePairs net).getD (2 * i.val + 1) 0 = (net.head i).val := by
  have h := getD_flatMap_pair ((List.finRange arcs).map fun i =>
    ((net.tail i).val, (net.head i).val)) i.val (by simpa using i.isLt)
  simpa [edgePairs] using h

abbrev cNodes : ℕ := 940
abbrev cArcs : ℕ := 941
abbrev cSource : ℕ := 942
abbrev cSink : ℕ := 943
abbrev cPadding : ℕ := 944
abbrev cIndex : ℕ := 945
abbrev cAddr : ℕ := 946
abbrev cValue : ℕ := 947
abbrev cStart : ℕ := 948
abbrev cZero : ℕ := 949
abbrev cOne : ℕ := 950
abbrev cTotal : ℕ := 951

def paddedEncodeInit : Stmt :=
  .seq (.const cAddr 0) (.seq (.load cNodes cAddr) (.seq (.const cAddr 1)
  (.seq (.load cArcs cAddr) (.seq (.const cAddr 2) (.seq (.load cSource cAddr)
  (.seq (.const cAddr 3) (.seq (.load cSink cAddr) (.seq (.const cAddr 4)
  (.seq (.load cPadding cAddr) (.seq (.const cStart 5) (.seq (.const cZero 0)
  (.seq (.const cOne 1) (.seq (.add cTotal cArcs cPadding) (.seq (.write cNodes)
  (.seq (.write cTotal) (.seq (.write cSource) (.seq (.write cSink) (.write cPadding))))))))))))))))))

def paddedOriginalBody : Stmt :=
  .seq (.add cAddr cIndex cIndex) (.seq (.add cAddr cAddr cStart)
  (.seq (.load cValue cAddr) (.seq (.write cValue) (.seq (inc cAddr)
  (.seq (.load cValue cAddr) (.seq (.write cValue) (.write cZero)))))))

def paddedBypassBody : Stmt :=
  .seq (.write cSource) (.seq (.write cSink) (.write cOne))

/-- Write the exact cited-flow encoding; all original costs become zero. -/
def paddedEncode : Stmt := .seq paddedEncodeInit
  (.seq (forUp cIndex cArcs paddedOriginalBody) (forUp cIndex cPadding paddedBypassBody))

@[mk_iff] structure PaddedBuildBase {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    (padding : ℕ) (c : Config) : Prop where
  rNodes : c.reg cNodes = nodes
  rArcs : c.reg cArcs = arcs
  rSource : c.reg cSource = net.source.val
  rSink : c.reg cSink = net.sink.val
  rPadding : c.reg cPadding = padding
  rStart : c.reg cStart = 5
  rZero : c.reg cZero = 0
  rOne : c.reg cOne = 1
  memory : c.mem = (initial (edgeInput net padding)).mem

def paddedHeader {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs) (padding : ℕ) : List ℕ :=
  [nodes, arcs + padding, net.source.val, net.sink.val, padding]

def originalCodes {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs) (count : ℕ) : List ℕ :=
  ((List.finRange arcs).take count).flatMap fun i => [(net.tail i).val, (net.head i).val, 0]

private theorem initial_edgeInput_endpoints {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    (padding : ℕ) (i : Fin arcs) :
    (initial (edgeInput net padding)).mem (5 + 2 * i.val) = (net.tail i).val ∧
      (initial (edgeInput net padding)).mem (5 + (2 * i.val + 1)) = (net.head i).val := by
  have harr := arr_initial (edgeInput net padding)
  simp only [edgeInput, arr_cons] at harr
  have hpairs : Arr (initial (edgeInput net padding)).mem 5 (edgePairs net) := harr.2.2.2.2.2
  constructor
  · rw [hpairs.getD (by simp only [edgePairs_length]; omega)]
    exact (edgePairs_get net i).1
  · rw [hpairs.getD (by simp only [edgePairs_length]; omega)]
    exact (edgePairs_get net i).2

theorem paddedEncodeInit_spec {nodes arcs S : ℕ} (net : IndexedNetwork nodes arcs)
    (padding : ℕ) (hS : 5 ≤ S) :
    HTB S paddedEncodeInit (fun c => c = initial (edgeInput net padding))
      (fun c => PaddedBuildBase net padding c ∧ c.out = paddedHeader net padding) 19 := by
  refine HTB.run_le (by decide) (by decide) fun c hc => ?_
  subst c
  have hm : (run paddedEncodeInit (initial (edgeInput net padding))).mem =
      (initial (edgeInput net padding)).mem := run_mem_of_stores (by decide) rfl _
  refine ⟨by addr_ok [paddedEncodeInit], ?_⟩
  constructor
  · constructor
    all_goals first | exact hm | simp +decide [paddedEncodeInit, edgeInput, initial_mem]
  · simp +decide [paddedEncodeInit, edgeInput, initial_mem, paddedHeader]

def PaddedOriginalInv {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs) (padding j : ℕ)
    (c : Config) : Prop := PaddedBuildBase net padding c ∧
      c.out = paddedHeader net padding ++ originalCodes net j

def PaddedBypassInv {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs) (padding j : ℕ)
    (c : Config) : Prop := PaddedBuildBase net padding c ∧
      c.out = paddedHeader net padding ++ originalCodes net arcs ++
        encArcs (numberedNodeNumber net) (List.replicate j bypassArc)

private theorem PaddedBuildBase.run {nodes arcs : ℕ} {net : IndexedNetwork nodes arcs}
    {padding : ℕ} {c : Config} {program : Stmt} (hs : LoopFree program)
    (hst : stores program = false)
    (hw : ∀ r ∈ wregs program,
      r ∉ [cNodes, cArcs, cSource, cSink, cPadding, cStart, cZero, cOne])
    (h : PaddedBuildBase net padding c) : PaddedBuildBase net padding (RAM.run program c) := by
  have hr : ∀ r ∈ [cNodes, cArcs, cSource, cSink, cPadding, cStart, cZero, cOne],
      (RAM.run program c).reg r = c.reg r := by
    intro r hr
    exact run_reg_of_not_mem hs (fun hm => hw r hm hr) c
  constructor
  · rw [hr cNodes (by simp)]; exact h.rNodes
  · rw [hr cArcs (by simp)]; exact h.rArcs
  · rw [hr cSource (by simp)]; exact h.rSource
  · rw [hr cSink (by simp)]; exact h.rSink
  · rw [hr cPadding (by simp)]; exact h.rPadding
  · rw [hr cStart (by simp)]; exact h.rStart
  · rw [hr cZero (by simp)]; exact h.rZero
  · rw [hr cOne (by simp)]; exact h.rOne
  · rw [run_mem_of_stores hs hst]; exact h.memory

private theorem originalCodes_succ {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    (i : Fin arcs) : originalCodes net (i.val + 1) = originalCodes net i.val ++
      [(net.tail i).val, (net.head i).val, 0] := by
  have ht : (List.finRange arcs).take (i.val + 1) =
      (List.finRange arcs).take i.val ++ [i] := by
    rw [List.take_add_one, List.getElem?_eq_getElem (by simpa using i.isLt)]
    simp
  simp [originalCodes, ht]

theorem paddedOriginalBody_spec {nodes arcs S : ℕ} (net : IndexedNetwork nodes arcs)
    (padding j : ℕ) (hj : j < arcs) (hS : 2 * arcs + 5 ≤ S) :
    HTB S paddedOriginalBody
      (fun c => PaddedOriginalInv net padding j c ∧ c.reg cIndex = j ∧ c.reg cArcs = arcs)
      (fun c => PaddedOriginalInv net padding (j + 1) c ∧ c.reg cIndex = j ∧ c.reg cArcs = arcs) 10 := by
  refine HTB.run_le (by decide) (by decide) fun c ⟨⟨hb, ho⟩, hi, hm⟩ => ?_
  let i : Fin arcs := ⟨j, hj⟩
  have hends := initial_edgeInput_endpoints net padding i
  have ht : c.mem (j + j + 5) = (net.tail i).val := by
    rw [hb.memory]
    rw [show j + j + 5 = 5 + 2 * i.val by dsimp [i]; omega]
    exact hends.1
  have hh : c.mem (j + j + 5 + 1) = (net.head i).val := by
    rw [hb.memory]
    rw [show j + j + 5 + 1 = 5 + (2 * i.val + 1) by dsimp [i]; omega]
    exact hends.2
  refine ⟨by addr_ok [paddedOriginalBody, hi, hb.rStart],
    ⟨PaddedBuildBase.run (by decide) rfl (by decide) hb, ?_⟩, ?_, ?_⟩
  · have hs := originalCodes_succ net i
    simp only [i, Fin.val_mk] at hs
    simp +decide [paddedOriginalBody, run_inc, hi, hb.rStart, hb.rZero, ht, hh, ho, hs,
      List.append_assoc, i]
  · simp +decide [paddedOriginalBody, run_inc, hi]
  · simp +decide [paddedOriginalBody, run_inc, hm]

theorem paddedBypassBody_spec {nodes arcs S : ℕ} (net : IndexedNetwork nodes arcs)
    (padding j : ℕ) :
    HTB S paddedBypassBody
      (fun c => PaddedBypassInv net padding j c ∧ c.reg cIndex = j ∧ c.reg cPadding = padding)
      (fun c => PaddedBypassInv net padding (j + 1) c ∧ c.reg cIndex = j ∧
        c.reg cPadding = padding) 3 := by
  refine HTB.of_HT rfl <| HT.run_le (by decide) (by decide)
    fun c ⟨⟨hb, ho⟩, hi, hm⟩ => ?_
  refine ⟨⟨PaddedBuildBase.run (by decide) rfl (by decide) hb, ?_⟩, ?_, ?_⟩
  · simp +decide [paddedBypassBody, hb.rSource, hb.rSink, hb.rOne, ho,
      List.replicate_succ', encArcs_append, encArcs, bypassArc, numberedNodeNumber,
      List.append_assoc]
  · simp [paddedBypassBody, hi]
  · simp [paddedBypassBody, hm]

theorem originalCodes_all {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs) :
    originalCodes net arcs = encArcs (numberedNodeNumber net) (numberedArcs net) := by
  have ht : (List.finRange arcs).take arcs = List.finRange arcs := by
    apply List.take_of_length_le
    simp
  simp [originalCodes, ht, encArcs, numberedArcs, numberedArc, List.flatMap_map]

theorem paddedEncode_spec {nodes arcs S : ℕ} (net : IndexedNetwork nodes arcs)
    (padding : ℕ) (hS : 2 * arcs + 5 ≤ S) :
    HTB S paddedEncode (fun c => c = initial (edgeInput net padding))
      (fun c => c.out = netInput (numberedNodeNumber net) nodes padding
        (paddedMaxFlowNetwork net padding)) (40 * (arcs + padding + 1)) := by
  have horiginal := HTB.forUpC (S := S) (i := cIndex) (n := cArcs) (N := arcs)
    (body := paddedOriginalBody) (PaddedOriginalInv net padding) 10 (by decide) (by decide)
    (by decide) (fun j => by indep [PaddedOriginalInv, paddedBuildBase_iff])
    (fun j hj => paddedOriginalBody_spec net padding j hj hS)
  have hbypass := HTB.forUpC (S := S) (i := cIndex) (n := cPadding) (N := padding)
    (body := paddedBypassBody) (PaddedBypassInv net padding) 3 (by decide) (by decide)
    (by decide) (fun j => by indep [PaddedBypassInv, paddedBuildBase_iff])
    (fun j _ => paddedBypassBody_spec net padding j)
  have hfirst := (paddedEncodeInit_spec net padding (by omega)).seq
    (horiginal.pre fun c ⟨hb, ho⟩ => ⟨⟨hb, by simpa [originalCodes] using ho⟩, hb.rArcs⟩)
  have hsecond := hbypass.pre (P' := fun c => PaddedOriginalInv net padding arcs c ∧
      c.reg cIndex = arcs ∧ c.reg cArcs = arcs) fun c ⟨⟨hb, ho⟩, _, _⟩ =>
    ⟨⟨hb, by simpa [encArcs] using ho⟩, hb.rPadding⟩
  refine (HTB.assoc (hfirst.seq hsecond)).mono (fun _ h => h) (fun c ⟨⟨_, ho⟩, _, _⟩ => ?_) (by omega)
  rw [ho, originalCodes_all]
  simp [netInput, paddedMaxFlowNetwork, paddedHeader, encArcs_append, numberedNodeNumber,
    List.append_assoc]

/-- The encoder is one uniform RAM program, with linear time and input-only memory. -/
theorem paddedEncode_computes {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs) (padding : ℕ) :
    ∃ steps, ComputesIn paddedEncode (edgeInput net padding)
      (netInput (numberedNodeNumber net) nodes padding (paddedMaxFlowNetwork net padding))
      steps (2 * arcs + 5) ∧ steps ≤ 40 * (arcs + padding + 1) := by
  obtain ⟨steps, htime, hcomputes⟩ := (paddedEncode_spec net padding (S := 2 * arcs + 5)
    (by omega)).computesIn
  exact ⟨steps, hcomputes, htime⟩

/-- Length reader for the existing verified three-stage RAM composition. -/
def paddedInputLength : Stmt := .seq (.const xA 1) (.seq (.load xL xA)
  (.seq (.add xL xL xL) (.seq (.const xV 5) (.add xL xL xV))))

theorem paddedInputLength_spec {nodes arcs S : ℕ} (net : IndexedNetwork nodes arcs)
    (padding : ℕ) (hS : 2 ≤ S) :
    HTB S paddedInputLength (fun c => c = initial (edgeInput net padding))
      (LenPost (edgeInput net padding)) 5 := by
  refine HTB.run_le (by decide) (by decide) fun c hc => ?_
  subst c
  refine ⟨by addr_ok [paddedInputLength], ?_, ?_, ?_, ?_⟩
  · simp +decide [paddedInputLength, initial_mem, edgeInput, edgeInput_length]; omega
  · exact run_mem_of_stores (by decide) rfl _
  · exact run_out_of_writes (by decide) rfl _
  · intro r hr
    have hne : r ≠ xA ∧ r ≠ xL ∧ r ≠ xV := by
      rcases hr with hmod | hzero | hzero
      · unfold xA xL xV
        constructor
        · intro he; subst r; exact hmod (by decide)
        · constructor
          · intro he; subst r; exact hmod (by decide)
          · intro he; subst r; exact hmod (by decide)
      · subst r; decide
      · subst r; decide
    rw [run_reg_of_not_mem (by decide)
      (by simp [paddedInputLength, wregs, hne.1, hne.2.1, hne.2.2])]
    rfl

end STACS2027.Runtimes.Flow

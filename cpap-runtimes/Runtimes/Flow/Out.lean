module

public import Runtimes.Flow.Edges
public import Runtimes.Flow.Tri
import Mathlib.Tactic

/-!
# The output of the networks on the RAM

After the edge pass (`EdgesPost`), the output phases write the encoded network:

* `outSink_spec` (shared): the sink bundles — for the `r`-th edge `e` of `eList cs`,
  `CNT[r] = ϖ(e)` arcs `B + r → 1` with costs `0, 1, …` — appended to the output, for any
  numbering with `num sink = 1` and `num y_e = B + r`;
* `out4_spec`: the four-cycle network, `out = netEnc4 cs` (header, source arcs,
  opposing-pair arcs, sink bundles), within `C · (t + 1)` steps;
* `out3_spec`: the triangle network, `out = netEnc3 cs`.

The output phases do not store, and keep the registers `gT gNE gEID gCNT` (`OB cs k aE aC`: the
identifiers `EID` at `aE`, the counts `CNT` at `aC`); they read `EID` and `CNT` only, so they run
within any space bound `S` above both tables (`out4_specA`, `out3_specA`, for any layout: the
dictionary layout of the edge pass, `out4_spec`, `out3_spec`, with `S ≥ bOFF g cs k`, or the
layout of the sorting front end, `Runtimes/Flow/SortTri.lean`).
-/

@[expose] public section

namespace STACS2027.Runtimes.Flow

open STACS2027 STACS2027.RAM

/-- What the output phases keep: `t`, the number of edges, the identifiers and the counts. -/
@[mk_iff] structure OB (cs : List Cycle) (k aE aC : ℕ) (c : Config) : Prop where
  rt : c.reg gT = cs.length
  rne : c.reg gNE = (eList cs).length
  reid : c.reg gEID = aE
  rcnt : c.reg gCNT = aC
  meid : Tab c.mem aE (k * cs.length) (eid cs)
  mcnt : Tab c.mem aC (k * cs.length) (cntF cs (k * cs.length))

section out

variable {g : Graph} {cs : List Cycle} {k : ℕ} {S aE aC : ℕ}

/-- The tables read by the output phases fit below `S ≥ bOFF g cs k`. -/
theorem fits_out (hS : bOFF g cs k ≤ S) :
    bEID g cs k + k * cs.length ≤ S ∧ bCNT g cs k + k * cs.length ≤ S := by
  have h1 : bCNT g cs k = bEID g cs k + k * cs.length := rfl
  have h2 : bOFF g cs k = bCNT g cs k + k * cs.length := rfl
  omega

theorem OB.of_post {c : Config} (h : EdgesPost g cs k c) : OB cs k (bEID g cs k) (bCNT g cs k) c :=
  ⟨h.ga.rt, h.rne, h.reid, h.rcnt, h.meid, h.mcnt⟩

/-- A loop-free block that stores nothing and keeps `gT gNE gEID gCNT` keeps `OB`. -/
theorem OB.run {s : Stmt} (hs : LoopFree s) (hst : stores s = false)
    (hW : ∀ r ∈ wregs s, r ≠ gT ∧ r ≠ gNE ∧ r ≠ gEID ∧ r ≠ gCNT) {c : Config}
    (h : OB cs k aE aC c) : OB cs k aE aC (RAM.run s c) := by
  have hm := run_mem_of_stores hs hst c
  refine ⟨?_, ?_, ?_, ?_, hm ▸ h.meid, hm ▸ h.mcnt⟩
  · rw [run_reg_of_not_mem hs (fun h' => (hW _ h').1 rfl) c]; exact h.rt
  · rw [run_reg_of_not_mem hs (fun h' => (hW _ h').2.1 rfl) c]; exact h.rne
  · rw [run_reg_of_not_mem hs (fun h' => (hW _ h').2.2.1 rfl) c]; exact h.reid
  · rw [run_reg_of_not_mem hs (fun h' => (hW _ h').2.2.2 rfl) c]; exact h.rcnt

/-! ### Sums of counts -/

theorem sum_countP_eq {α : Type} (l : List α) (f : α → ℕ) (E : ℕ) :
    ∑ r ∈ Finset.range E, l.countP (fun x => f x = r) = l.countP (fun x => f x < E) := by
  induction E with
  | zero => simp
  | succ E ih =>
    rw [Finset.sum_range_succ, ih]
    clear ih
    induction l with
    | nil => simp
    | cons a l ih =>
      simp only [List.countP_cons, decide_eq_true_eq]
      by_cases h1 : f a < E
      · have h2 : f a < E + 1 := by omega
        have h3 : f a ≠ E := by omega
        simp only [h1, h2, h3, ↓reduceIte]; omega
      · by_cases h3 : f a = E
        · rw [h3]
          simp only [lt_irrefl, Nat.lt_succ_self, ↓reduceIte]
          omega
        · have h2 : ¬ f a < E + 1 := by omega
          simp only [h1, h2, h3, ↓reduceIte]; omega

theorem sum_cntF_le (n E : ℕ) : ∑ r ∈ Finset.range E, cntF cs n r ≤ n := by
  unfold cntF
  rw [sum_countP_eq (List.range n) (eid cs) E]
  exact List.countP_le_length.trans (by simp)

/-! ### The sink bundles -/

/-- The invariant of the inner loop of the sink bundles (edge `r`, after `j` arcs). -/
def InnerInv (cs : List Cycle) (k aE aC B : ℕ) (num : FlowNode → ℕ) (pre : List ℕ) (r j : ℕ)
    (c : Config) : Prop :=
  OB cs k aE aC c ∧ c.reg gEB = B ∧ c.reg sOne = 1 ∧ c.reg sE = B + r ∧ c.reg sR = r ∧
    c.out = pre ++ encArcs num (sinkLayer ((eList cs).take r) (wcount cs)) ++
      encArcs num ((List.range j).map fun j =>
        (⟨.edgeNode ((eList cs).getD r (0, 0)), .sink, j⟩ : Arc))

/-- The invariant of the sink bundles after `r` edges. -/
def SinkInv (cs : List Cycle) (k aE aC B : ℕ) (num : FlowNode → ℕ) (pre : List ℕ) (r : ℕ)
    (c : Config) : Prop :=
  OB cs k aE aC c ∧ c.reg gEB = B ∧ c.reg sOne = 1 ∧
    c.out = pre ++ encArcs num (sinkLayer ((eList cs).take r) (wcount cs))

theorem sinkInner_spec (B : ℕ) (num : FlowNode → ℕ) (hsink : num .sink = 1) (pre : List ℕ) {r : ℕ}
    (hr : r < (eList cs).length)
    (hnum : num (.edgeNode ((eList cs).getD r (0, 0))) = B + r) (w j : ℕ) :
    HT sinkInner (fun c => InnerInv cs k aE aC B num pre r j c ∧ c.reg sJ = j ∧ c.reg sC = w)
      (fun c => InnerInv cs k aE aC B num pre r (j + 1) c ∧ c.reg sJ = j ∧ c.reg sC = w) 3 := by
  refine HT.run_le (by decide) (by decide) fun c ⟨⟨hO, hB, h1, hE, hR, ho⟩, hJ, hC⟩ => ?_
  have _ := hr
  refine ⟨⟨OB.run (by decide) rfl (by decide) hO, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  all_goals simp only [sinkInner, run_seq', run_write, emit_reg, emit_out, hB, h1, hE, hR, hJ, hC]
  rw [ho, List.range_succ, List.map_append, encArcs_append, List.append_assoc, List.append_assoc,
    List.map_singleton]
  simp only [encArcs, List.flatMap_cons, List.flatMap_nil, List.append_nil, hnum, hsink]
  simp

theorem sinkBody_spec (hcs : ∀ c ∈ cs, IsCycle g k c) (hC : aC + k * cs.length ≤ S) (B : ℕ)
    (num : FlowNode → ℕ) (hsink : num .sink = 1) (pre : List ℕ)
    (hnum : ∀ r, r < (eList cs).length → num (.edgeNode ((eList cs).getD r (0, 0))) = B + r)
    (r : ℕ) (hr : r < (eList cs).length) :
    HTB S sinkBody (fun c => SinkInv cs k aE aC B num pre r c ∧ c.reg sR = r ∧ c.reg gNE = (eList cs).length)
      (fun c => SinkInv cs k aE aC B num pre (r + 1) c ∧ c.reg sR = r ∧ c.reg gNE = (eList cs).length)
      (7 * cntF cs (k * cs.length) r + 6) := by
  have hlen := length_occs hcs
  have hE := length_eList_le cs
  set w := cntF cs (k * cs.length) r with hw
  have hww : w = wcount cs ((eList cs).getD r (0, 0)) := by
    rw [hw, ← hlen]; exact cntF_final (fun c hc => (hcs c hc).edges_nodup) hr
  have hE' : (eList cs).length ≤ k * cs.length := hE.trans (length_occs hcs).le
  -- the load
  have h0 : HTB S (.seq (ld sC gCNT sR) (.add sE gEB sR))
      (fun c => SinkInv cs k aE aC B num pre r c ∧ c.reg sR = r ∧ c.reg gNE = (eList cs).length)
      (fun c => InnerInv cs k aE aC B num pre r 0 c ∧ c.reg sC = w) 3 :=
    HTB.of_HT_addrOK (by decide) (fun c ⟨⟨hO, _, _, _⟩, hR, _⟩ => by
      addr_ok [hO.rcnt, hR]) <| by
    refine HT.run_le (by decide) (by decide) fun c ⟨⟨hO, hB, h1, ho⟩, hR, _⟩ => ?_
    have hc : c.mem (c.reg gCNT + r) = w := by
      rw [hO.rcnt]; exact hO.mcnt.get (by omega)
    refine ⟨⟨OB.run (by decide) rfl (by decide) hO, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    all_goals simp +decide only [run_seq', run_ld, run_add, setReg_reg, setReg_out, ↓reduceIte,
      hB, h1, hR, hc]
    simp [ho, encArcs]
  have hl := HTB.forUpC (S := S) (i := sJ) (n := sC) (N := w) (body := sinkInner)
    (InnerInv cs k aE aC B num pre r) 3 (by decide) (by decide) (by decide)
    (fun j => by indep [InnerInv, oB_iff]) (fun j _ => HTB.of_HT rfl (sinkInner_spec B num hsink
      pre hr (hnum r hr) w j))
  refine HTB.assoc ((h0.seq hl).mono (fun _ h => h) (fun c ⟨⟨hO, hB, h1, _, hR, ho⟩, _, _⟩ =>
    ⟨⟨hO, hB, h1, ?_⟩, hR, hO.rne⟩) (by omega))
  rw [ho, sinkLayer_take_succ _ _ hr, encArcs_append, List.append_assoc, ← hww]

/-- **The sink bundles**: `ϖ(e)` arcs `B + r → 1` of costs `0, 1, …` for the `r`-th edge `e`,
appended to the output. -/
theorem outSink_spec (hcs : ∀ c ∈ cs, IsCycle g k c) (hC : aC + k * cs.length ≤ S) (B : ℕ)
    (num : FlowNode → ℕ) (hsink : num .sink = 1) (pre : List ℕ)
    (hnum : ∀ r, r < (eList cs).length → num (.edgeNode ((eList cs).getD r (0, 0))) = B + r) :
    HTB S outSink (fun c => OB cs k aE aC c ∧ c.reg gEB = B ∧ c.reg sOne = 1 ∧ c.out = pre)
      (fun c => OB cs k aE aC c ∧ c.reg gEB = B ∧ c.reg sOne = 1 ∧
        c.out = pre ++ encArcs num (sinkLayer (eList cs) (wcount cs)))
      (17 * (k * cs.length) + 3) := by
  have hl := HTB.forUp (S := S) (i := sR) (n := gNE) (N := (eList cs).length) (body := sinkBody)
    (SinkInv cs k aE aC B num pre) (fun r => 7 * cntF cs (k * cs.length) r + 6) (by decide) (by decide)
    (by decide) (fun j => by indep [SinkInv, oB_iff])
    (fun r hr => sinkBody_spec hcs hC B num hsink pre hnum r hr)
  have hsum := sum_cntF_le (cs := cs) (k * cs.length) (eList cs).length
  have hE : (eList cs).length ≤ k * cs.length := (length_eList_le cs).trans (length_occs hcs).le
  refine hl.mono (fun c ⟨hO, hB, h1, ho⟩ => ⟨⟨hO, hB, h1, by simp [ho, encArcs, sinkLayer]⟩, hO.rne⟩)
    (fun c ⟨⟨hO, hB, h1, ho⟩, _, _⟩ => ⟨hO, hB, h1, by rw [ho, List.take_length]⟩) ?_
  have : ∑ j ∈ Finset.range (eList cs).length, (7 * cntF cs (k * cs.length) j + 6 + 4) =
      7 * ∑ j ∈ Finset.range (eList cs).length, cntF cs (k * cs.length) j + 10 * (eList cs).length := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    simp; ring
  rw [this]; omega

/-! ### The four-cycle network -/

/-- The header of the encoded four-cycle network. -/
def hdr4L (cs : List Cycle) : List ℕ := [n4 cs, 10 * cs.length, 0, 1, 2 * cs.length]

/-- The state after the header (with the output so far). -/
def HInv4 (cs : List Cycle) (k aE aC : ℕ) (c : Config) : Prop :=
  OB cs k aE aC c ∧ c.reg gEB = 2 + 2 * cs.length ∧ c.reg sOne = 1 ∧ c.reg sZ0 = 0

theorem hdr4_spec :
    HT hdr4 (fun c => OB cs k aE aC c ∧ c.out = [])
      (fun c => HInv4 cs k aE aC c ∧ c.out = hdr4L cs) 14 := by
  refine HT.run_le (by decide) (by decide) fun c ⟨hO, ho⟩ =>
    ⟨⟨OB.run (by decide) rfl (by decide) hO, ?_, ?_, ?_⟩, ?_⟩
  all_goals simp +decide only [hdr4, run_seq', run_add, run_addc, run_const, run_write, setReg_reg,
    setReg_out, emit_reg, emit_out, ↓reduceIte, hO.rt, hO.rne, ho]
  · omega
  · simp [hdr4L, n4]; omega

/-- The invariant of the source arcs after `i` cycles. -/
def SrcInv4 (cs : List Cycle) (k aE aC : ℕ) (i : ℕ) (c : Config) : Prop :=
  HInv4 cs k aE aC c ∧ c.reg sA = 2 + 2 * i ∧
    c.out = hdr4L cs ++ encArcs (num4 cs) (sourceLayer i)

theorem srcBody4_spec (i : ℕ) :
    HT srcBody4 (fun c => SrcInv4 cs k aE aC i c ∧ c.reg sI = i ∧ c.reg gT = cs.length)
      (fun c => SrcInv4 cs k aE aC (i + 1) c ∧ c.reg sI = i ∧ c.reg gT = cs.length) 12 := by
  refine HT.run_le (by decide) (by decide) fun c ⟨⟨⟨hO, hB, h1, h0⟩, hA, ho⟩, hI, hT⟩ => ?_
  refine ⟨⟨⟨OB.run (by decide) rfl (by decide) hO, ?_, ?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩
  all_goals simp +decide only [srcBody4, run_seq', run_write, run_inc (show sA ≠ rT by decide),
    setReg_reg, setReg_out, emit_reg, emit_out, ↓reduceIte, hB, h1, h0, hA, hI, hT, ho]
  · omega
  · rw [sourceLayer_succ, encArcs_append, encArcs_srcChunk4]
    simp only [List.append_assoc, List.cons_append, List.nil_append]

theorem src4_spec :
    HT src4 (fun c => HInv4 cs k aE aC c ∧ c.out = hdr4L cs)
      (fun c => SrcInv4 cs k aE aC cs.length c) (16 * cs.length + 4) := by
  have h0 : HT (.const sA 2) (fun c => HInv4 cs k aE aC c ∧ c.out = hdr4L cs)
      (fun c => SrcInv4 cs k aE aC 0 c ∧ c.reg gT = cs.length) 1 := by
    refine HT.run_le (by decide) (by decide) fun c ⟨hH, ho⟩ => ?_
    refine ⟨⟨(show Indep [sA] (HInv4 cs k aE aC) by indep [HInv4, oB_iff]).setReg (by decide) _ hH,
      by simp, by simp [ho, sourceLayer, encArcs]⟩, by simp +decide [hH.1.rt]⟩
  have hl := HT.forUpC (i := sI) (n := gT) (N := cs.length) (body := srcBody4)
    (SrcInv4 cs k aE aC) 12 (by decide) (by decide) (by decide)
    (fun j => by indep [SrcInv4, HInv4, oB_iff]) (fun i _ => srcBody4_spec i)
  exact (h0.seq hl).mono (fun _ h => h) (fun _ h => h.1) (by omega)

/-- The output after the source arcs and the first `i` cycles' opposing-pair arcs. -/
def PairInv4 (cs : List Cycle) (k aE aC : ℕ) (i : ℕ) (c : Config) : Prop :=
  HInv4 cs k aE aC c ∧ c.reg sA = 2 + 2 * i ∧ c.reg sBase = i * 4 ∧
    c.out = hdr4L cs ++ encArcs (num4 cs) (sourceLayer cs.length) ++
      encArcs (num4 cs) (pairLayer i (cyc cs))

theorem pairBody4_spec (hcs : ∀ c ∈ cs, IsCycle g 4 c) (hE : aE + 4 * cs.length ≤ S) (i : ℕ)
    (hi : i < cs.length) :
    HTB S pairBody4 (fun c => PairInv4 cs 4 aE aC i c ∧ c.reg sI = i ∧ c.reg gT = cs.length)
      (fun c => PairInv4 cs 4 aE aC (i + 1) c ∧ c.reg sI = i ∧ c.reg gT = cs.length) 38 :=
    HTB.of_HT_addrOK (by decide) (fun c ⟨⟨⟨hO, _⟩, _, hBase, _⟩, _⟩ => by
      addr_ok [pairBody4, pairArc, hBase, hO.reid]) <| by
  refine HT.run_le (by decide) (by decide) fun c ⟨⟨⟨hO, hB, h1, h0⟩, hA, hBase, ho⟩, hI, hT⟩ => ?_
  have e0 : c.mem (aE + i * 4) = eid cs (i * 4 + 0) :=
    hO.meid.get (occ_lt (k := 4) hi (j := 0) (by omega))
  have e1 : c.mem (aE + (i * 4 + 1)) = eid cs (i * 4 + 1) :=
    hO.meid.get (occ_lt (k := 4) hi (j := 1) (by omega))
  have e2 : c.mem (aE + (i * 4 + 2)) = eid cs (i * 4 + 2) :=
    hO.meid.get (occ_lt (k := 4) hi (j := 2) (by omega))
  have e3 : c.mem (aE + (i * 4 + 3)) = eid cs (i * 4 + 3) :=
    hO.meid.get (occ_lt (k := 4) hi (j := 3) (by omega))
  refine ⟨⟨⟨OB.run (by decide) rfl (by decide) hO, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_, ?_⟩
  all_goals simp +decide only [pairBody4, pairArc, run_seq', run_addc (show sBase ≠ rT by decide),
    run_ld, run_add, run_write, run_inc (show sA ≠ rT by decide),
    setReg_reg, setReg_mem, setReg_out, emit_reg, emit_mem,
    emit_out, ↓reduceIte, hBase, hO.reid, hB, h1, h0, hA, hI, hT, Nat.add_zero, e0, e1, e2, e3]
  · omega
  · ring
  · rw [ho, pairLayer_succ, encArcs_append, pairChunk4 hcs hi]
    rw [encArcs_pairChunk4]
    simp only [List.append_assoc, List.cons_append, List.nil_append]

theorem pair4_spec (hcs : ∀ c ∈ cs, IsCycle g 4 c) (hE : aE + 4 * cs.length ≤ S) :
    HTB S pair4 (fun c => SrcInv4 cs 4 aE aC cs.length c)
      (fun c => PairInv4 cs 4 aE aC cs.length c) (42 * cs.length + 5) := by
  have h0 : HTB S (.seq (.const sA 2) (.const sBase 0)) (fun c => SrcInv4 cs 4 aE aC cs.length c)
      (fun c => PairInv4 cs 4 aE aC 0 c ∧ c.reg gT = cs.length) 2 := HTB.of_HT rfl <| by
    refine HT.run_le (by decide) (by decide) fun c ⟨hH, _, ho⟩ => ?_
    have hH' : HInv4 cs 4 aE aC (RAM.run (.seq (.const sA 2) (.const sBase 0)) c) :=
      (show Indep [sA, sBase] (HInv4 cs 4 aE aC) by indep [HInv4, oB_iff]) c _
        (agree_run (by decide) rfl rfl (by decide) c) hH
    refine ⟨⟨hH', by simp +decide, by simp +decide, ?_⟩, by simp +decide [hH.1.rt]⟩
    simp [ho, pairLayer, encArcs]
  have hl := HTB.forUpC (S := S) (i := sI) (n := gT) (N := cs.length) (body := pairBody4)
    (PairInv4 cs 4 aE aC) 38 (by decide) (by decide) (by decide)
    (fun j => by indep [PairInv4, HInv4, oB_iff]) (fun i hi => pairBody4_spec hcs hE i hi)
  exact HTB.assoc ((h0.seq hl).mono (fun _ h => h) (fun _ h => h.1) (by omega))

/-- **The output of the four-cycle network**, for identifiers at `aE` and counts at `aC`:
`out4` writes the encoded network `netEnc4 cs`, accessing only `EID` and `CNT`. -/
theorem out4_specA (hcs : ∀ c ∈ cs, IsCycle g 4 c) (hE : aE + 4 * cs.length ≤ S)
    (hC : aC + 4 * cs.length ≤ S) :
    HTB S out4 (fun c => OB cs 4 aE aC c ∧ c.out = []) (fun c => c.out = netEnc4 cs)
      (130 * cs.length + 30) := by
  have h1 : HTB S hdr4 (fun c => OB cs 4 aE aC c ∧ c.out = [])
      (fun c => HInv4 cs 4 aE aC c ∧ c.out = hdr4L cs) 14 :=
    HTB.of_HT rfl hdr4_spec
  have h4 := outSink_spec (aE := aE) hcs hC (2 + 2 * cs.length) (num4 cs) rfl
    (hdr4L cs ++ encArcs (num4 cs) (sourceLayer cs.length) ++
      encArcs (num4 cs) (pairLayer cs.length (cyc cs))) (fun r hr => num4_eList hr)
  refine (h1.seq ((HTB.of_HT rfl src4_spec).seq ((pair4_spec hcs hE).seq
    (h4.pre fun c ⟨⟨hO, hB, h1, _⟩, _, _, ho⟩ => ⟨hO, hB, h1, ho⟩)))).mono (fun _ h => h)
    (fun c ⟨_, _, _, ho⟩ => ?_) (by omega)
  rw [ho, netEnc4, netInput, length_net4 hcs, net4, encArcs_append, encArcs_append]
  simp [hdr4L]

/-- **The output of the four-cycle network**: after the edge pass, `out4` writes the encoded
network `netEnc4 cs`. -/
theorem out4_spec (hcs : ∀ c ∈ cs, IsCycle g 4 c) (hS : bOFF g cs 4 ≤ S) :
    HTB S out4 (EdgesPost g cs 4) (fun c => c.out = netEnc4 cs) (130 * cs.length + 30) :=
  (out4_specA hcs (fits_out hS).1 (fits_out hS).2).pre fun _ h => ⟨OB.of_post h, h.rout⟩

/-! ### The triangle network -/

/-- The header of the encoded triangle network. -/
def hdr3L (cs : List Cycle) : List ℕ := [n3 cs, 7 * cs.length, 0, 1, cs.length]

/-- The state after the header. -/
def HInv3 (cs : List Cycle) (k aE aC : ℕ) (c : Config) : Prop :=
  OB cs k aE aC c ∧ c.reg gEB = 2 + cs.length ∧ c.reg sOne = 1 ∧ c.reg sZ0 = 0

theorem hdr3_spec :
    HT hdr3 (fun c => OB cs k aE aC c ∧ c.out = [])
      (fun c => HInv3 cs k aE aC c ∧ c.out = hdr3L cs) 14 := by
  refine HT.run_le (by decide) (by decide) fun c ⟨hO, ho⟩ =>
    ⟨⟨OB.run (by decide) rfl (by decide) hO, ?_, ?_, ?_⟩, ?_⟩
  all_goals simp +decide only [hdr3, run_seq', run_add, run_addc, run_const, run_write, setReg_reg,
    setReg_out, emit_reg, emit_out, ↓reduceIte, hO.rt, hO.rne, ho]
  · omega
  · simp [hdr3L, n3]; omega

/-- The invariant of the source arcs after `i` triangles. -/
def SrcInv3 (cs : List Cycle) (k aE aC : ℕ) (i : ℕ) (c : Config) : Prop :=
  HInv3 cs k aE aC c ∧ c.reg sA = 2 + i ∧ c.out = hdr3L cs ++ encArcs (num3 cs) (triangleSourceLayer i)

theorem srcBody3_spec (i : ℕ) :
    HT srcBody3 (fun c => SrcInv3 cs k aE aC i c ∧ c.reg sI = i ∧ c.reg gT = cs.length)
      (fun c => SrcInv3 cs k aE aC (i + 1) c ∧ c.reg sI = i ∧ c.reg gT = cs.length) 5 := by
  refine HT.run_le (by decide) (by decide) fun c ⟨⟨⟨hO, hB, h1, h0⟩, hA, ho⟩, hI, hT⟩ => ?_
  refine ⟨⟨⟨OB.run (by decide) rfl (by decide) hO, ?_, ?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩
  all_goals simp +decide only [srcBody3, run_seq', run_write, run_inc (show sA ≠ rT by decide),
    setReg_reg, setReg_out, emit_reg, emit_out, ↓reduceIte, hB, h1, h0, hA, hI, hT, ho]
  · omega
  · rw [triangleSourceLayer_succ, encArcs_append, encArcs_srcChunk3]
    simp only [List.append_assoc, List.cons_append, List.nil_append]

theorem src3_spec :
    HT src3 (fun c => HInv3 cs k aE aC c ∧ c.out = hdr3L cs)
      (fun c => SrcInv3 cs k aE aC cs.length c) (9 * cs.length + 4) := by
  have h0 : HT (.const sA 2) (fun c => HInv3 cs k aE aC c ∧ c.out = hdr3L cs)
      (fun c => SrcInv3 cs k aE aC 0 c ∧ c.reg gT = cs.length) 1 := by
    refine HT.run_le (by decide) (by decide) fun c ⟨hH, ho⟩ => ?_
    refine ⟨⟨(show Indep [sA] (HInv3 cs k aE aC) by indep [HInv3, oB_iff]).setReg (by decide) _ hH,
      by simp, by simp [ho, triangleSourceLayer, encArcs]⟩, by simp +decide [hH.1.rt]⟩
  have hl := HT.forUpC (i := sI) (n := gT) (N := cs.length) (body := srcBody3)
    (SrcInv3 cs k aE aC) 5 (by decide) (by decide) (by decide)
    (fun j => by indep [SrcInv3, HInv3, oB_iff]) (fun i _ => srcBody3_spec i)
  exact (h0.seq hl).mono (fun _ h => h) (fun _ h => h.1) (by omega)

/-- The output after the source arcs and the arcs of the first `i` triangles. -/
def TriInv3 (cs : List Cycle) (k aE aC : ℕ) (i : ℕ) (c : Config) : Prop :=
  HInv3 cs k aE aC c ∧ c.reg sA = 2 + i ∧ c.reg sBase = i * 3 ∧
    c.out = hdr3L cs ++ encArcs (num3 cs) (triangleSourceLayer cs.length) ++
      encArcs (num3 cs) (triangleLayer i (cyc cs))

theorem triBody3_spec (hcs : ∀ c ∈ cs, IsCycle g 3 c) (hE : aE + 3 * cs.length ≤ S) (i : ℕ)
    (hi : i < cs.length) :
    HTB S triBody3 (fun c => TriInv3 cs 3 aE aC i c ∧ c.reg sI = i ∧ c.reg gT = cs.length)
      (fun c => TriInv3 cs 3 aE aC (i + 1) c ∧ c.reg sI = i ∧ c.reg gT = cs.length) 28 :=
    HTB.of_HT_addrOK (by decide) (fun c ⟨⟨⟨hO, _⟩, _, hBase, _⟩, _⟩ => by
      addr_ok [triBody3, pairArc, hBase, hO.reid]) <| by
  refine HT.run_le (by decide) (by decide) fun c ⟨⟨⟨hO, hB, h1, h0⟩, hA, hBase, ho⟩, hI, hT⟩ => ?_
  have e0 : c.mem (aE + i * 3) = eid cs (i * 3 + 0) :=
    hO.meid.get (occ_lt (k := 3) hi (j := 0) (by omega))
  have e1 : c.mem (aE + (i * 3 + 1)) = eid cs (i * 3 + 1) :=
    hO.meid.get (occ_lt (k := 3) hi (j := 1) (by omega))
  have e2 : c.mem (aE + (i * 3 + 2)) = eid cs (i * 3 + 2) :=
    hO.meid.get (occ_lt (k := 3) hi (j := 2) (by omega))
  refine ⟨⟨⟨OB.run (by decide) rfl (by decide) hO, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_, ?_⟩
  all_goals simp +decide only [triBody3, pairArc, run_seq', run_addc (show sBase ≠ rT by decide),
    run_ld, run_add, run_write, run_inc (show sA ≠ rT by decide),
    setReg_reg, setReg_mem, setReg_out, emit_reg, emit_mem,
    emit_out, ↓reduceIte, hBase, hO.reid, hB, h1, h0, hA, hI, hT, Nat.add_zero, e0, e1, e2]
  · omega
  · ring
  · rw [ho, triangleLayer_succ, encArcs_append, triChunk3 hcs hi, encArcs_triChunk3]
    simp only [List.append_assoc, List.cons_append, List.nil_append]

theorem tri3_spec (hcs : ∀ c ∈ cs, IsCycle g 3 c) (hE : aE + 3 * cs.length ≤ S) :
    HTB S tri3 (fun c => SrcInv3 cs 3 aE aC cs.length c)
      (fun c => TriInv3 cs 3 aE aC cs.length c) (32 * cs.length + 5) := by
  have h0 : HTB S (.seq (.const sA 2) (.const sBase 0)) (fun c => SrcInv3 cs 3 aE aC cs.length c)
      (fun c => TriInv3 cs 3 aE aC 0 c ∧ c.reg gT = cs.length) 2 := HTB.of_HT rfl <| by
    refine HT.run_le (by decide) (by decide) fun c ⟨hH, _, ho⟩ => ?_
    have hH' : HInv3 cs 3 aE aC (RAM.run (.seq (.const sA 2) (.const sBase 0)) c) :=
      (show Indep [sA, sBase] (HInv3 cs 3 aE aC) by indep [HInv3, oB_iff]) c _
        (agree_run (by decide) rfl rfl (by decide) c) hH
    refine ⟨⟨hH', by simp +decide, by simp +decide, ?_⟩, by simp +decide [hH.1.rt]⟩
    simp [ho, triangleLayer, encArcs]
  have hl := HTB.forUpC (S := S) (i := sI) (n := gT) (N := cs.length) (body := triBody3)
    (TriInv3 cs 3 aE aC) 28 (by decide) (by decide) (by decide)
    (fun j => by indep [TriInv3, HInv3, oB_iff]) (fun i hi => triBody3_spec hcs hE i hi)
  exact HTB.assoc ((h0.seq hl).mono (fun _ h => h) (fun _ h => h.1) (by omega))

/-- **The output of the triangle network**, for identifiers at `aE` and counts at `aC`:
`out3` writes `netEnc3 cs`, accessing only `EID` and `CNT` (the layout of the sorting front end
as well as that of the dictionary). -/
theorem out3_specA (hcs : ∀ c ∈ cs, IsCycle g 3 c) (hE : aE + 3 * cs.length ≤ S)
    (hC : aC + 3 * cs.length ≤ S) :
    HTB S out3 (fun c => OB cs 3 aE aC c ∧ c.out = []) (fun c => c.out = netEnc3 cs)
      (100 * cs.length + 30) := by
  have h1 : HTB S hdr3 (fun c => OB cs 3 aE aC c ∧ c.out = [])
      (fun c => HInv3 cs 3 aE aC c ∧ c.out = hdr3L cs) 14 :=
    HTB.of_HT rfl hdr3_spec
  have h4 := outSink_spec (aE := aE) hcs hC (2 + cs.length) (num3 cs) rfl
    (hdr3L cs ++ encArcs (num3 cs) (triangleSourceLayer cs.length) ++
      encArcs (num3 cs) (triangleLayer cs.length (cyc cs))) (fun r hr => num3_eList hr)
  refine (h1.seq ((HTB.of_HT rfl src3_spec).seq ((tri3_spec hcs hE).seq
    (h4.pre fun c ⟨⟨hO, hB, h1, _⟩, _, _, ho⟩ => ⟨hO, hB, h1, ho⟩)))).mono (fun _ h => h)
    (fun c ⟨_, _, _, ho⟩ => ?_) (by omega)
  rw [ho, netEnc3, netInput, length_net3 hcs, net3, encArcs_append, encArcs_append]
  simp [hdr3L]

/-- **The output of the triangle network**: after the edge pass, `out3` writes `netEnc3 cs`. -/
theorem out3_spec (hcs : ∀ c ∈ cs, IsCycle g 3 c) (hS : bOFF g cs 3 ≤ S) :
    HTB S out3 (EdgesPost g cs 3) (fun c => c.out = netEnc3 cs) (100 * cs.length + 30) :=
  (out3_specA hcs (fits_out hS).1 (fits_out hS).2).pre fun _ h => ⟨OB.of_post h, h.rout⟩

end out

end STACS2027.Runtimes.Flow

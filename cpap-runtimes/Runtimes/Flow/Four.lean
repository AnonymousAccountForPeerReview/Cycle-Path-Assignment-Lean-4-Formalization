module

public import Runtimes.Flow.Solver
public import NPHardness.AssignmentFamilies
import Mathlib.Tactic

/-!
# The four-cycle network of a list of cycles (Theorem 2, permutation-robust)

Section 3 builds the network `fourCycleNetwork g` from the enumeration `cycles g 4`. A RAM
program receives the cycles from an enumeration algorithm, which may list them in another
order: any `cs` with `cs.Perm (cycles g 4)`. This file builds the same network from any list
`cs` of simple four-cycles of `g` (`net4 cs`, with `net4 (cycles g 4) = fourCycleNetwork g`,
`net4_cycles`) and proves Section 3's correspondence for it, in the form used by the machines:

* `flow_of_assignment4`: every assignment `ps` of `cs` induces an integral flow of value `2t` and
  cost `cost ps` (as Section 3's `flow_of_assignment`);
* `assignment_of_flow4`: from every integral flow of value `2t`, the assignment **read off**
  the flow — for cycle `C_i`, the option `optionIndex q₀ q₁` where `q₀`, `q₁` tell whether the
  arcs `x_{C_i,{e₁,e₃}} → y_{e₃}` and `x_{C_i,{e₂,e₄}} → y_{e₄}` carry flow (`readOff4`) — is an
  assignment of cost at most the cost of the flow (Section 3's `assignment_of_flow` proves the
  existence of such an assignment; the read-off is the one of its proof);
* `optimal_of_minFlow4`: the read-off of a minimum-cost flow of value `2t` is an optimal
  assignment of `cs`; with `cs.Perm (cycles g 4)`, its cost is the optimum of `CPAP(G, 4)`
  (`OptCost`, `optCost_of_optimal`).

The proofs follow Section 3 (`Tractability/FlowEquivalence.lean`), with `cycles g 4` replaced by
`cs` and the generic layers `sourceLayer`, `pairLayer`, `sinkLayer` of
`Tractability/NetworkCounts.lean`.
-/

@[expose] public section

namespace STACS2027.Runtimes.Flow

open STACS2027

/-! ### Lists of cycles -/

/-- `C_i`, the `i`-th cycle of the list (`[]` if there is none). -/
abbrev cyc (cs : List Cycle) (i : ℕ) : Cycle := cs.getD i []

/-- The occurrences of edges on the cycles: the edges of `C_0`, then those of `C_1`, … -/
def occs (cs : List Cycle) : List Edge := cs.flatMap cycleEdges

/-- The edges lying on a cycle of the list, each once, in order of first occurrence (Section 3's
`cycleEdgeList` for `cs = cycles g 4`, `triangleEdgeList` for `cs = cycles g 3`). -/
def eList (cs : List Cycle) : List Edge := (occs cs).eraseDups

/-- `ϖ(e)`: the number of cycles of the list containing `e` (Section 3's `cycleCount`,
`triangleCount`). -/
def wcount (cs : List Cycle) (e : Edge) : ℕ := cs.countP fun c => (cycleEdges c).contains e

theorem cyc_mem {cs : List Cycle} {i : ℕ} (hi : i < cs.length) : cyc cs i ∈ cs := by
  rw [cyc, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  exact List.getElem_mem hi

theorem eList_nodup (cs : List Cycle) : (eList cs).Nodup := nodup_eraseDups _

theorem mem_eList {cs : List Cycle} {e : Edge} : e ∈ eList cs ↔ ∃ c ∈ cs, e ∈ cycleEdges c := by
  simp [eList, occs, List.mem_eraseDups, List.mem_flatMap]

theorem mem_eList_occs {cs : List Cycle} {e : Edge} : e ∈ eList cs ↔ e ∈ occs cs := List.mem_eraseDups

theorem wcount_eq_countP (cs : List Cycle) (e : Edge) :
    wcount cs e = cs.countP fun c => decide (e ∈ cycleEdges c) := by
  rw [wcount]
  apply List.countP_congr
  intro c _
  simp

theorem wcount_eq_sum (cs : List Cycle) (e : Edge) :
    wcount cs e = ((List.range cs.length).map fun i =>
      if e ∈ cycleEdges (cyc cs i) then 1 else 0).sum := by
  rw [wcount_eq_countP, countP_eq_sum_range _ []]
  congr 1
  apply List.map_congr_left
  intro i _
  simp

theorem wcount_le (cs : List Cycle) (e : Edge) : wcount cs e ≤ cs.length := by
  rw [wcount]; exact List.countP_le_length

/-- `ϖ(e)` is the number of occurrences of `e`, when no cycle repeats an edge. -/
theorem wcount_eq_count {cs : List Cycle} (hn : ∀ c ∈ cs, (cycleEdges c).Nodup) (e : Edge) :
    wcount cs e = (occs cs).count e := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    have hc := hn c (by simp)
    have ih' := ih (fun d hd => hn d (by simp [hd]))
    simp only [wcount, occs] at ih' ⊢
    rw [List.countP_cons, List.flatMap_cons, List.count_append, ih']
    by_cases he : e ∈ cycleEdges c
    · simp [he, hc.count_of_mem he]; omega
    · simp [he, List.count_eq_zero.mpr he]

theorem sum_wcount {cs : List Cycle} (hn : ∀ c ∈ cs, (cycleEdges c).Nodup) :
    ((eList cs).map (wcount cs)).sum = (occs cs).length := by
  have h := sum_counts (eList cs) (occs cs) (fun _ => 1) (eList_nodup cs)
    (fun e he => mem_eList_occs.mpr he)
  simp only [Nat.mul_one, List.map_const', List.sum_replicate, smul_eq_mul] at h
  rw [← h]
  congr 1
  apply List.map_congr_left
  intro e _
  exact wcount_eq_count hn e

theorem length_eList_le (cs : List Cycle) : (eList cs).length ≤ (occs cs).length :=
  length_eraseDups_le _

/-- The occurrences of a list of `k`-cycles: `k` per cycle. -/
theorem length_occs {g : Graph} {k : ℕ} {cs : List Cycle} (hcs : ∀ c ∈ cs, IsCycle g k c) :
    (occs cs).length = k * cs.length := by
  induction cs with
  | nil => simp [occs]
  | cons c cs ih =>
    rw [occs, List.flatMap_cons, List.length_append, ← occs, ih (fun d hd => hcs d (by simp [hd])),
      (hcs c (by simp)).edge_length]
    simp only [List.length_cons]; ring

theorem eraseDups_perm {L L' : List Edge} (h : L.Perm L') : L.eraseDups.Perm L'.eraseDups :=
  (List.perm_ext_iff_of_nodup (nodup_eraseDups _) (nodup_eraseDups _)).mpr fun e => by
    simp only [List.mem_eraseDups]; exact h.mem_iff

/-! ### Assignments of a list of cycles -/

theorem validChoices_nil_left {ps : List (List Edge)} (h : ValidChoices [] ps) : ps = [] := by
  cases ps with
  | nil => rfl
  | cons _ _ => exact False.elim h

theorem validChoices_cons {o : List (List Edge)} {os : List (List (List Edge))} {p : List Edge}
    {ps : List (List Edge)} : ValidChoices (o :: os) (p :: ps) ↔ p ∈ o ∧ ValidChoices os ps :=
  Iff.rfl

/-- Assignments are transported along a permutation of the cycles. -/
theorem validChoices_perm {cs ds : List Cycle} (h : cs.Perm ds) :
    ∀ {ps : List (List Edge)}, ValidChoices (cs.map selectedOptions) ps →
      ∃ qs, ValidChoices (ds.map selectedOptions) qs ∧ ps.Perm qs := by
  induction h with
  | nil =>
    intro ps hv
    exact ⟨[], trivial, by rw [validChoices_nil_left hv]⟩
  | cons x _ ih =>
    intro ps hv
    cases ps with
    | nil => exact False.elim hv
    | cons p ps =>
      obtain ⟨hp, hv⟩ := validChoices_cons.mp hv
      obtain ⟨qs, hq, hperm⟩ := ih hv
      exact ⟨p :: qs, validChoices_cons.mpr ⟨hp, hq⟩, hperm.cons p⟩
  | swap x y l =>
    intro ps hv
    match ps, hv with
    | p :: q :: r, hv =>
      obtain ⟨hp, hv⟩ := validChoices_cons.mp hv
      obtain ⟨hq, hr⟩ := validChoices_cons.mp hv
      exact ⟨q :: p :: r, validChoices_cons.mpr ⟨hq, validChoices_cons.mpr ⟨hp, hr⟩⟩,
        List.Perm.swap q p r⟩
  | trans _ _ ih₁ ih₂ =>
    intro ps hv
    obtain ⟨qs, hq, hp₁⟩ := ih₁ hv
    obtain ⟨rs, hr, hp₂⟩ := ih₂ hq
    exact ⟨rs, hr, hp₁.trans hp₂⟩

/-- `CPAP(G, k)` through any permutation `cs` of the enumerated cycles. -/
theorem hasAssignment_iff_perm {g : Graph} {k : ℕ} {cs : List Cycle} (h : cs.Perm (cycles g k))
    (budget : ℕ) : HasAssignment g k budget ↔
      ∃ ps, ValidChoices (cs.map selectedOptions) ps ∧ cost ps ≤ budget := by
  constructor
  · rintro ⟨ps, hv, hc⟩
    obtain ⟨qs, hq, hperm⟩ := validChoices_perm h.symm hv
    exact ⟨qs, hq, by rw [← cost_perm hperm]; exact hc⟩
  · rintro ⟨ps, hv, hc⟩
    obtain ⟨qs, hq, hperm⟩ := validChoices_perm h hv
    exact ⟨qs, hq, by rw [← cost_perm hperm]; exact hc⟩

/-- `C` is the optimum of `CPAP(G, k)`: the least budget admitting an assignment. -/
def OptCost (g : Graph) (k C : ℕ) : Prop :=
  HasAssignment g k C ∧ ∀ B, HasAssignment g k B → C ≤ B

/-- An optimal assignment of a permutation of the enumerated cycles has the optimal cost. -/
theorem optCost_of_optimal {g : Graph} {k : ℕ} {cs : List Cycle} (h : cs.Perm (cycles g k))
    {ps : List (List Edge)} (hv : ValidChoices (cs.map selectedOptions) ps)
    (hopt : ∀ ps', ValidChoices (cs.map selectedOptions) ps' → cost ps ≤ cost ps') :
    OptCost g k (cost ps) :=
  ⟨(hasAssignment_iff_perm h _).mpr ⟨ps, hv, le_rfl⟩, fun B hB => by
    obtain ⟨ps', hv', hc'⟩ := (hasAssignment_iff_perm h B).mp hB
    exact (hopt ps' hv').trans hc'⟩

theorem zipWith_selected (cs : List Cycle) (f : ℕ → ℕ) :
    List.zipWith selected cs ((List.range cs.length).map f) =
      (List.range cs.length).map fun i => selected (cyc cs i) (f i) := by
  apply List.ext_getElem
  · simp
  · intro n h1 h2
    simp only [List.getElem_zipWith, List.getElem_map, List.getElem_range, cyc]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp at h1; omega)]
    rfl

/-! ### The network -/

/-- **The four-cycle network of the list `cs`**: Section 3's three layers for the cycles of
`cs` (source arcs, opposing-pair arcs, sink bundles), in this order. -/
def net4 (cs : List Cycle) : List Arc :=
  sourceLayer cs.length ++ pairLayer cs.length (cyc cs) ++ sinkLayer (eList cs) (wcount cs)

/-- On the enumerated cycles it is Section 3's network `𝓕`. -/
theorem net4_cycles (g : Graph) : net4 (cycles g 4) = fourCycleNetwork g := rfl

section four

variable {g : Graph} {cs : List Cycle}

theorem cyc_isCycle (hcs : ∀ c ∈ cs, IsCycle g 4 c) {i : ℕ} (hi : i < cs.length) :
    IsCycle g 4 (cyc cs i) := hcs _ (cyc_mem hi)

theorem opp_nodup (hcs : ∀ c ∈ cs, IsCycle g 4 c) {i : ℕ} (hi : i < cs.length) (p : Bool) :
    (opposingPair (cyc cs i) p).Nodup := by
  obtain ⟨a, b, u, v, hc, hab, hau, hav, hbu, hbv, huv⟩ := fourCycle_shape (cyc_isCycle hcs hi)
  rw [hc]
  exact opposingPair_nodup hab hau hav hbu hbv huv p

theorem net4_nodup (hcs : ∀ c ∈ cs, IsCycle g 4 c) : (net4 cs).Nodup := by
  rw [net4, List.nodup_append, List.nodup_append]
  refine ⟨⟨sourceLayer_nodup _, pairLayer_nodup _ _ (fun i hi p => opp_nodup hcs hi p), ?_⟩,
    sinkLayer_nodup _ (eList_nodup cs) _, ?_⟩
  · intro a ha b hb
    obtain ⟨i, p, _, rfl⟩ := (mem_sourceLayer _ a).mp ha
    obtain ⟨i', p', e, _, _, rfl⟩ := (mem_pairLayer _ _ b).mp hb
    simp
  · intro a ha b hb
    obtain ⟨e, j, _, _, rfl⟩ := (mem_sinkLayer _ _ b).mp hb
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨i, p, _, rfl⟩ := (mem_sourceLayer _ a).mp ha
      simp
    · obtain ⟨i', p', e', _, _, rfl⟩ := (mem_pairLayer _ _ a).mp ha
      simp

/-- `10t` arcs. -/
theorem length_net4 (hcs : ∀ c ∈ cs, IsCycle g 4 c) : (net4 cs).length = 10 * cs.length := by
  rw [net4, List.length_append, List.length_append, sourceLayer_length, sinkLayer_length,
    sum_wcount (fun c hc => (hcs c hc).edges_nodup), length_occs hcs, pairLayer_length]
  · omega
  · intro i hi p
    obtain ⟨a, b, u, v, hc, _⟩ := fourCycle_shape (cyc_isCycle hcs hi)
    rw [hc]
    exact opposingPair_length_four a b u v p

theorem length_eList4 (hcs : ∀ c ∈ cs, IsCycle g 4 c) : (eList cs).length ≤ 4 * cs.length :=
  (length_eList_le cs).trans (length_occs hcs).le

/-! ### Flows given by a predicate -/

/-- The flow of `net4 cs` made of the arcs satisfying `P`. -/
def flowOf4 (cs : List Cycle) (P : Arc → Bool) : List Arc := (net4 cs).filter P

theorem inflow_flowOf4 (cs : List Cycle) (P : Arc → Bool) (v : FlowNode) :
    inflow (flowOf4 cs P) v =
      (sourceLayer cs.length).countP (fun a => a.head.beq v && P a) +
      (pairLayer cs.length (cyc cs)).countP (fun a => a.head.beq v && P a) +
      (sinkLayer (eList cs) (wcount cs)).countP (fun a => a.head.beq v && P a) := by
  simp only [inflow, flowOf4, net4, List.countP_filter, List.countP_append]

theorem outflow_flowOf4 (cs : List Cycle) (P : Arc → Bool) (v : FlowNode) :
    outflow (flowOf4 cs P) v =
      (sourceLayer cs.length).countP (fun a => a.tail.beq v && P a) +
      (pairLayer cs.length (cyc cs)).countP (fun a => a.tail.beq v && P a) +
      (sinkLayer (eList cs) (wcount cs)).countP (fun a => a.tail.beq v && P a) := by
  simp only [outflow, flowOf4, net4, List.countP_filter, List.countP_append]

theorem flowCost_flowOf4 (cs : List Cycle) (P : Arc → Bool) :
    flowCost (flowOf4 cs P) = flowCost ((sinkLayer (eList cs) (wcount cs)).filter P) := by
  simp only [flowOf4, net4, List.filter_append, flowCost, List.map_append, List.sum_append]
  have h₁ : (((sourceLayer cs.length).filter P).map Arc.cost).sum = 0 := by
    apply List.sum_eq_zero_iff_forall_eq_nat.mpr
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    obtain ⟨i, p, _, rfl⟩ := (mem_sourceLayer _ a).mp (List.mem_filter.mp ha).1
    rfl
  have h₂ : (((pairLayer cs.length (cyc cs)).filter P).map Arc.cost).sum = 0 := by
    apply List.sum_eq_zero_iff_forall_eq_nat.mpr
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    obtain ⟨i, p, e, _, _, rfl⟩ := (mem_pairLayer _ _ a).mp (List.mem_filter.mp ha).1
    rfl
  omega

theorem flowValue_flowOf4 (cs : List Cycle) (P : Arc → Bool) :
    flowValue (flowOf4 cs P) = (sourceLayer cs.length).countP P := by
  rw [flowValue, outflow_flowOf4, sourceLayer_tail_source,
    pairLayer_tail_other _ _ P _ (fun _ _ h => by cases h),
    sinkLayer_tail_other _ _ P _ (fun _ h => by cases h)]
  omega

theorem inflow_flowOf4_pair (cs : List Cycle) (P : Arc → Bool) (i : ℕ) (p : Bool) :
    inflow (flowOf4 cs P) (.pair i p) =
      if i < cs.length then (if P ⟨.source, .pair i p, 0⟩ then 1 else 0) else 0 := by
  rw [inflow_flowOf4, sourceLayer_head_pair, pairLayer_head_other _ _ P _ (fun _ h => by cases h),
    sinkLayer_head_other _ _ P _ (by intro h; cases h)]
  omega

theorem outflow_flowOf4_pair (cs : List Cycle) (P : Arc → Bool) (i : ℕ) (p : Bool) :
    outflow (flowOf4 cs P) (.pair i p) =
      if i < cs.length then
        (opposingPair (cyc cs i) p).countP (fun e => P ⟨.pair i p, .edgeNode e, 0⟩)
      else 0 := by
  rw [outflow_flowOf4, sourceLayer_tail_other _ P _ (by intro h; cases h), pairLayer_tail_pair,
    sinkLayer_tail_other _ _ P _ (fun _ h => by cases h)]
  omega

theorem inflow_flowOf4_edge (hcs : ∀ c ∈ cs, IsCycle g 4 c) (P : Arc → Bool) (e₀ : Edge) :
    inflow (flowOf4 cs P) (.edgeNode e₀) =
      ((List.range cs.length).map fun i =>
        (if e₀ ∈ opposingPair (cyc cs i) false ∧ P ⟨.pair i false, .edgeNode e₀, 0⟩ = true then 1 else 0) +
        (if e₀ ∈ opposingPair (cyc cs i) true ∧ P ⟨.pair i true, .edgeNode e₀, 0⟩ = true then 1 else 0)).sum := by
  rw [inflow_flowOf4, sourceLayer_head_other _ P _ (fun _ _ h => by cases h),
    pairLayer_head_edge _ _ P e₀ (fun i hi p => opp_nodup hcs hi p),
    sinkLayer_head_other _ _ P _ (by intro h; cases h)]
  omega

theorem outflow_flowOf4_edge (cs : List Cycle) (P : Arc → Bool) (e₀ : Edge) :
    outflow (flowOf4 cs P) (.edgeNode e₀) =
      if e₀ ∈ eList cs then
        (List.range (wcount cs e₀)).countP (fun j => P ⟨.edgeNode e₀, .sink, j⟩)
      else 0 := by
  rw [outflow_flowOf4, sourceLayer_tail_other _ P _ (by intro h; cases h),
    pairLayer_tail_other _ _ P _ (fun _ _ h => by cases h),
    sinkLayer_tail_edge _ (eList_nodup cs)]
  omega

theorem inflow_flowOf4_triangle (cs : List Cycle) (P : Arc → Bool) (i : ℕ) :
    inflow (flowOf4 cs P) (.triangle i) = 0 := by
  rw [inflow_flowOf4, sourceLayer_head_other _ P _ (fun _ _ h => by cases h),
    pairLayer_head_other _ _ P _ (fun _ h => by cases h),
    sinkLayer_head_other _ _ P _ (by intro h; cases h)]

theorem outflow_flowOf4_triangle (cs : List Cycle) (P : Arc → Bool) (i : ℕ) :
    outflow (flowOf4 cs P) (.triangle i) = 0 := by
  rw [outflow_flowOf4, sourceLayer_tail_other _ P _ (by intro h; cases h),
    pairLayer_tail_other _ _ P _ (fun _ _ h => by cases h),
    sinkLayer_tail_other _ _ P _ (fun _ h => by cases h)]

/-! ### Loads -/

theorem inflow4_edge_eq_load (hcs : ∀ c ∈ cs, IsCycle g 4 c) (P : Arc → Bool) (f : ℕ → List Edge)
    (hf : ∀ i, i < cs.length → ∃ j, j < 4 ∧ f i = selected (cyc cs i) j)
    (hP : ∀ i, i < cs.length → ∀ p, ∀ e ∈ opposingPair (cyc cs i) p,
      (P ⟨.pair i p, .edgeNode e, 0⟩ = true ↔ e ∈ f i)) (e₀ : Edge) :
    inflow (flowOf4 cs P) (.edgeNode e₀) = load ((List.range cs.length).map f) e₀ := by
  rw [inflow_flowOf4_edge hcs P e₀]
  rw [load_eq_sum_indicator]
  · apply congrArg List.sum
    apply List.map_congr_left
    intro i hi
    have hi' := List.mem_range.mp hi
    obtain ⟨a, b, u, v, hc, hab, hau, hav, hbu, hbv, huv⟩ := fourCycle_shape (cyc_isCycle hcs hi')
    obtain ⟨j, hj, hfi⟩ := hf i hi'
    have hpart := mem_opposingPair_four hab hau hav hbu hbv huv e₀
    have hPf := hP i hi' false
    have hPt := hP i hi' true
    rw [hc] at hPf hPt hfi ⊢
    by_cases hm : e₀ ∈ f i
    · simp only [hm, ↓reduceIte]
      have hce : e₀ ∈ cycleEdges [a, b, u, v] := by
        rw [hfi] at hm; exact selected_mem_cycleEdges hm
      rcases hpart.1.mp hce with hp | hp
      · have hnp : e₀ ∉ opposingPair [a, b, u, v] true := fun h => hpart.2 ⟨hp, h⟩
        simp [hp, hnp, (hPf e₀ hp).mpr hm]
      · have hnp : e₀ ∉ opposingPair [a, b, u, v] false := fun h => hpart.2 ⟨h, hp⟩
        simp [hp, hnp, (hPt e₀ hp).mpr hm]
    · simp only [hm, ↓reduceIte]
      have h₁ : ¬ (e₀ ∈ opposingPair [a, b, u, v] false ∧ P ⟨.pair i false, .edgeNode e₀, 0⟩ = true) := by
        rintro ⟨hp, hPe⟩
        exact hm ((hPf e₀ hp).mp hPe)
      have h₂ : ¬ (e₀ ∈ opposingPair [a, b, u, v] true ∧ P ⟨.pair i true, .edgeNode e₀, 0⟩ = true) := by
        rintro ⟨hp, hPe⟩
        exact hm ((hPt e₀ hp).mp hPe)
      simp [h₁, h₂]
  · intro i hi
    obtain ⟨j, _, hfi⟩ := hf i hi
    rw [hfi]
    exact selected_nodup (cyc_isCycle hcs hi).2.2.1 j

theorem path_mem_eList4 {i : ℕ} (hi : i < cs.length)
    {j : ℕ} {e : Edge} (he : e ∈ selected (cyc cs i) j) : e ∈ eList cs :=
  mem_eList.mpr ⟨cyc cs i, cyc_mem hi, selected_mem_cycleEdges he⟩

theorem load_le_wcount4 (hcs : ∀ c ∈ cs, IsCycle g 4 c) (f : ℕ → List Edge)
    (hf : ∀ i, i < cs.length → ∃ j, j < 4 ∧ f i = selected (cyc cs i) j) (e : Edge) :
    load ((List.range cs.length).map f) e ≤ wcount cs e := by
  rw [load_eq_sum_indicator, wcount_eq_sum]
  · apply sum_map_le_sum_map
    intro i hi
    obtain ⟨j, _, hfi⟩ := hf i (List.mem_range.mp hi)
    by_cases hm : e ∈ f i
    · have hce : e ∈ cycleEdges (cyc cs i) := by
        rw [hfi] at hm; exact selected_mem_cycleEdges hm
      simp only [hm, hce, ↓reduceIte, le_refl]
    · simp [hm]
  · intro i hi
    obtain ⟨j, _, hfi⟩ := hf i hi
    rw [hfi]
    exact selected_nodup (cyc_isCycle hcs hi).2.2.1 j

theorem load_eq_zero4 (hcs : ∀ c ∈ cs, IsCycle g 4 c) (f : ℕ → List Edge)
    (hf : ∀ i, i < cs.length → ∃ j, j < 4 ∧ f i = selected (cyc cs i) j) {e : Edge}
    (he : e ∉ eList cs) : load ((List.range cs.length).map f) e = 0 := by
  rw [load_eq_sum_indicator]
  · apply List.sum_eq_zero_iff_forall_eq_nat.mpr
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    obtain ⟨j, _, hfi⟩ := hf i (List.mem_range.mp hi)
    have : e ∉ f i := fun hm => he (path_mem_eList4 (List.mem_range.mp hi) (hfi ▸ hm))
    simp [this]
  · intro i hi
    obtain ⟨j, _, hfi⟩ := hf i hi
    rw [hfi]
    exact selected_nodup (cyc_isCycle hcs hi).2.2.1 j

theorem cost_eq_load_sum4 (hcs : ∀ c ∈ cs, IsCycle g 4 c) (f : ℕ → List Edge)
    (hf : ∀ i, i < cs.length → ∃ j, j < 4 ∧ f i = selected (cyc cs i) j) :
    cost ((List.range cs.length).map f) =
      ((eList cs).map fun e => pairCount (load ((List.range cs.length).map f) e)).sum := by
  apply cost_eq_load_sum _ _ (eList_nodup cs)
  · intro p hp
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
    obtain ⟨j, _, hfi⟩ := hf i (List.mem_range.mp hi)
    rw [hfi]
    exact selected_nodup (cyc_isCycle hcs (List.mem_range.mp hi)).2.2.1 j
  · intro p hp e he
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
    obtain ⟨j, _, hfi⟩ := hf i (List.mem_range.mp hi)
    exact path_mem_eList4 (List.mem_range.mp hi) (hfi ▸ he)

/-! ### From an assignment to a flow -/

/-- **An assignment induces a flow** of value `2t` and the same cost (Section 3's
`flow_of_assignment`, for the list `cs`). -/
theorem flow_of_assignment4 (hcs : ∀ c ∈ cs, IsCycle g 4 c) (ps : List (List Edge))
    (hv : ValidChoices (cs.map selectedOptions) ps) :
    ∃ flow, IsFlow (net4 cs) flow ∧ flowValue flow = 2 * cs.length ∧ flowCost flow = cost ps := by
  refine ⟨flowOf4 cs (assignmentPredicate ps), ?_⟩
  obtain ⟨hlen, hall⟩ := validChoices_getD hv
  obtain ⟨f, hfdef⟩ : ∃ f : ℕ → List Edge, f = fun i => ps.getD i [] := ⟨_, rfl⟩
  have hps : ps = (List.range cs.length).map f := by
    rw [hfdef, ← hlen]; exact (map_getD_range ps []).symm
  have hf : ∀ i, i < cs.length → ∃ j, j < 4 ∧ f i = selected (cyc cs i) j := by
    intro i hi
    obtain ⟨a, b, u, v, hc, _⟩ := fourCycle_shape (cyc_isCycle hcs hi)
    have : f i ∈ selectedOptions (cyc cs i) := by
      rw [hfdef]; exact hall i hi
    rw [hc] at this ⊢
    exact (mem_selectedOptions_four a b u v (f i)).mp this
  have hP : ∀ i, i < cs.length → ∀ p, ∀ e ∈ opposingPair (cyc cs i) p,
      (assignmentPredicate ps ⟨.pair i p, .edgeNode e, 0⟩ = true ↔ e ∈ f i) := by
    intro i _ p e _
    simp [assignmentPredicate, hfdef]
  refine ⟨⟨List.filter_sublist, ?_⟩, ?_, ?_⟩
  · intro v hvs hvz
    cases v with
    | source => exact absurd rfl hvs
    | sink => exact absurd rfl hvz
    | triangle i => rw [inflow_flowOf4_triangle, outflow_flowOf4_triangle]
    | pair i p =>
      rw [inflow_flowOf4_pair, outflow_flowOf4_pair]
      by_cases hi : i < cs.length
      · simp only [hi, ↓reduceIte]
        obtain ⟨a, b, u, v, hc, hab, hau, hav, hbu, hbv, huv⟩ := fourCycle_shape (cyc_isCycle hcs hi)
        obtain ⟨j, hj, hfi⟩ := hf i hi
        have hcount : (opposingPair (cyc cs i) p).countP
            (fun e => assignmentPredicate ps ⟨.pair i p, .edgeNode e, 0⟩) =
            (opposingPair [a, b, u, v] p).countP (fun e => decide (e ∈ selected [a, b, u, v] j)) := by
          rw [hc] at hfi ⊢
          apply List.countP_congr
          intro e _
          simp [assignmentPredicate, hfdef, ← hfi]
        rw [hcount, opposingPair_countP_selected hab hau hav hbu hbv huv hj p]
        rfl
      · simp only [hi, ↓reduceIte]
    | edgeNode e₀ =>
      rw [inflow4_edge_eq_load hcs _ f hf hP, outflow_flowOf4_edge]
      by_cases hm : e₀ ∈ eList cs
      · simp only [hm, ↓reduceIte]
        have hc : (List.range (wcount cs e₀)).countP
            (fun j => assignmentPredicate ps ⟨.edgeNode e₀, .sink, j⟩) =
            (List.range (wcount cs e₀)).countP (fun j => decide (j < load ps e₀)) := by
          apply List.countP_congr
          intro j _
          simp [assignmentPredicate]
        rw [hc, countP_lt_range, hps]
        have := load_le_wcount4 hcs f hf e₀
        omega
      · simp only [hm, ↓reduceIte]
        exact load_eq_zero4 hcs f hf hm
  · rw [flowValue_flowOf4]
    have hall' : ∀ a ∈ sourceLayer cs.length, assignmentPredicate ps a = true := by
      intro a ha
      obtain ⟨i, p, _, rfl⟩ := (mem_sourceLayer _ a).mp ha
      rfl
    rw [List.countP_eq_length.mpr hall', sourceLayer_length]
  · rw [flowCost_flowOf4, sinkLayer_cost]
    have hcost : cost ps = ((eList cs).map fun e => pairCount (load ps e)).sum := by
      rw [hps]; exact cost_eq_load_sum4 hcs f hf
    rw [hcost]
    apply congrArg List.sum
    apply List.map_congr_left
    intro e _
    have hc : ((List.range (wcount cs e)).map fun j =>
        if assignmentPredicate ps ⟨.edgeNode e, .sink, j⟩ then j else 0) =
        (List.range (wcount cs e)).map fun j => if j < load ps e then j else 0 := by
      apply List.map_congr_left
      intro j _
      simp [assignmentPredicate]
    have hle : load ps e ≤ wcount cs e := by rw [hps]; exact load_le_wcount4 hcs f hf e
    rw [hc, sum_range_if_lt _ _ hle]

/-! ### From a flow to an assignment: the read-off -/

/-- Does the arc `x_{C_i,{e₁,e₃}} → y_{e₃}` carry flow? -/
def q0 (cs : List Cycle) (P : Arc → Bool) (i : ℕ) : Bool :=
  P ⟨.pair i false, .edgeNode (chosenEdge (cyc cs i) 0 false), 0⟩

/-- Does the arc `x_{C_i,{e₂,e₄}} → y_{e₄}` carry flow? -/
def q1 (cs : List Cycle) (P : Arc → Bool) (i : ℕ) : Bool :=
  P ⟨.pair i true, .edgeNode (chosenEdge (cyc cs i) 1 true), 0⟩

/-- **The read-off**: for each cycle, the option (deleted position) selected by the flow
`P`: the path whose two edges are the edges of the two opposing pairs carrying flow. -/
def readOff4 (cs : List Cycle) (P : Arc → Bool) : List ℕ :=
  (List.range cs.length).map fun i => optionIndex (q0 cs P i) (q1 cs P i)

/-- **The read-off of a flow is an assignment of no greater cost** (the construction in the
proof of Section 3's `assignment_of_flow`, for the list `cs`). -/
theorem assignment_of_flow4 (hcs : ∀ c ∈ cs, IsCycle g 4 c) (F : List Arc)
    (hF : IsFlow (net4 cs) F) (hval : flowValue F = 2 * cs.length) :
    ValidChoices (cs.map selectedOptions)
        (List.zipWith selected cs (readOff4 cs fun a => decide (a ∈ F))) ∧
      cost (List.zipWith selected cs (readOff4 cs fun a => decide (a ∈ F))) ≤ flowCost F := by
  classical
  obtain ⟨P, hPdef⟩ : ∃ P : Arc → Bool, P = fun a => decide (a ∈ F) := ⟨_, rfl⟩
  rw [← hPdef]
  have hFP : F = flowOf4 cs P := by
    rw [hPdef]; exact (Sublist.filter_mem_eq hF.1 (net4_nodup hcs)).symm
  have hcons := hF.2
  rw [hFP] at hval hcons
  -- every source arc carries flow
  have hsource : ∀ i, i < cs.length → ∀ p, P ⟨.source, .pair i p, 0⟩ = true := by
    rw [flowValue_flowOf4] at hval
    have := List.countP_eq_length.mp (by rw [hval, sourceLayer_length])
    intro i hi p
    exact this _ ((mem_sourceLayer _ _).mpr ⟨i, p, hi, rfl⟩)
  -- each pair node sends its unit along exactly one of its two arcs
  have hpair : ∀ i, i < cs.length → ∀ p, (opposingPair (cyc cs i) p).countP
      (fun e => P ⟨.pair i p, .edgeNode e, 0⟩) = 1 := by
    intro i hi p
    have h := hcons (.pair i p) (by intro h; cases h) (by intro h; cases h)
    rw [inflow_flowOf4_pair, outflow_flowOf4_pair] at h
    simp only [hi, ↓reduceIte, hsource i hi p] at h
    exact h.symm
  obtain ⟨f, hfdef⟩ : ∃ f : ℕ → List Edge,
      f = fun i => selected (cyc cs i) (optionIndex (q0 cs P i) (q1 cs P i)) := ⟨_, rfl⟩
  have hpaths : List.zipWith selected cs (readOff4 cs P) = (List.range cs.length).map f := by
    rw [readOff4, zipWith_selected, hfdef]
  rw [hpaths]
  have hf : ∀ i, i < cs.length → ∃ j, j < 4 ∧ f i = selected (cyc cs i) j :=
    fun i _ => ⟨optionIndex (q0 cs P i) (q1 cs P i), optionIndex_lt _ _, by rw [hfdef]⟩
  have hP : ∀ i, i < cs.length → ∀ p, ∀ e ∈ opposingPair (cyc cs i) p,
      (P ⟨.pair i p, .edgeNode e, 0⟩ = true ↔ e ∈ f i) := by
    intro i hi p e he
    obtain ⟨a, b, u, v, hc, hab, hau, hav, hbu, hbv, huv⟩ := fourCycle_shape (cyc_isCycle hcs hi)
    have hcount := hpair i hi p
    clear hPdef hFP hcons hval hF hsource hpair hpaths
    obtain ⟨d12, d13, d14, d23, d24, d34⟩ := fourCycle_edges_distinct hab hau hav hbu hbv huv
    have d21 := Ne.symm d12
    have d31 := Ne.symm d13
    have d41 := Ne.symm d14
    have d32 := Ne.symm d23
    have d42 := Ne.symm d24
    have d43 := Ne.symm d34
    obtain ⟨pf, pt⟩ := opposingPair_four a b u v
    obtain ⟨cf0, _⟩ := chosenEdge_four a b u v 0
    obtain ⟨_, ct1⟩ := chosenEdge_four a b u v 1
    simp only [hfdef, q0, q1]
    rw [hc] at he hcount ⊢
    rw [cf0, ct1]
    simp only [Nat.zero_lt_succ, ite_true, true_or, ite_true]
    rw [mem_selected_four_iff a b u v (optionIndex_lt _ _)]
    obtain ⟨hof, hot⟩ := chosenEdge_optionIndex a b u v
      (P ⟨.pair i false, .edgeNode (edge u v), 0⟩) (P ⟨.pair i true, .edgeNode (edge v a), 0⟩)
    rw [hof, hot]
    cases p
    · rw [pf] at he hcount
      simp only [List.countP_cons, List.countP_nil, Nat.zero_add] at hcount
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · cases h3 : P ⟨.pair i false, .edgeNode (edge u v), 0⟩ <;>
          cases h1 : P ⟨.pair i false, .edgeNode (edge a b), 0⟩ <;>
          simp_all
        all_goals split <;> simp_all
      · cases h3 : P ⟨.pair i false, .edgeNode (edge u v), 0⟩ <;>
          cases h1 : P ⟨.pair i false, .edgeNode (edge a b), 0⟩ <;>
          simp_all
        all_goals split <;> simp_all
    · rw [pt] at he hcount
      simp only [List.countP_cons, List.countP_nil, Nat.zero_add] at hcount
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · cases h4 : P ⟨.pair i true, .edgeNode (edge v a), 0⟩ <;>
          cases h2 : P ⟨.pair i true, .edgeNode (edge b u), 0⟩ <;>
          simp_all
        all_goals split <;> simp_all
      · cases h4 : P ⟨.pair i true, .edgeNode (edge v a), 0⟩ <;>
          cases h2 : P ⟨.pair i true, .edgeNode (edge b u), 0⟩ <;>
          simp_all
        all_goals split <;> simp_all
  refine ⟨?_, ?_⟩
  · apply validChoices_of_getD
    · simp
    · intro i hi
      rw [getD_map_range _ f [] hi]
      obtain ⟨a, b, u, v, hc, _⟩ := fourCycle_shape (cyc_isCycle hcs hi)
      change f i ∈ selectedOptions (cyc cs i)
      rw [hfdef]
      simp only
      rw [hc, mem_selectedOptions_four]
      exact ⟨_, optionIndex_lt _ _, rfl⟩
  · rw [hFP, flowCost_flowOf4, sinkLayer_cost, cost_eq_load_sum4 hcs f hf]
    apply sum_map_le_sum_map
    intro e he
    have h := hcons (.edgeNode e) (by intro h; cases h) (by intro h; cases h)
    rw [inflow4_edge_eq_load hcs P f hf hP, outflow_flowOf4_edge] at h
    simp only [he, ↓reduceIte] at h
    rw [h]
    exact sum_range_if_ge_pairCount _ _

/-- **A minimum-cost flow yields an optimal assignment**: the read-off of a minimum-cost
integral flow of value `2t` of `net4 cs` is an assignment of `cs` of least cost. -/
theorem optimal_of_minFlow4 (hcs : ∀ c ∈ cs, IsCycle g 4 c) {F : List Arc}
    (hF : IsMinFlow (net4 cs) (2 * cs.length) F) :
    ValidChoices (cs.map selectedOptions)
        (List.zipWith selected cs (readOff4 cs fun a => decide (a ∈ F))) ∧
      ∀ ps, ValidChoices (cs.map selectedOptions) ps →
        cost (List.zipWith selected cs (readOff4 cs fun a => decide (a ∈ F))) ≤ cost ps := by
  obtain ⟨hflow, hval, hmin⟩ := hF
  obtain ⟨hv, hc⟩ := assignment_of_flow4 hcs F hflow hval
  refine ⟨hv, fun ps hps => ?_⟩
  obtain ⟨F', hF', hval', hcost'⟩ := flow_of_assignment4 hcs ps hps
  exact hc.trans ((hmin F' hF' hval').trans hcost'.le)

end four

end STACS2027.Runtimes.Flow

module

public import Runtimes.Flow.Enc4
import Mathlib.Tactic

/-!
# The triangle network of a list of triangles (the corollary for `k = 3`)

As `Runtimes/Flow/Four.lean` for four-cycles: the triangle network of Section 3 built from any
list `cs` of triangles of `g` (`net3 cs`, with `net3 (cycles g 3) = triangleNetwork g`), and

* `flow_of_assignment3`: every assignment induces an integral flow of value `t` and the same cost;
* `assignment_of_flow3`: from an integral flow of value `t`, the assignment read off the flow —
  for triangle `C_i = [a, b, u]` with edges `ab, bu, ua`, the path `[ab]` (position `2`) if the
  arc `x_{C_i} → y_{ab}` carries flow, else `[bu]` (position `0`) if `x_{C_i} → y_{bu}` does,
  else `[ua]` (position `1`) (`readOff3`) — has cost at most that of the flow;
* `optimal_of_minFlow3`: the read-off of a minimum-cost flow is an optimal assignment;
* the numbering (`num3`: `s = 0`, `z = 1`, `x_{C_i} = 2 + i`, `y_e = 2 + t + r`), `goodNet3`, the
  layers as written by the machine (`triChunk3`), and `readOff3_select` (the bits at positions
  `t + 3i` and `t + 3i + 1`).
-/

@[expose] public section

namespace STACS2027.Runtimes.Flow

open STACS2027

/-- **The triangle network of the list `cs`**: Section 3's layers for the triangles of `cs`. -/
def net3 (cs : List Cycle) : List Arc :=
  triangleSourceLayer cs.length ++ triangleLayer cs.length (cyc cs) ++ sinkLayer (eList cs) (wcount cs)

/-- On the enumerated triangles it is Section 3's triangle network. -/
theorem net3_cycles (g : Graph) : net3 (cycles g 3) = triangleNetwork g := rfl

theorem selected_three (a b u : ℕ) :
    selected [a, b, u] 0 = [edge b u] ∧ selected [a, b, u] 1 = [edge u a] ∧
      selected [a, b, u] 2 = [edge a b] := by
  simp [selected, pathEdges]

section tri

variable {g : Graph} {cs : List Cycle}

theorem tri_isCycle (hcs : ∀ c ∈ cs, IsCycle g 3 c) {i : ℕ} (hi : i < cs.length) :
    IsCycle g 3 (cyc cs i) := hcs _ (cyc_mem hi)

theorem net3_nodup (hcs : ∀ c ∈ cs, IsCycle g 3 c) : (net3 cs).Nodup := by
  rw [net3, List.nodup_append, List.nodup_append]
  refine ⟨⟨triangleSourceLayer_nodup _,
    triangleLayer_nodup _ _ (fun i hi => (tri_isCycle hcs hi).edges_nodup), ?_⟩,
    sinkLayer_nodup _ (eList_nodup cs) _, ?_⟩
  · intro a ha b hb
    obtain ⟨i, _, rfl⟩ := (mem_triangleSourceLayer _ a).mp ha
    obtain ⟨i', e, _, _, rfl⟩ := (mem_triangleLayer _ _ b).mp hb
    simp
  · intro a ha b hb
    obtain ⟨e, j, _, _, rfl⟩ := (mem_sinkLayer _ _ b).mp hb
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨i, _, rfl⟩ := (mem_triangleSourceLayer _ a).mp ha
      simp
    · obtain ⟨i', e', _, _, rfl⟩ := (mem_triangleLayer _ _ a).mp ha
      simp

theorem tri_edges_length (hcs : ∀ c ∈ cs, IsCycle g 3 c) {i : ℕ} (hi : i < cs.length) :
    (cycleEdges (cyc cs i)).length = 3 := (tri_isCycle hcs hi).edge_length

/-- `7t` arcs. -/
theorem length_net3 (hcs : ∀ c ∈ cs, IsCycle g 3 c) : (net3 cs).length = 7 * cs.length := by
  rw [net3, List.length_append, List.length_append, triangleSourceLayer_length, sinkLayer_length,
    sum_wcount (fun c hc => (hcs c hc).edges_nodup), length_occs hcs, triangleLayer_length]
  · omega
  · intro i hi
    exact tri_edges_length hcs hi

theorem length_eList3 (hcs : ∀ c ∈ cs, IsCycle g 3 c) : (eList cs).length ≤ 3 * cs.length :=
  (length_eList_le cs).trans (length_occs hcs).le

/-! ### Flows given by a predicate -/

/-- The flow of `net3 cs` made of the arcs satisfying `P`. -/
def flowOf3 (cs : List Cycle) (P : Arc → Bool) : List Arc := (net3 cs).filter P

theorem inflow_flowOf3 (cs : List Cycle) (P : Arc → Bool) (v : FlowNode) :
    inflow (flowOf3 cs P) v =
      (triangleSourceLayer cs.length).countP (fun a => a.head.beq v && P a) +
      (triangleLayer cs.length (cyc cs)).countP (fun a => a.head.beq v && P a) +
      (sinkLayer (eList cs) (wcount cs)).countP (fun a => a.head.beq v && P a) := by
  simp only [inflow, flowOf3, net3, List.countP_filter, List.countP_append]

theorem outflow_flowOf3 (cs : List Cycle) (P : Arc → Bool) (v : FlowNode) :
    outflow (flowOf3 cs P) v =
      (triangleSourceLayer cs.length).countP (fun a => a.tail.beq v && P a) +
      (triangleLayer cs.length (cyc cs)).countP (fun a => a.tail.beq v && P a) +
      (sinkLayer (eList cs) (wcount cs)).countP (fun a => a.tail.beq v && P a) := by
  simp only [outflow, flowOf3, net3, List.countP_filter, List.countP_append]

theorem flowCost_flowOf3 (cs : List Cycle) (P : Arc → Bool) :
    flowCost (flowOf3 cs P) = flowCost ((sinkLayer (eList cs) (wcount cs)).filter P) := by
  simp only [flowOf3, net3, List.filter_append, flowCost, List.map_append, List.sum_append]
  have h₁ : (((triangleSourceLayer cs.length).filter P).map Arc.cost).sum = 0 := by
    apply List.sum_eq_zero_iff_forall_eq_nat.mpr
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    obtain ⟨i, _, rfl⟩ := (mem_triangleSourceLayer _ a).mp (List.mem_filter.mp ha).1
    rfl
  have h₂ : (((triangleLayer cs.length (cyc cs)).filter P).map Arc.cost).sum = 0 := by
    apply List.sum_eq_zero_iff_forall_eq_nat.mpr
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    obtain ⟨i, e, _, _, rfl⟩ := (mem_triangleLayer _ _ a).mp (List.mem_filter.mp ha).1
    rfl
  omega

theorem flowValue_flowOf3 (cs : List Cycle) (P : Arc → Bool) :
    flowValue (flowOf3 cs P) = (triangleSourceLayer cs.length).countP P := by
  rw [flowValue, outflow_flowOf3, triangleSourceLayer_tail_source,
    triangleLayer_tail_other _ _ P _ (fun _ h => by cases h),
    sinkLayer_tail_other _ _ P _ (fun _ h => by cases h)]
  omega

theorem inflow_flowOf3_triangle (cs : List Cycle) (P : Arc → Bool) (i : ℕ) :
    inflow (flowOf3 cs P) (.triangle i) =
      if i < cs.length then (if P ⟨.source, .triangle i, 0⟩ then 1 else 0) else 0 := by
  rw [inflow_flowOf3, triangleSourceLayer_head_triangle,
    triangleLayer_head_other _ _ P _ (fun _ h => by cases h),
    sinkLayer_head_other _ _ P _ (by intro h; cases h)]
  omega

theorem outflow_flowOf3_triangle (cs : List Cycle) (P : Arc → Bool) (i : ℕ) :
    outflow (flowOf3 cs P) (.triangle i) =
      if i < cs.length then
        (cycleEdges (cyc cs i)).countP (fun e => P ⟨.triangle i, .edgeNode e, 0⟩)
      else 0 := by
  rw [outflow_flowOf3, triangleSourceLayer_tail_other _ P _ (by intro h; cases h),
    triangleLayer_tail_triangle, sinkLayer_tail_other _ _ P _ (fun _ h => by cases h)]
  omega

theorem inflow_flowOf3_edge (hcs : ∀ c ∈ cs, IsCycle g 3 c) (P : Arc → Bool) (e₀ : Edge) :
    inflow (flowOf3 cs P) (.edgeNode e₀) =
      ((List.range cs.length).map fun i =>
        if e₀ ∈ cycleEdges (cyc cs i) ∧ P ⟨.triangle i, .edgeNode e₀, 0⟩ = true then 1
        else 0).sum := by
  rw [inflow_flowOf3, triangleSourceLayer_head_other _ P _ (fun _ h => by cases h),
    triangleLayer_head_edge _ _ P e₀ (fun i hi => (tri_isCycle hcs hi).edges_nodup),
    sinkLayer_head_other _ _ P _ (by intro h; cases h)]
  omega

theorem outflow_flowOf3_edge (cs : List Cycle) (P : Arc → Bool) (e₀ : Edge) :
    outflow (flowOf3 cs P) (.edgeNode e₀) =
      if e₀ ∈ eList cs then
        (List.range (wcount cs e₀)).countP (fun j => P ⟨.edgeNode e₀, .sink, j⟩)
      else 0 := by
  rw [outflow_flowOf3, triangleSourceLayer_tail_other _ P _ (by intro h; cases h),
    triangleLayer_tail_other _ _ P _ (fun _ h => by cases h),
    sinkLayer_tail_edge _ (eList_nodup cs)]
  omega

theorem inflow_flowOf3_pair (cs : List Cycle) (P : Arc → Bool) (i : ℕ) (p : Bool) :
    inflow (flowOf3 cs P) (.pair i p) = 0 := by
  rw [inflow_flowOf3, triangleSourceLayer_head_other _ P _ (fun _ h => by cases h),
    triangleLayer_head_other _ _ P _ (fun _ h => by cases h),
    sinkLayer_head_other _ _ P _ (by intro h; cases h)]

theorem outflow_flowOf3_pair (cs : List Cycle) (P : Arc → Bool) (i : ℕ) (p : Bool) :
    outflow (flowOf3 cs P) (.pair i p) = 0 := by
  rw [outflow_flowOf3, triangleSourceLayer_tail_other _ P _ (by intro h; cases h),
    triangleLayer_tail_other _ _ P _ (fun _ h => by cases h),
    sinkLayer_tail_other _ _ P _ (fun _ h => by cases h)]

/-! ### Loads -/

theorem tri_path_edge (hcs : ∀ c ∈ cs, IsCycle g 3 c) {i : ℕ} (hi : i < cs.length) {q : List Edge}
    (hq : q ∈ selectedOptions (cyc cs i)) : ∃ e ∈ cycleEdges (cyc cs i), q = [e] := by
  obtain ⟨a, b, u, hc, _⟩ := triangle_shape (tri_isCycle hcs hi)
  rw [hc] at hq ⊢
  exact (mem_selectedOptions_three a b u q).mp hq

theorem inflow3_edge_eq_load (hcs : ∀ c ∈ cs, IsCycle g 3 c) (P : Arc → Bool) (f : ℕ → List Edge)
    (hf : ∀ i, i < cs.length → ∃ e ∈ cycleEdges (cyc cs i), f i = [e])
    (hP : ∀ i, i < cs.length → ∀ e ∈ cycleEdges (cyc cs i),
      (P ⟨.triangle i, .edgeNode e, 0⟩ = true ↔ e ∈ f i)) (e₀ : Edge) :
    inflow (flowOf3 cs P) (.edgeNode e₀) = load ((List.range cs.length).map f) e₀ := by
  rw [inflow_flowOf3_edge hcs, load_eq_sum_indicator]
  · apply congrArg List.sum
    apply List.map_congr_left
    intro i hi
    have hi' := List.mem_range.mp hi
    obtain ⟨e, he, hfi⟩ := hf i hi'
    by_cases hm : e₀ ∈ f i
    · have hce : e₀ ∈ cycleEdges (cyc cs i) := by
        rw [hfi] at hm; simp at hm; subst hm; exact he
      simp only [hm, hce, (hP i hi' e₀ hce).mpr hm, and_self, ↓reduceIte]
    · have : ¬ (e₀ ∈ cycleEdges (cyc cs i) ∧ P ⟨.triangle i, .edgeNode e₀, 0⟩ = true) := by
        rintro ⟨hce, hPe⟩
        exact hm ((hP i hi' e₀ hce).mp hPe)
      simp only [hm, this, ↓reduceIte]
  · intro i hi
    obtain ⟨e, _, hfi⟩ := hf i hi
    rw [hfi]; simp

theorem tri_edge_mem_eList {i : ℕ} (hi : i < cs.length) {e : Edge} (he : e ∈ cycleEdges (cyc cs i)) :
    e ∈ eList cs := mem_eList.mpr ⟨cyc cs i, cyc_mem hi, he⟩

theorem load_le_wcount3 (f : ℕ → List Edge)
    (hf : ∀ i, i < cs.length → ∃ e ∈ cycleEdges (cyc cs i), f i = [e]) (e : Edge) :
    load ((List.range cs.length).map f) e ≤ wcount cs e := by
  rw [load_eq_sum_indicator, wcount_eq_sum]
  · apply sum_map_le_sum_map
    intro i hi
    obtain ⟨e', he', hfi⟩ := hf i (List.mem_range.mp hi)
    by_cases hm : e ∈ f i
    · have hce : e ∈ cycleEdges (cyc cs i) := by
        rw [hfi] at hm; simp at hm; subst hm; exact he'
      simp only [hm, hce, ↓reduceIte, le_refl]
    · simp [hm]
  · intro i hi
    obtain ⟨e', _, hfi⟩ := hf i hi
    rw [hfi]; simp

theorem load_eq_zero3 (f : ℕ → List Edge)
    (hf : ∀ i, i < cs.length → ∃ e ∈ cycleEdges (cyc cs i), f i = [e]) {e : Edge}
    (he : e ∉ eList cs) : load ((List.range cs.length).map f) e = 0 := by
  rw [load_eq_sum_indicator]
  · apply List.sum_eq_zero_iff_forall_eq_nat.mpr
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    obtain ⟨e', he', hfi⟩ := hf i (List.mem_range.mp hi)
    have : e ∉ f i := by
      intro hm
      rw [hfi] at hm; simp at hm; subst hm
      exact he (tri_edge_mem_eList (List.mem_range.mp hi) he')
    simp [this]
  · intro i hi
    obtain ⟨e', _, hfi⟩ := hf i hi
    rw [hfi]; simp

theorem cost_eq_load_sum3 (f : ℕ → List Edge)
    (hf : ∀ i, i < cs.length → ∃ e ∈ cycleEdges (cyc cs i), f i = [e]) :
    cost ((List.range cs.length).map f) =
      ((eList cs).map fun e => pairCount (load ((List.range cs.length).map f) e)).sum := by
  apply cost_eq_load_sum _ _ (eList_nodup cs)
  · intro p hp
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
    obtain ⟨e, _, hfi⟩ := hf i (List.mem_range.mp hi)
    rw [hfi]; simp
  · intro p hp e he
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
    obtain ⟨e', he', hfi⟩ := hf i (List.mem_range.mp hi)
    rw [hfi] at he; simp at he; subst he
    exact tri_edge_mem_eList (List.mem_range.mp hi) he'

/-! ### From an assignment to a flow -/

/-- **An assignment induces a flow** of value `t` and the same cost. -/
theorem flow_of_assignment3 (hcs : ∀ c ∈ cs, IsCycle g 3 c) (ps : List (List Edge))
    (hv : ValidChoices (cs.map selectedOptions) ps) :
    ∃ flow, IsFlow (net3 cs) flow ∧ flowValue flow = cs.length ∧ flowCost flow = cost ps := by
  refine ⟨flowOf3 cs (triangleAssignmentPredicate ps), ?_⟩
  obtain ⟨hlen, hall⟩ := validChoices_getD hv
  obtain ⟨f, hfdef⟩ : ∃ f : ℕ → List Edge, f = fun i => ps.getD i [] := ⟨_, rfl⟩
  have hps : ps = (List.range cs.length).map f := by
    rw [hfdef, ← hlen]; exact (map_getD_range ps []).symm
  have hf : ∀ i, i < cs.length → ∃ e ∈ cycleEdges (cyc cs i), f i = [e] := by
    intro i hi
    have : f i ∈ selectedOptions (cyc cs i) := by rw [hfdef]; exact hall i hi
    exact tri_path_edge hcs hi this
  have hP : ∀ i, i < cs.length → ∀ e ∈ cycleEdges (cyc cs i),
      (triangleAssignmentPredicate ps ⟨.triangle i, .edgeNode e, 0⟩ = true ↔ e ∈ f i) := by
    intro i _ e _
    simp [triangleAssignmentPredicate, hfdef]
  refine ⟨⟨List.filter_sublist, ?_⟩, ?_, ?_⟩
  · intro v hvs hvz
    cases v with
    | source => exact absurd rfl hvs
    | sink => exact absurd rfl hvz
    | pair i p => rw [inflow_flowOf3_pair, outflow_flowOf3_pair]
    | triangle i =>
      rw [inflow_flowOf3_triangle, outflow_flowOf3_triangle]
      by_cases hi : i < cs.length
      · simp only [hi, ↓reduceIte]
        obtain ⟨e, he, hfi⟩ := hf i hi
        have hpsi : ps.getD i [] = [e] := by rw [hfdef] at hfi; exact hfi
        have hcount : (cycleEdges (cyc cs i)).countP
            (fun e' => triangleAssignmentPredicate ps ⟨.triangle i, .edgeNode e', 0⟩) =
            (cycleEdges (cyc cs i)).countP (fun e' => decide (e' = e)) := by
          apply List.countP_congr
          intro e' _
          simp only [triangleAssignmentPredicate, hpsi, List.mem_singleton]
        rw [hcount]
        have hc : (cycleEdges (cyc cs i)).countP (fun e' => decide (e' = e)) =
            (cycleEdges (cyc cs i)).count e := by
          simp only [List.count]
          apply List.countP_congr
          intro e' _
          simp
        rw [hc, (tri_isCycle hcs hi).edges_nodup.count_of_mem he]
        rfl
      · simp only [hi, ↓reduceIte]
    | edgeNode e₀ =>
      rw [inflow3_edge_eq_load hcs _ f hf hP, outflow_flowOf3_edge]
      by_cases hm : e₀ ∈ eList cs
      · simp only [hm, ↓reduceIte]
        have hc : (List.range (wcount cs e₀)).countP
            (fun j => triangleAssignmentPredicate ps ⟨.edgeNode e₀, .sink, j⟩) =
            (List.range (wcount cs e₀)).countP (fun j => decide (j < load ps e₀)) := by
          apply List.countP_congr
          intro j _
          simp [triangleAssignmentPredicate]
        rw [hc, countP_lt_range, hps]
        have := load_le_wcount3 f hf e₀
        omega
      · simp only [hm, ↓reduceIte]
        exact load_eq_zero3 f hf hm
  · rw [flowValue_flowOf3]
    have hall' : ∀ a ∈ triangleSourceLayer cs.length, triangleAssignmentPredicate ps a = true := by
      intro a ha
      obtain ⟨i, _, rfl⟩ := (mem_triangleSourceLayer _ a).mp ha
      rfl
    rw [List.countP_eq_length.mpr hall', triangleSourceLayer_length]
  · rw [flowCost_flowOf3, sinkLayer_cost]
    have hcost : cost ps = ((eList cs).map fun e => pairCount (load ps e)).sum := by
      rw [hps]; exact cost_eq_load_sum3 f hf
    rw [hcost]
    apply congrArg List.sum
    apply List.map_congr_left
    intro e _
    have hc : ((List.range (wcount cs e)).map fun j =>
        if triangleAssignmentPredicate ps ⟨.edgeNode e, .sink, j⟩ then j else 0) =
        (List.range (wcount cs e)).map fun j => if j < load ps e then j else 0 := by
      apply List.map_congr_left
      intro j _
      simp [triangleAssignmentPredicate]
    have hle : load ps e ≤ wcount cs e := by rw [hps]; exact load_le_wcount3 f hf e
    rw [hc, sum_range_if_lt _ _ hle]

/-! ### From a flow to an assignment: the read-off -/

/-- The position read off triangle `i`: `2` if the arc to its first edge carries flow, else
`0` if the arc to its second edge does, else `1`. -/
def pos3 (cs : List Cycle) (P : Arc → Bool) (i : ℕ) : ℕ :=
  if P ⟨.triangle i, .edgeNode ((cycleEdges (cyc cs i)).getD 0 (0, 0)), 0⟩ then 2
  else if P ⟨.triangle i, .edgeNode ((cycleEdges (cyc cs i)).getD 1 (0, 0)), 0⟩ then 0 else 1

/-- **The read-off** of a flow on the triangle network. -/
def readOff3 (cs : List Cycle) (P : Arc → Bool) : List ℕ :=
  (List.range cs.length).map (pos3 cs P)

/-- **The read-off of a flow is an assignment of no greater cost.** -/
theorem assignment_of_flow3 (hcs : ∀ c ∈ cs, IsCycle g 3 c) (F : List Arc)
    (hF : IsFlow (net3 cs) F) (hval : flowValue F = cs.length) :
    ValidChoices (cs.map selectedOptions)
        (List.zipWith selected cs (readOff3 cs fun a => decide (a ∈ F))) ∧
      cost (List.zipWith selected cs (readOff3 cs fun a => decide (a ∈ F))) ≤ flowCost F := by
  classical
  obtain ⟨P, hPdef⟩ : ∃ P : Arc → Bool, P = fun a => decide (a ∈ F) := ⟨_, rfl⟩
  rw [← hPdef]
  have hFP : F = flowOf3 cs P := by
    rw [hPdef]; exact (Sublist.filter_mem_eq hF.1 (net3_nodup hcs)).symm
  have hcons := hF.2
  rw [hFP] at hval hcons
  have hsource : ∀ i, i < cs.length → P ⟨.source, .triangle i, 0⟩ = true := by
    rw [flowValue_flowOf3] at hval
    have := List.countP_eq_length.mp (by rw [hval, triangleSourceLayer_length])
    intro i hi
    exact this _ ((mem_triangleSourceLayer _ _).mpr ⟨i, hi, rfl⟩)
  have htri : ∀ i, i < cs.length → (cycleEdges (cyc cs i)).countP
      (fun e => P ⟨.triangle i, .edgeNode e, 0⟩) = 1 := by
    intro i hi
    have h := hcons (.triangle i) (by intro h; cases h) (by intro h; cases h)
    rw [inflow_flowOf3_triangle, outflow_flowOf3_triangle] at h
    simp only [hi, ↓reduceIte, hsource i hi] at h
    exact h.symm
  obtain ⟨f, hfdef⟩ : ∃ f : ℕ → List Edge, f = fun i => selected (cyc cs i) (pos3 cs P i) := ⟨_, rfl⟩
  have hpaths : List.zipWith selected cs (readOff3 cs P) = (List.range cs.length).map f := by
    rw [readOff3, zipWith_selected, hfdef]
  rw [hpaths]
  -- the shape of each triangle and the unique arc carrying flow
  have key : ∀ i, i < cs.length → (∃ e ∈ cycleEdges (cyc cs i), f i = [e]) ∧
      ∀ e ∈ cycleEdges (cyc cs i), (P ⟨.triangle i, .edgeNode e, 0⟩ = true ↔ e ∈ f i) := by
    intro i hi
    obtain ⟨a, b, u, hc, hab, hau, hbu⟩ := triangle_shape (tri_isCycle hcs hi)
    obtain ⟨d1, d2, d3⟩ := triangle_edges_distinct hab hau hbu
    have h1 := htri i hi
    obtain ⟨s0, s1, s2⟩ := selected_three a b u
    simp only [hfdef, pos3]
    rw [hc] at h1 ⊢
    rw [cycleEdges_three] at h1 ⊢
    simp only [List.countP_cons, List.countP_nil, Nat.zero_add, List.getD_cons_zero,
      List.getD_cons_succ] at h1 ⊢
    cases hA : P ⟨.triangle i, .edgeNode (edge a b), 0⟩ <;>
      cases hB : P ⟨.triangle i, .edgeNode (edge b u), 0⟩ <;>
      cases hC : P ⟨.triangle i, .edgeNode (edge u a), 0⟩ <;>
      simp only [hA, hB, hC, ↓reduceIte, Bool.false_eq_true] at h1 ⊢
    all_goals first | (exfalso; omega) | skip
    · refine ⟨⟨edge u a, by simp, s1⟩, ?_⟩
      intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl <;> simp [hA, hB, hC, s1, d2, d3]
    · refine ⟨⟨edge b u, by simp, s0⟩, ?_⟩
      intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl <;> simp [hA, hB, hC, s0, d1, Ne.symm d3]
    · refine ⟨⟨edge a b, by simp, s2⟩, ?_⟩
      intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl <;> simp [hA, hB, hC, s2, Ne.symm d1, Ne.symm d2]
  refine ⟨?_, ?_⟩
  · apply validChoices_of_getD
    · simp
    · intro i hi
      rw [getD_map_range _ f [] hi]
      obtain ⟨e, he, hfi⟩ := (key i hi).1
      obtain ⟨a, b, u, hc, _⟩ := triangle_shape (tri_isCycle hcs hi)
      change f i ∈ selectedOptions (cyc cs i)
      rw [hfi, hc, mem_selectedOptions_three]
      exact ⟨e, hc ▸ he, rfl⟩
  · have hf : ∀ i, i < cs.length → ∃ e ∈ cycleEdges (cyc cs i), f i = [e] := fun i hi => (key i hi).1
    have hP : ∀ i, i < cs.length → ∀ e ∈ cycleEdges (cyc cs i),
        (P ⟨.triangle i, .edgeNode e, 0⟩ = true ↔ e ∈ f i) := fun i hi => (key i hi).2
    rw [hFP, flowCost_flowOf3, sinkLayer_cost, cost_eq_load_sum3 f hf]
    apply sum_map_le_sum_map
    intro e he
    have h := hcons (.edgeNode e) (by intro h; cases h) (by intro h; cases h)
    rw [inflow3_edge_eq_load hcs P f hf hP, outflow_flowOf3_edge] at h
    simp only [he, ↓reduceIte] at h
    rw [h]
    exact sum_range_if_ge_pairCount _ _

/-- **A minimum-cost flow yields an optimal assignment.** -/
theorem optimal_of_minFlow3 (hcs : ∀ c ∈ cs, IsCycle g 3 c) {F : List Arc}
    (hF : IsMinFlow (net3 cs) cs.length F) :
    ValidChoices (cs.map selectedOptions)
        (List.zipWith selected cs (readOff3 cs fun a => decide (a ∈ F))) ∧
      ∀ ps, ValidChoices (cs.map selectedOptions) ps →
        cost (List.zipWith selected cs (readOff3 cs fun a => decide (a ∈ F))) ≤ cost ps := by
  obtain ⟨hflow, hval, hmin⟩ := hF
  obtain ⟨hv, hc⟩ := assignment_of_flow3 hcs F hflow hval
  refine ⟨hv, fun ps hps => ?_⟩
  obtain ⟨F', hF', hval', hcost'⟩ := flow_of_assignment3 hcs ps hps
  exact hc.trans ((hmin F' hF' hval').trans hcost'.le)

/-! ### Numbers -/

end tri

/-- The numbering of the nodes of the triangle network. -/
def num3 (cs : List Cycle) : FlowNode → ℕ
  | .source => 0
  | .sink => 1
  | .pair _ _ => 0
  | .triangle i => 2 + i
  | .edgeNode e => 2 + cs.length + (eList cs).idxOf e

/-- The number of nodes of the triangle network. -/
def n3 (cs : List Cycle) : ℕ := 2 + cs.length + (eList cs).length

/-- **The encoded triangle network** with required value `t`. -/
def netEnc3 (cs : List Cycle) : List ℕ := netInput (num3 cs) (n3 cs) cs.length (net3 cs)

theorem triangleSourceLayer_succ (t : ℕ) :
    triangleSourceLayer (t + 1) = triangleSourceLayer t ++ [⟨.source, .triangle t, 0⟩] := by
  simp [triangleSourceLayer, List.range_succ]

theorem triangleLayer_succ (t : ℕ) (C : ℕ → Cycle) :
    triangleLayer (t + 1) C = triangleLayer t C ++
      (cycleEdges (C t)).map fun e => (⟨.triangle t, .edgeNode e, 0⟩ : Arc) := by
  simp only [triangleLayer, List.range_succ, List.flatMap_append, List.flatMap_singleton]

section tri2

variable {g : Graph} {cs : List Cycle}

/-- The three arcs of triangle `i`, by occurrences. -/
theorem triChunk3 (hcs : ∀ c ∈ cs, IsCycle g 3 c) {i : ℕ} (hi : i < cs.length) :
    ((cycleEdges (cyc cs i)).map fun e => (⟨.triangle i, .edgeNode e, 0⟩ : Arc)) =
      [⟨.triangle i, .edgeNode ((occs cs).getD (i * 3 + 0) (0, 0)), 0⟩,
        ⟨.triangle i, .edgeNode ((occs cs).getD (i * 3 + 1) (0, 0)), 0⟩,
        ⟨.triangle i, .edgeNode ((occs cs).getD (i * 3 + 2) (0, 0)), 0⟩] := by
  rw [occs_getD_cyc hcs hi (by omega), occs_getD_cyc hcs hi (by omega),
    occs_getD_cyc hcs hi (by omega)]
  obtain ⟨a, b, u, hc, _⟩ := triangle_shape (tri_isCycle hcs hi)
  rw [hc]
  simp [cycleEdges_three]

@[simp] theorem num3_source (cs : List Cycle) : num3 cs .source = 0 := rfl
@[simp] theorem num3_sink (cs : List Cycle) : num3 cs .sink = 1 := rfl
@[simp] theorem num3_triangle (cs : List Cycle) (i : ℕ) : num3 cs (.triangle i) = 2 + i := rfl

/-- The encoding of the three arcs of triangle `i`. -/
theorem encArcs_triChunk3 (cs : List Cycle) (i : ℕ) :
    encArcs (num3 cs) [⟨.triangle i, .edgeNode ((occs cs).getD (i * 3 + 0) (0, 0)), 0⟩,
        ⟨.triangle i, .edgeNode ((occs cs).getD (i * 3 + 1) (0, 0)), 0⟩,
        ⟨.triangle i, .edgeNode ((occs cs).getD (i * 3 + 2) (0, 0)), 0⟩] =
      [2 + i, 2 + cs.length + eid cs (i * 3), 0, 2 + i, 2 + cs.length + eid cs (i * 3 + 1), 0,
        2 + i, 2 + cs.length + eid cs (i * 3 + 2), 0] := rfl

/-- The encoding of the source arc of triangle `i`. -/
theorem encArcs_srcChunk3 (cs : List Cycle) (i : ℕ) :
    encArcs (num3 cs) [⟨.source, .triangle i, 0⟩] = [0, 2 + i, 0] := rfl

theorem num3_occ (cs : List Cycle) (q : ℕ) :
    num3 cs (.edgeNode ((occs cs).getD q (0, 0))) = 2 + cs.length + eid cs q := rfl

theorem num3_eList {r : ℕ} (hr : r < (eList cs).length) :
    num3 cs (.edgeNode ((eList cs).getD r (0, 0))) = 2 + cs.length + r := by
  simp only [num3]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr, Option.getD_some,
    (eList_nodup cs).idxOf_getElem r hr]

theorem nodeOf_net3 {v : FlowNode} (hv : NodeOf (net3 cs) v) :
    v = .source ∨ v = .sink ∨ (∃ i, i < cs.length ∧ v = .triangle i) ∨
      (∃ e ∈ eList cs, v = .edgeNode e) := by
  rcases hv with rfl | rfl | ⟨a, ha, hva⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · rw [net3] at ha
    rcases List.mem_append.mp ha with ha | ha
    · rcases List.mem_append.mp ha with ha | ha
      · obtain ⟨i, hi, rfl⟩ := (mem_triangleSourceLayer _ a).mp ha
        rcases hva with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inr (Or.inl ⟨i, hi, rfl⟩))
      · obtain ⟨i, e, hi, he, rfl⟩ := (mem_triangleLayer _ _ a).mp ha
        rcases hva with rfl | rfl
        · exact Or.inr (Or.inr (Or.inl ⟨i, hi, rfl⟩))
        · exact Or.inr (Or.inr (Or.inr ⟨e, tri_edge_mem_eList hi he, rfl⟩))
    · obtain ⟨e, j, he, _, rfl⟩ := (mem_sinkLayer _ _ a).mp ha
      rcases hva with rfl | rfl
      · exact Or.inr (Or.inr (Or.inr ⟨e, he, rfl⟩))
      · exact Or.inr (Or.inl rfl)

/-- **The numbered triangle network is in the class of the solver.** -/
theorem goodNet3 (hcs : ∀ c ∈ cs, IsCycle g 3 c) : GoodNet (num3 cs) (n3 cs) (net3 cs) where
  lt v hv := by
    rcases nodeOf_net3 hv with rfl | rfl | ⟨i, hi, rfl⟩ | ⟨e, he, rfl⟩
    · simp only [num3, n3]; omega
    · simp only [num3, n3]; omega
    · simp only [num3, n3]; omega
    · simp only [num3, n3]; have := List.idxOf_lt_length_of_mem he; omega
  inj v w hv hw h := by
    rcases nodeOf_net3 hv with rfl | rfl | ⟨i, hi, rfl⟩ | ⟨e, he, rfl⟩ <;>
    rcases nodeOf_net3 hw with rfl | rfl | ⟨i', hi', rfl⟩ | ⟨e', he', rfl⟩
    all_goals simp only [num3] at h
    all_goals first
      | rfl
      | (exfalso; omega)
      | (have : i = i' := by omega
         rw [this])
      | (have he2 : (eList cs).idxOf e = (eList cs).idxOf e' := by omega
         rw [(List.idxOf_inj he).mp he2])
  head_ne a ha := by
    rw [net3] at ha
    rcases List.mem_append.mp ha with ha | ha
    · rcases List.mem_append.mp ha with ha | ha
      · obtain ⟨i, _, rfl⟩ := (mem_triangleSourceLayer _ a).mp ha; simp
      · obtain ⟨i, e, _, _, rfl⟩ := (mem_triangleLayer _ _ a).mp ha; simp
    · obtain ⟨e, j, _, _, rfl⟩ := (mem_sinkLayer _ _ a).mp ha; simp
  tail_ne a ha := by
    rw [net3] at ha
    rcases List.mem_append.mp ha with ha | ha
    · rcases List.mem_append.mp ha with ha | ha
      · obtain ⟨i, _, rfl⟩ := (mem_triangleSourceLayer _ a).mp ha; simp
      · obtain ⟨i, e, _, _, rfl⟩ := (mem_triangleLayer _ _ a).mp ha; simp
    · obtain ⟨e, j, _, _, rfl⟩ := (mem_sinkLayer _ _ a).mp ha; simp
  cost_lt a ha := by
    rw [length_net3 hcs]
    rw [net3] at ha
    rcases List.mem_append.mp ha with ha | ha
    · rcases List.mem_append.mp ha with ha | ha
      · obtain ⟨i, hi, rfl⟩ := (mem_triangleSourceLayer _ a).mp ha; simp only; omega
      · obtain ⟨i, e, hi, _, rfl⟩ := (mem_triangleLayer _ _ a).mp ha; simp only; omega
    · obtain ⟨e, j, _, hj, rfl⟩ := (mem_sinkLayer _ _ a).mp ha
      have := wcount_le cs e
      simp only; omega
  nodes_le := by
    rw [length_net3 hcs, n3]
    have := length_eList3 hcs
    omega

/-! ### The arcs read by the extraction -/

theorem triangleLayer_getD (hcs : ∀ c ∈ cs, IsCycle g 3 c) {i j : ℕ} (hi : i < cs.length)
    (hj : j < 3) (d : Arc) : (triangleLayer cs.length (cyc cs)).getD (i * 3 + j) d =
      ⟨.triangle i, .edgeNode ((cycleEdges (cyc cs i)).getD j (0, 0)), 0⟩ := by
  rw [triangleLayer, List.flatMap_def, getD_flatten_uniform d _ (k := 3) _ (by simpa using hi) hj]
  · rw [List.getD_eq_getElem?_getD (l := List.map _ _), List.getElem?_map,
      List.getElem?_range hi]
    simp only [Option.map_some, Option.getD_some]
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by rw [tri_edges_length hcs hi]; exact hj)]
    rfl
  · intro l hl
    obtain ⟨i', hi', rfl⟩ := List.mem_map.mp hl
    rw [List.length_map]; exact tri_edges_length hcs (List.mem_range.mp hi')

theorem net3_getD (hcs : ∀ c ∈ cs, IsCycle g 3 c) {i j : ℕ} (hi : i < cs.length) (hj : j < 3)
    (d : Arc) : (net3 cs).getD (cs.length + (i * 3 + j)) d =
      ⟨.triangle i, .edgeNode ((cycleEdges (cyc cs i)).getD j (0, 0)), 0⟩ := by
  have hp : i * 3 + j < (triangleLayer cs.length (cyc cs)).length := by
    rw [triangleLayer_length _ _ (fun i' hi' => tri_edges_length hcs hi')]
    omega
  have h := getD_append_right' (triangleSourceLayer cs.length)
    (triangleLayer cs.length (cyc cs) ++ sinkLayer (eList cs) (wcount cs)) d (i * 3 + j)
  rw [triangleSourceLayer_length] at h
  rw [net3, List.append_assoc, h, List.getD_eq_getElem?_getD, List.getElem?_append_left hp,
    ← List.getD_eq_getElem?_getD, triangleLayer_getD hcs hi hj]

/-- **The read-off of a `0/1` vector**: the bits at positions `t + 3i` and `t + 3i + 1`. -/
theorem readOff3_select (hcs : ∀ c ∈ cs, IsCycle g 3 c) {bits : List ℕ}
    (hlen : bits.length = (net3 cs).length) :
    readOff3 cs (fun a => decide (a ∈ select (net3 cs) bits)) =
      (List.range cs.length).map fun i =>
        if bits.getD (cs.length + (i * 3 + 0)) 0 ≠ 0 then 2
        else if bits.getD (cs.length + (i * 3 + 1)) 0 ≠ 0 then 0 else 1 := by
  have hN := length_net3 hcs
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.mp hi
  have d : Arc := ⟨.source, .source, 0⟩
  have h0 := getD_mem_select (bits := bits) d (net3_nodup hcs)
    (j := cs.length + (i * 3 + 0)) (by omega) (by omega)
  have h1 := getD_mem_select (bits := bits) d (net3_nodup hcs)
    (j := cs.length + (i * 3 + 1)) (by omega) (by omega)
  rw [net3_getD hcs hi' (by omega)] at h0 h1
  simp only [pos3]
  by_cases b0 : bits.getD (cs.length + (i * 3 + 0)) 0 ≠ 0
  · simp only [h0.mpr b0, decide_true, ↓reduceIte, b0, ne_eq, not_false_eq_true]
  · have : ¬ (⟨.triangle i, .edgeNode ((cycleEdges (cyc cs i)).getD 0 (0, 0)), 0⟩ : Arc) ∈
        select (net3 cs) bits := fun h => b0 (h0.mp h)
    simp only [this, decide_false, Bool.false_eq_true, ↓reduceIte, b0]
    by_cases b1 : bits.getD (cs.length + (i * 3 + 1)) 0 ≠ 0
    · simp only [h1.mpr b1, decide_true, ↓reduceIte, b1, ne_eq, not_false_eq_true]
    · have : ¬ (⟨.triangle i, .edgeNode ((cycleEdges (cyc cs i)).getD 1 (0, 0)), 0⟩ : Arc) ∈
          select (net3 cs) bits := fun h => b1 (h1.mp h)
      simp only [this, decide_false, Bool.false_eq_true, ↓reduceIte, b1]

end tri2

end STACS2027.Runtimes.Flow

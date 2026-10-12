module

public import Tractability.FourCycles

/-!
# Counting arcs of a flow at each node

A flow given as `(fourCycleNetwork g).filter P` has, at each kind of node, an inflow
and outflow that the structure of the network determines: the pair node `x_{C_i,p}`
is entered only by its source arc and left only by its two pair arcs; the edge node
`y_e` is entered by the pair arcs naming `e` and left by its `ϖ(e)` sink arcs.

The counts are first proved for the three arc layers with the cycle list, the edge
list and the multiplicities abstracted (`t`, `C`, `es`, `w`), so that no proof
unfolds the enumeration `cycles g 4`.
-/

@[expose] public section
namespace STACS2027

/-! ## Node and arc equality -/

theorem FlowNode.beq_iff (a b : FlowNode) : a.beq b = true ↔ a = b := by
  cases a <;> cases b <;> simp [FlowNode.beq]

instance : DecidableEq FlowNode := fun a b =>
  decidable_of_iff (a.beq b = true) (FlowNode.beq_iff a b)

theorem FlowNode.beq_eq_decide (a b : FlowNode) : a.beq b = decide (a = b) := by
  by_cases h : a = b
  · rw [(FlowNode.beq_iff a b).mpr h]; simp [h]
  · have hb : a.beq b ≠ true := fun hb => h ((FlowNode.beq_iff a b).mp hb)
    simp [h]; exact Bool.eq_false_iff.mpr hb

theorem Arc.ext_iff (a b : Arc) : a = b ↔ a.tail = b.tail ∧ a.head = b.head ∧ a.cost = b.cost := by
  cases a; cases b; simp

instance : DecidableEq Arc := fun a b =>
  decidable_of_iff (a.tail = b.tail ∧ a.head = b.head ∧ a.cost = b.cost) (Arc.ext_iff a b).symm

/-! ## Sums -/

theorem sum_map_range_single (n i₀ : Nat) (f : Nat → Nat) (h : ∀ i, i ≠ i₀ → f i = 0) :
    ((List.range n).map f).sum = if i₀ < n then f i₀ else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    by_cases h₁ : i₀ < n
    · have h₂ : n ≠ i₀ := by omega
      have h₃ : i₀ < n + 1 := by omega
      simp [h₁, h₃, h n h₂]
    · by_cases h₃ : i₀ = n
      · subst h₃
        simp [h₁]
      · have h₄ : n ≠ i₀ := fun e => h₃ e.symm
        have h₅ : ¬ i₀ < n + 1 := by omega
        simp [h₁, h₅, h n h₄]

theorem sum_map_single {α : Type} [DecidableEq α] (l : List α) (hl : l.Nodup) (x₀ : α)
    (f : α → Nat) (h : ∀ x ∈ l, x ≠ x₀ → f x = 0) :
    (l.map f).sum = if x₀ ∈ l then f x₀ else 0 := by
  induction l with
  | nil => simp
  | cons x l ih =>
    obtain ⟨hx, hl⟩ := List.nodup_cons.mp hl
    simp only [List.map_cons, List.sum_cons]
    rw [ih hl (fun y hy => h y (List.mem_cons_of_mem x hy))]
    by_cases hxx : x = x₀
    · subst hxx
      simp [hx]
    · have hxx' : ¬ x₀ = x := fun e => hxx e.symm
      simp [hxx', h x List.mem_cons_self hxx]

theorem sum_flatMap_nat {α : Type} (l : List α) (f : α → List Nat) :
    (l.flatMap f).sum = (l.map fun x => (f x).sum).sum := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [List.flatMap_cons, List.sum_append, ih]

theorem countP_flatMap' {α β : Type} (l : List α) (f : α → List β) (q : β → Bool) :
    (l.flatMap f).countP q = (l.map fun x => (f x).countP q).sum := by
  rw [List.countP_flatMap]; rfl

/-! ## The three layers, abstractly -/

/-- The source arcs for `t` cycles. -/
def sourceLayer (t : Nat) : List Arc :=
  (List.range t).flatMap fun i => [⟨.source, .pair i false, 0⟩, ⟨.source, .pair i true, 0⟩]

/-- The pair arcs for `t` cycles `C 0, …, C (t - 1)`. -/
def pairLayer (t : Nat) (C : Nat → Cycle) : List Arc :=
  (List.range t).flatMap fun i =>
    [false, true].flatMap fun p => (opposingPair (C i) p).map fun e => ⟨.pair i p, .edgeNode e, 0⟩

/-- The sink arcs for the edges `es` with multiplicities `w`. -/
def sinkLayer (es : List Edge) (w : Edge → Nat) : List Arc :=
  es.flatMap fun e => (List.range (w e)).map fun j => ⟨.edgeNode e, .sink, j⟩

theorem sourceArcs_eq (g : Graph) : sourceArcs g = sourceLayer (cycles g 4).length := rfl

theorem pairArcs_eq (g : Graph) : pairArcs g = pairLayer (cycles g 4).length (fourCycle g) := rfl

theorem sinkArcs_eq (g : Graph) : sinkArcs g = sinkLayer (cycleEdgeList g) (cycleCount g) := rfl

/-! ### Source layer -/

theorem sourceLayer_countP (t : Nat) (q : Arc → Bool) :
    (sourceLayer t).countP q = ((List.range t).map fun i =>
      (if q ⟨.source, .pair i false, 0⟩ then 1 else 0) +
        (if q ⟨.source, .pair i true, 0⟩ then 1 else 0)).sum := by
  rw [sourceLayer, countP_flatMap']
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [List.countP_cons, List.countP_nil, Nat.zero_add]
  omega

theorem sourceLayer_head_pair (t : Nat) (P : Arc → Bool) (i₀ : Nat) (p₀ : Bool) :
    (sourceLayer t).countP (fun a => a.head.beq (.pair i₀ p₀) && P a) =
      if i₀ < t then (if P ⟨.source, .pair i₀ p₀, 0⟩ then 1 else 0) else 0 := by
  rw [sourceLayer_countP, sum_map_range_single _ i₀]
  · split
    · cases p₀ <;> simp [FlowNode.beq]
    · rfl
  · intro i hi
    cases p₀ <;> simp [FlowNode.beq, hi]

theorem sourceLayer_head_other (t : Nat) (P : Arc → Bool) (v : FlowNode)
    (hv : ∀ i p, v ≠ .pair i p) :
    (sourceLayer t).countP (fun a => a.head.beq v && P a) = 0 := by
  rw [sourceLayer_countP]
  apply List.sum_eq_zero_iff_forall_eq_nat.mpr
  intro x hx
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
  have h₁ := hv i false
  have h₂ := hv i true
  cases v <;> simp_all [FlowNode.beq]

theorem mem_sourceLayer (t : Nat) (a : Arc) :
    a ∈ sourceLayer t ↔ ∃ i p, i < t ∧ a = ⟨.source, .pair i p, 0⟩ := by
  simp only [sourceLayer, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false]
  constructor
  · rintro ⟨i, hi, rfl | rfl⟩
    · exact ⟨i, false, hi, rfl⟩
    · exact ⟨i, true, hi, rfl⟩
  · rintro ⟨i, p, hi, rfl⟩
    exact ⟨i, hi, by cases p <;> simp⟩

theorem sourceLayer_tail_source (t : Nat) (P : Arc → Bool) :
    (sourceLayer t).countP (fun a => a.tail.beq .source && P a) = (sourceLayer t).countP P := by
  apply List.countP_congr
  intro a ha
  obtain ⟨i, p, _, rfl⟩ := (mem_sourceLayer t a).mp ha
  simp [FlowNode.beq]

theorem sourceLayer_tail_other (t : Nat) (P : Arc → Bool) (v : FlowNode) (hv : v ≠ .source) :
    (sourceLayer t).countP (fun a => a.tail.beq v && P a) = 0 := by
  apply List.countP_eq_zero.mpr
  intro a ha
  obtain ⟨i, p, _, rfl⟩ := (mem_sourceLayer t a).mp ha
  cases v <;> simp_all [FlowNode.beq]

theorem sourceLayer_length (t : Nat) : (sourceLayer t).length = 2 * t := by
  simp only [sourceLayer, List.length_flatMap, List.length_cons, List.length_nil]
  rw [sum_map_const, List.length_range]
  omega

/-! ### Pair layer -/

theorem pairLayer_countP (t : Nat) (C : Nat → Cycle) (q : Arc → Bool) :
    (pairLayer t C).countP q = ((List.range t).map fun i =>
      (opposingPair (C i) false).countP (fun e => q ⟨.pair i false, .edgeNode e, 0⟩) +
        (opposingPair (C i) true).countP (fun e => q ⟨.pair i true, .edgeNode e, 0⟩)).sum := by
  rw [pairLayer, countP_flatMap']
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.countP_append,
    List.countP_map, Function.comp_def]

theorem mem_pairLayer (t : Nat) (C : Nat → Cycle) (a : Arc) :
    a ∈ pairLayer t C ↔
      ∃ i p e, i < t ∧ e ∈ opposingPair (C i) p ∧ a = ⟨.pair i p, .edgeNode e, 0⟩ := by
  simp only [pairLayer, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false, List.mem_map]
  constructor
  · rintro ⟨i, hi, p, hp, e, he, rfl⟩
    exact ⟨i, p, e, hi, he, rfl⟩
  · rintro ⟨i, p, e, hi, he, rfl⟩
    exact ⟨i, hi, p, by cases p <;> simp, e, he, rfl⟩

theorem pairLayer_tail_pair (t : Nat) (C : Nat → Cycle) (P : Arc → Bool) (i₀ : Nat) (p₀ : Bool) :
    (pairLayer t C).countP (fun a => a.tail.beq (.pair i₀ p₀) && P a) =
      if i₀ < t then (opposingPair (C i₀) p₀).countP (fun e => P ⟨.pair i₀ p₀, .edgeNode e, 0⟩)
      else 0 := by
  rw [pairLayer_countP, sum_map_range_single _ i₀]
  · split
    · cases p₀ <;> simp [FlowNode.beq]
    · rfl
  · intro i hi
    cases p₀ <;> simp [FlowNode.beq, hi]

theorem pairLayer_tail_other (t : Nat) (C : Nat → Cycle) (P : Arc → Bool) (v : FlowNode)
    (hv : ∀ i p, v ≠ .pair i p) :
    (pairLayer t C).countP (fun a => a.tail.beq v && P a) = 0 := by
  apply List.countP_eq_zero.mpr
  intro a ha
  obtain ⟨i, p, e, _, _, rfl⟩ := (mem_pairLayer t C a).mp ha
  have := hv i p
  cases v <;> simp_all [FlowNode.beq]

theorem pairLayer_head_other (t : Nat) (C : Nat → Cycle) (P : Arc → Bool) (v : FlowNode)
    (hv : ∀ e, v ≠ .edgeNode e) :
    (pairLayer t C).countP (fun a => a.head.beq v && P a) = 0 := by
  apply List.countP_eq_zero.mpr
  intro a ha
  obtain ⟨i, p, e, _, _, rfl⟩ := (mem_pairLayer t C a).mp ha
  have := hv e
  cases v <;> simp_all [FlowNode.beq]

theorem countP_eq_mem_indicator {α : Type} [DecidableEq α] (l : List α) (hl : l.Nodup) (x₀ : α)
    (b : Bool) :
    l.countP (fun x => decide (x = x₀) && b) = if x₀ ∈ l ∧ b = true then 1 else 0 := by
  cases b
  · simp
  · simp only [Bool.and_true, and_true]
    have hc : l.countP (fun x => decide (x = x₀)) = l.count x₀ := by
      simp only [List.count]
      apply List.countP_congr
      intro x _
      simp
    rw [hc]
    by_cases hm : x₀ ∈ l
    · simp [hm, hl.count_of_mem hm]
    · simp [hm, List.count_eq_zero.mpr hm]

/-- The pair arcs entering `y_e`: one for each pair of each cycle containing `e`, when the
opposing pairs have no repeated edge. -/
theorem pairLayer_head_edge (t : Nat) (C : Nat → Cycle) (P : Arc → Bool) (e₀ : Edge)
    (hn : ∀ i, i < t → ∀ p, (opposingPair (C i) p).Nodup) :
    (pairLayer t C).countP (fun a => a.head.beq (.edgeNode e₀) && P a) =
      ((List.range t).map fun i =>
        (if e₀ ∈ opposingPair (C i) false ∧ P ⟨.pair i false, .edgeNode e₀, 0⟩ = true then 1 else 0) +
        (if e₀ ∈ opposingPair (C i) true ∧ P ⟨.pair i true, .edgeNode e₀, 0⟩ = true then 1 else 0)).sum := by
  rw [pairLayer_countP]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.mp hi
  have key : ∀ p : Bool, (opposingPair (C i) p).countP
      (fun e => FlowNode.beq (.edgeNode e) (.edgeNode e₀) && P ⟨.pair i p, .edgeNode e, 0⟩) =
      if e₀ ∈ opposingPair (C i) p ∧ P ⟨.pair i p, .edgeNode e₀, 0⟩ = true then 1 else 0 := by
    intro p
    rw [← countP_eq_mem_indicator _ (hn i hi' p)]
    apply List.countP_congr
    intro e _
    simp only [FlowNode.beq, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨rfl, h⟩; exact ⟨rfl, h⟩
    · rintro ⟨rfl, h⟩; exact ⟨rfl, h⟩
  rw [key false, key true]

/-! ### Sink layer -/

theorem mem_sinkLayer (es : List Edge) (w : Edge → Nat) (a : Arc) :
    a ∈ sinkLayer es w ↔ ∃ e j, e ∈ es ∧ j < w e ∧ a = ⟨.edgeNode e, .sink, j⟩ := by
  simp only [sinkLayer, List.mem_flatMap, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨e, he, j, hj, rfl⟩
    exact ⟨e, j, he, hj, rfl⟩
  · rintro ⟨e, j, he, hj, rfl⟩
    exact ⟨e, he, j, hj, rfl⟩

theorem sinkLayer_countP (es : List Edge) (w : Edge → Nat) (q : Arc → Bool) :
    (sinkLayer es w).countP q = (es.map fun e =>
      (List.range (w e)).countP fun j => q ⟨.edgeNode e, .sink, j⟩).sum := by
  rw [sinkLayer, countP_flatMap']
  congr 1
  apply List.map_congr_left
  intro e _
  simp only [List.countP_map, Function.comp_def]

theorem sinkLayer_head_other (es : List Edge) (w : Edge → Nat) (P : Arc → Bool) (v : FlowNode)
    (hv : v ≠ .sink) :
    (sinkLayer es w).countP (fun a => a.head.beq v && P a) = 0 := by
  apply List.countP_eq_zero.mpr
  intro a ha
  obtain ⟨e, j, _, _, rfl⟩ := (mem_sinkLayer es w a).mp ha
  cases v <;> simp_all [FlowNode.beq]

theorem sinkLayer_tail_other (es : List Edge) (w : Edge → Nat) (P : Arc → Bool) (v : FlowNode)
    (hv : ∀ e, v ≠ .edgeNode e) :
    (sinkLayer es w).countP (fun a => a.tail.beq v && P a) = 0 := by
  apply List.countP_eq_zero.mpr
  intro a ha
  obtain ⟨e, j, _, _, rfl⟩ := (mem_sinkLayer es w a).mp ha
  have := hv e
  cases v <;> simp_all [FlowNode.beq]

theorem sinkLayer_tail_edge (es : List Edge) (hes : es.Nodup) (w : Edge → Nat) (P : Arc → Bool)
    (e₀ : Edge) :
    (sinkLayer es w).countP (fun a => a.tail.beq (.edgeNode e₀) && P a) =
      if e₀ ∈ es then (List.range (w e₀)).countP (fun j => P ⟨.edgeNode e₀, .sink, j⟩) else 0 := by
  rw [sinkLayer_countP, sum_map_single _ hes e₀]
  · split
    · simp [FlowNode.beq]
    · rfl
  · intro e _ he
    simp [FlowNode.beq, he]

theorem sinkLayer_cost (es : List Edge) (w : Edge → Nat) (P : Arc → Bool) :
    flowCost ((sinkLayer es w).filter P) = (es.map fun e =>
      ((List.range (w e)).map fun j => if P ⟨.edgeNode e, .sink, j⟩ then j else 0).sum).sum := by
  simp only [flowCost, sinkLayer, List.filter_flatMap, List.map_flatMap]
  rw [sum_flatMap_nat]
  congr 1
  apply List.map_congr_left
  intro e _
  induction (List.range (w e)) with
  | nil => simp
  | cons j js ih =>
    simp only [List.map_cons, List.sum_cons, List.filter_cons]
    split <;> simp_all

/-! ## `eraseDups` -/

/-- `eraseDups` has no duplicates. -/
theorem nodup_eraseDups {α : Type} [BEq α] [LawfulBEq α] (l : List α) : l.eraseDups.Nodup := by
  match l with
  | [] => simp
  | a :: l =>
    rw [List.eraseDups_cons]
    apply List.nodup_cons.mpr
    refine ⟨?_, ?_⟩
    · intro h
      rw [List.mem_eraseDups, List.mem_filter] at h
      simp at h
    · have : (l.filter fun b => !b == a).length < (a :: l).length :=
        Nat.lt_of_le_of_lt (List.length_filter_le _ _) (by simp)
      exact nodup_eraseDups _
termination_by l.length

theorem cycleEdgeList_nodup (g : Graph) : (cycleEdgeList g).Nodup := nodup_eraseDups _

theorem mem_cycleEdgeList (g : Graph) (e : Edge) :
    e ∈ cycleEdgeList g ↔ ∃ c ∈ cycles g 4, e ∈ cycleEdges c := by
  simp [cycleEdgeList, List.mem_eraseDups, List.mem_flatMap]

/-! ## Flows given by a predicate -/

/-- The flow consisting of the arcs of the network satisfying `P`. -/
def flowOf (g : Graph) (P : Arc → Bool) : List Arc := (fourCycleNetwork g).filter P

theorem flowOf_sublist (g : Graph) (P : Arc → Bool) : (flowOf g P).Sublist (fourCycleNetwork g) :=
  List.filter_sublist

theorem inflow_flowOf (g : Graph) (P : Arc → Bool) (v : FlowNode) :
    inflow (flowOf g P) v =
      (sourceLayer (cycles g 4).length).countP (fun a => a.head.beq v && P a) +
      (pairLayer (cycles g 4).length (fourCycle g)).countP (fun a => a.head.beq v && P a) +
      (sinkLayer (cycleEdgeList g) (cycleCount g)).countP (fun a => a.head.beq v && P a) := by
  simp only [inflow, flowOf, fourCycleNetwork, List.countP_filter, List.countP_append,
    sourceArcs_eq, pairArcs_eq, sinkArcs_eq]

theorem outflow_flowOf (g : Graph) (P : Arc → Bool) (v : FlowNode) :
    outflow (flowOf g P) v =
      (sourceLayer (cycles g 4).length).countP (fun a => a.tail.beq v && P a) +
      (pairLayer (cycles g 4).length (fourCycle g)).countP (fun a => a.tail.beq v && P a) +
      (sinkLayer (cycleEdgeList g) (cycleCount g)).countP (fun a => a.tail.beq v && P a) := by
  simp only [outflow, flowOf, fourCycleNetwork, List.countP_filter, List.countP_append,
    sourceArcs_eq, pairArcs_eq, sinkArcs_eq]

theorem flowCost_flowOf (g : Graph) (P : Arc → Bool) :
    flowCost (flowOf g P) = flowCost ((sinkLayer (cycleEdgeList g) (cycleCount g)).filter P) := by
  simp only [flowOf, fourCycleNetwork, List.filter_append, flowCost, List.map_append,
    List.sum_append, sourceArcs_eq, pairArcs_eq, sinkArcs_eq]
  have h₁ : (((sourceLayer (cycles g 4).length).filter P).map Arc.cost).sum = 0 := by
    apply List.sum_eq_zero_iff_forall_eq_nat.mpr
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    obtain ⟨i, p, _, rfl⟩ := (mem_sourceLayer _ a).mp (List.mem_filter.mp ha).1
    rfl
  have h₂ : (((pairLayer (cycles g 4).length (fourCycle g)).filter P).map Arc.cost).sum = 0 := by
    apply List.sum_eq_zero_iff_forall_eq_nat.mpr
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    obtain ⟨i, p, e, _, _, rfl⟩ := (mem_pairLayer _ _ a).mp (List.mem_filter.mp ha).1
    rfl
  omega

theorem flowValue_flowOf (g : Graph) (P : Arc → Bool) :
    flowValue (flowOf g P) = (sourceLayer (cycles g 4).length).countP P := by
  rw [flowValue, outflow_flowOf, sourceLayer_tail_source,
    pairLayer_tail_other _ _ P _ (fun _ _ h => by cases h),
    sinkLayer_tail_other _ _ P _ (fun _ h => by cases h)]
  omega

theorem inflow_flowOf_pair (g : Graph) (P : Arc → Bool) (i : Nat) (p : Bool) :
    inflow (flowOf g P) (.pair i p) =
      if i < (cycles g 4).length then (if P ⟨.source, .pair i p, 0⟩ then 1 else 0) else 0 := by
  rw [inflow_flowOf, sourceLayer_head_pair, pairLayer_head_other _ _ P _ (fun _ h => by cases h),
    sinkLayer_head_other _ _ P _ (by intro h; cases h)]
  omega

theorem outflow_flowOf_pair (g : Graph) (P : Arc → Bool) (i : Nat) (p : Bool) :
    outflow (flowOf g P) (.pair i p) =
      if i < (cycles g 4).length then
        (opposingPair (fourCycle g i) p).countP (fun e => P ⟨.pair i p, .edgeNode e, 0⟩)
      else 0 := by
  rw [outflow_flowOf, sourceLayer_tail_other _ P _ (by intro h; cases h), pairLayer_tail_pair,
    sinkLayer_tail_other _ _ P _ (fun _ h => by cases h)]
  omega

theorem inflow_flowOf_edge (g : Graph) (P : Arc → Bool) (e₀ : Edge)
    (hn : ∀ i, i < (cycles g 4).length → ∀ p, (opposingPair (fourCycle g i) p).Nodup) :
    inflow (flowOf g P) (.edgeNode e₀) =
      ((List.range (cycles g 4).length).map fun i =>
        (if e₀ ∈ opposingPair (fourCycle g i) false ∧ P ⟨.pair i false, .edgeNode e₀, 0⟩ = true then 1 else 0) +
        (if e₀ ∈ opposingPair (fourCycle g i) true ∧ P ⟨.pair i true, .edgeNode e₀, 0⟩ = true then 1 else 0)).sum := by
  rw [inflow_flowOf, sourceLayer_head_other _ P _ (fun _ _ h => by cases h),
    pairLayer_head_edge _ _ P e₀ hn, sinkLayer_head_other _ _ P _ (by intro h; cases h)]
  omega

theorem outflow_flowOf_edge (g : Graph) (P : Arc → Bool) (e₀ : Edge) :
    outflow (flowOf g P) (.edgeNode e₀) =
      if e₀ ∈ cycleEdgeList g then
        (List.range (cycleCount g e₀)).countP (fun j => P ⟨.edgeNode e₀, .sink, j⟩)
      else 0 := by
  rw [outflow_flowOf, sourceLayer_tail_other _ P _ (by intro h; cases h),
    pairLayer_tail_other _ _ P _ (fun _ _ h => by cases h),
    sinkLayer_tail_edge _ (cycleEdgeList_nodup g)]
  omega

/-- The four-cycle network has no arc at a triangle node. -/
theorem inflow_flowOf_triangle (g : Graph) (P : Arc → Bool) (i : Nat) :
    inflow (flowOf g P) (.triangle i) = 0 := by
  rw [inflow_flowOf, sourceLayer_head_other _ P _ (fun _ _ h => by cases h),
    pairLayer_head_other _ _ P _ (fun _ h => by cases h),
    sinkLayer_head_other _ _ P _ (by intro h; cases h)]

theorem outflow_flowOf_triangle (g : Graph) (P : Arc → Bool) (i : Nat) :
    outflow (flowOf g P) (.triangle i) = 0 := by
  rw [outflow_flowOf, sourceLayer_tail_other _ P _ (by intro h; cases h),
    pairLayer_tail_other _ _ P _ (fun _ _ h => by cases h),
    sinkLayer_tail_other _ _ P _ (fun _ h => by cases h)]

theorem inflow_flowOf_source (g : Graph) (P : Arc → Bool) : inflow (flowOf g P) .source = 0 := by
  rw [inflow_flowOf, sourceLayer_head_other _ P _ (fun _ _ h => by cases h),
    pairLayer_head_other _ _ P _ (fun _ h => by cases h),
    sinkLayer_head_other _ _ P _ (by intro h; cases h)]

theorem outflow_flowOf_sink (g : Graph) (P : Arc → Bool) : outflow (flowOf g P) .sink = 0 := by
  rw [outflow_flowOf, sourceLayer_tail_other _ P _ (by intro h; cases h),
    pairLayer_tail_other _ _ P _ (fun _ _ h => by cases h),
    sinkLayer_tail_other _ _ P _ (fun _ h => by cases h)]

end STACS2027

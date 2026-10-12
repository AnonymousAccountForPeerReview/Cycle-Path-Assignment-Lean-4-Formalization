module

public import Runtimes.Flow.MaxFlowNetwork
public import Runtimes.Flow.IndexedFacts
import Mathlib.Data.List.FinRange
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-! The exact projection of the fixed-demand minimum-cost reduction to maximum indexed
unit-capacity flow. Arc occurrences remain separate even when their endpoints coincide. -/

@[expose] public section

namespace STACS2027.Runtimes.Flow

open STACS2027

/-- The first `m` output bits belong to the original indexed arc occurrences. -/
def maxFlowProjection {arcs : ℕ} (bits : List ℕ) : IndexedFlow arcs :=
  fun i => bits.getD i.val 0 != 0

/-- Signed divergence in the reified arc-list representation. -/
def listBalance (flow : List Arc) (v : FlowNode) : ℤ :=
  (flow.map fun a => (if a.tail = v then (1 : ℤ) else 0) -
    (if a.head = v then (1 : ℤ) else 0)).sum

theorem listBalance_eq (flow : List Arc) (v : FlowNode) :
    listBalance flow v = (outflow flow v : ℤ) - (inflow flow v : ℤ) := by
  induction flow with
  | nil => simp [listBalance, outflow, inflow]
  | cons a flow ih =>
    by_cases ht : a.tail = v <;> by_cases hh : a.head = v <;>
      simp [listBalance, outflow, inflow, FlowNode.beq_iff, ht, hh] at ih ⊢ <;>
      omega

theorem sum_select_ofFn {n : ℕ} (A : Fin n → Arc) (bits : List ℕ) (weight : Arc → ℤ) :
    ((select (List.ofFn A) bits).map weight).sum =
      ∑ i : Fin n, if bits.getD i.val 0 = 0 then 0 else weight (A i) := by
  induction n generalizing bits with
  | zero => simp [select]
  | succ n ih =>
    rw [List.ofFn_succ, Fin.sum_univ_succ]
    cases bits with
    | nil => simp [select]
    | cons b bits =>
      by_cases hb : b = 0
      · simp only [select, hb, ↓reduceIte, List.getD_cons_zero, Fin.val_zero,
          Fin.val_succ, List.getD_cons_succ, zero_add]
        exact ih _ bits
      · simp only [select, hb, ↓reduceIte, List.map_cons, List.sum_cons, List.getD_cons_zero,
          Fin.val_zero, Fin.val_succ, List.getD_cons_succ]
        rw [ih]

theorem select_append (left right : List Arc) (bits : List ℕ) (hlen : left.length ≤ bits.length) :
    select (left ++ right) bits = select left bits ++ select right (bits.drop left.length) := by
  induction left generalizing bits with
  | nil => simp [select]
  | cons a left ih =>
    cases bits with
    | nil => simp at hlen
    | cons b bits =>
      have hlen' : left.length ≤ bits.length := by simpa using hlen
      by_cases hb : b = 0 <;> simp [select, hb, ih bits hlen']

theorem select_replicate (a : Arc) (n : ℕ) (bits : List ℕ) :
    ∃ b ≤ n, select (List.replicate n a) bits = List.replicate b a := by
  induction n generalizing bits with
  | zero => exact ⟨0, le_rfl, rfl⟩
  | succ n ih =>
    cases bits with
    | nil => exact ⟨0, Nat.zero_le _, rfl⟩
    | cons x bits =>
      obtain ⟨b, hb, he⟩ := ih bits
      by_cases hx : x = 0
      · exact ⟨b, by omega, by simp [List.replicate_succ, select, hx, he]⟩
      · exact ⟨b + 1, by omega, by simp [List.replicate_succ, select, hx, he]⟩

/-- Selection splits into original occurrences and selected direct bypass occurrences. -/
theorem maxFlow_selected_split {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    (bits : List ℕ) (hlen : bits.length = 2 * arcs) :
    ∃ b ≤ arcs, select (maxFlowNetwork net) bits =
      select (numberedArcs net) bits ++ List.replicate b bypassArc := by
  rw [maxFlowNetwork, select_append _ _ bits (by simp; omega), numberedArcs_length]
  obtain ⟨b, hb, he⟩ := select_replicate bypassArc arcs (bits.drop arcs)
  exact ⟨b, hb, by rw [he]⟩

/-- Divergence of the selected original occurrences is exactly indexed divergence. -/
theorem projection_balance {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    (bits : List ℕ) (v : Fin nodes) :
    listBalance (select (numberedArcs net) bits) (numberedNode net v) =
      indexedBalance net (maxFlowProjection bits) v := by
  rw [listBalance, numberedArcs, ← List.ofFn_eq_map, sum_select_ofFn]
  unfold indexedBalance maxFlowProjection
  apply Finset.sum_congr rfl
  intro i _
  have ht : numberedNode net (net.tail i) = numberedNode net v ↔ net.tail i = v :=
    ⟨fun h => numberedNode_injective net h, congrArg (numberedNode net)⟩
  have hh : numberedNode net (net.head i) = numberedNode net v ↔ net.head i = v :=
    ⟨fun h => numberedNode_injective net h, congrArg (numberedNode net)⟩
  by_cases hb : bits.getD i.val 0 = 0 <;> simp_all [numberedArc]

theorem numbered_selected_cost {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    (bits : List ℕ) : flowCost (select (numberedArcs net) bits) = 0 := by
  apply List.sum_eq_zero
  intro cost hcost
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hcost
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp ((select_sublist _ _).subset ha)
  rfl

theorem listBalance_append (left right : List Arc) (v : FlowNode) :
    listBalance (left ++ right) v = listBalance left v + listBalance right v := by
  simp [listBalance, List.map_append, List.sum_append]

theorem bypass_balance (b : ℕ) (v : FlowNode) :
    listBalance (List.replicate b bypassArc) v =
      if v = .source then (b : ℤ) else if v = .sink then -(b : ℤ) else 0 := by
  rw [listBalance_eq]
  by_cases hs : v = .source
  · subst v; simp [outflow, inflow, bypassArc, List.countP_replicate, FlowNode.beq]
  · by_cases ht : v = .sink
    · subst v; simp [outflow, inflow, bypassArc, List.countP_replicate, FlowNode.beq]
    · have hs' : FlowNode.source.beq v = false := by
        cases h : FlowNode.source.beq v
        · rfl
        · exact False.elim (hs ((FlowNode.beq_iff _ _).mp h).symm)
      have ht' : FlowNode.sink.beq v = false := by
        cases h : FlowNode.sink.beq v
        · rfl
        · exact False.elim (ht ((FlowNode.beq_iff _ _).mp h).symm)
      simp [outflow, inflow, bypassArc, List.countP_replicate, hs', ht', hs, ht]

/-- Selected original arcs never enter the source when the original network does not. -/
theorem numbered_selected_source_inflow {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    (hhead : ∀ i, net.head i ≠ net.source) (bits : List ℕ) :
    inflow (select (numberedArcs net) bits) .source = 0 := by
  apply List.countP_eq_zero.mpr
  intro a ha
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp ((select_sublist _ _).subset ha)
  have hn : (numberedArc net i).head ≠ .source := by
    intro he
    exact hhead i (numberedNode_injective net (he.trans (numberedNode_source net).symm))
  cases he : (numberedArc net i).head.beq .source
  · simp
  · exact False.elim (hn ((FlowNode.beq_iff _ _).mp he))

/-- The divergence over every numbered vertex sums to zero. -/
theorem indexedBalance_sum {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    (flow : IndexedFlow arcs) : (∑ v : Fin nodes, indexedBalance net flow v) = 0 := by
  unfold indexedBalance
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro i _
  cases hf : flow i
  · simp
  · simp only [ite_true, Finset.sum_sub_distrib]
    simp [eq_comm]

theorem isIndexedFlow_of_conservation {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    (flow : IndexedFlow arcs) (d : ℕ)
    (hs : indexedBalance net flow net.source = (d : ℤ))
    (hc : ∀ v, v ≠ net.source → v ≠ net.sink → indexedBalance net flow v = 0) :
    IsIndexedFlow net d flow := by
  have hterm : ∀ v, indexedBalance net flow v =
      (if v = net.source then (d : ℤ) else 0) +
      (if v = net.sink then indexedBalance net flow net.sink else 0) := by
    intro v
    by_cases hsource : v = net.source
    · subst v; simp [hs, net.source_ne_sink]
    · by_cases hsink : v = net.sink
      · subst v; simp [hsource]
      · simp [hc v hsource hsink, hsource, hsink]
  have hsum := indexedBalance_sum net flow
  have hsumEq : (∑ v : Fin nodes, indexedBalance net flow v) =
      (d : ℤ) + indexedBalance net flow net.sink := by
    calc
      _ = ∑ v : Fin nodes, ((if v = net.source then (d : ℤ) else 0) +
          (if v = net.sink then indexedBalance net flow net.sink else 0)) :=
        Finset.sum_congr rfl (fun v _ => hterm v)
      _ = _ := by rw [Finset.sum_add_distrib]; simp
  rw [hsumEq] at hsum
  have ht : indexedBalance net flow net.sink = -(d : ℤ) := by omega
  intro v
  by_cases hsource : v = net.source
  · subst v; simp [hs]
  · by_cases hsink : v = net.sink
    · subst v; simp [hsource, ht]
    · simp [hsource, hsink, hc v hsource hsink]

/-- A feasible selected fixed-demand flow projects to a feasible indexed original flow. -/
theorem maxFlow_projection_feasible {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    (hhead : ∀ i, net.head i ≠ net.source) (bits : List ℕ) (hlen : bits.length = 2 * arcs)
    (hf : IsFlow (maxFlowNetwork net) (select (maxFlowNetwork net) bits)) :
    IsIndexedFlow net (flowValue (select (numberedArcs net) bits)) (maxFlowProjection bits) := by
  apply isIndexedFlow_of_conservation
  · rw [← projection_balance, numberedNode_source, listBalance_eq,
      numbered_selected_source_inflow net hhead]
    simp [flowValue]
  · intro v hs ht
    have hs' : numberedNode net v ≠ .source := by
      intro he
      exact hs (numberedNode_injective net (he.trans (numberedNode_source net).symm))
    have ht' : numberedNode net v ≠ .sink := by
      intro he
      exact ht (numberedNode_injective net (he.trans (numberedNode_sink net).symm))
    have hbal : listBalance (select (maxFlowNetwork net) bits) (numberedNode net v) = 0 := by
      rw [listBalance_eq, hf.2 _ hs' ht', sub_self]
    obtain ⟨b, _, he⟩ := maxFlow_selected_split net bits hlen
    rw [he, listBalance_append, bypass_balance] at hbal
    simp only [hs', ht', ite_false, add_zero] at hbal
    exact (projection_balance net bits v).symm.trans hbal

/-- The Boolean vector encoding of an indexed flow. -/
def indexedBits {arcs : ℕ} (flow : IndexedFlow arcs) : List ℕ :=
  List.ofFn fun i => if flow i then 1 else 0

theorem projection_indexedBits {arcs : ℕ} (flow : IndexedFlow arcs) :
    maxFlowProjection (indexedBits flow) = flow := by
  funext i
  unfold maxFlowProjection indexedBits
  rw [List.getD_eq_getElem?_getD]
  simp only [List.getElem?_ofFn, i.isLt, ↓reduceDIte, Option.getD_some]
  cases flow i <;> rfl

/-- Feasible indexed original flows reify to actual unit-capacity arc sublists. -/
theorem indexed_flow_reified {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    (hhead : ∀ i, net.head i ≠ net.source) {flow : IndexedFlow arcs} {d : ℕ}
    (hf : IsIndexedFlow net d flow) :
    IsFlow (numberedArcs net) (select (numberedArcs net) (indexedBits flow)) ∧
      flowValue (select (numberedArcs net) (indexedBits flow)) = d := by
  let chosen := select (numberedArcs net) (indexedBits flow)
  have hbalance : ∀ v, listBalance chosen (numberedNode net v) = indexedBalance net flow v := by
    intro v
    rw [projection_balance, projection_indexedBits]
  refine ⟨⟨select_sublist _ _, fun v hs ht => ?_⟩, ?_⟩
  · have hz : listBalance chosen v = 0 := by
      by_cases hv : ∃ w, numberedNode net w = v
      · obtain ⟨w, rfl⟩ := hv
        have hws : w ≠ net.source := by intro he; exact hs (he ▸ numberedNode_source net)
        have hwt : w ≠ net.sink := by intro he; exact ht (he ▸ numberedNode_sink net)
        rw [hbalance, hf w]
        simp [hws, hwt]
      · unfold listBalance
        apply List.sum_eq_zero
        intro term hterm
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hterm
        obtain ⟨i, _, rfl⟩ := List.mem_map.mp ((select_sublist _ _).subset ha)
        have htail : numberedNode net (net.tail i) ≠ v := fun he => hv ⟨_, he⟩
        have hhead' : numberedNode net (net.head i) ≠ v := fun he => hv ⟨_, he⟩
        simp [numberedArc, htail, hhead']
    rw [listBalance_eq] at hz
    exact_mod_cast (sub_eq_zero.mp hz).symm
  · have hs := hbalance net.source
    rw [numberedNode_source, listBalance_eq, numbered_selected_source_inflow net hhead,
      hf net.source] at hs
    simpa [flowValue] using hs

/-- Every indexed unit-capacity feasible flow has value at most the number of occurrences. -/
theorem indexed_flow_value_le_arcs {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    (hhead : ∀ i, net.head i ≠ net.source) {flow : IndexedFlow arcs} {d : ℕ}
    (hf : IsIndexedFlow net d flow) : d ≤ arcs := by
  have heq := (indexed_flow_reified net hhead hf).2
  rw [← heq]
  exact le_trans List.countP_le_length (by
    simpa using (select_sublist (numberedArcs net) (indexedBits flow)).length_le)

/-- A feasible original flow of value `d` extends to fixed demand `m` with exactly `m-d`
selected cost-one bypasses. -/
theorem indexed_flow_fixedDemand {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    (hhead : ∀ i, net.head i ≠ net.source) {flow : IndexedFlow arcs} {d : ℕ}
    (hf : IsIndexedFlow net d flow) :
    let chosen := select (numberedArcs net) (indexedBits flow) ++ List.replicate (arcs - d) bypassArc
    IsFlow (maxFlowNetwork net) chosen ∧ flowValue chosen = arcs ∧ flowCost chosen = arcs - d := by
  dsimp only
  have hrep := indexed_flow_reified net hhead hf
  have hbound := indexed_flow_value_le_arcs net hhead hf
  refine ⟨⟨?_, fun v hs ht => ?_⟩, ?_, ?_⟩
  · exact hrep.1.1.append ((List.replicate_sublist_replicate bypassArc).mpr (Nat.sub_le _ _))
  · have hbal : listBalance
        (select (numberedArcs net) (indexedBits flow) ++ List.replicate (arcs - d) bypassArc) v = 0 := by
      rw [listBalance_append, bypass_balance, listBalance_eq, hrep.1.2 v hs ht]
      simp [hs, ht]
    rw [listBalance_eq] at hbal
    exact_mod_cast (sub_eq_zero.mp hbal).symm
  · have hbypass : flowValue (List.replicate (arcs - d) bypassArc) = arcs - d := by
      simp [flowValue, outflow, bypassArc, List.countP_replicate, FlowNode.beq]
    change outflow _ _ = _
    rw [outflow, List.countP_append]
    change flowValue (select (numberedArcs net) (indexedBits flow)) +
      flowValue (List.replicate (arcs - d) bypassArc) = arcs
    rw [hrep.2, hbypass]
    omega
  · change (List.map Arc.cost _).sum = _
    rw [List.map_append, List.sum_append]
    change flowCost (select (numberedArcs net) (indexedBits flow)) +
      flowCost (List.replicate (arcs - d) bypassArc) = arcs - d
    rw [numbered_selected_cost]
    simp [flowCost, bypassArc]

/-- Exact optimality projection of the min-cost reduction: its original bits form a
maximum-value integral indexed flow, with parallel occurrences retained separately. -/
theorem maxFlow_projection_optimal {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    (_hn : nodes ≤ 2 * arcs + 2) (hhead : ∀ i, net.head i ≠ net.source)
    (_htail : ∀ i, net.tail i ≠ net.sink) (bits : List ℕ)
    (hlen : bits.length = 2 * arcs) (_hbits : ∀ b ∈ bits, b ≤ 1)
    (hmin : IsMinFlow (maxFlowNetwork net) arcs (select (maxFlowNetwork net) bits)) :
    ∃ d, IsIndexedFlow net d (maxFlowProjection bits) ∧
      ∀ (flow : IndexedFlow arcs) (q : ℕ), IsIndexedFlow net q flow → q ≤ d := by
  let d := flowValue (select (numberedArcs net) bits)
  have hfeas := maxFlow_projection_feasible net hhead bits hlen hmin.1
  obtain ⟨b, _, hsplit⟩ := maxFlow_selected_split net bits hlen
  have hdb : d + b = arcs := by
    have hv := hmin.2.1
    rw [hsplit, flowValue, outflow, List.countP_append] at hv
    have hbypass : outflow (List.replicate b bypassArc) .source = b := by
      simp [outflow, bypassArc, List.countP_replicate, FlowNode.beq]
    change outflow (select (numberedArcs net) bits) .source +
      outflow (List.replicate b bypassArc) .source = arcs at hv
    rw [hbypass] at hv
    exact hv
  have hcost : flowCost (select (maxFlowNetwork net) bits) = b := by
    rw [hsplit]
    change (List.map Arc.cost _).sum = _
    rw [List.map_append, List.sum_append]
    change flowCost (select (numberedArcs net) bits) +
      flowCost (List.replicate b bypassArc) = b
    rw [numbered_selected_cost]
    simp [flowCost, bypassArc]
  refine ⟨d, hfeas, fun flow q hf => ?_⟩
  obtain ⟨hflow, hvalue, hothercost⟩ := indexed_flow_fixedDemand net hhead hf
  have hineq := hmin.2.2 _ hflow hvalue
  rw [hcost, hothercost] at hineq
  have hbound := indexed_flow_value_le_arcs net hhead hf
  omega

end STACS2027.Runtimes.Flow

module

public import Runtimes.Flow.PaddedNetwork
public import Runtimes.Flow.MaxFlowProjection

/-! Padding the bypass budget preserves the exact maximum-flow projection.  This permits
the original indexed network to retain isolated vertices and the global vertex numbering. -/

@[expose] public section

namespace STACS2027.Runtimes.Flow

open STACS2027

theorem paddedMaxFlow_selected_split {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    (padding : ℕ) (bits : List ℕ) (hlen : bits.length = arcs + padding) :
    ∃ b ≤ padding, select (paddedMaxFlowNetwork net padding) bits =
      select (numberedArcs net) bits ++ List.replicate b bypassArc := by
  rw [paddedMaxFlowNetwork, select_append _ _ bits (by simp; omega), numberedArcs_length]
  obtain ⟨b, hb, he⟩ := select_replicate bypassArc padding (bits.drop arcs)
  exact ⟨b, hb, by rw [he]⟩

theorem paddedMaxFlow_projection_feasible {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    (padding : ℕ) (hhead : ∀ i, net.head i ≠ net.source) (bits : List ℕ)
    (hlen : bits.length = arcs + padding)
    (hf : IsFlow (paddedMaxFlowNetwork net padding) (select (paddedMaxFlowNetwork net padding) bits)) :
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
    have hbal : listBalance (select (paddedMaxFlowNetwork net padding) bits) (numberedNode net v) = 0 := by
      rw [listBalance_eq, hf.2 _ hs' ht', sub_self]
    obtain ⟨b, _, he⟩ := paddedMaxFlow_selected_split net padding bits hlen
    rw [he, listBalance_append, bypass_balance] at hbal
    simp only [hs', ht', ite_false, add_zero] at hbal
    exact (projection_balance net bits v).symm.trans hbal

/-- A feasible original flow extends to the padded fixed demand with exactly the unused
part of that demand supplied by unit-cost direct bypasses. -/
theorem indexed_flow_paddedDemand {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    (padding : ℕ) (hpadding : arcs ≤ padding)
    (hhead : ∀ i, net.head i ≠ net.source) {flow : IndexedFlow arcs} {d : ℕ}
    (hf : IsIndexedFlow net d flow) :
    let chosen := select (numberedArcs net) (indexedBits flow) ++ List.replicate (padding - d) bypassArc
    IsFlow (paddedMaxFlowNetwork net padding) chosen ∧
      flowValue chosen = padding ∧ flowCost chosen = padding - d := by
  dsimp only
  have hrep := indexed_flow_reified net hhead hf
  have hbound := le_trans (indexed_flow_value_le_arcs net hhead hf) hpadding
  refine ⟨⟨?_, fun v hs ht => ?_⟩, ?_, ?_⟩
  · exact hrep.1.1.append ((List.replicate_sublist_replicate bypassArc).mpr (Nat.sub_le _ _))
  · have hbal : listBalance
        (select (numberedArcs net) (indexedBits flow) ++ List.replicate (padding - d) bypassArc) v = 0 := by
      rw [listBalance_append, bypass_balance, listBalance_eq, hrep.1.2 v hs ht]
      simp [hs, ht]
    rw [listBalance_eq] at hbal
    exact_mod_cast (sub_eq_zero.mp hbal).symm
  · have hbypass : flowValue (List.replicate (padding - d) bypassArc) = padding - d := by
      simp [flowValue, outflow, bypassArc, List.countP_replicate, FlowNode.beq]
    change outflow _ _ = _
    rw [outflow, List.countP_append]
    change flowValue (select (numberedArcs net) (indexedBits flow)) +
      flowValue (List.replicate (padding - d) bypassArc) = padding
    rw [hrep.2, hbypass]
    omega
  · change (List.map Arc.cost _).sum = _
    rw [List.map_append, List.sum_append]
    change flowCost (select (numberedArcs net) (indexedBits flow)) +
      flowCost (List.replicate (padding - d) bypassArc) = padding - d
    rw [numbered_selected_cost]
    simp [flowCost, bypassArc]

/-- Optimal fixed-demand flow with a sufficient bypass budget projects to a maximum
indexed original flow, including when the original graph has isolated vertices. -/
theorem paddedMaxFlow_projection_optimal {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    (padding : ℕ) (hpadding : arcs ≤ padding)
    (_hn : nodes ≤ arcs + padding + 2) (hhead : ∀ i, net.head i ≠ net.source)
    (_htail : ∀ i, net.tail i ≠ net.sink) (bits : List ℕ)
    (hlen : bits.length = arcs + padding) (_hbits : ∀ b ∈ bits, b ≤ 1)
    (hmin : IsMinFlow (paddedMaxFlowNetwork net padding) padding
      (select (paddedMaxFlowNetwork net padding) bits)) :
    ∃ d, IsIndexedFlow net d (maxFlowProjection bits) ∧
      ∀ (flow : IndexedFlow arcs) (q : ℕ), IsIndexedFlow net q flow → q ≤ d := by
  let d := flowValue (select (numberedArcs net) bits)
  have hfeas := paddedMaxFlow_projection_feasible net padding hhead bits hlen hmin.1
  obtain ⟨b, _, hsplit⟩ := paddedMaxFlow_selected_split net padding bits hlen
  have hdb : d + b = padding := by
    have hv := hmin.2.1
    rw [hsplit, flowValue, outflow, List.countP_append] at hv
    have hbypass : outflow (List.replicate b bypassArc) .source = b := by
      simp [outflow, bypassArc, List.countP_replicate, FlowNode.beq]
    change outflow (select (numberedArcs net) bits) .source +
      outflow (List.replicate b bypassArc) .source = padding at hv
    rw [hbypass] at hv
    exact hv
  have hcost : flowCost (select (paddedMaxFlowNetwork net padding) bits) = b := by
    rw [hsplit]
    change (List.map Arc.cost _).sum = _
    rw [List.map_append, List.sum_append]
    change flowCost (select (numberedArcs net) bits) +
      flowCost (List.replicate b bypassArc) = b
    rw [numbered_selected_cost]
    simp [flowCost, bypassArc]
  refine ⟨d, hfeas, fun flow q hf => ?_⟩
  obtain ⟨hflow, hvalue, hothercost⟩ := indexed_flow_paddedDemand net padding hpadding hhead hf
  have hineq := hmin.2.2 _ hflow hvalue
  rw [hcost, hothercost] at hineq
  have hbound := le_trans (indexed_flow_value_le_arcs net hhead hf) hpadding
  omega

/-- A correct solver answer on the padded reduction supplies the maximum indexed flow;
the infeasible-answer case is excluded by the direct bypass witness. -/
theorem paddedMaxFlow_answer_optimal {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    (padding : ℕ) (hpadding : arcs ≤ padding)
    (hn : nodes ≤ arcs + padding + 2) (hhead : ∀ i, net.head i ≠ net.source)
    (htail : ∀ i, net.tail i ≠ net.sink) (out : List ℕ)
    (hanswer : FlowAnswer (paddedMaxFlowNetwork net padding) padding out) :
    ∃ (bits : List ℕ) (d : ℕ), out = 1 :: bits ∧ bits.length = arcs + padding ∧
      (∀ b ∈ bits, b ≤ 1) ∧ IsIndexedFlow net d (maxFlowProjection bits) ∧
      ∀ (flow : IndexedFlow arcs) (q : ℕ), IsIndexedFlow net q flow → q ≤ d := by
  rcases hanswer with ⟨_, hinfeasible⟩ | ⟨bits, he, hlen, hbits, hmin⟩
  · exact False.elim (hinfeasible ⟨_, paddedMaxFlowNetwork_feasible net⟩)
  · have hlen' : bits.length = arcs + padding := by simpa using hlen
    obtain ⟨d, hd, hmax⟩ :=
      paddedMaxFlow_projection_optimal net padding hpadding hn hhead htail bits hlen' hbits hmin
    exact ⟨bits, d, he, hlen', hbits, hd, hmax⟩

end STACS2027.Runtimes.Flow

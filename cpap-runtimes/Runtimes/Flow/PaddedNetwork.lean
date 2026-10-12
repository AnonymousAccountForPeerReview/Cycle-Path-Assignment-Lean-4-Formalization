module

public import Runtimes.Flow.MaxFlowNetwork
import Mathlib.Tactic

/-! # Fixed-demand padding for sparse unit-capacity cut networks -/

@[expose] public section

namespace STACS2027.Runtimes.Flow

open STACS2027

/-- Padding uses the original instance size even after branches erase graph edges. -/
def paddedMaxFlowNetwork {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    (padding : ℕ) : List Arc := numberedArcs net ++ List.replicate padding bypassArc

@[simp] theorem paddedMaxFlowNetwork_length {nodes arcs : ℕ}
    (net : IndexedNetwork nodes arcs) (padding : ℕ) :
    (paddedMaxFlowNetwork net padding).length = arcs + padding := by simp [paddedMaxFlowNetwork]

private theorem nodeOf_paddedMaxFlowNetwork {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs) (padding : ℕ)
    (v : FlowNode) (hv : NodeOf (paddedMaxFlowNetwork net padding) v) :
    ∃ w : Fin nodes, numberedNode net w = v := by
  rcases hv with rfl | rfl | ⟨a, ha, h⟩
  · exact ⟨net.source, numberedNode_source net⟩
  · exact ⟨net.sink, numberedNode_sink net⟩
  · rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
      rcases h with rfl | rfl
      · exact ⟨net.tail i, rfl⟩
      · exact ⟨net.head i, rfl⟩
    · have heq : a = bypassArc := (List.mem_replicate.mp ha).2
      subst a
      rcases h with rfl | rfl
      · exact ⟨net.source, numberedNode_source net⟩
      · exact ⟨net.sink, numberedNode_sink net⟩

/-- The maximum-flow reduction belongs to exactly the existing cited solver class.
The source/sink incidence restrictions are those obtained by contracting terminals and
discarding edges entering the source or leaving the sink. -/
theorem paddedMaxFlowNetwork_good {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs) (padding : ℕ)
    (hn : nodes ≤ arcs + padding + 2)
    (hsize : 2 ≤ arcs + padding)
    (hhead : ∀ i, net.head i ≠ net.source) (htail : ∀ i, net.tail i ≠ net.sink) :
    GoodNet (numberedNodeNumber net) nodes (paddedMaxFlowNetwork net padding) := by
  constructor
  · intro v hv
    obtain ⟨w, rfl⟩ := nodeOf_paddedMaxFlowNetwork net padding v hv
    simpa using w.isLt
  · intro v w hv hw hnum
    obtain ⟨v', rfl⟩ := nodeOf_paddedMaxFlowNetwork net padding v hv
    obtain ⟨w', rfl⟩ := nodeOf_paddedMaxFlowNetwork net padding w hw
    have hval : v'.val = w'.val := by simpa using hnum
    exact congrArg (numberedNode net) (Fin.val_injective hval)
  · intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
      intro h
      apply hhead i
      apply numberedNode_injective net
      exact h.trans (numberedNode_source net).symm
    · have heq : a = bypassArc := (List.mem_replicate.mp ha).2
      subst a
      simp [bypassArc]
  · intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
      intro h
      apply htail i
      apply numberedNode_injective net
      exact h.trans (numberedNode_sink net).symm
    · have heq : a = bypassArc := (List.mem_replicate.mp ha).2
      subst a
      simp [bypassArc]
  · intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
      simp only [numberedArc, paddedMaxFlowNetwork_length]
      have hi := i.isLt
      omega
    · obtain ⟨hpos, heq⟩ := List.mem_replicate.mp ha
      subst a
      simp only [bypassArc, paddedMaxFlowNetwork_length]
      omega
  · simpa using hn

/-- The fixed demand is always feasible, even when the original graph has no source/sink
path: selecting all bypasses supplies exactly `padding` units. -/
theorem paddedMaxFlowNetwork_feasible {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs) :
    IsFlow (paddedMaxFlowNetwork net padding) (List.replicate padding bypassArc) ∧
      flowValue (List.replicate padding bypassArc) = padding := by
  constructor
  · constructor
    · exact List.sublist_append_right _ _
    · intro v hs ht
      have hs' : FlowNode.source.beq v = false := by
        cases h : FlowNode.source.beq v
        · rfl
        · have hv := (FlowNode.beq_iff _ _).mp h
          exact (hs hv.symm).elim
      have ht' : FlowNode.sink.beq v = false := by
        cases h : FlowNode.sink.beq v
        · rfl
        · have hv := (FlowNode.beq_iff _ _).mp h
          exact (ht hv.symm).elim
      simp [inflow, outflow, bypassArc, List.countP_replicate, hs', ht']
  · simp [flowValue, outflow, bypassArc, List.countP_replicate, FlowNode.beq]

end STACS2027.Runtimes.Flow

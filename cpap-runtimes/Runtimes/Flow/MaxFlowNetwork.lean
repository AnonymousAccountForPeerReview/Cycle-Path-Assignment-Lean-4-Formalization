module

public import Runtimes.Flow.Indexed
import Mathlib.Tactic

/-!
# A fixed-demand min-cost network for a unit-capacity maximum flow

Every original occurrence receives cost zero. Adding `m` cost-one bypasses from source to
sink makes demand `m` feasible. Minimizing the selected bypasses maximizes original flow.
-/

@[expose] public section

namespace STACS2027.Runtimes.Flow

open STACS2027

/-- Reify a numbered vertex using the Section 3 flow-node type. -/
def numberedNode {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs) (v : Fin nodes) : FlowNode :=
  if v = net.source then .source else if v = net.sink then .sink else .triangle v.val

/-- Numbering of the reified vertices; unused flow-node constructors receive zero. -/
def numberedNodeNumber {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs) : FlowNode → ℕ
  | .source => net.source.val
  | .sink => net.sink.val
  | .triangle v => v
  | _ => 0

@[simp] theorem numberedNodeNumber_numberedNode {nodes arcs : ℕ}
    (net : IndexedNetwork nodes arcs) (v : Fin nodes) :
    numberedNodeNumber net (numberedNode net v) = v.val := by
  by_cases hs : v = net.source
  · subst v
    simp [numberedNode, numberedNodeNumber]
  · by_cases ht : v = net.sink
    · subst v
      simp [numberedNode, numberedNodeNumber, net.source_ne_sink, Ne.symm net.source_ne_sink]
    · simp [numberedNode, numberedNodeNumber, hs, ht]

@[simp] theorem numberedNode_source {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs) :
    numberedNode net net.source = .source := by simp [numberedNode]

@[simp] theorem numberedNode_sink {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs) :
    numberedNode net net.sink = .sink := by
  simp [numberedNode, Ne.symm net.source_ne_sink]

/-- Numbered vertices remain distinct after reification. -/
theorem numberedNode_injective {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs) :
    Function.Injective (numberedNode net) := by
  intro v w h
  apply Fin.val_injective
  simpa using congrArg (numberedNodeNumber net) h

/-- The zero-cost arc of an original unit-capacity occurrence. -/
def numberedArc {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs) (i : Fin arcs) : Arc :=
  ⟨numberedNode net (net.tail i), numberedNode net (net.head i), 0⟩

/-- Original zero-cost arc occurrences in their given order. -/
def numberedArcs {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs) : List Arc :=
  (List.finRange arcs).map (numberedArc net)

/-- A unit-cost source-to-sink bypass occurrence. -/
def bypassArc : Arc := ⟨.source, .sink, 1⟩

/-- The fixed-demand maximum-flow reduction: `m` original arcs and `m` bypasses. -/
def maxFlowNetwork {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs) : List Arc :=
  numberedArcs net ++ List.replicate arcs bypassArc

@[simp] theorem numberedArcs_length {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs) :
    (numberedArcs net).length = arcs := by simp [numberedArcs]

@[simp] theorem maxFlowNetwork_length {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs) :
    (maxFlowNetwork net).length = 2 * arcs := by simp [maxFlowNetwork]; omega

private theorem nodeOf_maxFlowNetwork {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    (v : FlowNode) (hv : NodeOf (maxFlowNetwork net) v) :
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
theorem maxFlowNetwork_good {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    (hn : nodes ≤ 2 * arcs + 2)
    (hhead : ∀ i, net.head i ≠ net.source) (htail : ∀ i, net.tail i ≠ net.sink) :
    GoodNet (numberedNodeNumber net) nodes (maxFlowNetwork net) := by
  constructor
  · intro v hv
    obtain ⟨w, rfl⟩ := nodeOf_maxFlowNetwork net v hv
    simpa using w.isLt
  · intro v w hv hw hnum
    obtain ⟨v', rfl⟩ := nodeOf_maxFlowNetwork net v hv
    obtain ⟨w', rfl⟩ := nodeOf_maxFlowNetwork net w hw
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
      simp only [numberedArc, maxFlowNetwork_length]
      have hi := i.isLt
      omega
    · obtain ⟨hpos, heq⟩ := List.mem_replicate.mp ha
      subst a
      simp only [bypassArc, maxFlowNetwork_length]
      omega
  · simpa using hn

/-- The fixed demand is always feasible, even when the original graph has no source/sink
path: selecting all bypasses supplies exactly `m` units. -/
theorem maxFlowNetwork_feasible {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs) :
    IsFlow (maxFlowNetwork net) (List.replicate arcs bypassArc) ∧
      flowValue (List.replicate arcs bypassArc) = arcs := by
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

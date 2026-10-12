module

public import ApproximationHardness.Embed.PlanVertexComplete
public import ApproximationHardness.Embed.PlanDartLoop
public import ApproximationHardness.Embed.PlanInitialization
import Mathlib.Tactic.IntervalCases
import Lean.Elab.Tactic.Omega

/-! Finite semantic bounds for every entry of the compiled forest-plan tables. -/

@[expose] public section

namespace STACS2027.Embed.PlanRAM
open RAM

/-- Both real and synthetic forest nodes have at most two parts. -/
theorem forest_parts_bound {F : ForestData} (hF : F.Valid) (v : Nat) :
    (F.parts v).length≤2 := by
  by_cases hv : v<2*F.E
  · exact ForestData.real_parts_bound hF hv
  · have hn : ¬F.IsVertex v := by intro h;exact hv h.1
    by_cases ht : F.IsTop v
    · obtain ⟨he,hr,hroot⟩ := ForestData.top_of_isTop ht
      rw [he,ForestData.parts_top hr hroot]
      split <;> simp
    · rw [ForestData.parts_other hn ht];simp

/-- Every node part is a real vertex and every dart part is a valid dart. -/
theorem forest_item_bound {F : ForestData} (hF : F.Valid) {v : Nat} {it : Item}
    (hi : it∈F.parts v) :
    match it with
    | .node w => w<4*F.E
    | .dart d => d<2*F.E := by
  cases it with
  | dart d =>
    rcases ForestData.dart_part hi with h | ⟨r,_,_,_,he,hd,_⟩
    · exact (ForestData.mem_dartsAt.mp h.2.1).1
    · omega
  | node w =>
    rcases ForestData.node_part hi with ⟨_,q,hq,_,_,he⟩ | ⟨r,hr,_,_,he⟩
    · have hq' := (ForestData.mem_dartsAt.mp hq).1
      have hb := hF.rep_lt (pair q) (pair_lt hq')
      omega
    · rcases he with he | ⟨hz,_,he⟩
      · have hb := hr.1;omega
      · have hb := hF.rep_lt (pair (F.zOf r)) (pair_lt hz)
        omega

/-- The actual DFS invariant bounds both halves of its postorder. -/
theorem forest_post_bound {G : DG} {s : DS} (hI : G.Inv s) :
    ∀v∈s.post,v<4*G.E := by
  intro v hv
  rcases (hI.post_mem v).mp hv with ⟨hl,_⟩ | ⟨hl,hs,_⟩
  · omega
  · have hb := (hI.vert (v-2*G.E) (by omega)).1
    omega

/-- The zero mutable-memory predicate follows from the initialized actual solver representation. -/
theorem initial_mutable {L : DFSRAM.Layout} {c : Config}
    (hr : RAMSolver.Rep (solverLayout L) c RAMSolver.initialState) : MutableZero L c := by
  intro j hj i hi
  rw [hr.arrays j hj i hi]
  interval_cases j <;> rfl

/-- Preserved scalar registers and zero arrays preserve the exact initialized solver. -/
theorem initial_rep_frame {L : DFSRAM.Layout} {c d : Config}
    (hr : RAMSolver.Rep (solverLayout L) c RAMSolver.initialState)
    (hb : RAMSolver.Bases (solverLayout L) d) (hz : MutableZero L d)
    (hf : ∀r,r<20 →d.reg r=c.reg r) :
    RAMSolver.Rep (solverLayout L) d RAMSolver.initialState := by
  refine ⟨hb,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro j hj i hi
    rw [hz j hj i hi]
    interval_cases j <;> rfl
  · exact (hf 6 (by decide)).trans hr.index
  · exact (hf 7 (by decide)).trans hr.mode
  · exact (hf 8 (by decide)).trans hr.node
  · exact (hf 9 (by decide)).trans hr.group
  · exact (hf 10 (by decide)).trans hr.upperLow
  · exact (hf 11 (by decide)).trans hr.resultLow
  · exact (hf 12 (by decide)).trans hr.upperHead
  · exact (hf 13 (by decide)).trans hr.lowerHead
  · exact (hf 14 (by decide)).trans hr.positiveHead
  · exact (hf 15 (by decide)).trans hr.positiveTail
  · exact (hf 16 (by decide)).trans hr.negativeHead
  · exact (hf 17 (by decide)).trans hr.negativeTail
  · exact (hf 18 (by decide)).trans hr.lowerClassHead
  · exact (hf 19 (by decide)).trans hr.lowerClassTail

end STACS2027.Embed.PlanRAM

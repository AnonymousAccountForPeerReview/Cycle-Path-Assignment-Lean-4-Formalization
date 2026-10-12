module

public import NPHardness.PlanarAssemblyNodes
public import NPHardness.PlanarAssemblyFaces

/-!
The number of nodes lost by simultaneous port assembly is at most the number
of marked port darts. The proof retains every original node cycle without a
marked dart and constructs distinct actual assembled-node cycle labels for
those retained cycles. Disjoint attachment endpoints are the only separation
hypothesis; no Euler or output-planarity condition is assumed.
-/

@[expose] public section
namespace STACS2027.PlanarAssembly.PortPairing
open Complexity Complexity.Planar PlanarGluing
attribute [local instance] Classical.propDecidable
variable {n : Nat} {G : Hypermap n} (P : PortPairing G)

def MarkedNode (d : Fin n) : Prop :=
  ∃ a, P.marked a=true ∧ Reaches G.node d a

theorem marked_active {d : Fin n} (hd : P.marked d=true) : P.switch d≠d := by
  intro he
  have hs := P.switch_marked hd
  have hm := P.face_separated (P.pair d) (by rw [P.pair_marked,hd])
  rw [←hs,he,hd] at hm
  contradiction

theorem switch_opposite_mark {d : Fin n} (hd : P.switch d≠d) :
    P.marked (P.switch d)=!P.marked d := by
  cases hm : P.marked d
  · cases hi : P.marked (faceInverse G d)
    · have he : P.switch d=d := by simp only [switch,hm,hi,Bool.false_eq_true,↓reduceIte]
      exact False.elim (hd he)
    · simp only [switch,hm,hi,Bool.false_eq_true,↓reduceIte,P.pair_marked,Bool.not_false]
  · rw [P.switch_marked hm,P.face_separated _ (by rw [P.pair_marked,hm])]
    rfl

theorem markedNode_of_reaches {a b : Fin n} (h : Reaches G.node a b) :
    P.MarkedNode a ↔ P.MarkedNode b := by
  constructor
  · rintro ⟨d,hd,ha⟩
    exact ⟨d,hd,(h.symm (hm_node_inj G)).trans ha⟩
  · rintro ⟨d,hd,hb⟩
    exact ⟨d,hd,h.trans hb⟩

theorem markedNode_active_iff (hdisj : P.DisjointNodeSwitches) {d : Fin n}
    (hd : P.switch d≠d) : P.MarkedNode d ↔ P.marked d=true := by
  constructor
  · rintro ⟨a,ha,hda⟩
    have he := hdisj d a hd (P.marked_active ha) hda
    rwa [he]
  · intro hm
    exact ⟨d,hm,Reaches.refl _ _⟩

/-- Redirect a marked original node to the other node paired at its unique
attachment endpoint. Original unmarked nodes retain their own cycle label. -/
noncomputable def retainedNodeLabel (d : Fin n) : Fin n :=
  if h : P.MarkedNode d then cmin G.node (P.switch (Classical.choose h)) else cmin G.node d

theorem retainedNodeLabel_marked (hdisj : P.DisjointNodeSwitches)
    {d a : Fin n} (ha : P.marked a=true) (hda : Reaches G.node d a) :
    P.retainedNodeLabel d=cmin G.node (P.switch a) := by
  have hd : P.MarkedNode d := ⟨a,ha,hda⟩
  rw [retainedNodeLabel,dite_eq_left hd]
  have hs := Classical.choose_spec hd
  have he := hdisj (Classical.choose hd) a (P.marked_active hs.1) (P.marked_active ha)
    ((hs.2.symm (hm_node_inj G)).trans hda)
  rw [he]

theorem retainedNodeLabel_unmarked {d : Fin n} (hd : ¬P.MarkedNode d) :
    P.retainedNodeLabel d=cmin G.node d := by
  rw [retainedNodeLabel,dite_eq_right hd]

theorem retainedNodeLabel_old_step (hdisj : P.DisjointNodeSwitches) (d : Fin n) :
    P.retainedNodeLabel (G.node d)=P.retainedNodeLabel d := by
  by_cases hd : P.MarkedNode d
  · obtain ⟨a,ha,hda⟩ := hd
    rw [P.retainedNodeLabel_marked hdisj ha hda,
      P.retainedNodeLabel_marked hdisj ha ((Reaches.step G.node d).symm (hm_node_inj G) |>.trans hda)]
  · have hn : ¬P.MarkedNode (G.node d) := fun hn => hd
      ((P.markedNode_of_reaches (Reaches.step G.node d)).mpr hn)
    rw [P.retainedNodeLabel_unmarked hd,P.retainedNodeLabel_unmarked hn,cmin_step (hm_node_inj G)]

theorem retainedNodeLabel_switch (hdisj : P.DisjointNodeSwitches) (d : Fin n) :
    P.retainedNodeLabel (P.switch d)=P.retainedNodeLabel d := by
  by_cases he : P.switch d=d
  · rw [he]
  · have hs := P.switch_active he
    cases hd : P.marked d
    · have hj : P.marked (P.switch d)=true := by
        rw [P.switch_opposite_mark he,hd]; rfl
      have hu : ¬P.MarkedNode d := by
        intro hm
        have := (P.markedNode_active_iff hdisj he).mp hm
        simp [hd] at this
      rw [P.retainedNodeLabel_marked hdisj hj (Reaches.refl _ _),
        P.switch_involutive,P.retainedNodeLabel_unmarked hu]
    · have hj : P.marked (P.switch d)=false := by
        rw [P.switch_opposite_mark he,hd]; rfl
      have hu : ¬P.MarkedNode (P.switch d) := by
        intro hm
        have := (P.markedNode_active_iff hdisj hs).mp hm
        simp [hj] at this
      rw [P.retainedNodeLabel_marked hdisj hd (Reaches.refl _ _),
        P.retainedNodeLabel_unmarked hu]

theorem retainedNodeLabel_step (hdisj : P.DisjointNodeSwitches) (d : Fin n) :
    P.retainedNodeLabel (P.assembled.node d)=P.retainedNodeLabel d := by
  change P.retainedNodeLabel (G.node (P.switch d))=P.retainedNodeLabel d
  rw [P.retainedNodeLabel_old_step hdisj,P.retainedNodeLabel_switch hdisj]

noncomputable def retainedNodeRoot (d : Fin n) : Bool :=
  CycleMin G.node d && !decide (P.MarkedNode d)

/-- Retained old node roots have distinct labels invariant under the new node
permutation, so each contributes an actual distinct assembled node cycle. -/
theorem retained_nodes_le (hdisj : P.DisjointNodeSwitches) :
    (List.finRange n).countP P.retainedNodeRoot ≤ cycleCount P.assembled.node := by
  let roots := (List.finRange n).filter P.retainedNodeRoot
  have hlabel : ∀d∈roots,P.retainedNodeLabel d=d := by
    intro d hd
    have hh := (List.mem_filter.mp hd).2
    simp only [retainedNodeRoot,Bool.and_eq_true,Bool.not_eq_true',decide_eq_false_iff_not] at hh
    rw [P.retainedNodeLabel_unmarked hh.2,(cmin_eq_iff (hm_node_inj G) d).mpr hh.1]
  have he : roots.map P.retainedNodeLabel=roots := by
    calc roots.map P.retainedNodeLabel = roots.map id := List.map_congr_left hlabel
         _ = roots := List.map_id roots
  have hb := cycleCount_ge P.assembled.node P.retainedNodeLabel
    (P.retainedNodeLabel_step hdisj) roots (by rw [he]; exact (List.nodup_finRange n).filter _)
  simpa only [roots,←List.countP_eq_length_filter] using hb

/-- There is at most one discarded old node cycle per marked attachment dart. -/
theorem marked_nodes_le :
    (List.finRange n).countP (fun d => CycleMin G.node d && decide (P.MarkedNode d)) ≤
      (List.finRange n).countP P.marked := by
  classical
  let roots := (List.finRange n).filter fun d => CycleMin G.node d && decide (P.MarkedNode d)
  have hex : ∀d∈roots,∃a,P.marked a=true ∧ Reaches G.node d a := by
    intro d hd
    have hh := (List.mem_filter.mp hd).2
    simp only [Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2
  let pick : Fin n → Fin n := fun d => if h:d∈roots then Classical.choose (hex d h) else d
  have hpick : ∀d∈roots,P.marked (pick d)=true ∧ Reaches G.node d (pick d) := by
    intro d hd
    simpa only [pick,dite_eq_left hd] using Classical.choose_spec (hex d hd)
  have hnd : (roots.map pick).Nodup := by
    apply nodup_map_of_injOn' pick ((List.nodup_finRange n).filter _)
    intro a ha b hb he
    have hca : CycleMin G.node a=true := by
      have hh := (List.mem_filter.mp ha).2
      simp only [Bool.and_eq_true] at hh
      exact hh.1
    have hcb : CycleMin G.node b=true := by
      have hh := (List.mem_filter.mp hb).2
      simp only [Bool.and_eq_true] at hh
      exact hh.1
    have hra := (hpick a ha).2
    have hrb := (hpick b hb).2
    have hc : Reaches G.node a b := hra.trans (by rw [he]; exact hrb.symm (hm_node_inj G))
    obtain ⟨k,hk⟩ := hc
    have hmin := cmin_iterate (hm_node_inj G) a k
    rw [hk,(cmin_eq_iff (hm_node_inj G) a).mpr hca,
      (cmin_eq_iff (hm_node_inj G) b).mpr hcb] at hmin
    exact hmin.symm
  have hb := length_le_countP P.marked (roots.map pick) hnd (by
    intro a ha
    obtain ⟨d,hd,rfl⟩ := List.mem_map.mp ha
    exact (hpick d hd).1)
  simpa only [List.length_map,roots,←List.countP_eq_length_filter] using hb

/-- At most two vertices are lost for each matched pair of port edges, while
both edge copies remain in the assembled multigraph. -/
theorem node_count_loss (hdisj : P.DisjointNodeSwitches) :
    cycleCount G.node ≤ cycleCount P.assembled.node + (List.finRange n).countP P.marked := by
  have hsplit := countP_split (CycleMin G.node) (fun d => decide (P.MarkedNode d)) (List.finRange n)
  have hkeep := P.retained_nodes_le hdisj
  have hdrop := P.marked_nodes_le
  change _ ≤ cycleCount P.assembled.node at hkeep
  rw [cycleCount_eq]
  change _ = _ + (List.finRange n).countP P.retainedNodeRoot at hsplit
  omega

end STACS2027.PlanarAssembly.PortPairing

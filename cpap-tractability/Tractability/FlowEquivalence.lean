module

public import Tractability.FlowTools

/-!
# Theorem 2: assignments and integral flows

An assignment of `CPAP(G, 4)` yields an integral flow of value `2t` and the same
cost (`flow_of_assignment`), and an integral flow of value `2t` yields an assignment
of no greater cost (`assignment_of_flow`). Hence `CPAP(G, 4)` has an assignment of
cost at most `B` exactly when the network has such a flow (`hasAssignment_iff_flow`).
-/

@[expose] public section
namespace STACS2027

/-! ## Shared facts -/

theorem sum_map_le_sum_map {α : Type} (l : List α) (f g : α → Nat) (h : ∀ x ∈ l, f x ≤ g x) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => exact Nat.le_refl _
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons]
    have := h x List.mem_cons_self
    have := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    omega

/-- On a four-cycle, each opposing pair meets each of the four paths in exactly one edge. -/
theorem opposingPair_countP_selected {a b u v : Nat} (hab : a ≠ b) (hau : a ≠ u) (hav : a ≠ v)
    (hbu : b ≠ u) (hbv : b ≠ v) (huv : u ≠ v) {j : Nat} (hj : j < 4) (p : Bool) :
    (opposingPair [a, b, u, v] p).countP (fun e => decide (e ∈ selected [a, b, u, v] j)) = 1 := by
  have hc : (opposingPair [a, b, u, v] p).countP (fun e => decide (e ∈ selected [a, b, u, v] j)) =
      (opposingPair [a, b, u, v] p).count (chosenEdge [a, b, u, v] j p) := by
    simp only [List.count]
    apply List.countP_congr
    intro e he
    simp only [decide_eq_true_eq, beq_iff_eq]
    constructor
    · exact fun hs => pair_mem_selected_unique hab hau hav hbu hbv huv hj p he hs
    · rintro rfl; exact chosenEdge_mem_selected a b u v hj p
  rw [hc]
  exact (opposingPair_nodup hab hau hav hbu hbv huv p).count_of_mem (chosenEdge_mem_pair a b u v j p)

/-- The inflow of an edge node is the load of the edge, for any flow whose pair arcs are
exactly those naming an edge of the chosen path. -/
theorem inflow_edge_eq_load (g : Graph) (P : Arc → Bool) (f : Nat → List Edge)
    (hf : ∀ i, i < (cycles g 4).length → ∃ j, j < 4 ∧ f i = selected (fourCycle g i) j)
    (hP : ∀ i, i < (cycles g 4).length → ∀ p, ∀ e ∈ opposingPair (fourCycle g i) p,
      (P ⟨.pair i p, .edgeNode e, 0⟩ = true ↔ e ∈ f i)) (e₀ : Edge) :
    inflow (flowOf g P) (.edgeNode e₀) = load ((List.range (cycles g 4).length).map f) e₀ := by
  rw [inflow_flowOf_edge g P e₀ (fun i hi p => opposingPair_fourCycle_nodup g hi p)]
  rw [load_eq_sum_indicator]
  · apply congrArg List.sum
    apply List.map_congr_left
    intro i hi
    have hi' := List.mem_range.mp hi
    obtain ⟨a, b, u, v, hc, hab, hau, hav, hbu, hbv, huv⟩ := fourCycle_shape (fourCycle_isCycle g hi')
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
    exact selected_nodup (fourCycle_isCycle g hi).2.2.1 j

theorem path_edges_mem_cycleEdgeList (g : Graph) {i : Nat} (hi : i < (cycles g 4).length)
    {j : Nat} {e : Edge} (he : e ∈ selected (fourCycle g i) j) : e ∈ cycleEdgeList g :=
  (mem_cycleEdgeList g e).mpr ⟨fourCycle g i, fourCycle_mem g hi, selected_mem_cycleEdges he⟩

/-- The load of an edge is at most the number of cycles containing it. -/
theorem load_le_cycleCount (g : Graph) (f : Nat → List Edge)
    (hf : ∀ i, i < (cycles g 4).length → ∃ j, j < 4 ∧ f i = selected (fourCycle g i) j) (e : Edge) :
    load ((List.range (cycles g 4).length).map f) e ≤ cycleCount g e := by
  rw [load_eq_sum_indicator, cycleCount_eq_sum]
  · apply sum_map_le_sum_map
    intro i hi
    obtain ⟨j, _, hfi⟩ := hf i (List.mem_range.mp hi)
    by_cases hm : e ∈ f i
    · have hce : e ∈ cycleEdges (fourCycle g i) := by
        rw [hfi] at hm; exact selected_mem_cycleEdges hm
      simp [hm, hce]
    · simp [hm]
  · intro i hi
    obtain ⟨j, _, hfi⟩ := hf i hi
    rw [hfi]
    exact selected_nodup (fourCycle_isCycle g hi).2.2.1 j

theorem load_eq_zero_of_not_mem (g : Graph) (f : Nat → List Edge)
    (hf : ∀ i, i < (cycles g 4).length → ∃ j, j < 4 ∧ f i = selected (fourCycle g i) j) {e : Edge}
    (he : e ∉ cycleEdgeList g) : load ((List.range (cycles g 4).length).map f) e = 0 := by
  rw [load_eq_sum_indicator]
  · apply List.sum_eq_zero_iff_forall_eq_nat.mpr
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    obtain ⟨j, _, hfi⟩ := hf i (List.mem_range.mp hi)
    have : e ∉ f i := fun hm => he (path_edges_mem_cycleEdgeList g (List.mem_range.mp hi) (hfi ▸ hm))
    simp [this]
  · intro i hi
    obtain ⟨j, _, hfi⟩ := hf i hi
    rw [hfi]
    exact selected_nodup (fourCycle_isCycle g hi).2.2.1 j

/-- The pairwise cost of the paths is the load objective over the cycle edges. -/
theorem cost_paths_eq_load_sum (g : Graph) (f : Nat → List Edge)
    (hf : ∀ i, i < (cycles g 4).length → ∃ j, j < 4 ∧ f i = selected (fourCycle g i) j) :
    cost ((List.range (cycles g 4).length).map f) =
      ((cycleEdgeList g).map fun e => pairCount (load ((List.range (cycles g 4).length).map f) e)).sum := by
  apply cost_eq_load_sum _ _ (cycleEdgeList_nodup g)
  · intro p hp
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
    obtain ⟨j, _, hfi⟩ := hf i (List.mem_range.mp hi)
    rw [hfi]
    exact selected_nodup (fourCycle_isCycle g (List.mem_range.mp hi)).2.2.1 j
  · intro p hp e he
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
    obtain ⟨j, _, hfi⟩ := hf i (List.mem_range.mp hi)
    exact path_edges_mem_cycleEdgeList g (List.mem_range.mp hi) (hfi ▸ he)

/-! ## From an assignment to a flow -/

/-- The arcs of the flow induced by the paths `ps` (indexed like `cycles g 4`): every source
arc, the pair arc naming the edge of the path in its pair, and the `l(e)` cheapest sink arcs
of each edge. -/
def assignmentPredicate (ps : List (List Edge)) : Arc → Bool
  | ⟨.source, _, _⟩ => true
  | ⟨.pair i _, .edgeNode e, _⟩ => decide (e ∈ ps.getD i [])
  | ⟨.edgeNode e, .sink, j⟩ => decide (j < load ps e)
  | _ => false

theorem flow_of_assignment (g : Graph) (ps : List (List Edge))
    (hv : ValidChoices ((cycles g 4).map selectedOptions) ps) :
    IsFlow (fourCycleNetwork g) (flowOf g (assignmentPredicate ps)) ∧
      flowValue (flowOf g (assignmentPredicate ps)) = 2 * (cycles g 4).length ∧
      flowCost (flowOf g (assignmentPredicate ps)) = cost ps := by
  obtain ⟨hlen, hall⟩ := validChoices_getD hv
  obtain ⟨f, hfdef⟩ : ∃ f : Nat → List Edge, f = fun i => ps.getD i [] := ⟨_, rfl⟩
  have hps : ps = (List.range (cycles g 4).length).map f := by
    rw [hfdef, ← hlen]; exact (map_getD_range ps []).symm
  have hf : ∀ i, i < (cycles g 4).length → ∃ j, j < 4 ∧ f i = selected (fourCycle g i) j := by
    intro i hi
    obtain ⟨a, b, u, v, hc, _⟩ := fourCycle_shape (fourCycle_isCycle g hi)
    have : f i ∈ selectedOptions (fourCycle g i) := by rw [hfdef]; exact hall i hi
    rw [hc] at this ⊢
    exact (mem_selectedOptions_four a b u v (f i)).mp this
  have hP : ∀ i, i < (cycles g 4).length → ∀ p, ∀ e ∈ opposingPair (fourCycle g i) p,
      (assignmentPredicate ps ⟨.pair i p, .edgeNode e, 0⟩ = true ↔ e ∈ f i) := by
    intro i _ p e _
    simp [assignmentPredicate, hfdef]
  refine ⟨⟨flowOf_sublist g _, ?_⟩, ?_, ?_⟩
  · intro v hvs hvz
    cases v with
    | source => exact absurd rfl hvs
    | sink => exact absurd rfl hvz
    | triangle i => rw [inflow_flowOf_triangle, outflow_flowOf_triangle]
    | pair i p =>
      rw [inflow_flowOf_pair, outflow_flowOf_pair]
      by_cases hi : i < (cycles g 4).length
      · simp only [hi, ↓reduceIte]
        obtain ⟨a, b, u, v, hc, hab, hau, hav, hbu, hbv, huv⟩ := fourCycle_shape (fourCycle_isCycle g hi)
        obtain ⟨j, hj, hfi⟩ := hf i hi
        have hcount : (opposingPair (fourCycle g i) p).countP
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
      rw [inflow_edge_eq_load g _ f hf hP, outflow_flowOf_edge]
      by_cases hm : e₀ ∈ cycleEdgeList g
      · simp only [hm, ↓reduceIte]
        have hc : (List.range (cycleCount g e₀)).countP
            (fun j => assignmentPredicate ps ⟨.edgeNode e₀, .sink, j⟩) =
            (List.range (cycleCount g e₀)).countP (fun j => decide (j < load ps e₀)) := by
          apply List.countP_congr
          intro j _
          simp [assignmentPredicate]
        rw [hc, countP_lt_range, hps]
        have := load_le_cycleCount g f hf e₀
        omega
      · simp only [hm, ↓reduceIte]
        exact load_eq_zero_of_not_mem g f hf hm
  · rw [flowValue_flowOf]
    have hall' : ∀ a ∈ sourceLayer (cycles g 4).length, assignmentPredicate ps a = true := by
      intro a ha
      obtain ⟨i, p, _, rfl⟩ := (mem_sourceLayer _ a).mp ha
      rfl
    rw [List.countP_eq_length.mpr hall', sourceLayer_length]
  · rw [flowCost_flowOf, sinkLayer_cost]
    have hcost : cost ps = ((cycleEdgeList g).map fun e => pairCount (load ps e)).sum := by
      rw [hps]; exact cost_paths_eq_load_sum g f hf
    rw [hcost]
    apply congrArg List.sum
    apply List.map_congr_left
    intro e _
    have hc : ((List.range (cycleCount g e)).map fun j =>
        if assignmentPredicate ps ⟨.edgeNode e, .sink, j⟩ then j else 0) =
        (List.range (cycleCount g e)).map fun j => if j < load ps e then j else 0 := by
      apply List.map_congr_left
      intro j _
      simp [assignmentPredicate]
    have hle : load ps e ≤ cycleCount g e := by rw [hps]; exact load_le_cycleCount g f hf e
    rw [hc, sum_range_if_lt _ _ hle]

/-! ## From a flow to an assignment -/

theorem assignment_of_flow (g : Graph) (F : List Arc) (hF : IsFlow (fourCycleNetwork g) F)
    (hval : flowValue F = 2 * (cycles g 4).length) :
    ∃ ps, ValidChoices ((cycles g 4).map selectedOptions) ps ∧ cost ps ≤ flowCost F := by
  classical
  obtain ⟨P, hPdef⟩ : ∃ P : Arc → Bool, P = fun a => decide (a ∈ F) := ⟨_, rfl⟩
  have hFP : F = flowOf g P := by
    rw [hPdef]; exact (Sublist.filter_mem_eq hF.1 (fourCycleNetwork_nodup g)).symm
  have hcons := hF.2
  rw [hFP] at hval hcons
  -- every source arc carries flow
  have hsource : ∀ i, i < (cycles g 4).length → ∀ p, P ⟨.source, .pair i p, 0⟩ = true := by
    rw [flowValue_flowOf] at hval
    have := List.countP_eq_length.mp (by rw [hval, sourceLayer_length])
    intro i hi p
    exact this _ ((mem_sourceLayer _ _).mpr ⟨i, p, hi, rfl⟩)
  -- each pair node sends its unit along exactly one of its two arcs
  have hpair : ∀ i, i < (cycles g 4).length → ∀ p, (opposingPair (fourCycle g i) p).countP
      (fun e => P ⟨.pair i p, .edgeNode e, 0⟩) = 1 := by
    intro i hi p
    have h := hcons (.pair i p) (by intro h; cases h) (by intro h; cases h)
    rw [inflow_flowOf_pair, outflow_flowOf_pair] at h
    simp only [hi, ↓reduceIte, hsource i hi p] at h
    exact h.symm
  -- the chosen edges and the paths
  obtain ⟨q₀, hq₀⟩ : ∃ q₀ : Nat → Bool,
      q₀ = fun i => P ⟨.pair i false, .edgeNode (chosenEdge (fourCycle g i) 0 false), 0⟩ := ⟨_, rfl⟩
  obtain ⟨q₁, hq₁⟩ : ∃ q₁ : Nat → Bool,
      q₁ = fun i => P ⟨.pair i true, .edgeNode (chosenEdge (fourCycle g i) 1 true), 0⟩ := ⟨_, rfl⟩
  obtain ⟨f, hfdef⟩ : ∃ f : Nat → List Edge,
      f = fun i => selected (fourCycle g i) (optionIndex (q₀ i) (q₁ i)) := ⟨_, rfl⟩
  have hf : ∀ i, i < (cycles g 4).length → ∃ j, j < 4 ∧ f i = selected (fourCycle g i) j :=
    fun i _ => ⟨optionIndex (q₀ i) (q₁ i), optionIndex_lt _ _, by rw [hfdef]⟩
  have hP : ∀ i, i < (cycles g 4).length → ∀ p, ∀ e ∈ opposingPair (fourCycle g i) p,
      (P ⟨.pair i p, .edgeNode e, 0⟩ = true ↔ e ∈ f i) := by
    intro i hi p e he
    obtain ⟨a, b, u, v, hc, hab, hau, hav, hbu, hbv, huv⟩ := fourCycle_shape (fourCycle_isCycle g hi)
    have hcount := hpair i hi p
    clear hPdef hFP hcons hval hF hsource hpair
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
    simp only [hfdef, hq₀, hq₁]
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
      · -- e = e₁
        cases h3 : P ⟨.pair i false, .edgeNode (edge u v), 0⟩ <;>
          cases h1 : P ⟨.pair i false, .edgeNode (edge a b), 0⟩ <;>
          simp_all <;> (split <;> simp_all)
      · -- e = e₃
        cases h3 : P ⟨.pair i false, .edgeNode (edge u v), 0⟩ <;>
          cases h1 : P ⟨.pair i false, .edgeNode (edge a b), 0⟩ <;>
          simp_all <;> (split <;> simp_all)
    · rw [pt] at he hcount
      simp only [List.countP_cons, List.countP_nil, Nat.zero_add] at hcount
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · -- e = e₂
        cases h4 : P ⟨.pair i true, .edgeNode (edge v a), 0⟩ <;>
          cases h2 : P ⟨.pair i true, .edgeNode (edge b u), 0⟩ <;>
          simp_all <;> (split <;> simp_all)
      · -- e = e₄
        cases h4 : P ⟨.pair i true, .edgeNode (edge v a), 0⟩ <;>
          cases h2 : P ⟨.pair i true, .edgeNode (edge b u), 0⟩ <;>
          simp_all <;> (split <;> simp_all)
  refine ⟨(List.range (cycles g 4).length).map f, ?_, ?_⟩
  · apply validChoices_of_getD
    · simp
    · intro i hi
      rw [getD_map_range _ f [] hi]
      obtain ⟨a, b, u, v, hc, _⟩ := fourCycle_shape (fourCycle_isCycle g hi)
      change f i ∈ selectedOptions (fourCycle g i)
      rw [hfdef]
      simp only
      rw [hc, mem_selectedOptions_four]
      exact ⟨_, optionIndex_lt _ _, rfl⟩
  · rw [hFP, flowCost_flowOf, sinkLayer_cost, cost_paths_eq_load_sum g f hf]
    apply sum_map_le_sum_map
    intro e he
    have h := hcons (.edgeNode e) (by intro h; cases h) (by intro h; cases h)
    rw [inflow_edge_eq_load g P f hf hP, outflow_flowOf_edge] at h
    simp only [he, ↓reduceIte] at h
    rw [h]
    exact sum_range_if_ge_pairCount _ _

/-! ## Theorem 2 -/

/-- **Theorem 2**, the reduction of Appendix A: `CPAP(G, 4)` has an assignment of cost at most
`budget` iff the network has an integral flow of value `2t` and cost at most `budget`, `t` being
the number of simple four-cycles. The minimum cost of such a flow is therefore `OPT`. -/
theorem cpap4_iff_flow (g : Graph) (budget : Nat) :
    HasAssignment g 4 budget ↔
      ∃ flow, IsFlow (fourCycleNetwork g) flow ∧
        flowValue flow = 2 * (cycles g 4).length ∧ flowCost flow ≤ budget := by
  constructor
  · rintro ⟨ps, hv, hc⟩
    obtain ⟨hflow, hval, hcost⟩ := flow_of_assignment g ps hv
    exact ⟨_, hflow, hval, hcost ▸ hc⟩
  · rintro ⟨F, hF, hval, hcost⟩
    obtain ⟨ps, hv, hc⟩ := assignment_of_flow g F hF hval
    exact ⟨ps, hv, Nat.le_trans hc hcost⟩

end STACS2027

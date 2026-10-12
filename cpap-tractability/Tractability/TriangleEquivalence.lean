module

public import Tractability.TriangleCounts
public import Tractability.FlowEquivalence

/-!
# Corollary `K3TimeComplexity`: triangle assignments and integral flows

An assignment of `CPAP(G, 3)` yields an integral flow of value `t` and the same cost
in the triangle network, and an integral flow of value `t` yields an assignment of no
greater cost: "an integral flow of value `t` selects one edge per triangle and has
minimum cost exactly when the corresponding assignment is optimal".
-/

@[expose] public section
namespace STACS2027

/-! ## Shared facts -/

theorem triangle_path_edge (g : Graph) {i : Nat} (hi : i < (cycles g 3).length) {q : List Edge}
    (hq : q ∈ selectedOptions (triangleAt g i)) :
    ∃ e ∈ cycleEdges (triangleAt g i), q = [e] := by
  obtain ⟨a, b, u, hc, _⟩ := triangle_shape (triangleAt_isCycle g hi)
  rw [hc] at hq ⊢
  exact (mem_selectedOptions_three a b u q).mp hq

theorem triangle_edge_mem_list (g : Graph) {i : Nat} (hi : i < (cycles g 3).length)
    {e : Edge} (he : e ∈ cycleEdges (triangleAt g i)) : e ∈ triangleEdgeList g :=
  (mem_triangleEdgeList g e).mpr ⟨triangleAt g i, triangleAt_mem g hi, he⟩

/-- The inflow of an edge node is the load of the edge, for any flow whose edge arcs are
exactly those naming the chosen edge of the triangle. -/
theorem inflow_triangle_edge_eq_load (g : Graph) (P : Arc → Bool) (f : Nat → List Edge)
    (hf : ∀ i, i < (cycles g 3).length → ∃ e ∈ cycleEdges (triangleAt g i), f i = [e])
    (hP : ∀ i, i < (cycles g 3).length → ∀ e ∈ cycleEdges (triangleAt g i),
      (P ⟨.triangle i, .edgeNode e, 0⟩ = true ↔ e ∈ f i)) (e₀ : Edge) :
    inflow (triangleFlowOf g P) (.edgeNode e₀) =
      load ((List.range (cycles g 3).length).map f) e₀ := by
  rw [inflow_triangleFlowOf_edge, load_eq_sum_indicator]
  · apply congrArg List.sum
    apply List.map_congr_left
    intro i hi
    have hi' := List.mem_range.mp hi
    obtain ⟨e, he, hfi⟩ := hf i hi'
    by_cases hm : e₀ ∈ f i
    · have hce : e₀ ∈ cycleEdges (triangleAt g i) := by
        rw [hfi] at hm; simp at hm; subst hm; exact he
      simp [hm, hce, (hP i hi' e₀ hce).mpr hm]
    · have : ¬ (e₀ ∈ cycleEdges (triangleAt g i) ∧ P ⟨.triangle i, .edgeNode e₀, 0⟩ = true) := by
        rintro ⟨hce, hPe⟩
        exact hm ((hP i hi' e₀ hce).mp hPe)
      simp [hm, this]
  · intro i hi
    obtain ⟨e, _, hfi⟩ := hf i hi
    rw [hfi]; simp

/-- The load of an edge is at most the number of triangles containing it. -/
theorem load_le_triangleCount (g : Graph) (f : Nat → List Edge)
    (hf : ∀ i, i < (cycles g 3).length → ∃ e ∈ cycleEdges (triangleAt g i), f i = [e]) (e : Edge) :
    load ((List.range (cycles g 3).length).map f) e ≤ triangleCount g e := by
  rw [load_eq_sum_indicator, triangleCount_eq_sum]
  · apply sum_map_le_sum_map
    intro i hi
    obtain ⟨e', he', hfi⟩ := hf i (List.mem_range.mp hi)
    by_cases hm : e ∈ f i
    · have hce : e ∈ cycleEdges (triangleAt g i) := by
        rw [hfi] at hm; simp at hm; subst hm; exact he'
      simp [hm, hce]
    · simp [hm]
  · intro i hi
    obtain ⟨e', _, hfi⟩ := hf i hi
    rw [hfi]; simp

theorem triangle_load_eq_zero_of_not_mem (g : Graph) (f : Nat → List Edge)
    (hf : ∀ i, i < (cycles g 3).length → ∃ e ∈ cycleEdges (triangleAt g i), f i = [e]) {e : Edge}
    (he : e ∉ triangleEdgeList g) : load ((List.range (cycles g 3).length).map f) e = 0 := by
  rw [load_eq_sum_indicator]
  · apply List.sum_eq_zero_iff_forall_eq_nat.mpr
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    obtain ⟨e', he', hfi⟩ := hf i (List.mem_range.mp hi)
    have : e ∉ f i := by
      intro hm
      rw [hfi] at hm; simp at hm; subst hm
      exact he (triangle_edge_mem_list g (List.mem_range.mp hi) he')
    simp [this]
  · intro i hi
    obtain ⟨e', _, hfi⟩ := hf i hi
    rw [hfi]; simp

/-- The pairwise cost of the paths is the load objective over the triangle edges. -/
theorem triangle_cost_eq_load_sum (g : Graph) (f : Nat → List Edge)
    (hf : ∀ i, i < (cycles g 3).length → ∃ e ∈ cycleEdges (triangleAt g i), f i = [e]) :
    cost ((List.range (cycles g 3).length).map f) =
      ((triangleEdgeList g).map fun e =>
        pairCount (load ((List.range (cycles g 3).length).map f) e)).sum := by
  apply cost_eq_load_sum _ _ (triangleEdgeList_nodup g)
  · intro p hp
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
    obtain ⟨e, _, hfi⟩ := hf i (List.mem_range.mp hi)
    rw [hfi]; simp
  · intro p hp e he
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
    obtain ⟨e', he', hfi⟩ := hf i (List.mem_range.mp hi)
    rw [hfi] at he; simp at he; subst he
    exact triangle_edge_mem_list g (List.mem_range.mp hi) he'

/-! ## From an assignment to a flow -/

/-- The arcs of the flow induced by the paths `ps` (indexed like `cycles g 3`): every source
arc, the edge arc naming the chosen edge of each triangle, and the `l(e)` cheapest sink arcs of
each edge. -/
def triangleAssignmentPredicate (ps : List (List Edge)) : Arc → Bool
  | ⟨.source, _, _⟩ => true
  | ⟨.triangle i, .edgeNode e, _⟩ => decide (e ∈ ps.getD i [])
  | ⟨.edgeNode e, .sink, j⟩ => decide (j < load ps e)
  | _ => false

theorem triangle_flow_of_assignment (g : Graph) (ps : List (List Edge))
    (hv : ValidChoices ((cycles g 3).map selectedOptions) ps) :
    IsFlow (triangleNetwork g) (triangleFlowOf g (triangleAssignmentPredicate ps)) ∧
      flowValue (triangleFlowOf g (triangleAssignmentPredicate ps)) = (cycles g 3).length ∧
      flowCost (triangleFlowOf g (triangleAssignmentPredicate ps)) = cost ps := by
  obtain ⟨hlen, hall⟩ := validChoices_getD hv
  obtain ⟨f, hfdef⟩ : ∃ f : Nat → List Edge, f = fun i => ps.getD i [] := ⟨_, rfl⟩
  have hps : ps = (List.range (cycles g 3).length).map f := by
    rw [hfdef, ← hlen]; exact (map_getD_range ps []).symm
  have hf : ∀ i, i < (cycles g 3).length → ∃ e ∈ cycleEdges (triangleAt g i), f i = [e] := by
    intro i hi
    have : f i ∈ selectedOptions (triangleAt g i) := by rw [hfdef]; exact hall i hi
    exact triangle_path_edge g hi this
  have hP : ∀ i, i < (cycles g 3).length → ∀ e ∈ cycleEdges (triangleAt g i),
      (triangleAssignmentPredicate ps ⟨.triangle i, .edgeNode e, 0⟩ = true ↔ e ∈ f i) := by
    intro i _ e _
    simp [triangleAssignmentPredicate, hfdef]
  refine ⟨⟨triangleFlowOf_sublist g _, ?_⟩, ?_, ?_⟩
  · intro v hvs hvz
    cases v with
    | source => exact absurd rfl hvs
    | sink => exact absurd rfl hvz
    | pair i p => rw [inflow_triangleFlowOf_pair, outflow_triangleFlowOf_pair]
    | triangle i =>
      rw [inflow_triangleFlowOf_triangle, outflow_triangleFlowOf_triangle]
      by_cases hi : i < (cycles g 3).length
      · simp only [hi, ↓reduceIte]
        obtain ⟨e, he, hfi⟩ := hf i hi
        have hpsi : ps.getD i [] = [e] := by rw [hfdef] at hfi; exact hfi
        have hcount : (cycleEdges (triangleAt g i)).countP
            (fun e' => triangleAssignmentPredicate ps ⟨.triangle i, .edgeNode e', 0⟩) =
            (cycleEdges (triangleAt g i)).countP (fun e' => decide (e' = e)) := by
          apply List.countP_congr
          intro e' _
          simp only [triangleAssignmentPredicate, hpsi, List.mem_singleton]
        rw [hcount]
        have hc : (cycleEdges (triangleAt g i)).countP (fun e' => decide (e' = e)) =
            (cycleEdges (triangleAt g i)).count e := by
          simp only [List.count]
          apply List.countP_congr
          intro e' _
          simp
        rw [hc, (triangleAt_edges_nodup g hi).count_of_mem he]
        rfl
      · simp only [hi, ↓reduceIte]
    | edgeNode e₀ =>
      rw [inflow_triangle_edge_eq_load g _ f hf hP, outflow_triangleFlowOf_edge]
      by_cases hm : e₀ ∈ triangleEdgeList g
      · simp only [hm, ↓reduceIte]
        have hc : (List.range (triangleCount g e₀)).countP
            (fun j => triangleAssignmentPredicate ps ⟨.edgeNode e₀, .sink, j⟩) =
            (List.range (triangleCount g e₀)).countP (fun j => decide (j < load ps e₀)) := by
          apply List.countP_congr
          intro j _
          simp [triangleAssignmentPredicate]
        rw [hc, countP_lt_range, hps]
        have := load_le_triangleCount g f hf e₀
        omega
      · simp only [hm, ↓reduceIte]
        exact triangle_load_eq_zero_of_not_mem g f hf hm
  · rw [flowValue_triangleFlowOf]
    have hall' : ∀ a ∈ triangleSourceLayer (cycles g 3).length,
        triangleAssignmentPredicate ps a = true := by
      intro a ha
      obtain ⟨i, _, rfl⟩ := (mem_triangleSourceLayer _ a).mp ha
      rfl
    rw [List.countP_eq_length.mpr hall', triangleSourceLayer_length]
  · rw [flowCost_triangleFlowOf, sinkLayer_cost]
    have hcost : cost ps = ((triangleEdgeList g).map fun e => pairCount (load ps e)).sum := by
      rw [hps]; exact triangle_cost_eq_load_sum g f hf
    rw [hcost]
    apply congrArg List.sum
    apply List.map_congr_left
    intro e _
    have hc : ((List.range (triangleCount g e)).map fun j =>
        if triangleAssignmentPredicate ps ⟨.edgeNode e, .sink, j⟩ then j else 0) =
        (List.range (triangleCount g e)).map fun j => if j < load ps e then j else 0 := by
      apply List.map_congr_left
      intro j _
      simp [triangleAssignmentPredicate]
    have hle : load ps e ≤ triangleCount g e := by rw [hps]; exact load_le_triangleCount g f hf e
    rw [hc, sum_range_if_lt _ _ hle]

/-! ## From a flow to an assignment -/

theorem countP_one_unique {α : Type} {l : List α} {p : α → Bool} (h : l.countP p = 1)
    {a b : α} (ha : a ∈ l) (hpa : p a = true) (hb : b ∈ l) (hpb : p b = true) : a = b := by
  induction l with
  | nil => simp at ha
  | cons x l ih =>
    rw [List.countP_cons] at h
    rcases List.mem_cons.mp ha with rfl | ha' <;> rcases List.mem_cons.mp hb with rfl | hb'
    · rfl
    · exfalso
      have hpos : 0 < l.countP p := List.countP_pos_iff.mpr ⟨b, hb', hpb⟩
      simp only [hpa, ↓reduceIte] at h
      omega
    · exfalso
      have hpos : 0 < l.countP p := List.countP_pos_iff.mpr ⟨a, ha', hpa⟩
      simp only [hpb, ↓reduceIte] at h
      omega
    · have hl : l.countP p = 1 := by
        have hpos : 0 < l.countP p := List.countP_pos_iff.mpr ⟨a, ha', hpa⟩
        split at h <;> omega
      exact ih hl ha' hb'

/-- The edge of the triangle `C_i` whose arc carries flow, as a path. -/
def triangleChoice (g : Graph) (P : Arc → Bool) (i : Nat) : List Edge :=
  match (cycleEdges (triangleAt g i)).find? fun e => P ⟨.triangle i, .edgeNode e, 0⟩ with
  | some e => [e]
  | none => []

theorem triangle_assignment_of_flow (g : Graph) (F : List Arc) (hF : IsFlow (triangleNetwork g) F)
    (hval : flowValue F = (cycles g 3).length) :
    ∃ ps, ValidChoices ((cycles g 3).map selectedOptions) ps ∧ cost ps ≤ flowCost F := by
  classical
  obtain ⟨P, hPdef⟩ : ∃ P : Arc → Bool, P = fun a => decide (a ∈ F) := ⟨_, rfl⟩
  have hFP : F = triangleFlowOf g P := by
    rw [hPdef]; exact (Sublist.filter_mem_eq hF.1 (triangleNetwork_nodup g)).symm
  have hcons := hF.2
  rw [hFP] at hval hcons
  -- every source arc carries flow
  have hsource : ∀ i, i < (cycles g 3).length → P ⟨.source, .triangle i, 0⟩ = true := by
    rw [flowValue_triangleFlowOf] at hval
    have := List.countP_eq_length.mp (by rw [hval, triangleSourceLayer_length])
    intro i hi
    exact this _ ((mem_triangleSourceLayer _ _).mpr ⟨i, hi, rfl⟩)
  -- each triangle node sends its unit along exactly one of its three arcs
  have htri : ∀ i, i < (cycles g 3).length → (cycleEdges (triangleAt g i)).countP
      (fun e => P ⟨.triangle i, .edgeNode e, 0⟩) = 1 := by
    intro i hi
    have h := hcons (.triangle i) (by intro h; cases h) (by intro h; cases h)
    rw [inflow_triangleFlowOf_triangle, outflow_triangleFlowOf_triangle] at h
    simp only [hi, ↓reduceIte, hsource i hi] at h
    exact h.symm
  obtain ⟨f, hfdef⟩ : ∃ f : Nat → List Edge, f = triangleChoice g P := ⟨_, rfl⟩
  have hf : ∀ i, i < (cycles g 3).length → ∃ e ∈ cycleEdges (triangleAt g i), f i = [e] := by
    intro i hi
    have h1 := htri i hi
    obtain ⟨e, he, hpe⟩ := List.countP_pos_iff.mp (by omega : 0 < (cycleEdges (triangleAt g i)).countP
      (fun e => P ⟨.triangle i, .edgeNode e, 0⟩))
    rw [hfdef, triangleChoice]
    cases hfind : (cycleEdges (triangleAt g i)).find? (fun e => P ⟨.triangle i, .edgeNode e, 0⟩) with
    | none =>
      exfalso
      exact (List.find?_eq_none.mp hfind) e he (by simpa using hpe)
    | some e' =>
      exact ⟨e', List.mem_of_find?_eq_some hfind, rfl⟩
  have hP : ∀ i, i < (cycles g 3).length → ∀ e ∈ cycleEdges (triangleAt g i),
      (P ⟨.triangle i, .edgeNode e, 0⟩ = true ↔ e ∈ f i) := by
    intro i hi e he
    obtain ⟨e', he', hfi⟩ := hf i hi
    have hpe' : P ⟨.triangle i, .edgeNode e', 0⟩ = true := by
      rw [hfdef, triangleChoice] at hfi
      cases hfind : (cycleEdges (triangleAt g i)).find? (fun e => P ⟨.triangle i, .edgeNode e, 0⟩) with
      | none => rw [hfind] at hfi; simp at hfi
      | some e'' =>
        rw [hfind] at hfi
        simp only [List.cons.injEq, and_true] at hfi
        subst hfi
        have h := List.find?_some hfind
        exact h
    rw [hfi]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · intro hpe
      exact countP_one_unique (htri i hi) he hpe he' hpe'
    · rintro rfl; exact hpe'
  refine ⟨(List.range (cycles g 3).length).map f, ?_, ?_⟩
  · apply validChoices_of_getD
    · simp
    · intro i hi
      rw [getD_map_range _ f [] hi]
      obtain ⟨e, he, hfi⟩ := hf i hi
      obtain ⟨a, b, u, hc, _⟩ := triangle_shape (triangleAt_isCycle g hi)
      change f i ∈ selectedOptions (triangleAt g i)
      rw [hfi, hc, mem_selectedOptions_three]
      exact ⟨e, hc ▸ he, rfl⟩
  · rw [hFP, flowCost_triangleFlowOf, sinkLayer_cost, triangle_cost_eq_load_sum g f hf]
    apply sum_map_le_sum_map
    intro e he
    have h := hcons (.edgeNode e) (by intro h; cases h) (by intro h; cases h)
    rw [inflow_triangle_edge_eq_load g P f hf hP, outflow_triangleFlowOf_edge] at h
    simp only [he, ↓reduceIte] at h
    rw [h]
    exact sum_range_if_ge_pairCount _ _

/-! ## The corollary -/

/-- **Corollary `K3TimeComplexity`**, the reduction: `CPAP(G, 3)` has an assignment of cost at
most `budget` iff the triangle network has an integral flow of value `t` and cost at most
`budget`, `t` being the number of triangles. The minimum cost of such a flow is therefore
`OPT`. -/
theorem cpap3_iff_flow (g : Graph) (budget : Nat) :
    HasAssignment g 3 budget ↔
      ∃ flow, IsFlow (triangleNetwork g) flow ∧
        flowValue flow = (cycles g 3).length ∧ flowCost flow ≤ budget := by
  constructor
  · rintro ⟨ps, hv, hc⟩
    obtain ⟨hflow, hval, hcost⟩ := triangle_flow_of_assignment g ps hv
    exact ⟨_, hflow, hval, hcost ▸ hc⟩
  · rintro ⟨F, hF, hval, hcost⟩
    obtain ⟨ps, hv, hc⟩ := triangle_assignment_of_flow g F hF hval
    exact ⟨ps, hv, Nat.le_trans hc hcost⟩

end STACS2027

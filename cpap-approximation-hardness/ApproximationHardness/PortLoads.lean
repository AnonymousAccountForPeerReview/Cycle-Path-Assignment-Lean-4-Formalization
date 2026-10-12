module

public import ApproximationHardness.CrossCost

/-!
# Loads at the literal ports of a clause gadget

Each literal edge of a clause gadget lies on exactly one of the gadget's `k`-cycles, so
the chosen paths of the gadget load it at most once. The lemmas below transport the
local facts about a clause gadget (`clauseFamily_blocked_lower`, the port loads) to its
placed copy in the Theorem 8 graph, indexed by the placed literals of the clause.
-/

set_option maxRecDepth 100000

@[expose] public section
namespace STACS2027
open Complexity.SAT

/-! ## Loads are bounded by the number of cycles through an edge -/

theorem count_selectedAt_le {c : Cycle} (hc : (cycleEdges c).Nodup) (v : Nat) (e : Edge) :
    (selectedAt c v).count e ≤ if e ∈ cycleEdges c then 1 else 0 := by
  rw [← hc.count]
  exact (List.filter_sublist (l := cycleEdges c)).count_le e

theorem load_chosen_le_countP (cs : List Cycle) (hc : ∀ c ∈ cs, (cycleEdges c).Nodup)
    (choose : Cycle → Nat) (e : Edge) :
    load (chosenFamily cs choose) e ≤ cs.countP fun c => decide (e ∈ cycleEdges c) := by
  unfold load chosenFamily
  rw [List.map_map, ← sum_map_countP_eq_length]
  apply sum_map_le_sum_map
  intro c hcm
  have := count_selectedAt_le (hc c hcm) (choose c) e
  simp only [Function.comp_def]
  by_cases h : e ∈ cycleEdges c
  · simp [h] at this ⊢; exact this
  · simp [h] at this ⊢; exact this

theorem clauseThree5_ports_once :
    ∀ e ∈ clauseThreePorts5, clauseThreeCycles5.countP (fun c => decide (e ∈ cycleEdges c)) ≤ 1 := by
  decide

theorem clauseTwo5_ports_once :
    ∀ e ∈ ([(0,1),(4,5)] : List Edge), clauseTwoCycles5.countP (fun c => decide (e ∈ cycleEdges c)) ≤ 1 := by
  decide

theorem clauseTwo6_ports_once :
    ∀ e ∈ ([(0,1),(4,5)] : List Edge), clauseTwoCycles6.countP (fun c => decide (e ∈ cycleEdges c)) ≤ 1 := by
  decide

/-- Each active literal port of a clause gadget carries load at most one. -/
theorem clauseFamily_port_load_le_one {k : Nat} (hk : 5 ≤ k) (c : List PlacedLiteral)
    (choose : Cycle → Nat) {e : Edge} (he : e ∈ activeClausePorts c) :
    load (chosenFamily (clauseFamily k hk c) choose) e ≤ 1 := by
  unfold clauseFamily
  unfold activeClausePorts at he
  by_cases hc : c.length = 2
  · simp only [hc, ↓reduceIte] at he ⊢
    by_cases h6 : k = 6
    · subst h6
      simp only [↓reduceIte]
      refine Nat.le_trans (load_chosen_le_countP _ ?_ choose e) (clauseTwo6_ports_once e he)
      intro d hd
      exact (clauseTwo6_cycles_valid d hd).edges_nodup
    · simp only [h6, ↓reduceIte]
      obtain ⟨hb, hn, hnl⟩ := clauseTwo_links_wellformed k
      have hv := linkSteps_from_base_valid 24 (clauseTwoLinks k) hb hn hnl
      have heq := expanded_family_port_eq hv clauseTwoCycles5 (clauseTwoExpansion k hk)
        clauseTwo5_cycles_self (fun d hd => (clauseTwoExpansion_spec hk hd).1)
        (fun d hd => (clauseTwoExpansion_spec hk hd).2)
        ((by decide : ∀ e ∈ ([(0,1),(4,5)] : List Edge), e ∈ clauseTwoSkeleton) e he)
        (clauseTwo_ports_unchanged h6 e he) (fun d => choose (clauseTwoExpansion k hk d))
      change load (clauseTwoCycles5.map fun d =>
        selectedAt (clauseTwoExpansion k hk d) (choose (clauseTwoExpansion k hk d))) e ≤ 1
      rw [heq]
      refine Nat.le_trans (load_chosen_le_countP _ ?_ _ e) (clauseTwo5_ports_once e he)
      intro d hd
      exact (clauseTwo5_cycles_self d hd).edges_nodup
  · simp only [hc, ↓reduceIte] at he ⊢
    obtain ⟨hb, hn, hnl⟩ := clauseThree_links_wellformed k
    have hv := linkSteps_from_base_valid 18 (clauseThreeLinks k) hb hn hnl
    have heq := expanded_family_port_eq hv clauseThreeCycles5 (clauseThreeExpansion k hk)
      clauseThree5_cycles_self (fun d hd => (clauseThreeExpansion_spec hk hd).1)
      (fun d hd => (clauseThreeExpansion_spec hk hd).2)
      ((by decide : ∀ e ∈ clauseThreePorts5, e ∈ clauseThree5) e he)
      (clauseThree_ports_unchanged k e he) (fun d => choose (clauseThreeExpansion k hk d))
    change load (clauseThreeCycles5.map fun d =>
      selectedAt (clauseThreeExpansion k hk d) (choose (clauseThreeExpansion k hk d))) e ≤ 1
    rw [heq]
    refine Nat.le_trans (load_chosen_le_countP _ ?_ _ e) (clauseThree5_ports_once e he)
    intro d hd
    exact (clauseThree5_cycles_self d hd).edges_nodup

/-! ## Slots and ports -/

/-- A placeholder placed literal for `getD`. -/
def defaultPlaced : PlacedLiteral := ⟨⟨0, true⟩, 0⟩

/-- The literal edge of slot `i`. -/
def slotEdge (i : Nat) : Edge := edge (clauseEndpoint i false) (clauseEndpoint i true)

theorem slotEdge_values : slotEdge 0 = (0, 1) ∧ slotEdge 1 = (4, 5) ∧ slotEdge 2 = (10, 11) := by
  decide

theorem slotEdge_mem_activeClausePorts {c : List PlacedLiteral} (hc : c.length = 2 ∨ c.length = 3)
    {i : Nat} (hi : i < c.length) : slotEdge i ∈ activeClausePorts c := by
  unfold activeClausePorts
  obtain ⟨h0, h1, h2⟩ := slotEdge_values
  rcases hc with hc | hc
  · simp only [hc, ↓reduceIte]
    have : i = 0 ∨ i = 1 := by omega
    rcases this with rfl | rfl <;> simp [h0, h1]
  · have hne : c.length ≠ 2 := by omega
    simp only [hne, ↓reduceIte]
    have : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases this with rfl | rfl | rfl <;> simp [h0, h1, h2, clauseThreePorts5]

/-- The sum of the loads at the active ports, indexed by slots. -/
theorem sum_slots_eq_sum_activePorts {c : List PlacedLiteral} (hc : c.length = 2 ∨ c.length = 3)
    (g : Edge → Nat) :
    ((List.range c.length).map fun i => g (slotEdge i)).sum = ((activeClausePorts c).map g).sum := by
  unfold activeClausePorts
  obtain ⟨h0, h1, h2⟩ := slotEdge_values
  rcases hc with hc | hc
  · simp [hc, h0, h1, List.range_succ]
  · have hne : c.length ≠ 2 := by omega
    simp only [hne, ↓reduceIte]
    simp [hc, h0, h1, h2, clauseThreePorts5, List.range_succ]

/-! ## Transport from the placed clause gadget to the local one -/

/-- The chosen paths of the placed clause gadget `j` are the relabelled chosen paths of a
choice on the local gadget, with the same cost and the same loads at the literal ports,
slot `i` of the local gadget being the port of the `i`-th placed literal. -/
theorem clauseChosen_local {k : Nat} (hk : 5 ≤ k) {f : CNF} (hf : BoundedOccurrence f)
    {j : Nat} (hj : j < (placeFormula [] f).length) (choose : Cycle → Nat)
    (hv : ∀ c ∈ placedClauseFamily k hk (variableBound f) j (placeFormula [] f)[j], choose c ∈ c) :
    ∃ pick : Cycle → Nat, (∀ c ∈ clauseFamily k hk (placeFormula [] f)[j], pick c ∈ c) ∧
      cost (clauseChosen k hk f choose j) = cost (chosenFamily (clauseFamily k hk (placeFormula [] f)[j]) pick) ∧
      ∀ i, i < (placeFormula [] f)[j].length →
        load (clauseChosen k hk f choose j) (literalPortGlobal k ((placeFormula [] f)[j].getD i defaultPlaced)) =
          load (chosenFamily (clauseFamily k hk (placeFormula [] f)[j]) pick) (slotEdge i) := by
  have hcm := List.getElem_mem hj
  have hinj : ∀ a, a < gadgetWidth k → ∀ b, b < gadgetWidth k →
      clauseVertex (gadgetWidth k) (variableBound f) j (placeFormula [] f)[j] a =
      clauseVertex (gadgetWidth k) (variableBound f) j (placeFormula [] f)[j] b → a = b :=
    fun _ ha _ hb he => clauseVertex_injective (width := gadgetWidth k)
      (n := variableBound f) (j := j) (c := (placeFormula [] f)[j])
      (by have := gadgetWidth_ge k; omega) (hf.placed_clause_nodup hcm) (hf.placed_clause_bounds hcm) ha hb he
  obtain ⟨pick, hpick, hpaths, hcost⟩ := mapped_choice_cost (clauseGraph_below k _) (clauseGraph_normalized k _)
    (clauseFamily_valid hk _) (clauseVertex (gadgetWidth k) (variableBound f) j (placeFormula [] f)[j])
    hinj choose hv
  refine ⟨pick, hpick, ?_, ?_⟩
  · rw [clauseChosen_at hk f choose j hj]
    exact hcost
  · intro i hi
    have hi3 : i < 3 := by have := hf.placed_clause_size hcm; omega
    have hip : (placeFormula [] f)[j][i]? = some ((placeFormula [] f)[j].getD i defaultPlaced) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
      rfl
    have hport : literalPortGlobal k ((placeFormula [] f)[j].getD i defaultPlaced) = mapEdge
        (clauseVertex (gadgetWidth k) (variableBound f) j (placeFormula [] f)[j]) (slotEdge i) :=
      (mapped_attachment_edge hi3 hip).symm
    rw [clauseChosen_at hk f choose j hj]
    change load (chosenFamily ((clauseFamily k hk (placeFormula [] f)[j]).map
      (List.map (clauseVertex (gadgetWidth k) (variableBound f) j (placeFormula [] f)[j]))) choose) _ = _
    rw [hpaths, hport]
    exact load_relabel (clauseGraph_below k _) (clauseGraph_normalized k _)
      (clauseVertex (gadgetWidth k) (variableBound f) j (placeFormula [] f)[j]) hinj
      (chosenFamily_supported (clauseFamily_valid hk _) pick) (clauseGraph_ports k _ hi3)

/-- The placed clause gadget loads each of its literal ports at most once. -/
theorem clauseChosen_port_load_le_one {k : Nat} (hk : 5 ≤ k) {f : CNF} (hf : BoundedOccurrence f)
    {j : Nat} (hj : j < (placeFormula [] f).length) (choose : Cycle → Nat)
    (hv : ∀ c ∈ placedClauseFamily k hk (variableBound f) j (placeFormula [] f)[j], choose c ∈ c)
    {p : PlacedLiteral} (hp : p ∈ (placeFormula [] f)[j]) :
    load (clauseChosen k hk f choose j) (literalPortGlobal k p) ≤ 1 := by
  obtain ⟨pick, hpick, _, hload⟩ := clauseChosen_local hk hf hj choose hv
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hp
  have hgetD : (placeFormula [] f)[j][i] = (placeFormula [] f)[j].getD i defaultPlaced := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl
  rw [hgetD, hload i hi]
  exact clauseFamily_port_load_le_one hk _ pick
    (slotEdge_mem_activeClausePorts (hf.placed_clause_size (List.getElem_mem hj)) hi)

/-- Observation (iii) of Theorem 8, placed: the cost of the clause gadget plus the loads at
all its literal ports is at least two. -/
theorem clauseChosen_blocked_lower {k : Nat} (hk : 5 ≤ k) {f : CNF} (hf : BoundedOccurrence f)
    {j : Nat} (hj : j < (placeFormula [] f).length) (choose : Cycle → Nat)
    (hv : ∀ c ∈ placedClauseFamily k hk (variableBound f) j (placeFormula [] f)[j], choose c ∈ c) :
    2 ≤ cost (clauseChosen k hk f choose j) +
      ((placeFormula [] f)[j].map fun p => load (clauseChosen k hk f choose j) (literalPortGlobal k p)).sum := by
  obtain ⟨pick, hpick, hcost, hload⟩ := clauseChosen_local hk hf hj choose hv
  have hsize := hf.placed_clause_size (List.getElem_mem hj)
  have hsum : ((placeFormula [] f)[j].map fun p => load (clauseChosen k hk f choose j) (literalPortGlobal k p)).sum =
      ((activeClausePorts (placeFormula [] f)[j]).map
        (load (chosenFamily (clauseFamily k hk (placeFormula [] f)[j]) pick))).sum := by
    rw [sum_map_eq_sum_range_getD _ defaultPlaced, ← sum_slots_eq_sum_activePorts hsize]
    apply congrArg List.sum
    apply List.map_congr_left
    intro i hi
    exact hload i (List.mem_range.mp hi)
  rw [hsum, hcost]
  exact clauseFamily_blocked_lower hk _ pick hpick

/-- The cost of the placed clause gadget is at least one. -/
theorem clauseChosen_cost_positive {k : Nat} (hk : 5 ≤ k) {f : CNF} (hf : BoundedOccurrence f)
    {j : Nat} (hj : j < (placeFormula [] f).length) (choose : Cycle → Nat)
    (hv : ∀ c ∈ placedClauseFamily k hk (variableBound f) j (placeFormula [] f)[j], choose c ∈ c) :
    1 ≤ cost (clauseChosen k hk f choose j) := by
  rw [clauseChosen_at hk f choose j hj]
  exact placedClauseFamily_cost_positive hk hf ⟨j, hj⟩ choose hv

end STACS2027

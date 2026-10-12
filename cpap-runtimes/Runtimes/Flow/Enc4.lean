module

public import Runtimes.Flow.EdgeSpec
import Mathlib.Tactic

/-!
# The four-cycle network as numbers

The nodes of `net4 cs` are numbered `s = 0`, `z = 1`, `x_{C_i,{e₁,e₃}} = 2 + 2i`,
`x_{C_i,{e₂,e₄}} = 3 + 2i`, and `y_e = 2 + 2t + r` for the `r`-th edge of `eList cs` (`num4`), so
`n4 cs = 2 + 2t + |eList cs|` nodes. This file proves

* `goodNet4`: the numbered network is in the class of the solver (`GoodNet`);
* the layers as the machine writes them: `sourceLayer_succ`, `pairLayer_succ` and `pairChunk4`
  (the four arcs of cycle `i` name the edges of the occurrences `4i, 4i + 2, 4i + 1, 4i + 3`);
* `net4_getD_q0`, `net4_getD_q1`: the arcs read by the extraction are at positions
  `2t + 4i + 1` and `2t + 4i + 3`, and `readOff4_select`: on a `0/1` vector, the read-off is
  given by the bits at these positions.
-/

@[expose] public section

namespace STACS2027.Runtimes.Flow

open STACS2027

/-- The numbering of the nodes of the four-cycle network. -/
def num4 (cs : List Cycle) : FlowNode → ℕ
  | .source => 0
  | .sink => 1
  | .pair i p => 2 + 2 * i + (if p then 1 else 0)
  | .triangle _ => 0
  | .edgeNode e => 2 + 2 * cs.length + (eList cs).idxOf e

/-- The number of nodes of the four-cycle network. -/
def n4 (cs : List Cycle) : ℕ := 2 + 2 * cs.length + (eList cs).length

/-- **The encoded four-cycle network** with required value `2t`: what the construction
machine of Theorem 2 outputs. -/
def netEnc4 (cs : List Cycle) : List ℕ := netInput (num4 cs) (n4 cs) (2 * cs.length) (net4 cs)

/-! ### The layers, arc by arc -/

theorem sourceLayer_succ (t : ℕ) :
    sourceLayer (t + 1) = sourceLayer t ++ [⟨.source, .pair t false, 0⟩, ⟨.source, .pair t true, 0⟩] := by
  simp [sourceLayer, List.range_succ, List.flatMap_append]

theorem pairLayer_succ (t : ℕ) (C : ℕ → Cycle) :
    pairLayer (t + 1) C = pairLayer t C ++ ([false, true].flatMap fun p =>
      (opposingPair (C t) p).map fun e => (⟨.pair t p, .edgeNode e, 0⟩ : Arc)) := by
  simp only [pairLayer, List.range_succ, List.flatMap_append, List.flatMap_singleton]

theorem sinkLayer_take_succ (es : List Edge) (w : Edge → ℕ) {r : ℕ} (hr : r < es.length) :
    sinkLayer (es.take (r + 1)) w = sinkLayer (es.take r) w ++
      (List.range (w (es.getD r (0, 0)))).map fun j => (⟨.edgeNode (es.getD r (0, 0)), .sink, j⟩ : Arc) := by
  rw [List.take_add_one, List.getElem?_eq_getElem hr, Option.toList_some, sinkLayer, sinkLayer,
    List.flatMap_append, List.flatMap_singleton, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hr, Option.getD_some]

section four

variable {g : Graph} {cs : List Cycle}

/-- The four arcs of cycle `i` in the opposing-pair layer, by occurrences. -/
theorem pairChunk4 (hcs : ∀ c ∈ cs, IsCycle g 4 c) {i : ℕ} (hi : i < cs.length) :
    ([false, true].flatMap fun p =>
      (opposingPair (cyc cs i) p).map fun e => (⟨.pair i p, .edgeNode e, 0⟩ : Arc)) =
      [⟨.pair i false, .edgeNode ((occs cs).getD (i * 4 + 0) (0, 0)), 0⟩,
        ⟨.pair i false, .edgeNode ((occs cs).getD (i * 4 + 2) (0, 0)), 0⟩,
        ⟨.pair i true, .edgeNode ((occs cs).getD (i * 4 + 1) (0, 0)), 0⟩,
        ⟨.pair i true, .edgeNode ((occs cs).getD (i * 4 + 3) (0, 0)), 0⟩] := by
  rw [occs_getD_cyc hcs hi (by omega), occs_getD_cyc hcs hi (by omega),
    occs_getD_cyc hcs hi (by omega), occs_getD_cyc hcs hi (by omega)]
  obtain ⟨a, b, u, v, hc, _⟩ := fourCycle_shape (cyc_isCycle hcs hi)
  rw [hc]
  obtain ⟨pf, pt⟩ := opposingPair_four a b u v
  simp [pf, pt, cycleEdges_four]

@[simp] theorem num4_source (cs : List Cycle) : num4 cs .source = 0 := rfl
@[simp] theorem num4_sink (cs : List Cycle) : num4 cs .sink = 1 := rfl
@[simp] theorem num4_pair_false (cs : List Cycle) (i : ℕ) : num4 cs (.pair i false) = 2 + 2 * i := rfl
@[simp] theorem num4_pair_true (cs : List Cycle) (i : ℕ) :
    num4 cs (.pair i true) = 2 + 2 * i + 1 := rfl

/-- The encoding of the four arcs of cycle `i`. -/
theorem encArcs_pairChunk4 (cs : List Cycle) (i : ℕ) :
    encArcs (num4 cs) [⟨.pair i false, .edgeNode ((occs cs).getD (i * 4 + 0) (0, 0)), 0⟩,
        ⟨.pair i false, .edgeNode ((occs cs).getD (i * 4 + 2) (0, 0)), 0⟩,
        ⟨.pair i true, .edgeNode ((occs cs).getD (i * 4 + 1) (0, 0)), 0⟩,
        ⟨.pair i true, .edgeNode ((occs cs).getD (i * 4 + 3) (0, 0)), 0⟩] =
      [2 + 2 * i, 2 + 2 * cs.length + eid cs (i * 4), 0,
        2 + 2 * i, 2 + 2 * cs.length + eid cs (i * 4 + 2), 0,
        2 + 2 * i + 1, 2 + 2 * cs.length + eid cs (i * 4 + 1), 0,
        2 + 2 * i + 1, 2 + 2 * cs.length + eid cs (i * 4 + 3), 0] := rfl

/-- The encoding of the source arcs of cycle `i`. -/
theorem encArcs_srcChunk4 (cs : List Cycle) (i : ℕ) :
    encArcs (num4 cs) [⟨.source, .pair i false, 0⟩, ⟨.source, .pair i true, 0⟩] =
      [0, 2 + 2 * i, 0, 0, 2 + 2 * i + 1, 0] := rfl

theorem num4_occ (cs : List Cycle) (q : ℕ) :
    num4 cs (.edgeNode ((occs cs).getD q (0, 0))) = 2 + 2 * cs.length + eid cs q := rfl

theorem num4_eList {r : ℕ} (hr : r < (eList cs).length) :
    num4 cs (.edgeNode ((eList cs).getD r (0, 0))) = 2 + 2 * cs.length + r := by
  simp only [num4]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr, Option.getD_some,
    (eList_nodup cs).idxOf_getElem r hr]

/-! ### The class of the solver -/

theorem nodeOf_net4 {v : FlowNode} (hv : NodeOf (net4 cs) v) :
    v = .source ∨ v = .sink ∨ (∃ i p, i < cs.length ∧ v = .pair i p) ∨
      (∃ e ∈ eList cs, v = .edgeNode e) := by
  rcases hv with rfl | rfl | ⟨a, ha, hva⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · rw [net4] at ha
    rcases List.mem_append.mp ha with ha | ha
    · rcases List.mem_append.mp ha with ha | ha
      · obtain ⟨i, p, hi, rfl⟩ := (mem_sourceLayer _ a).mp ha
        rcases hva with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inr (Or.inl ⟨i, p, hi, rfl⟩))
      · obtain ⟨i, p, e, hi, he, rfl⟩ := (mem_pairLayer _ _ a).mp ha
        rcases hva with rfl | rfl
        · exact Or.inr (Or.inr (Or.inl ⟨i, p, hi, rfl⟩))
        · exact Or.inr (Or.inr (Or.inr ⟨e, mem_eList.mpr ⟨cyc cs i, cyc_mem hi,
            opposingPair_sub_cycleEdges _ p e he⟩, rfl⟩))
    · obtain ⟨e, j, he, _, rfl⟩ := (mem_sinkLayer _ _ a).mp ha
      rcases hva with rfl | rfl
      · exact Or.inr (Or.inr (Or.inr ⟨e, he, rfl⟩))
      · exact Or.inr (Or.inl rfl)

theorem num4_lt {v : FlowNode} (hv : NodeOf (net4 cs) v) :
    num4 cs v < n4 cs := by
  rcases nodeOf_net4 hv with rfl | rfl | ⟨i, p, hi, rfl⟩ | ⟨e, he, rfl⟩
  · simp only [num4, n4]; omega
  · simp only [num4, n4]; omega
  · simp only [num4, n4]; split <;> omega
  · simp only [num4, n4]; have := List.idxOf_lt_length_of_mem he; omega

/-- **The numbered four-cycle network is in the class of the solver.** -/
theorem goodNet4 (hcs : ∀ c ∈ cs, IsCycle g 4 c) : GoodNet (num4 cs) (n4 cs) (net4 cs) where
  lt v hv := num4_lt hv
  inj v w hv hw h := by
    rcases nodeOf_net4 hv with rfl | rfl | ⟨i, p, hi, rfl⟩ | ⟨e, he, rfl⟩ <;>
    rcases nodeOf_net4 hw with rfl | rfl | ⟨i', p', hi', rfl⟩ | ⟨e', he', rfl⟩
    all_goals simp only [num4] at h
    all_goals first
      | rfl
      | (exfalso; cases p <;> simp at h <;> omega)
      | (exfalso; cases p' <;> simp at h <;> omega)
      | (exfalso; omega)
      | (cases p <;> cases p' <;> simp at h ⊢ <;> omega)
      | (have he2 : (eList cs).idxOf e = (eList cs).idxOf e' := by omega
         rw [(List.idxOf_inj he).mp he2])
  head_ne a ha := by
    rw [net4] at ha
    rcases List.mem_append.mp ha with ha | ha
    · rcases List.mem_append.mp ha with ha | ha
      · obtain ⟨i, p, _, rfl⟩ := (mem_sourceLayer _ a).mp ha; simp
      · obtain ⟨i, p, e, _, _, rfl⟩ := (mem_pairLayer _ _ a).mp ha; simp
    · obtain ⟨e, j, _, _, rfl⟩ := (mem_sinkLayer _ _ a).mp ha; simp
  tail_ne a ha := by
    rw [net4] at ha
    rcases List.mem_append.mp ha with ha | ha
    · rcases List.mem_append.mp ha with ha | ha
      · obtain ⟨i, p, _, rfl⟩ := (mem_sourceLayer _ a).mp ha; simp
      · obtain ⟨i, p, e, _, _, rfl⟩ := (mem_pairLayer _ _ a).mp ha; simp
    · obtain ⟨e, j, _, _, rfl⟩ := (mem_sinkLayer _ _ a).mp ha; simp
  cost_lt a ha := by
    rw [length_net4 hcs]
    rw [net4] at ha
    rcases List.mem_append.mp ha with ha | ha
    · rcases List.mem_append.mp ha with ha | ha
      · obtain ⟨i, p, hi, rfl⟩ := (mem_sourceLayer _ a).mp ha; simp only; omega
      · obtain ⟨i, p, e, hi, _, rfl⟩ := (mem_pairLayer _ _ a).mp ha; simp only; omega
    · obtain ⟨e, j, _, hj, rfl⟩ := (mem_sinkLayer _ _ a).mp ha
      have := wcount_le cs e
      simp only; omega
  nodes_le := by
    rw [length_net4 hcs, n4]
    have := length_eList4 hcs
    omega

/-! ### The arcs read by the extraction -/

theorem getD_append_right' {α : Type} (l l' : List α) (d : α) (x : ℕ) :
    (l ++ l').getD (l.length + x) d = l'.getD x d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]

theorem pairLayer_getD (hcs : ∀ c ∈ cs, IsCycle g 4 c) {i j : ℕ} (hi : i < cs.length) (hj : j < 4)
    (d : Arc) : (pairLayer cs.length (cyc cs)).getD (i * 4 + j) d =
      ([false, true].flatMap fun p =>
        (opposingPair (cyc cs i) p).map fun e => (⟨.pair i p, .edgeNode e, 0⟩ : Arc)).getD j d := by
  rw [pairLayer, List.flatMap_def, getD_flatten_uniform d _ (k := 4) _ (by simpa using hi) hj]
  · rw [List.getD_eq_getElem?_getD (l := List.map _ _), List.getElem?_map,
      List.getElem?_range hi]
    rfl
  · intro l hl
    obtain ⟨i', hi', rfl⟩ := List.mem_map.mp hl
    rw [pairChunk4 hcs (List.mem_range.mp hi')]
    rfl

/-- The arc `x_{C_i,{e₁,e₃}} → y_{e₃}` is at position `2t + 4i + 1`. -/
theorem net4_getD_q0 (hcs : ∀ c ∈ cs, IsCycle g 4 c) {i : ℕ} (hi : i < cs.length) (d : Arc) :
    (net4 cs).getD (2 * cs.length + (i * 4 + 1)) d =
      ⟨.pair i false, .edgeNode (chosenEdge (cyc cs i) 0 false), 0⟩ := by
  have hp : i * 4 + 1 < (pairLayer cs.length (cyc cs)).length := by
    rw [pairLayer_length _ _ (fun i' hi' p => by
      obtain ⟨a, b, u, v, hc, _⟩ := fourCycle_shape (cyc_isCycle hcs hi')
      rw [hc]; exact opposingPair_length_four a b u v p)]
    omega
  rw [net4, List.append_assoc, ← sourceLayer_length cs.length, getD_append_right',
    List.getD_eq_getElem?_getD, List.getElem?_append_left hp, ← List.getD_eq_getElem?_getD,
    pairLayer_getD hcs hi (by omega)]
  obtain ⟨a, b, u, v, hc, _⟩ := fourCycle_shape (cyc_isCycle hcs hi)
  rw [hc]
  obtain ⟨pf, pt⟩ := opposingPair_four a b u v
  obtain ⟨cf, _⟩ := chosenEdge_four a b u v 0
  simp [pf, pt, cf]

/-- The arc `x_{C_i,{e₂,e₄}} → y_{e₄}` is at position `2t + 4i + 3`. -/
theorem net4_getD_q1 (hcs : ∀ c ∈ cs, IsCycle g 4 c) {i : ℕ} (hi : i < cs.length) (d : Arc) :
    (net4 cs).getD (2 * cs.length + (i * 4 + 3)) d =
      ⟨.pair i true, .edgeNode (chosenEdge (cyc cs i) 1 true), 0⟩ := by
  have hp : i * 4 + 3 < (pairLayer cs.length (cyc cs)).length := by
    rw [pairLayer_length _ _ (fun i' hi' p => by
      obtain ⟨a, b, u, v, hc, _⟩ := fourCycle_shape (cyc_isCycle hcs hi')
      rw [hc]; exact opposingPair_length_four a b u v p)]
    omega
  rw [net4, List.append_assoc, ← sourceLayer_length cs.length, getD_append_right',
    List.getD_eq_getElem?_getD, List.getElem?_append_left hp, ← List.getD_eq_getElem?_getD,
    pairLayer_getD hcs hi (by omega)]
  obtain ⟨a, b, u, v, hc, _⟩ := fourCycle_shape (cyc_isCycle hcs hi)
  rw [hc]
  obtain ⟨pf, pt⟩ := opposingPair_four a b u v
  obtain ⟨_, ct⟩ := chosenEdge_four a b u v 1
  simp [pf, pt, ct]

/-- **The read-off of a `0/1` vector**: the bits at positions `2t + 4i + 1` and `2t + 4i + 3`. -/
theorem readOff4_select (hcs : ∀ c ∈ cs, IsCycle g 4 c) {bits : List ℕ}
    (hlen : bits.length = (net4 cs).length) :
    readOff4 cs (fun a => decide (a ∈ select (net4 cs) bits)) =
      (List.range cs.length).map fun i =>
        optionIndex (decide (bits.getD (2 * cs.length + (i * 4 + 1)) 0 ≠ 0))
          (decide (bits.getD (2 * cs.length + (i * 4 + 3)) 0 ≠ 0)) := by
  have hN := length_net4 hcs
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.mp hi
  have d : Arc := ⟨.source, .source, 0⟩
  have h0 := getD_mem_select (bits := bits) d (net4_nodup hcs)
    (j := 2 * cs.length + (i * 4 + 1)) (by omega) (by omega)
  have h1 := getD_mem_select (bits := bits) d (net4_nodup hcs)
    (j := 2 * cs.length + (i * 4 + 3)) (by omega) (by omega)
  rw [net4_getD_q0 hcs hi'] at h0
  rw [net4_getD_q1 hcs hi'] at h1
  simp only [q0, q1]
  congr 1
  · exact decide_eq_decide.mpr h0
  · exact decide_eq_decide.mpr h1

end four

end STACS2027.Runtimes.Flow

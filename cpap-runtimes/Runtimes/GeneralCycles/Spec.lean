module

public import Runtimes.GeneralCycles.Definitions
import Mathlib.Tactic

/-! Endpoint-index tuple enumeration, exact canonical representatives, and uniqueness.
Vertex labels occur only as values, while every index is bounded by the input length. -/

@[expose] public section

namespace STACS2027.Runtimes.GeneralCycles

open STACS2027

theorem mem_tuples (N k : ℕ) (indices : List ℕ) :
    indices ∈ tuples N k ↔ indices.length = k ∧ ∀ i ∈ indices, i < N := by
  induction k generalizing indices with
  | zero =>
    constructor
    · intro h
      have he : indices = [] := by simpa [tuples] using h
      subst indices
      simp
    · rintro ⟨hl, _⟩
      have he : indices = [] := by simpa using hl
      subst indices
      simp [tuples]
  | succ k ih =>
    cases indices with
    | nil => simp [tuples]
    | cons i indices =>
      constructor
      · intro h
        obtain ⟨j, hj, hm⟩ := List.mem_flatMap.mp h
        obtain ⟨xs, hxs, he⟩ := List.mem_map.mp hm
        obtain ⟨rfl, rfl⟩ := List.cons.inj he
        obtain ⟨hl, hall⟩ := (ih xs).mp hxs
        exact ⟨by simp [hl], fun x hx => by
          rcases List.mem_cons.mp hx with rfl | hx
          · exact List.mem_range.mp hj
          · exact hall x hx⟩
      · rintro ⟨hl, hall⟩
        refine List.mem_flatMap.mpr ⟨i, List.mem_range.mpr (hall i (by simp)), ?_⟩
        exact List.mem_map.mpr ⟨indices, (ih indices).mpr
          ⟨by simp only [List.length_cons] at hl; omega,
            fun x hx => hall x (by simp [hx])⟩, rfl⟩

theorem tuples_nodup (N k : ℕ) : (tuples N k).Nodup := by
  induction k with
  | zero => simp [tuples]
  | succ k ih =>
    rw [tuples, List.nodup_flatMap]
    refine ⟨fun i _ => ih.map (fun _ _ h => (List.cons.inj h).2), ?_⟩
    refine (List.nodup_range : (List.range N).Nodup).imp fun {i j} hij xs hxs hys => ?_
    obtain ⟨a, _, ha⟩ := List.mem_map.mp hxs
    obtain ⟨b, _, hb⟩ := List.mem_map.mp hys
    exact hij (List.cons.inj (ha.trans hb.symm)).1

theorem length_tuples (N k : ℕ) : (tuples N k).length = N ^ k := by
  induction k with
  | zero => simp [tuples]
  | succ k ih =>
    simp [tuples, List.length_flatMap, ih, pow_succ, Nat.mul_comm]

theorem length_endpoints (g : Graph) : (endpoints g).length = 2 * g.length := by
  induction g with
  | nil => simp [endpoints]
  | cons e g ih => simp [endpoints, List.flatMap_cons] at ih ⊢; omega

theorem mem_endpoints_of_edge {g : Graph} {a b : ℕ} (h : edge a b ∈ g) :
    a ∈ endpoints g ∧ b ∈ endpoints g := by
  have he : (edge a b).1 ∈ endpoints g ∧ (edge a b).2 ∈ endpoints g := by
    constructor <;> apply List.mem_flatMap.mpr <;> exact ⟨edge a b, h, by simp⟩
  by_cases hab : a ≤ b
  · simpa [edge, Nat.min_eq_left hab, Nat.max_eq_right hab] using he
  · have hba : b ≤ a := by omega
    simpa [edge, Nat.min_eq_right hba, Nat.max_eq_left hba, and_comm] using he

theorem cycle_vertices_endpoints {g : Graph} {k : ℕ} {c : Cycle}
    (hc : IsCycle g k c) : ∀ v ∈ c, v ∈ endpoints g := by
  intro v hv
  obtain ⟨w, _, he⟩ := hc.vertex_incident hv
  exact (mem_endpoints_of_edge (hc.2.2.2 _ he)).1

theorem exists_indices (g : Graph) (c : Cycle) (hc : ∀ v ∈ c, v ∈ endpoints g) :
    ∃ indices ∈ tuples (endpoints g).length c.length, tupleLabels g indices = c := by
  induction c with
  | nil => exact ⟨[], by simp [tuples], rfl⟩
  | cons v c ih =>
    obtain ⟨i, hi, hiv⟩ := List.mem_iff_getElem.mp (hc v (by simp))
    obtain ⟨indices, hindices, hlabels⟩ := ih (fun w hw => hc w (by simp [hw]))
    refine ⟨i :: indices, ?_, ?_⟩
    · exact (mem_tuples _ _ _).mpr ⟨by have := (mem_tuples _ _ _).mp hindices; simp_all,
        by intro j hj; rcases List.mem_cons.mp hj with rfl | hj
           · exact hi
           · exact ((mem_tuples _ _ _).mp hindices).2 _ hj⟩
    · simpa [tupleLabels, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, hiv]
        using congrArg (v :: ·) hlabels

theorem accepted_labels_mem {g : Graph} {k : ℕ} {indices : List ℕ}
    (_hindices : indices ∈ tuples (endpoints g).length k) (ha : Accepted g k indices) :
    tupleLabels g indices ∈ cycles g k := by
  obtain ⟨c, hc, hsame⟩ := isCycle_represented ha.1
  have hmin : c ≤ tupleLabels g indices :=
    C4.cycleRepresentatives_min _ _ le_rfl (C4.rawCycles_sorted g k) _ hc _
      (isCycle_raw_enumerated ha.1) hsame
  obtain ⟨previous, hp, he⟩ := exists_indices g c (cycle_vertices_endpoints (enumerated_isCycle hc))
  have hp' : previous ∈ tuples (endpoints g).length k := by
    rwa [(enumerated_isCycle hc).2.1] at hp
  have hv : Valid g k previous := by simpa [Valid, he] using enumerated_isCycle hc
  have hnot := ha.2 previous hp' hv (by simpa [he] using hsame.symm)
  have hle : tupleLabels g indices ≤ c := le_of_not_gt (fun h => hnot (Or.inl (he ▸ h)))
  have heq := le_antisymm hmin hle
  simpa only [← heq] using hc

theorem exists_accepted_of_mem {g : Graph} {k : ℕ} {c : Cycle} (hc : c ∈ cycles g k) :
    ∃ indices ∈ tuples (endpoints g).length k, Accepted g k indices ∧ tupleLabels g indices = c := by
  classical
  let candidates := ((tuples (endpoints g).length k).filter fun i => tupleLabels g i = c).toFinset
  obtain ⟨i, hi, hei⟩ := exists_indices g c (cycle_vertices_endpoints (enumerated_isCycle hc))
  have hi' : i ∈ tuples (endpoints g).length k := by
    rwa [(enumerated_isCycle hc).2.1] at hi
  have hnon : candidates.Nonempty := ⟨i, by simp [candidates, hi', hei]⟩
  let indices := candidates.min' hnon
  have hmem : indices ∈ candidates := Finset.min'_mem candidates hnon
  have hindices : indices ∈ tuples (endpoints g).length k ∧ tupleLabels g indices = c := by
    change indices ∈ ((tuples (endpoints g).length k).filter
      fun i => tupleLabels g i = c).toFinset at hmem
    simpa only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] using hmem
  refine ⟨indices, hindices.1, ⟨?_, ?_⟩, hindices.2⟩
  · simpa [Valid, hindices.2] using enumerated_isCycle hc
  · intro previous hp hv hs hbefore
    have hmin : c ≤ tupleLabels g previous :=
      C4.cycleRepresentatives_min _ _ le_rfl (C4.rawCycles_sorted g k) _ hc _
        (isCycle_raw_enumerated hv) (by simpa [hindices.2] using hs)
    rcases hbefore with hlt | ⟨heq, hlt⟩
    · exact (not_lt_of_ge hmin) (by simpa [hindices.2] using hlt)
    · have hpCand : previous ∈ candidates := by simp [candidates, hp, heq, hindices.2]
      exact (not_lt_of_ge (Finset.min'_le candidates previous hpCand)) hlt

theorem accepted_indices_injective {g : Graph} {k : ℕ} {i j : List ℕ}
    (hi : i ∈ tuples (endpoints g).length k) (hj : j ∈ tuples (endpoints g).length k)
    (hai : Accepted g k i) (haj : Accepted g k j) (hlabels : tupleLabels g i = tupleLabels g j) :
    i = j := by
  have hji := hai.2 j hj haj.1 (by rw [hlabels]; exact SameCycle.refl _)
  have hij := haj.2 i hi hai.1 (by rw [hlabels]; exact SameCycle.refl _)
  apply le_antisymm
  · exact le_of_not_gt (fun h => hji (Or.inr ⟨hlabels.symm, h⟩))
  · exact le_of_not_gt (fun h => hij (Or.inr ⟨hlabels, h⟩))

theorem mem_outputCycles {g : Graph} {k : ℕ} {c : Cycle} :
    c ∈ outputCycles g k ↔ c ∈ cycles g k := by
  constructor
  · intro hc
    obtain ⟨indices, hi, rfl⟩ := List.mem_map.mp hc
    obtain ⟨ht, ha⟩ := List.mem_filter.mp hi
    exact accepted_labels_mem ht (of_decide_eq_true ha)
  · intro hc
    obtain ⟨indices, hi, ha, he⟩ := exists_accepted_of_mem hc
    exact List.mem_map.mpr ⟨indices, List.mem_filter.mpr ⟨hi, decide_eq_true ha⟩, he⟩

theorem outputCycles_nodup (g : Graph) (k : ℕ) : (outputCycles g k).Nodup := by
  unfold outputCycles
  apply ((tuples_nodup _ _).filter _).map_on
  intro i hi j hj he
  obtain ⟨hit, hai⟩ := List.mem_filter.mp hi
  obtain ⟨hjt, haj⟩ := List.mem_filter.mp hj
  exact accepted_indices_injective hit hjt (of_decide_eq_true hai) (of_decide_eq_true haj) he

theorem outputCycles_perm (g : Graph) (k : ℕ) : (outputCycles g k).Perm (cycles g k) :=
  (List.perm_ext_iff_of_nodup (outputCycles_nodup g k) (cycles_nodup g k)).mpr
    (fun _ => mem_outputCycles)

theorem outputCycles_length_le (g : Graph) (k : ℕ) :
    (outputCycles g k).length ≤ (2 * g.length) ^ k := by
  unfold outputCycles
  rw [List.length_map, ← length_endpoints g, ← length_tuples]
  exact List.length_filter_le _ _

theorem outputCycles_cycle_length {g : Graph} {k : ℕ} {c : Cycle}
    (hc : c ∈ outputCycles g k) : c.length = k :=
  (enumerated_isCycle (mem_outputCycles.mp hc)).2.1

theorem outputCycles_flatten_length (g : Graph) (k : ℕ) :
    (outputCycles g k).flatten.length = k * (outputCycles g k).length := by
  have key : ∀ (cs : List Cycle), (∀ c ∈ cs, c.length = k) →
      cs.flatten.length = k * cs.length := by
    intro cs
    induction cs with
    | nil => simp
    | cons c cs ih =>
      intro h
      have hc := h c (by simp)
      have hcs := ih (fun d hd => h d (by simp [hd]))
      simp [hc, hcs, Nat.mul_add, Nat.add_comm]
  exact key _ (fun _ hc => outputCycles_cycle_length hc)

theorem outputCycles_flatten_length_le (g : Graph) (k : ℕ) :
    (outputCycles g k).flatten.length ≤ k * (2 * g.length) ^ k := by
  rw [outputCycles_flatten_length]
  exact Nat.mul_le_mul_left _ (outputCycles_length_le g k)

end STACS2027.Runtimes.GeneralCycles

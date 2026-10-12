module

public import BoundedCost.Encoding

/-!
# Positions on a simple cycle

The edges of a simple `k`-cycle `c = [c₀, …, c_{k-1}]` are, in order, the edges
`{c_j, c_{j+1}}` (indices mod `k`). Two of them are vertex-disjoint iff their
positions are neither equal nor consecutive, and the path `selected c i`, which
omits vertex `c_i`, contains the edge at position `j` iff `j ≠ i` and `j + 1 ≠ i`.
Finally, for `k ≥ 4`, a set of positions whose edges pairwise share a vertex lies
within the two edges at one vertex.
-/

@[expose] public section
namespace STACS2027

/-- The position after `j` on a cycle of length `k`. -/
def next (k j : Nat) : Nat := if j + 1 < k then j + 1 else 0

theorem next_lt {k j : Nat} (hk : 0 < k) : next k j < k := by
  unfold next; split <;> omega

theorem next_eq_iff {k j m : Nat} :
    next k j = m ↔ (j + 1 < k ∧ m = j + 1) ∨ (¬ j + 1 < k ∧ m = 0) := by
  unfold next; split <;> constructor <;> intro h <;> omega

theorem next_inj {k a b : Nat} (ha : a < k) (hb : b < k) (h : next k a = next k b) : a = b := by
  unfold next at h; split at h <;> split at h <;> omega

theorem next_ne_self {k j : Nat} (hk : 2 ≤ k) (hj : j < k) : next k j ≠ j := by
  unfold next; split <;> omega

/-! ## Indexed access to the vertices and edges -/

theorem getD_inj {c : Cycle} (hn : c.Nodup) {x y : Nat} (hx : x < c.length) (hy : y < c.length)
    (h : c.getD x 0 = c.getD y 0) : x = y := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hx,
    List.getElem?_eq_getElem hy] at h
  simp only [Option.getD_some] at h
  exact (hn.getElem_inj (hi := hx) (hj := hy)).mp h

theorem getD_mem {α : Type} (l : List α) (d : α) {j : Nat} (hj : j < l.length) : l.getD j d ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  exact List.getElem_mem hj

theorem mem_iff_getD {α : Type} (l : List α) (d : α) (x : α) :
    x ∈ l ↔ ∃ j, j < l.length ∧ l.getD j d = x := by
  constructor
  · intro h
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem h
    exact ⟨j, hj, by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl⟩
  · rintro ⟨j, hj, rfl⟩
    exact getD_mem l d hj

theorem pathEdges_getD (l : List Nat) (j : Nat) (hj : j + 1 < l.length) :
    (pathEdges l).getD j (0, 0) = edge (l.getD j 0) (l.getD (j + 1) 0) := by
  induction l generalizing j with
  | nil => simp at hj
  | cons a l ih =>
    cases l with
    | nil => simp at hj
    | cons b rest =>
      cases j with
      | zero => simp [pathEdges]
      | succ j =>
        simp only [pathEdges, List.getD_cons_succ]
        exact ih (j) (by simp at hj ⊢; omega)

theorem cycleEdges_getD {c : Cycle} (hc : 0 < c.length) {j : Nat} (hj : j < c.length) :
    (cycleEdges c).getD j (0, 0) = edge (c.getD j 0) (c.getD (next c.length j) 0) := by
  unfold cycleEdges
  rw [pathEdges_getD _ _ (by simp; omega)]
  have h₁ : (c ++ c.take 1).getD j 0 = c.getD j 0 := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hj]
  have h₂ : (c ++ c.take 1).getD (j + 1) 0 = c.getD (next c.length j) 0 := by
    unfold next
    split
    · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left (by assumption)]
    · have hj' : j + 1 = c.length := by omega
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hj',
        Nat.sub_self]
      cases c with
      | nil => simp at hc
      | cons a l => simp
  rw [h₁, h₂]

/-! ## Incidence and disjointness by positions -/

theorem edge_fst_snd (a b : Nat) : ((edge a b).1 = a ∧ (edge a b).2 = b) ∨ ((edge a b).1 = b ∧ (edge a b).2 = a) := by
  simp only [edge]; omega

/-- Vertex `c_i` lies on the edge at position `j` iff `j = i` or `next j = i`. -/
theorem vertex_on_edgeAt {g : Graph} {k : Nat} {c : Cycle} (hc : IsCycle g k c) {i j : Nat}
    (hi : i < k) (hj : j < k) :
    (c.getD i 0 = ((cycleEdges c).getD j (0, 0)).1 ∨ c.getD i 0 = ((cycleEdges c).getD j (0, 0)).2) ↔
      (i = j ∨ i = next k j) := by
  have hk := hc.1
  have hlen := hc.2.1
  have hn := hc.2.2.1
  rw [cycleEdges_getD (by omega) (by omega), ← hlen]
  have hnext : next c.length j < c.length := next_lt (by omega)
  rcases edge_fst_snd (c.getD j 0) (c.getD (next c.length j) 0) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rw [h1, h2] <;> constructor
  · rintro (h | h)
    · exact Or.inl (getD_inj hn (by omega) (by omega) h)
    · exact Or.inr (getD_inj hn (by omega) hnext h)
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (h | h)
    · exact Or.inr (getD_inj hn (by omega) hnext h)
    · exact Or.inl (getD_inj hn (by omega) (by omega) h)
  · rintro (rfl | rfl)
    · exact Or.inr rfl
    · exact Or.inl rfl

theorem disjointEdges_edge (x y u v : Nat) :
    disjointEdges (edge x y) (edge u v) = true ↔ x ≠ u ∧ x ≠ v ∧ y ≠ u ∧ y ≠ v := by
  simp only [disjointEdges, edge, bne_iff_ne, Bool.and_eq_true, ne_eq]
  omega

/-- Two edges of a simple cycle are vertex-disjoint iff their positions are neither equal nor
consecutive. -/
theorem disjointEdges_edgeAt {g : Graph} {k : Nat} {c : Cycle} (hc : IsCycle g k c) {a b : Nat}
    (ha : a < k) (hb : b < k) :
    disjointEdges ((cycleEdges c).getD a (0, 0)) ((cycleEdges c).getD b (0, 0)) = true ↔
      ¬ (a = b ∨ a = next k b ∨ b = next k a) := by
  have hk := hc.1
  have hlen := hc.2.1
  have hn := hc.2.2.1
  rw [cycleEdges_getD (by omega) (by omega), cycleEdges_getD (by omega) (by omega), ← hlen,
    disjointEdges_edge]
  have hna : next c.length a < c.length := next_lt (by omega)
  have hnb : next c.length b < c.length := next_lt (by omega)
  have key : ∀ x y, x < c.length → y < c.length → (c.getD x 0 ≠ c.getD y 0 ↔ x ≠ y) := by
    intro x y hx hy
    constructor
    · rintro h rfl; exact h rfl
    · intro h h'; exact h (getD_inj hn hx hy h')
  rw [key _ _ (by omega) (by omega), key _ _ (by omega) hnb, key _ _ hna (by omega), key _ _ hna hnb]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩ (h | h | h)
    · exact h1 h
    · exact h2 h
    · exact h3 h.symm
  · intro h
    refine ⟨fun e => h (Or.inl e), fun e => h (Or.inr (Or.inl e)), fun e => h (Or.inr (Or.inr e.symm)), ?_⟩
    intro e
    exact h (Or.inl (next_inj (by omega) (by omega) e))

/-! ## The path omitting a vertex, by positions -/

/-- The edge at position `j` is on the path omitting `c_i` iff `j ≠ i` and `next j ≠ i`. -/
theorem mem_selected_iff_position {g : Graph} {k : Nat} {c : Cycle} (hc : IsCycle g k c) {i j : Nat}
    (hi : i < k) (hj : j < k) :
    (cycleEdges c).getD j (0, 0) ∈ selected c i ↔ ¬ (i = j ∨ i = next k j) := by
  have hlen := hc.2.1
  have hi' : i < c.length := by omega
  have hperm := selected_perm_selectedAt hc hi'
  rw [hperm.mem_iff, selectedAt_mem]
  have hci : c[i] = c.getD i 0 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']; rfl
  rw [hci]
  have hmem : (cycleEdges c).getD j (0, 0) ∈ cycleEdges c :=
    getD_mem _ _ (by rw [hc.edge_length]; exact hj)
  rw [← vertex_on_edgeAt hc hi hj]
  constructor
  · rintro ⟨_, h1, h2⟩ (h | h)
    · exact h1 h.symm
    · exact h2 h.symm
  · intro h
    exact ⟨hmem, fun e => h (Or.inl e.symm), fun e => h (Or.inr e.symm)⟩

theorem edgeAt_inj {g : Graph} {k : Nat} {c : Cycle} (hc : IsCycle g k c) {a b : Nat}
    (ha : a < k) (hb : b < k) (h : (cycleEdges c).getD a (0, 0) = (cycleEdges c).getD b (0, 0)) :
    a = b := by
  have hlen := hc.edge_length
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at h
  simp only [Option.getD_some] at h
  exact (hc.edges_nodup.getElem_inj (hi := by omega) (hj := by omega)).mp h

theorem exists_position {g : Graph} {k : Nat} {c : Cycle} (hc : IsCycle g k c) {e : Edge}
    (he : e ∈ cycleEdges c) : ∃ j, j < k ∧ (cycleEdges c).getD j (0, 0) = e := by
  obtain ⟨j, hj, h⟩ := (mem_iff_getD (cycleEdges c) (0, 0) e).mp he
  exact ⟨j, by rw [← hc.edge_length]; exact hj, h⟩

/-! ## A common vertex for pairwise intersecting edges (`k ≥ 4`) -/

theorem next_spec {k j : Nat} (hj : j < k) :
    (j + 1 < k ∧ next k j = j + 1) ∨ (j + 1 = k ∧ next k j = 0) := by
  unfold next; split <;> omega

/-- Positions whose edges pairwise share a vertex all lie at one vertex `c_i`: each is `i` or
has `next` equal to `i`. -/
theorem common_vertex_positions {k : Nat} (hk : 4 ≤ k) (S : List Nat) (hS : ∀ x ∈ S, x < k)
    (hpair : ∀ x ∈ S, ∀ y ∈ S, x = y ∨ x = next k y ∨ y = next k x) :
    ∃ i, i < k ∧ ∀ x ∈ S, x = i ∨ i = next k x := by
  cases S with
  | nil => exact ⟨0, by omega, fun x hx => by simp at hx⟩
  | cons a S =>
    have ha : a < k := hS a List.mem_cons_self
    by_cases hall : ∀ x ∈ a :: S, x = a
    · refine ⟨next k a, next_lt (by omega), ?_⟩
      intro x hx
      rw [hall x hx]
      exact Or.inr rfl
    · have hex : ∃ b, b ∈ a :: S ∧ b ≠ a := by
        apply Classical.byContradiction
        intro hne
        apply hall
        intro x hx
        apply Classical.byContradiction
        intro hxa
        exact hne ⟨x, hx, hxa⟩
      obtain ⟨b, hb, hba⟩ := hex
      have hbk : b < k := hS b hb
      have na := next_spec ha
      have nb := next_spec hbk
      have hab := hpair a List.mem_cons_self b hb
      -- the common vertex is the later of the two consecutive positions
      have hi : ∃ i, i < k ∧ (a = i ∨ i = next k a) ∧ (b = i ∨ i = next k b) ∧ (i = a ∨ i = b) := by
        rcases hab with hab | hab | hab
        · exact absurd hab.symm hba
        · exact ⟨a, ha, Or.inl rfl, Or.inr hab, Or.inl rfl⟩
        · exact ⟨b, hbk, Or.inr hab, Or.inl rfl, Or.inr rfl⟩
      obtain ⟨i, hik, hia, hib, hiab⟩ := hi
      refine ⟨i, hik, ?_⟩
      intro x hx
      have hxk := hS x hx
      have nx := next_spec hxk
      have hxa := hpair x hx a List.mem_cons_self
      have hxb := hpair x hx b hb
      omega

/-! ## Variables -/

theorem pathVariable_div {k i j : Nat} (hj : j < k) : pathVariable k i j / k = i := by
  unfold pathVariable
  rw [Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hj, Nat.add_zero]

theorem pathVariable_mod {k i j : Nat} (hj : j < k) : pathVariable k i j % k = j := by
  unfold pathVariable
  rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hj]

theorem pathVariable_inj {k i j i' j' : Nat} (hj : j < k) (hj' : j' < k)
    (h : pathVariable k i j = pathVariable k i' j') : i = i' ∧ j = j' := by
  have h₁ := congrArg (· / k) h
  have h₂ := congrArg (· % k) h
  rw [pathVariable_div hj, pathVariable_div hj'] at h₁
  rw [pathVariable_mod hj, pathVariable_mod hj'] at h₂
  exact ⟨h₁, h₂⟩

theorem pathVariable_lt {k i j t : Nat} (hi : i < t) (hj : j < k) : pathVariable k i j < k * t := by
  unfold pathVariable
  have : (i + 1) * k ≤ t * k := Nat.mul_le_mul_right k hi
  rw [Nat.mul_comm k t]
  rw [Nat.add_mul, Nat.one_mul] at this
  omega

/-! ## Named cycles and their edges -/

theorem kCycle_isCycle (g : Graph) {k i : Nat} (hi : i < (cycles g k).length) :
    IsCycle g k (kCycle g k i) :=
  enumerated_isCycle (getD_mem _ _ hi)

theorem kCycle_mem (g : Graph) {k i : Nat} (hi : i < (cycles g k).length) :
    kCycle g k i ∈ cycles g k :=
  getD_mem _ _ hi

theorem edgePosition_lt {g : Graph} {k i : Nat} (hi : i < (cycles g k).length) {e : Edge}
    (he : e ∈ cycleEdges (kCycle g k i)) : edgePosition g k i e < k := by
  unfold edgePosition
  have hlen := (kCycle_isCycle g hi).edge_length
  have := List.idxOf_lt_length_of_mem he
  omega

theorem cycleEdgeAt_edgePosition {g : Graph} {k i : Nat} (_hi : i < (cycles g k).length) {e : Edge}
    (he : e ∈ cycleEdges (kCycle g k i)) : cycleEdgeAt g k i (edgePosition g k i e) = e := by
  unfold cycleEdgeAt edgePosition
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem he)]
  simp only [Option.getD_some]
  exact List.getElem_idxOf (List.idxOf_lt_length_of_mem he)

theorem edgePosition_cycleEdgeAt {g : Graph} {k i : Nat} (hi : i < (cycles g k).length) {j : Nat}
    (hj : j < k) : edgePosition g k i (cycleEdgeAt g k i j) = j := by
  unfold edgePosition cycleEdgeAt
  have hlen := (kCycle_isCycle g hi).edge_length
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
  simp only [Option.getD_some]
  exact (kCycle_isCycle g hi).edges_nodup.idxOf_getElem j (by omega)

theorem cycleEdgeAt_mem {g : Graph} {k i : Nat} (hi : i < (cycles g k).length) {j : Nat} (hj : j < k) :
    cycleEdgeAt g k i j ∈ cycleEdges (kCycle g k i) :=
  getD_mem _ _ (by rw [(kCycle_isCycle g hi).edge_length]; exact hj)

theorem edgeVariable_eq {g : Graph} {k i : Nat} (hi : i < (cycles g k).length) {j : Nat} (hj : j < k) :
    edgeVariable g k i (cycleEdgeAt g k i j) = pathVariable k i j := by
  unfold edgeVariable
  rw [edgePosition_cycleEdgeAt hi hj]

end STACS2027

module

public import BoundedCost.CyclePositions
public import NPHardness.CPAP

/-!
# Algorithm 3, preprocessing: the `k`-cycle core

Algorithm 3 first restricts `G` to its *`k`-cycle core* `G_k`, "consisting of the vertices
and edges belonging to at least one `k`-cycle" (Appendix B of the manuscript), which is
claimed not to change "the feasible assignments or their costs". Here `kCycleCore g k`
keeps the edges of `g` lying on an enumerated simple `k`-cycle, and:

* its edges are exactly the edges on simple `k`-cycles of `g`, and its vertices exactly the
  vertices on them (`mem_kCycleCore_iff`, `mem_vertices_kCycleCore_iff`);
* it has the same simple `k`-cycles as `g` (`isCycle_kCycleCore_iff`), and even the same
  enumeration: `cycles (kCycleCore g k) k = cycles g k` (`cycles_kCycleCore`), because a
  walk of `g` that closes into a `k`-cycle uses only core edges and the enumeration of
  Section 5 visits vertices and neighbors in increasing order;
* hence the same assignments of every cost (`hasAssignment_kCycleCore_iff`) and the same
  encodings `Γ'`, `Γ_𝓘` and the zero-cost formula (`encodings_kCycleCore`).
-/

@[expose] public section
namespace STACS2027
open Complexity.SAT

/-- The `k`-cycle core `G_k` of `g`: the edges of `g` that lie on a simple `k`-cycle of `g`
(on one of the enumerated cycles `cycles g k`, which represent all of them). -/
def kCycleCore (g : Graph) (k : Nat) : Graph :=
  g.filter fun e => (cycles g k).any fun c => (cycleEdges c).contains e

/-! ## Edges and vertices of the core -/

/-- The edges of the core are exactly the edges on simple `k`-cycles of `g`. -/
theorem mem_kCycleCore_iff (g : Graph) (k : Nat) (e : Edge) :
    e ∈ kCycleCore g k ↔ ∃ c, IsCycle g k c ∧ e ∈ cycleEdges c := by
  simp only [kCycleCore, List.mem_filter, List.any_eq_true, List.contains_iff_mem]
  constructor
  · rintro ⟨_, c, hc, he⟩
    exact ⟨c, enumerated_isCycle hc, he⟩
  · rintro ⟨c, hc, he⟩
    obtain ⟨d, hd, hs⟩ := isCycle_represented hc
    exact ⟨hc.2.2.2 e he, d, hd, hs.1 e he⟩

theorem mem_of_mem_kCycleCore {g : Graph} {k : Nat} {e : Edge} (h : e ∈ kCycleCore g k) : e ∈ g :=
  (List.mem_filter.mp h).1

theorem mem_vertices_iff (g : Graph) (v : Nat) :
    v ∈ vertices g ↔ ∃ e ∈ g, e.1 = v ∨ e.2 = v := by
  have hflat : v ∈ g.flatMap (fun e => [e.1, e.2]) ↔ ∃ e ∈ g, e.1 = v ∨ e.2 = v := by
    simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro ⟨e, he, h | h⟩
      · exact ⟨e, he, Or.inl h.symm⟩
      · exact ⟨e, he, Or.inr h.symm⟩
    · rintro ⟨e, he, h | h⟩
      · exact ⟨e, he, Or.inl h.symm⟩
      · exact ⟨e, he, Or.inr h.symm⟩
  rw [← hflat]
  simp only [vertices, List.mem_filter, List.mem_range, List.contains_iff_mem]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨by have := le_foldr_max_of_mem h; omega, h⟩

/-- The vertices of the core are exactly the vertices on simple `k`-cycles of `g`. -/
theorem mem_vertices_kCycleCore_iff (g : Graph) (k v : Nat) :
    v ∈ vertices (kCycleCore g k) ↔ ∃ c, IsCycle g k c ∧ v ∈ c := by
  rw [mem_vertices_iff]
  constructor
  · rintro ⟨e, he, hv⟩
    obtain ⟨c, hc, hec⟩ := (mem_kCycleCore_iff g k e).mp he
    have hend := cycleEdges_endpoints hec
    rcases hv with rfl | rfl
    · exact ⟨c, hc, hend.1⟩
    · exact ⟨c, hc, hend.2⟩
  · rintro ⟨c, hc, hv⟩
    obtain ⟨w, _, hw⟩ := hc.vertex_incident hv
    refine ⟨edge v w, (mem_kCycleCore_iff g k _).mpr ⟨c, hc, hw⟩, ?_⟩
    rcases edge_fst_snd v w with ⟨h, _⟩ | ⟨_, h⟩
    · exact Or.inl h
    · exact Or.inr h

/-- The core has the same simple `k`-cycles as `g`. -/
theorem isCycle_kCycleCore_iff (g : Graph) (k : Nat) (c : Cycle) :
    IsCycle (kCycleCore g k) k c ↔ IsCycle g k c := by
  constructor
  · rintro ⟨h₁, h₂, h₃, h₄⟩
    exact ⟨h₁, h₂, h₃, fun e he => mem_of_mem_kCycleCore (h₄ e he)⟩
  · intro hc
    exact ⟨hc.1, hc.2.1, hc.2.2.1, fun e he => (mem_kCycleCore_iff g k e).mpr ⟨c, hc, he⟩⟩

/-! ## The enumeration on a subgraph -/

theorem range_filter_extend (P : Nat → Bool) (n d : Nat) (h : ∀ v, P v = true → v < n) :
    (List.range (n + d)).filter P = (List.range n).filter P := by
  rw [List.range_add, List.filter_append, List.filter_map]
  have : (List.range d).filter (P ∘ fun x => n + x) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro x _ hx
    have := h (n + x) hx
    omega
  rw [this, List.map_nil, List.append_nil]

theorem range_filter_eq (P : Nat → Bool) {n m : Nat} (hn : ∀ v, P v = true → v < n)
    (hm : ∀ v, P v = true → v < m) : (List.range n).filter P = (List.range m).filter P := by
  by_cases h : n ≤ m
  · have := range_filter_extend P n (m - n) hn
    rw [Nat.add_sub_cancel' h] at this
    exact this.symm
  · have := range_filter_extend P m (n - m) hm
    rw [Nat.add_sub_cancel' (by omega)] at this
    exact this

/-- Filtering the vertices of a subgraph `h` of `g` by a predicate that implies being a vertex
of `h` is filtering the vertices of `g`. -/
theorem vertices_filter_of_subgraph {h g : Graph} (hsub : ∀ e ∈ h, e ∈ g) (R : Nat → Bool)
    (hR : ∀ v, R v = true → v ∈ vertices h) :
    (vertices h).filter R = (vertices g).filter R := by
  have hhg : ∀ v, v ∈ vertices h → v ∈ vertices g := by
    intro v hv
    obtain ⟨e, he, hev⟩ := (mem_vertices_iff h v).mp hv
    exact (mem_vertices_iff g v).mpr ⟨e, hsub e he, hev⟩
  unfold vertices
  rw [List.filter_filter, List.filter_filter]
  have h₁ : ∀ v, (R v && (h.flatMap fun e => [e.1, e.2]).contains v) = R v := by
    intro v
    cases hv : R v
    · rfl
    · have := List.mem_filter.mp (hR v hv)
      simpa using this.2
  have h₂ : ∀ v, (R v && (g.flatMap fun e => [e.1, e.2]).contains v) = R v := by
    intro v
    cases hv : R v
    · rfl
    · have := List.mem_filter.mp (hhg v (hR v hv))
      simpa using this.2
  simp only [h₁, h₂]
  apply range_filter_eq
  · intro v hv
    exact List.mem_range.mp (List.mem_filter.mp (hR v hv)).1
  · intro v hv
    exact List.mem_range.mp (List.mem_filter.mp (hhg v (hR v hv))).1

theorem vertices_of_subgraph {h g : Graph} (hsub : ∀ e ∈ h, e ∈ g) :
    vertices h = (vertices g).filter fun v => (vertices h).contains v := by
  rw [← vertices_filter_of_subgraph hsub _ (fun v hv => by simpa using hv)]
  exact (List.filter_eq_self.mpr fun v hv => by simpa using hv).symm

theorem neighbors_of_subgraph {h g : Graph} (hsub : ∀ e ∈ h, e ∈ g) (u : Nat) :
    neighbors h u = (neighbors g u).filter fun w => h.contains (edge u w) := by
  unfold neighbors
  rw [vertices_filter_of_subgraph hsub _
    (fun w hw => (endpoints_mem_vertices (by simpa using hw)).2), List.filter_filter]
  apply List.filter_congr
  intro w _
  cases hw : h.contains (edge u w)
  · rfl
  · have hg : edge u w ∈ g := hsub _ (by simpa using hw)
    simp [hg]

theorem walksFrom_zero (g : Graph) (v : Nat) : walksFrom g v 0 = [[v]] := rfl

theorem walksFrom_succ (g : Graph) (v n : Nat) :
    walksFrom g v (n + 1) = (neighbors g v).flatMap fun w => (walksFrom g w n).map (v :: ·) := rfl

theorem walksFrom_head {g : Graph} {v n : Nat} {c : List Nat} (h : c ∈ walksFrom g v n) :
    ∃ rest, c = v :: rest := by
  cases n with
  | zero =>
    rw [walksFrom_zero] at h
    exact ⟨[], List.mem_singleton.mp h⟩
  | succ n =>
    rw [walksFrom_succ] at h
    obtain ⟨w, _, hw⟩ := List.mem_flatMap.mp h
    obtain ⟨c', _, rfl⟩ := List.mem_map.mp hw
    exact ⟨c', rfl⟩

theorem flatMap_filter_eq {α β : Type} (l : List α) (P : α → Bool) (F : α → List β) :
    (l.filter P).flatMap F = l.flatMap fun a => if P a then F a else [] := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.filter_cons]
    cases h : P a <;> simp [h, ih]

theorem flatMap_congr_mem {α β : Type} {l : List α} {F G : α → List β}
    (h : ∀ a ∈ l, F a = G a) : l.flatMap F = l.flatMap G := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons]
    rw [h a List.mem_cons_self, ih fun b hb => h b (List.mem_cons_of_mem a hb)]

/-- The walks of a subgraph `h` of `g` are the walks of `g` that use only edges of `h`, in the
same order. -/
theorem walksFrom_of_subgraph {h g : Graph} (hsub : ∀ e ∈ h, e ∈ g) (n v : Nat) :
    walksFrom h v n = (walksFrom g v n).filter fun c => (pathEdges c).all fun e => h.contains e := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
    rw [walksFrom_succ, walksFrom_succ, neighbors_of_subgraph hsub, List.filter_flatMap,
      flatMap_filter_eq]
    apply flatMap_congr_mem
    intro w _
    rw [ih, List.filter_map]
    have hcongr : (walksFrom g w n).filter
        ((fun c => (pathEdges c).all fun e => h.contains e) ∘ (v :: ·)) =
        (walksFrom g w n).filter fun c =>
          h.contains (edge v w) && (pathEdges c).all fun e => h.contains e := by
      apply List.filter_congr
      intro c hc
      obtain ⟨rest, rfl⟩ := walksFrom_head hc
      simp [pathEdges]
    rw [hcongr]
    cases h.contains (edge v w)
    · simp
    · simp

/-! ## The enumeration on the core -/

theorem isCycle_pathEdges_core {g : Graph} {k : Nat} {c : Cycle} (hc : IsCycle g k c) :
    ((pathEdges c).all fun e => (kCycleCore g k).contains e) = true := by
  rw [List.all_eq_true]
  intro e he
  rw [List.contains_iff_mem]
  exact (mem_kCycleCore_iff g k e).mpr ⟨c, hc, pathEdges_subset_append c (c.take 1) e he⟩

theorem rawCycles_kCycleCore (g : Graph) (k : Nat) : rawCycles (kCycleCore g k) k = rawCycles g k := by
  have hsub : ∀ e ∈ kCycleCore g k, e ∈ g := fun _ he => mem_of_mem_kCycleCore he
  -- the cycles among the walks from `v`, in `g` and in the core
  have hwalks : ∀ v, (walksFrom (kCycleCore g k) v (k - 1)).filter
      (fun c => decide (IsCycle (kCycleCore g k) k c)) =
      (walksFrom g v (k - 1)).filter fun c => decide (IsCycle g k c) := by
    intro v
    rw [walksFrom_of_subgraph hsub, List.filter_filter]
    apply List.filter_congr
    intro c _
    by_cases hc : IsCycle g k c
    · simp only [isCycle_pathEdges_core hc, Bool.and_true]
      simp [hc, (isCycle_kCycleCore_iff g k c).mpr hc]
    · have : ¬ IsCycle (kCycleCore g k) k c := fun h => hc ((isCycle_kCycleCore_iff g k c).mp h)
      simp [hc, this]
  -- a vertex off the core starts no cycle
  have hoff : ∀ v, v ∉ vertices (kCycleCore g k) →
      (walksFrom g v (k - 1)).filter (fun c => decide (IsCycle g k c)) = [] := by
    intro v hv
    apply List.filter_eq_nil_iff.mpr
    intro c hc hcyc
    have hcyc : IsCycle g k c := of_decide_eq_true hcyc
    obtain ⟨rest, rfl⟩ := walksFrom_head hc
    exact hv ((mem_vertices_kCycleCore_iff g k v).mpr ⟨_, hcyc, List.mem_cons_self⟩)
  unfold rawCycles
  rw [List.filter_flatMap, List.filter_flatMap, vertices_of_subgraph hsub, flatMap_filter_eq]
  apply flatMap_congr_mem
  intro v _
  by_cases hv : v ∈ vertices (kCycleCore g k)
  · have : (vertices (kCycleCore g k)).contains v = true := by simpa using hv
    rw [this, hwalks]
    rfl
  · have : (vertices (kCycleCore g k)).contains v = false := by simpa using hv
    rw [this, hoff v hv]
    rfl

/-- Restricting to the core does not change the enumerated simple `k`-cycles, nor their
order. -/
theorem cycles_kCycleCore (g : Graph) (k : Nat) : cycles (kCycleCore g k) k = cycles g k := by
  unfold cycles
  rw [rawCycles_kCycleCore]

/-- Restricting to the core changes neither the assignments nor their costs: for every budget
`B`, an assignment of cost at most `B` exists for the core iff it exists for `g`. -/
theorem hasAssignment_kCycleCore_iff (g : Graph) (k B : Nat) :
    HasAssignment (kCycleCore g k) k B ↔ HasAssignment g k B := by
  unfold HasAssignment
  rw [cycles_kCycleCore]

/-! ## The encodings on the core -/

/-- The encodings depend on the graph only through its enumerated `k`-cycles. -/
theorem encodings_congr {g g' : Graph} {k : Nat} (h : cycles g k = cycles g' k) :
    (∀ permitted, permittedFormula g k permitted = permittedFormula g' k permitted) ∧
      (∀ Ψ, almostFormula g k Ψ = almostFormula g' k Ψ) ∧
      zeroCostFormula g k = zeroCostFormula g' k := by
  refine ⟨fun permitted => ?_, fun Ψ => ?_, ?_⟩
  · unfold permittedFormula pathConstraints candidateOverlaps overlapClause edgeVariable edgePosition
      cycleEdgeAt kCycle
    rw [h]
  · unfold almostFormula pathConstraints candidateOverlaps overlapClause edgeVariable edgePosition
      cycleEdgeAt kCycle
    rw [h]
  · unfold zeroCostFormula pathConstraints edgesOnCycles prefixClauses cyclesThrough prefixVariable
      prefixOffset edgeVariable edgePosition cycleEdgeAt kCycle
    unfold cyclesThrough edgesOnCycles kCycle
    rw [h]

/-- Restricting to the core does not change `Γ'`, `Γ_𝓘` or the zero-cost formula. -/
theorem encodings_kCycleCore (g : Graph) (k : Nat) :
    (∀ Ψ, almostFormula (kCycleCore g k) k Ψ = almostFormula g k Ψ) ∧
      (∀ permitted, permittedFormula (kCycleCore g k) k permitted = permittedFormula g k permitted) ∧
      zeroCostFormula (kCycleCore g k) k = zeroCostFormula g k :=
  have h := encodings_congr (cycles_kCycleCore g k)
  ⟨h.2.1, h.1, h.2.2⟩

end STACS2027

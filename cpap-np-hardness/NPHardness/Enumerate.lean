module

public import NPHardness.CycleRepresentatives

/-!
Concrete graph-walk enumeration for reproducible finite gadget certificates.
All simple k-cycle vertex lists are enumerated, then explicitly deduplicated by
their edge sets. Coverage and pairwise inequivalence are both proved below.
-/

@[expose] public section
namespace STACS2027

/-- The endpoints of the edges of `g`, in increasing order. -/
def vertices (g : Graph) : List Nat :=
  (List.range ((g.flatMap fun e => [e.1, e.2]).foldr max 0 + 1)).filter fun v =>
    (g.flatMap fun e => [e.1, e.2]).contains v

/-- The neighbors of `v` in `g`, in increasing order. -/
def neighbors (g : Graph) (v : Nat) : List Nat :=
  (vertices g).filter fun w => g.contains (edge v w)

/-- The walks of `k` steps in `g` that start at `v`, as vertex lists. -/
def walksFrom (g : Graph) (v k : Nat) : List Cycle :=
  Nat.rec (motive := fun _ => Nat → List Cycle)
    (fun u => [[u]])
    (fun _ previous u => (neighbors g u).flatMap fun w => (previous w).map (u :: ·)) k v

/-- The simple `k`-cycles of `g`, once for each starting vertex and direction. -/
def rawCycles (g : Graph) (k : Nat) : List Cycle :=
  ((vertices g).flatMap fun v => walksFrom g v (k - 1)).filter fun c =>
    decide (IsCycle g k c)

/-- The simple `k`-cycles of `g`, one for each edge set. -/
def cycles (g : Graph) (k : Nat) : List Cycle := cycleRepresentatives (rawCycles g k)

theorem raw_enumerated_isCycle {g : Graph} {k : Nat} {c : Cycle}
    (h : c ∈ rawCycles g k) : IsCycle g k c :=
  of_decide_eq_true (List.mem_filter.mp h).2

theorem enumerated_isCycle {g : Graph} {k : Nat} {c : Cycle}
    (h : c ∈ cycles g k) : IsCycle g k c := by
  exact raw_enumerated_isCycle (cycleRepresentatives_subset _ c h)

theorem le_foldr_max_of_mem {xs : List Nat} {v : Nat} (h : v ∈ xs) :
    v ≤ xs.foldr max 0 := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_max_left ..
    · exact Nat.le_trans (ih h) (Nat.le_max_right ..)

theorem mem_vertices {g : Graph} {e : Edge} (he : e ∈ g) :
    e.1 ∈ vertices g ∧ e.2 ∈ vertices g := by
  have left : e.1 ∈ g.flatMap (fun e => [e.1, e.2]) :=
    List.mem_flatMap.mpr ⟨e, he, by simp⟩
  have right : e.2 ∈ g.flatMap (fun e => [e.1, e.2]) :=
    List.mem_flatMap.mpr ⟨e, he, by simp⟩
  constructor
  · apply List.mem_filter.mpr
    exact ⟨List.mem_range.mpr (by have := le_foldr_max_of_mem left; omega),
      by simpa using left⟩
  · apply List.mem_filter.mpr
    exact ⟨List.mem_range.mpr (by have := le_foldr_max_of_mem right; omega),
      by simpa using right⟩

theorem endpoints_mem_vertices {g : Graph} {a b : Nat} (h : edge a b ∈ g) :
    a ∈ vertices g ∧ b ∈ vertices g := by
  have he := mem_vertices h
  by_cases hab : a ≤ b
  · simpa [edge, Nat.min_eq_left hab, Nat.max_eq_right hab] using he
  · have hba : b ≤ a := by omega
    simpa [edge, Nat.min_eq_right hba, Nat.max_eq_left hba, and_comm] using he

theorem mem_walksFrom_of_path {g : Graph} (a : Nat) (tail : List Nat)
    (he : ∀ e ∈ pathEdges (a :: tail), e ∈ g) :
    a :: tail ∈ walksFrom g a tail.length := by
  induction tail generalizing a with
  | nil => change [a] ∈ [[a]]; simp
  | cons b tail ih =>
    have hab : edge a b ∈ g := he _ (by simp [pathEdges])
    have hrest : ∀ e ∈ pathEdges (b :: tail), e ∈ g := by
      intro e h; exact he e (by simp [pathEdges, h])
    have hb : b ∈ neighbors g a :=
      List.mem_filter.mpr ⟨(endpoints_mem_vertices hab).2, by simpa using hab⟩
    apply List.mem_flatMap.mpr
    refine ⟨b, hb, ?_⟩
    exact List.mem_map.mpr ⟨b :: tail, ih b hrest, rfl⟩

theorem pathEdges_subset_append (c d : List Nat) :
    ∀ e ∈ pathEdges c, e ∈ pathEdges (c ++ d) := by
  induction c with
  | nil => simp [pathEdges]
  | cons a c ih =>
    cases c with
    | nil => simp [pathEdges]
    | cons b tail =>
      intro e he
      simp only [pathEdges, List.mem_cons] at he
      rcases he with rfl | he
      · simp [pathEdges]
      · exact List.mem_cons_of_mem _ (ih e he)

/-- Every vertex representation is present before edge-set deduplication. -/
theorem isCycle_raw_enumerated {g : Graph} {k : Nat} {c : Cycle}
    (hc : IsCycle g k c) : c ∈ rawCycles g k := by
  have hdec : decide (IsCycle g k c) = true := decide_eq_true hc
  obtain ⟨hk, hlen, _hnodup, hedges⟩ := hc
  apply List.mem_filter.mpr
  refine ⟨?_, hdec⟩
  cases c with
  | nil => simp at hlen; omega
  | cons a tail =>
    cases tail with
    | nil => simp at hlen; omega
    | cons b rest =>
      have hab : edge a b ∈ g := hedges _ (by simp [cycleEdges, pathEdges])
      apply List.mem_flatMap.mpr
      refine ⟨a, (endpoints_mem_vertices hab).1, ?_⟩
      have hpath : ∀ e ∈ pathEdges (a :: b :: rest), e ∈ g := by
        intro e he
        exact hedges e (pathEdges_subset_append _ _ e he)
      have hw := mem_walksFrom_of_path a (b :: rest) hpath
      have hsize : (b :: rest).length = k - 1 := by simp only [List.length_cons] at hlen ⊢; omega
      simpa only [hsize] using hw

/-- Every simple k-cycle has an enumerated representative with the same edge set. -/
theorem isCycle_represented {g : Graph} {k : Nat} {c : Cycle}
    (hc : IsCycle g k c) : ∃ d ∈ cycles g k, SameCycle c d :=
  cycleRepresentatives_cover _ c (isCycle_raw_enumerated hc)

/-- Distinct enumerated entries represent distinct cycle edge sets. -/
theorem cycles_pairwise_different (g : Graph) (k : Nat) :
    (cycles g k).Pairwise (fun c d => ¬ SameCycle c d) :=
  cycleRepresentatives_pairwise _

theorem cycles_nodup (g : Graph) (k : Nat) : (cycles g k).Nodup :=
  cycleRepresentatives_nodup _

end STACS2027

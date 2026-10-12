module

public import NPHardness.SubdivisionPrograms

/-! Relabelling graphs and their simple cycles, with explicit injectivity. -/

@[expose] public section
namespace STACS2027

def mapEdge (f : Nat → Nat) (e : Edge) : Edge := edge (f e.1) (f e.2)
def mapGraph (f : Nat → Nat) (g : Graph) : Graph := g.map (mapEdge f)

theorem mapEdge_edge (f : Nat → Nat) (a b : Nat) : mapEdge f (edge a b) = edge (f a) (f b) := by
  by_cases h : a ≤ b
  · simp [mapEdge, edge, Nat.min_eq_left h, Nat.max_eq_right h]
  · have hba : b ≤ a := by omega
    change edge (f (min a b)) (f (max a b)) = _
    rw [Nat.min_eq_right hba, Nat.max_eq_left hba, edge_comm]

theorem pathEdges_map (f : Nat → Nat) (c : List Nat) :
    pathEdges (c.map f) = (pathEdges c).map (mapEdge f) := by
  induction c with
  | nil => rfl
  | cons a c ih =>
    cases c with
    | nil => rfl
    | cons b cs => simpa [pathEdges, mapEdge_edge] using congrArg (edge (f a) (f b) :: ·) ih

theorem cycleEdges_map (f : Nat → Nat) (c : Cycle) :
    cycleEdges (c.map f) = (cycleEdges c).map (mapEdge f) := by
  simp only [cycleEdges, ← List.map_take, ← List.map_append, pathEdges_map]

theorem IsCycle.vertex_bound {g : Graph} {k n : Nat} {c : Cycle}
    (hc : IsCycle g k c) (hb : VerticesBelow g n) : ∀ v ∈ c, v < n := by
  intro v hv
  obtain ⟨w, _, he⟩ := hc.vertex_incident hv
  exact ((edge_below v w n).mp (hb _ (hc.2.2.2 _ he))).1

theorem IsCycle.map {g : Graph} {k : Nat} {c : Cycle} (hc : IsCycle g k c) (f : Nat → Nat)
    (hi : ∀ a ∈ c, ∀ b ∈ c, f a = f b → a = b) : IsCycle (mapGraph f g) k (c.map f) := by
  refine ⟨hc.1, by simpa using hc.2.1, ?_, ?_⟩
  · rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
    exact hc.2.2.1.imp_of_mem (fun {a b} ha hb hne he => hne (hi a ha b hb he))
  · intro e he
    rw [cycleEdges_map] at he
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp he
    exact List.mem_map.mpr ⟨d, hc.2.2.2 d hd, rfl⟩

theorem IsCycle.graph_mono {g h : Graph} {k : Nat} {c : Cycle}
    (hc : IsCycle g k c) (hs : g ⊆ h) : IsCycle h k c :=
  ⟨hc.1, hc.2.1, hc.2.2.1, fun e he => hs (hc.2.2.2 e he)⟩

theorem realizeLinks_below (next : Nat) (ls : List Link)
    (hb : VerticesBelow (linkEdges ls) next) :
    VerticesBelow (realizeLinks next ls) (next + subdivisionCount ls) := by
  induction ls generalizing next with
  | nil => intro e he; simp [realizeLinks] at he
  | cons l ls ih =>
    have hl := (edge_below l.source l.target next).mp (hb _ (by simp [linkEdges]))
    have ht : VerticesBelow (linkEdges ls) (next + l.subdivisions) := by
      intro e he
      have h := hb e (List.mem_cons_of_mem _ he)
      constructor <;> omega
    have htail := ih (next + l.subdivisions) ht
    intro e he
    have hsize : next + subdivisionCount (l :: ls) = next + l.subdivisions + subdivisionCount ls := by
      simp [subdivisionCount, Nat.add_assoc]
    rw [hsize]
    rcases List.mem_append.mp he with he | he
    · have h := subdividedEdge_below _ _ _ _ hl.1 hl.2 e he
      constructor <;> omega
    · exact htail e he

end STACS2027

module

public import Runtimes.BoundedCost.Spec
public import Runtimes.ZeroCostSpec
import Mathlib.Tactic

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 STACS2027.RAM Complexity.SAT

/-- A graph representation of the cycle core with one edge occurrence for each
enumerated cycle position. Parallel list occurrences have the same graph support. -/
def coreOccurrenceGraph (g : Graph) (k : ℕ) : Graph := ZeroCost.occs g k

theorem coreOccurrenceGraph_length (g : Graph) (k : ℕ) :
    (coreOccurrenceGraph g k).length = k * (cycles g k).length := ZeroCost.length_occs g k

theorem coreOccurrenceGraph_support (g : Graph) (k : ℕ) (e : Edge) :
    e ∈ coreOccurrenceGraph g k ↔ e ∈ kCycleCore g k := by
  rw [mem_kCycleCore_iff]
  change e ∈ (cycles g k).flatMap cycleEdges ↔ _
  simp only [List.mem_flatMap]
  constructor
  · rintro ⟨c, hc, he⟩
    exact ⟨c, enumerated_isCycle hc, he⟩
  · rintro ⟨c, hc, he⟩
    obtain ⟨d, hd, hsame⟩ := isCycle_represented hc
    exact ⟨d, hd, hsame.1 e he⟩

theorem cycles_of_same_support {g h : Graph} (he : ∀ e, e ∈ h ↔ e ∈ g) (k : ℕ) :
    cycles h k = cycles g k := by
  have hsub : ∀ e ∈ h, e ∈ g := fun e hmem => (he e).mp hmem
  have hv : ∀ v, v ∈ vertices h ↔ v ∈ vertices g := by
    intro v
    simp only [mem_vertices_iff]
    constructor <;> rintro ⟨e, hmem, hend⟩
    · exact ⟨e, (he e).mp hmem, hend⟩
    · exact ⟨e, (he e).mpr hmem, hend⟩
  have hver : vertices h = vertices g := by
    rw [vertices_of_subgraph hsub]
    apply List.filter_eq_self.mpr
    intro v hmem
    simpa using (hv v).mpr hmem
  have hn : ∀ v, neighbors h v = neighbors g v := by
    intro v
    unfold neighbors
    rw [hver]
    apply List.filter_congr
    intro w _
    exact Bool.eq_iff_iff.mpr (by simpa using he (edge v w))
  have hw : ∀ n v, walksFrom h v n = walksFrom g v n := by
    intro n
    induction n with
    | zero => intro v; rfl
    | succ n ih =>
      intro v
      rw [walksFrom_succ, walksFrom_succ, hn]
      apply List.flatMap_congr
      intro w _
      rw [ih w]
  have hcycle : ∀ c, IsCycle h k c ↔ IsCycle g k c := by
    intro c
    unfold IsCycle
    exact and_congr_right (fun _ => and_congr_right (fun _ =>
      and_congr_right (fun _ => forall_congr' fun e => forall_congr' fun _ => he e)))
  unfold cycles rawCycles
  rw [hver]
  have hflat : (vertices g).flatMap (fun v => walksFrom h v (k - 1)) =
      (vertices g).flatMap (fun v => walksFrom g v (k - 1)) := by
    apply List.flatMap_congr
    intro v _
    exact hw _ _
  rw [hflat]
  congr 1
  apply List.filter_congr
  intro c _
  by_cases hc : IsCycle g k c
  · simp [hc, (hcycle c).mpr hc]
  · have hc' : ¬ IsCycle h k c := fun h => hc ((hcycle c).mp h)
    simp [hc, hc']

/-- The retained occurrence graph has the identical cycle enumeration, including
its order, so the bounded-cost input and output semantics need no permutation. -/
theorem coreOccurrenceGraph_cycles (g : Graph) (k : ℕ) :
    cycles (coreOccurrenceGraph g k) k = cycles g k :=
  (cycles_of_same_support (coreOccurrenceGraph_support g k) k).trans (cycles_kCycleCore g k)

theorem coreOccurrenceGraph_hasAssignment (g : Graph) (k Ψ : ℕ) :
    HasAssignment (coreOccurrenceGraph g k) k Ψ ↔ HasAssignment g k Ψ := by
  simp only [HasAssignment, coreOccurrenceGraph_cycles]

end STACS2027.Runtimes.BoundedCost

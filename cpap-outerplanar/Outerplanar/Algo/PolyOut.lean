module

public import Outerplanar.Algo.PolyBacktrack
public import Outerplanar.Algo.Combine
import Mathlib.Tactic

/-!
# The output of the polygon solver is an optimal assignment

`polyOut pg n k` lists the cycles of the pool, each rotated (`rotateTo`) to start at its
omitted vertex. The pool is the list of the convex `k`-cycles up to order (`PolyFacts`):

* a rotation of a `k`-cycle is a `k`-cycle with the same edges (`rotateTo_isCycle`), so the
  output cycles are `k`-cycles of `pg`, pairwise with different edge sets (distinct convex
  cycles never have the same edges, `ConvexCycle.eq_of_sameCycle`), and every `k`-cycle has
  the edges of one of them (`convex_of_isCycle`);
* the path `selected c 0` of a rotated cycle `c` has the edges of `selectedAt u u[j]` for
  the pool cycle `u` and its omitted index `j`, so the cost of the output is the total cost
  of the values chosen by the backtracking (`total_eq`), the optimum
  (`isMinCost_total_chosen`).

`optimalAssignmentOutput_polyOut`: on a polygon, given the facts `PolyFacts hP hk` about the
enumerations, the output of the solver is an optimal assignment output.
-/

@[expose] public section

namespace STACS2027.Poly

open IsPolygon TreeDP

/-! ### Rotations -/

/-- A rotation of a cycle is a cycle with the same edges. -/
theorem rotateTo_isCycle {g : Graph} {k : ℕ} {c : Cycle} (hc : IsCycle g k c) (j : ℕ) :
    IsCycle g k (rotateTo c j) ∧ SameCycle c (rotateTo c j) := by
  have h := List.take_append_drop j c
  have hc' : IsCycle g k (c.take j ++ c.drop j) := by rw [h]; exact hc
  refine ⟨hc'.append_swap, ?_⟩
  have := sameCycle_append_swap (c.take j) (c.drop j)
  rwa [h] at this

/-- A cycle written from its `j`-th vertex starts with that vertex. -/
theorem headD_rotateTo {c : List ℕ} {j : ℕ} (hj : j < c.length) :
    (rotateTo c j).headD 0 = c.getD j 0 := by
  rw [rotateTo, List.drop_eq_getElem_cons hj, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hj]
  rfl

variable {pg : Graph} {n k : ℕ}

theorem polyOut_eq :
    polyOut pg n k = (List.range (pool pg n k).length).map fun i =>
      rotateTo (cyc pg n k i) (valOf pg n k i) := rfl

/-- **The polygon solver is correct**: on a polygon `pg` on the positions `0, …, n - 1`,
for `k ≥ 3`, given the facts `PolyFacts hP hk` about the enumerations of the solver, the
output of the dynamic program of Appendix F is an optimal assignment output of
`CPAP(pg, k)`. -/
theorem optimalAssignmentOutput_polyOut (hP : IsPolygon pg n) (hk : 3 ≤ k)
    (F : PolyFacts hP hk) : OptimalAssignmentOutput pg k (polyOut pg n k).flatten := by
  have hk0 : 0 < k := by omega
  -- the pool cycles
  have hconv : ∀ i < (pool pg n k).length,
      ConvexCycle pg (cyc pg n k i) ∧ (cyc pg n k i).length = k := by
    intro i hi
    have h := cyc_mem F hi
    rw [convexCycles, List.mem_toFinset, hP.mem_convexList] at h
    exact h
  have hcyc : ∀ i < (pool pg n k).length, IsCycle pg k (cyc pg n k i) := by
    intro i hi
    have h := (hconv i hi).1.isCycle
    rwa [(hconv i hi).2] at h
  have hval : ∀ i, valOf pg n k i < k := fun _ => Nat.mod_lt _ hk0
  have hrot : ∀ i < (pool pg n k).length,
      IsCycle pg k (rotateTo (cyc pg n k i) (valOf pg n k i)) ∧
        SameCycle (cyc pg n k i) (rotateTo (cyc pg n k i) (valOf pg n k i)) :=
    fun i hi => rotateTo_isCycle (hcyc i hi) _
  have hmem : ∀ c ∈ polyOut pg n k, ∃ i < (pool pg n k).length,
      c = rotateTo (cyc pg n k i) (valOf pg n k i) := by
    intro c hc
    rw [polyOut_eq, List.mem_map] at hc
    obtain ⟨i, hi, rfl⟩ := hc
    exact ⟨i, List.mem_range.mp hi, rfl⟩
  have hall : ∀ c ∈ polyOut pg n k, IsCycle pg k c := by
    intro c hc
    obtain ⟨i, hi, rfl⟩ := hmem c hc
    exact (hrot i hi).1
  refine ⟨polyOut pg n k, rfl, hall, ?_, ?_, ?_⟩
  · -- pairwise different edge sets
    rw [polyOut_eq, List.pairwise_map]
    refine List.nodup_range.imp_of_mem ?_
    intro i j hi hj hij hs
    rw [List.mem_range] at hi hj
    have h := (hrot i hi).2.trans (hs.trans (hrot j hj).2.symm)
    have he := (hconv i hi).1.eq_of_sameCycle (hconv j hj).1 h
    rw [cyc_eq_getElem hi, cyc_eq_getElem hj] at he
    exact hij ((F.pool_nodup.getElem_inj_iff).mp he)
  · -- every `k`-cycle
    intro c hc
    obtain ⟨h1, h2, h3⟩ := hP.convex_of_isCycle hc
    have hd : c.insertionSort (· ≤ ·) ∈ pool pg n k := by
      rw [F.mem_pool, hP.mem_convexList]; exact ⟨h1, h2⟩
    have hi := List.idxOf_lt_length_iff.mpr hd
    have hci : cyc pg n k ((pool pg n k).idxOf (c.insertionSort (· ≤ ·))) =
        c.insertionSort (· ≤ ·) := by
      rw [cyc_eq_getElem hi]; exact List.getElem_idxOf hi
    refine ⟨_, List.mem_map.mpr ⟨_, List.mem_range.mpr hi, rfl⟩, ?_⟩
    rw [← hci] at h3
    exact h3.trans (hrot _ hi).2
  · -- the cost is the optimum
    have hcost : cost ((polyOut pg n k).map fun c => selected c 0) =
        (polygonProblem hP hk).total (chosen pg n hk0) := by
      rw [Algo.Comb.cost_selected_zero hall, polyOut_eq, List.map_map]
      -- the omitted vertex of each rotated cycle
      have h1 : cost ((List.range (pool pg n k).length).map
            ((fun c => selectedAt c (c.headD 0)) ∘ fun i =>
              rotateTo (cyc pg n k i) (valOf pg n k i))) =
          cost ((List.range (pool pg n k).length).map fun i =>
            selectedAt (cyc pg n k i) ((cyc pg n k i).getD (valOf pg n k i) 0)) := by
        apply cost_map_eq
        have hp : ∀ i ∈ List.range (pool pg n k).length,
            (((fun c => selectedAt c (c.headD 0)) ∘ fun i =>
              rotateTo (cyc pg n k i) (valOf pg n k i)) i).Perm
              (selectedAt (cyc pg n k i) ((cyc pg n k i).getD (valOf pg n k i) 0)) := by
          intro i hi
          rw [List.mem_range] at hi
          have hj : valOf pg n k i < (cyc pg n k i).length := by
            rw [(hconv i hi).2]; exact hval i
          simp only [Function.comp_apply]
          rw [headD_rotateTo hj]
          exact (hrot i hi).2.symm.selectedAt_perm (hrot i hi).1 (hcyc i hi) _
        exact List.pairwise_of_forall_mem_list fun i hi j hj =>
          overlap_perm (hp i hi) (hp j hj)
      -- the pool, indexed
      have h2 : (List.range (pool pg n k).length).map (fun i =>
            selectedAt (cyc pg n k i) ((cyc pg n k i).getD (valOf pg n k i) 0)) =
          (pool pg n k).map fun u =>
            selectedAt u (u.getD (valOf pg n k ((pool pg n k).idxOf u)) 0) := by
        apply List.ext_getElem (by simp)
        intro i h h'
        have hi : i < (pool pg n k).length := by simpa using h
        simp only [List.getElem_map, List.getElem_range]
        rw [cyc_eq_getElem hi, F.pool_nodup.idxOf_getElem i hi]
      -- the pool is the list of convex cycles, up to order
      have hperm : (pool pg n k).Perm (convexList pg n k) :=
        (List.perm_ext_iff_of_nodup F.pool_nodup convexList_nodup).mpr F.mem_pool
      have h3 : (convexList pg n k).map (fun u =>
            selectedAt u (u.getD (valOf pg n k ((pool pg n k).idxOf u)) 0)) =
          (convexList pg n k).map fun c => selectedAt c (chooseOf (chosen pg n hk0) c) := by
        apply List.map_congr_left
        intro c hc
        have hc' : c ∈ convexCycles pg n k := List.mem_toFinset.mpr hc
        simp [chooseOf, hc', omitted, chosen, idx]
      rw [h1, h2, cost_perm (hperm.map _), h3, hP.total_eq hk]
    rw [hcost]
    exact isMinCost_total_chosen F hk0

end STACS2027.Poly

module

public import Outerplanar.Algo.Poly
public import Outerplanar.DPCorrect

/-!
# The polygon solver: the combinatorial facts used by the correctness proof

`PolyFacts hP hk` collects what the correctness proof of the dynamic program
(`Outerplanar.Algo.PolyDP`) needs about the enumerations of `Outerplanar.Algo.Poly`: the
segment order, the children, the owned edges, the cycle pool, and the boundary sets.
They are proved in `Outerplanar.Algo.PolyPool` (`polyFacts`).
-/

@[expose] public section

namespace STACS2027.Poly

open IsPolygon

/-- The facts about the enumerations on a polygon `pg` with `n` positions, `k ≥ 3`. -/
structure PolyFacts {pg : Graph} {n k : ℕ} (hP : IsPolygon pg n) (hk : 3 ≤ k) : Prop where
  segOrder_nodup : (segOrder pg n).Nodup
  mem_segOrder : ∀ s, s ∈ segOrder pg n ↔ s ∈ segs pg n
  /-- Smaller segments first. -/
  segOrder_size : (segOrder pg n).Pairwise fun s t => s.2 - s.1 ≤ t.2 - t.1
  childSegs_nodup : ∀ s, (childSegs pg n s).Nodup
  mem_childSegs : ∀ s ∈ segs pg n, ∀ t, t ∈ childSegs pg n s ↔ t ∈ segs pg n ∧ IsChild pg n s t
  owned_nodup : ∀ s ∈ segs pg n, (owned pg n s).Nodup
  mem_owned : ∀ s ∈ segs pg n, ∀ e, e ∈ owned pg n s ↔ e ∈ polyEdges pg n ∧ (own hP e).1 = s
  pool_nodup : (pool pg n k).Nodup
  mem_pool : ∀ u, u ∈ pool pg n k ↔ u ∈ convexList pg n k
  /-- The boundary cycles of the tree dynamic program are those through both ends of the
  segment with another top. -/
  mem_boundary : ∀ s (hs : s ∈ segs pg n) (x : CycVar pg n k),
    x ∈ (polygonProblem hP hk).boundary ⟨s, hs⟩ ↔ s.1 ∈ x.1 ∧ s.2 ∈ x.1 ∧ topOf x.1 ≠ s

end STACS2027.Poly

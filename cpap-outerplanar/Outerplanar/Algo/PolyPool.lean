module

public import Outerplanar.Algo.PolyRP
import Mathlib.Tactic

/-!
# The polygon solver: the cycle pool and the boundary sets

On a polygon `pg` on `0, …, n - 1`, for `k ≥ 3`:

* `mem_pool`, `pool_nodup`: the pool (`Outerplanar.Algo.Poly`), the concatenation over the
  segments `s` in `segOrder` of the region paths of `s` with `k` entries (`rpF`), lists the
  convex `k`-cycles (`convexList`), each once: a convex cycle is a region path of its top
  segment (`convexCycle_iff_isRPath`, `top_mem_segs`), and different segments give
  different first and last entries;
* `ends_mem_of_inside_outside`: a region path closed by an edge (a convex cycle) with an
  entry strictly inside an edge `(c, d)` and an entry outside `[c, d]` visits both `c` and
  `d` (edges do not cross, `IsPolygon.noncross`);
* `mem_boundary`: the boundary variables of a segment `s` in the tree dynamic program
  (`polygonProblem`) are the cycles through both ends of `s` with another top;
* `polyFacts`: the facts `PolyFacts` used by the correctness proof of the dynamic program.
-/

@[expose] public section

namespace STACS2027.Poly

open IsPolygon

variable {pg : Graph} {n k : ℕ}

/-! ### Tops -/

/-- The top of a nonempty list: its first and last entry. -/
theorem topOf_eq {u : List ℕ} (hu : u ≠ []) : topOf u = (u.head hu, u.getLast hu) := by
  simp only [topOf, List.headD_eq_head?_getD, List.getLastD_eq_getLast?,
    List.head?_eq_some_head hu, List.getLast?_eq_some_getLast hu, Option.getD_some]

/-- The top of a region path from `a` to `b` is `(a, b)`. -/
theorem topOf_of_isRPath {a b : ℕ} {u : List ℕ} (hu : IsRPath pg a b u) : topOf u = (a, b) := by
  simp only [topOf, List.headD_eq_head?_getD, List.getLastD_eq_getLast?, hu.1, hu.2.1,
    Option.getD_some]

/-- The members of `rpF` have top `(a, b)`. -/
theorem topOf_of_mem_rpF {fuel a b L : ℕ} {u : List ℕ} (hu : u ∈ rpF pg n k fuel a b L) :
    topOf u = (a, b) :=
  topOf_of_isRPath (sound_rpF hu).1

/-- A convex cycle is a region path of its top segment. -/
theorem isRPath_of_convexCycle (hP : IsPolygon pg n) {u : List ℕ} (hc : ConvexCycle pg u)
    (hu : u ≠ []) : IsRPath pg (u.head hu) (u.getLast hu) u :=
  ((convexCycle_iff_isRPath (hP.mem_segs.mp (hP.top_mem_segs hc hu)).1).mp
    ⟨hc, List.head?_eq_some_head hu, List.getLast?_eq_some_getLast hu⟩).1

/-! ### Region paths through both ends of an edge -/

/-- If `c ∉ u` lies strictly between the ends of a region path `u`, two consecutive entries
`x < c < y` of `u` jump over it, every entry of `u` being at most `x` or at least `y`. -/
theorem straddle_gap {a b c : ℕ} {u : List ℕ} (hu : IsRPath pg a b u) (hac : a < c)
    (hcb : c < b) (hc : c ∉ u) : ∃ x y, Adj pg x y ∧ x < c ∧ c < y ∧ ∀ v ∈ u, v ≤ x ∨ y ≤ v := by
  obtain ⟨l₁, x, y, l₂, hsplit, hx, hy⟩ := exists_straddle hu.1 hu.2.1 hac hcb hc
  have hR : x < y ∧ Adj pg x y := by
    have := hu.2.2
    rw [hsplit] at this
    exact (List.isChain_append_cons_cons.mp this).2.1
  have hi : [x, y] <:+: u := ⟨l₁, l₂, by rw [hsplit]; simp⟩
  have hgap := ((infix_pair_iff hu.pairwise).mp hi).2.2.2
  refine ⟨x, y, hR.2, hx, hy, fun v hv => ?_⟩
  have := hgap v hv
  omega

/-- **Both ends of a crossed edge**: a region path `u` from `a` to `b`, closed by the edge
`(a, b)`, with an entry strictly between `c` and `d` and an entry outside `[c, d]`, for an
edge `(c, d)`, visits both `c` and `d`. -/
theorem ends_mem_of_inside_outside (hP : IsPolygon pg n) {a b c d : ℕ} {u : List ℕ}
    (hu : IsRPath pg a b u) (hab : Adj pg a b) (hcd : Adj pg c d) {y z : ℕ} (hy : y ∈ u)
    (hy1 : c < y) (hy2 : y < d) (hz : z ∈ u) (hz' : z < c ∨ d < z) : c ∈ u ∧ d ∈ u := by
  have hyb := hu.bounds hy
  have hzb := hu.bounds hz
  rcases hz' with hz' | hz'
  · have hc : c ∈ u := by
      by_contra hc
      obtain ⟨x, x', hxx', hx, hx', hside⟩ := straddle_gap hu (by omega) (by omega) hc
      have := hside y hy
      exact hP.noncross hx hx' (show x' < d by omega) hxx' hcd
    refine ⟨hc, ?_⟩
    by_contra hd
    have hbd : d ≤ b := by
      by_contra hbd
      exact hP.noncross (show a < c by omega) (show c < b by omega) (show b < d by omega) hab hcd
    have hbd' : d < b := lt_of_le_of_ne hbd (fun h => hd (h ▸ hu.last_mem))
    obtain ⟨x, x', hxx', hx, hx', hside⟩ := straddle_gap hu (by omega) hbd' hd
    have := hside y hy
    exact hP.noncross (show c < x by omega) hx hx' hcd hxx'
  · have hd : d ∈ u := by
      by_contra hd
      obtain ⟨x, x', hxx', hx, hx', hside⟩ := straddle_gap hu (by omega) (by omega) hd
      have := hside y hy
      exact hP.noncross (show c < x by omega) hx hx' hcd hxx'
    refine ⟨?_, hd⟩
    by_contra hc
    have hac : a ≤ c := by
      by_contra hac
      exact hP.noncross (show c < a by omega) (show a < d by omega) (show d < b by omega) hcd hab
    have hac' : a < c := lt_of_le_of_ne hac (fun h => hc (h ▸ hu.head_mem))
    obtain ⟨x, x', hxx', hx, hx', hside⟩ := straddle_gap hu hac' (by omega) hc
    have := hside y hy
    exact hP.noncross hx hx' (show x' < d by omega) hxx' hcd

/-! ### The pool -/

/-- **The pool lists the convex `k`-cycles.** -/
theorem mem_pool (hP : IsPolygon pg n) (hk : 3 ≤ k) (u : List ℕ) :
    u ∈ pool pg n k ↔ u ∈ convexList pg n k := by
  rw [pool, List.mem_flatMap, hP.mem_convexList]
  constructor
  · rintro ⟨s, hs, hu⟩
    have hs' := hP.mem_segs.mp (mem_segOrder.mp hs)
    have hsn := (hP.lt_of_adj hs'.1).2
    obtain ⟨hr, hl⟩ := (mem_rpF hP (by omega) hs'.1 (by omega) (by omega) (by omega)).mp hu
    exact ⟨((convexCycle_iff_isRPath hs'.1).mpr ⟨hr, by omega⟩).1, hl⟩
  · rintro ⟨hc, hl⟩
    have hu : u ≠ [] := by rintro rfl; simp at hl; omega
    have hT := hP.top_mem_segs hc hu
    have hT' := hP.mem_segs.mp hT
    have hTn := (hP.lt_of_adj hT'.1).2
    refine ⟨_, mem_segOrder.mpr hT, ?_⟩
    exact (mem_rpF hP (by omega) hT'.1 (by omega) (by omega) (by omega)).mpr
      ⟨isRPath_of_convexCycle hP hc hu, hl⟩

/-- **The pool lists each cycle once.** -/
theorem pool_nodup : (pool pg n k).Nodup := by
  rw [pool, List.nodup_flatMap]
  refine ⟨fun s _ => rpF_nodup _ _ _ _, ?_⟩
  refine List.Pairwise.imp (fun {s t} hne => ?_) segOrder_nodup
  intro u hu hu'
  have he := (topOf_of_mem_rpF hu).symm.trans (topOf_of_mem_rpF hu')
  exact hne (Prod.ext (congrArg Prod.fst he) (congrArg Prod.snd he))

/-! ### The boundary sets -/

/-- **The boundary cycles of a segment** `s`: the boundary variables of `s` in the tree
dynamic program are the cycles through both ends of `s` whose top is not `s`. -/
theorem mem_boundary (hP : IsPolygon pg n) (hk : 3 ≤ k) (s : ℕ × ℕ) (hs : s ∈ segs pg n)
    (x : CycVar pg n k) :
    x ∈ (polygonProblem hP hk).boundary ⟨s, hs⟩ ↔ s.1 ∈ x.1 ∧ s.2 ∈ x.1 ∧ topOf x.1 ≠ s := by
  simp only [TreeDP.Problem.boundary, Finset.mem_filter, Finset.mem_univ, true_and, mem_sub_iff]
  simp only [polygonProblem, Finset.mem_filter, Finset.mem_univ, true_and]
  have hu := ne_nil_of_mem_convexCycles hk x.2
  have hxc := (hP.mem_convexCycles.mp x.2).1
  have hT := hP.top_mem_segs hxc hu
  have hT' := hP.mem_segs.mp hT
  have hs' := hP.mem_segs.mp hs
  have hr := isRPath_of_convexCycle hP hxc hu
  rw [topOf_eq hu]
  constructor
  · rintro ⟨hnw, f, hf, hfs, hfx⟩
    have hf' := hP.mem_polyEdges.mp hf
    have hfs' := (hP.own_within_iff hf'.1 hf'.2 hs).mp hfs
    have hfe : edge f.1 f.2 = f := by
      simp [edge, Nat.min_eq_left hf'.2.le, Nat.max_eq_right hf'.2.le]
    rw [← hfe] at hfx
    obtain ⟨h1, h2⟩ := mem_of_mem_cycleEdges hfx
    have hfT : Within f (x.1.head hu, x.1.getLast hu) := ⟨(hr.bounds h1).1, (hr.bounds h2).2⟩
    rcases hP.nested_of_within hs hT hf'.2 hfs' hfT with hsT | hTs
    · have hne : (x.1.head hu, x.1.getLast hu) ≠ s := fun he => hnw (he ▸ Within.refl _)
      refine ⟨?_, ?_, hne⟩ <;>
      · simp only [Within] at hfs' hsT
        by_cases hfeq : f.1 = s.1 ∧ f.2 = s.2
        · first | exact hfeq.1 ▸ h1 | exact hfeq.2 ▸ h2
        · have hy : ∃ y ∈ x.1, s.1 < y ∧ y < s.2 := by
            by_cases h' : s.1 < f.1
            · exact ⟨f.1, h1, h', by omega⟩
            · exact ⟨f.2, h2, by omega, by omega⟩
          have hz : ∃ z ∈ x.1, z < s.1 ∨ s.2 < z := by
            by_cases h' : x.1.head hu < s.1
            · exact ⟨_, hr.head_mem, Or.inl h'⟩
            · refine ⟨_, hr.last_mem, Or.inr ?_⟩
              have : x.1.getLast hu ≠ s.2 := fun he =>
                hne (Prod.ext (by simp only; omega) (by simp only; omega))
              omega
          obtain ⟨y, hy, hy1, hy2⟩ := hy
          obtain ⟨z, hz, hz'⟩ := hz
          have := ends_mem_of_inside_outside hP hr hT'.1 hs'.1 hy hy1 hy2 hz hz'
          first | exact this.1 | exact this.2
    · exact absurd hTs hnw
  · rintro ⟨h1, h2, hne⟩
    have hb1 := hr.bounds h1
    have hb2 := hr.bounds h2
    refine ⟨fun hw => hne (Prod.ext (by simp only [Within] at hw; simp only; omega)
      (by simp only [Within] at hw; simp only; omega)), ?_⟩
    obtain ⟨A, B, hAB⟩ := List.append_of_mem h1
    have hpw := hr.pairwise
    rw [hAB] at hpw
    have hs2B : s.2 ∈ B := by
      have : s.2 ∈ A ++ s.1 :: B := hAB ▸ h2
      rcases List.mem_append.mp this with h' | h'
      · exfalso
        have := (List.pairwise_append.mp hpw).2.2 s.2 h' s.1 (by simp)
        omega
      · rcases List.mem_cons.mp h' with h' | h'
        · omega
        · exact h'
    obtain ⟨q, B', rfl⟩ : ∃ q B', B = q :: B' := by
      cases B with
      | nil => simp at hs2B
      | cons q B' => exact ⟨q, B', rfl⟩
    have hpw2 := (List.pairwise_append.mp hpw).2.1
    have hq1 : s.1 < q := (List.pairwise_cons.mp hpw2).1 q (by simp)
    have hq2 : q ≤ s.2 := by
      rcases List.mem_cons.mp hs2B with h' | h'
      · omega
      · exact ((List.pairwise_cons.mp (List.pairwise_cons.mp hpw2).2).1 s.2 h').le
    have hfe : edge s.1 q ∈ cycleEdges x.1 :=
      pathEdges_subset_cycleEdges _ _ (by rw [hAB]; exact edge_mem_pathEdges _ _ _ _)
    have hedge : edge s.1 q = (s.1, q) := by
      simp [edge, Nat.min_eq_left hq1.le, Nat.max_eq_right hq1.le]
    have hadj : Adj pg s.1 q := ⟨by omega, hxc.2.2 _ hfe⟩
    exact ⟨(s.1, q), hP.mem_polyEdges.mpr ⟨hadj, hq1⟩,
      (hP.own_within_iff (e := (s.1, q)) hadj hq1 hs).mpr ⟨le_rfl, hq2⟩, by rw [← hedge]; exact hfe⟩

/-! ### The facts used by the dynamic program -/

/-- **The combinatorial facts about the polygon solver** (`PolyFacts`). -/
theorem polyFacts {pg : Graph} {n k : ℕ} (hP : IsPolygon pg n) (hk : 3 ≤ k) : PolyFacts hP hk where
  segOrder_nodup := segOrder_nodup
  mem_segOrder _ := mem_segOrder
  segOrder_size := segOrder_size
  childSegs_nodup := childSegs_nodup
  mem_childSegs s _ t := mem_childSegs hP s t
  owned_nodup _ hs := owned_nodup hs
  mem_owned _ hs e := mem_owned hP hs e
  pool_nodup := pool_nodup
  mem_pool u := mem_pool hP hk u
  mem_boundary s hs x := mem_boundary hP hk s hs x

end STACS2027.Poly

module

public import MinorFree.Blocks
public import MinorFree.BicliquePlanar

/-!
# Paper interface: Section 8 and Appendix E of the accompanying paper

This module restates the development in the manuscript's terms. It adds no
construction; each theorem is proved from the development.

Section 8 studies `CPAP` on `K_{2,3}`-minor-free graphs. Lemma 19 (ANONYMIZED) says that
every 2-connected `K_{2,3}`-minor-free graph is outerplanar or `K₄`; Theorem 20 that every
`K_{2,3}`-minor-free graph has a perfect assignment for `k = 4`, by Algorithm 4 on the
outerplanar blocks (Lemma 25) and an explicit assignment on `K₄` blocks, combined over
the edge-disjoint blocks; Lemma 23 that planarity alone does not suffice, the optimal
four-cycle cost of the planar graph `K_{2,n−2}` being `Θ(n³)`. What is formalized is
Algorithm 4's assignment and Lemma 25 on any graph with a degree-two elimination order (the
order in which the algorithm deletes vertices) and the common-neighbour bound of Lemma 24; the
`K₄` assignment; the combination over edge-disjoint blocks within which every cycle lies; and
Lemma 23 in full, with exact constants and the planarity of `K_{2,r}` (a planar hypermap
embedding in the sense of the registered foundation's `Complexity.PlanarGraph`). Lemma 19, the
existence of the elimination order for outerplanar graphs, Lemma 24 for
`K_{2,3}`-minor-free graphs, the block decomposition, and Theorem 21 with Appendix F are
cited or stated as hypotheses here; they are formalized in the separate package
`cpap-outerplanar`, which depends on this one; its `STACS2027.k23_linear_ram`
and `STACS2027.outerplanar_linear_ram` prove the fixed-k linear-time algorithms.
Numbers are those of the paper.
-/

@[expose] public section
namespace STACS2027.Paper

/-! ## Appendix E, Algorithm 4 and Lemma 25 -/

/-- Algorithm 4 "repeatedly deletes a vertex of degree at most two, assigning any four-cycle
that disappears to the two edges incident to that vertex": a vertex order in which every vertex
has at most two later neighbours (`EliminationOrder`), and for each four-cycle the path omitting
the vertex opposite its earliest vertex, i.e. the two edges at the earliest vertex
(`algorithm4`). -/
theorem algorithm4_path {g : Graph} {rank : Nat → Nat} (hinj : ∀ a b, rank a = rank b → a = b)
    {c : Cycle} (hc : IsCycle g 4 c) :
    ∃ v u x w, (∀ y, y ∈ c ↔ y = v ∨ y = u ∨ y = x ∨ y = w) ∧
      (∀ e, e ∈ cycleEdges c ↔ e = edge v u ∨ e = edge u x ∨ e = edge x w ∨ e = edge w v) ∧
      (∀ e, e ∈ selected c ((earliestIndex rank c + 2) % 4) ↔ e = edge v u ∨ e = edge w v) ∧
      (rank v < rank u ∧ rank v < rank x ∧ rank v < rank w) := by
  obtain ⟨v, u, x, w, H⟩ := earliestView hinj hc
  exact ⟨v, u, x, w, H.mem, H.edges, H.path, H.earliest⟩

/-- **Lemma 24**, as the hypothesis `CommonNeighbourBound`: "in a `K_{2,3}`-minor-free graph,
any two distinct vertices have at most two common neighbours". -/
theorem common_neighbours_hypothesis (g : Graph) :
    CommonNeighbourBound g ↔ ∀ u w a b c, u ≠ w → edge u a ∈ g → edge w a ∈ g →
      edge u b ∈ g → edge w b ∈ g → edge u c ∈ g → edge w c ∈ g → a = b ∨ a = c ∨ b = c :=
  Iff.rfl

/-- **Lemma 25**. "For any outerplanar graph `G`, Algorithm 4
outputs a perfect cycle-path assignment `τ` with `cost(τ) = 0` for `k = 4`": on every graph
with a degree-two elimination order and the common-neighbour bound. -/
theorem outerplanar_algorithm4_perfect {g : Graph} {rank : Nat → Nat} (ho : EliminationOrder g rank)
    (hb : CommonNeighbourBound g) :
    ValidChoices ((cycles g 4).map selectedOptions) (algorithm4 rank g) ∧
      cost (algorithm4 rank g) = 0 :=
  algorithm4_perfect ho hb

/-- "Two distinct four-cycles receive edge-disjoint paths": the perfectness argument of
Lemma 25's proof, cycle by cycle. -/
theorem outerplanar_algorithm4_disjoint {g : Graph} {rank : Nat → Nat} (ho : EliminationOrder g rank)
    (hb : CommonNeighbourBound g) {c d : Cycle} (hc : IsCycle g 4 c) (hd : IsCycle g 4 d)
    (hne : ¬ SameCycle c d) :
    overlap (selected c ((earliestIndex rank c + 2) % 4))
      (selected d ((earliestIndex rank d + 2) % 4)) = 0 :=
  algorithm4_disjoint ho hb hc hd hne

/-! ## Theorem 20 -/

/-- "For a `K₄` with vertices `1, 2, 3, 4`, assign its three four-cycles as follows: …; these
paths use every edge exactly once." -/
theorem k4_assignment : HasAssignment k4 4 0 := k4_perfect

/-- A `K₄` block contains no `k`-cycles when `k ≥ 5`, as the full proof of Theorem 21
in Appendix F states; the remaining cases are handled by exhaustive search. -/
theorem k4_no_long_cycles {k : Nat} (hk : 5 ≤ k) : cycles k4 k = [] := k4_cycles_nil hk

/-- "Every cycle lies in a unique block, and distinct blocks have disjoint edge sets, so both
the assignments and their costs can be optimized independently": assignments of the blocks
combine with the summed cost. -/
theorem blockwise_combination {blocks : List Graph} {k : Nat} (budget : Graph → Nat)
    (hdisj : EdgeDisjoint blocks) (hsplit : CyclesInBlocks blocks k)
    (hb : ∀ b ∈ blocks, HasAssignment b k (budget b)) :
    HasAssignment blocks.flatten k (blocks.map budget).sum :=
  hasAssignment_blocks budget hdisj hsplit hb

/-- **Theorem 20**. "Every `K_{2,3}`-minor-free graph admits a
perfect cycle-path assignment for `k = 4`": for a graph whose four-cycles lie within pairwise
edge-disjoint blocks, each outerplanar (given by an elimination order and the common-neighbour
bound) or a copy of `K₄` (Lemma 19). -/
theorem k23_perfect_of_blocks {blocks : List Graph} (hdisj : EdgeDisjoint blocks)
    (hsplit : CyclesInBlocks blocks 4) (hb : ∀ b ∈ blocks, OuterplanarOrK4 b) :
    HasAssignment blocks.flatten 4 0 :=
  perfect_assignment_of_blocks hdisj hsplit hb

/-! ## Appendix E, Lemma 23 -/

/-- "Every assignment has total load `Q = (n − 2)(n − 3)`" on `K_{2,n−2}`, and in general
`Q = (k − 2) t`. -/
theorem total_load_general {g : Graph} {k : Nat} (hg : g.Nodup) {ps : List (List Edge)}
    (hv : ValidChoices ((cycles g k).map selectedOptions) ps) :
    (g.map (load ps)).sum = (k - 2) * (cycles g k).length :=
  assignment_total_load hg hv

/-- "By Cauchy–Schwarz, `c(τ) = (∑_e l(e)² − Q)/2 ≥ (Q²/m − Q)/2`": `Q² ≤ m (2 c(τ) + Q)`. -/
theorem cauchy_schwarz_lower_bound {g : Graph} {k : Nat} (hg : g.Nodup) {ps : List (List Edge)}
    (hv : ValidChoices ((cycles g k).map selectedOptions) ps) :
    ((k - 2) * (cycles g k).length) * ((k - 2) * (cycles g k).length) ≤
      g.length * (2 * cost ps + (k - 2) * (cycles g k).length) :=
  cost_lower_bound hg hv

/-- "`K_{2,n−2}` has `m = 2(n − 2)` edges and `binom(n − 2, 2)` four-cycles" (`r = n − 2`). -/
theorem biclique_counts (r : Nat) :
    (biclique r).length = 2 * r ∧ (cycles (biclique r) 4).length = pairCount r :=
  ⟨biclique_length r, biclique_cycle_count r⟩

/-- "Each edge belongs to exactly `n − 3` four-cycles." -/
theorem biclique_edge_count {r : Nat} {e : Edge} (he : e ∈ biclique r) :
    ((cycles (biclique r) 4).filter fun c => decide (e ∈ cycleEdges c)).length = r - 1 :=
  biclique_edge_cycles he

/-- "Take `G = K_{2,n−2}`", a planar graph (`r = n − 2`): in the sense of the registered
foundation, a planar hypermap on its half-edges embeds it. -/
theorem biclique_planar' (r : Nat) : Complexity.PlanarGraph (biclique r) :=
  (biclique_planar_family r).1

/-- **Lemma 23.** "There is a family of planar graphs on `n` vertices whose optimal four-cycle
assignment cost is `Θ(n³)`": `K_{2,r}` (`n = r + 2`) is planar, and every assignment of it has
cost at least `(n − 2)(n − 3)(n − 5)/4` and at most `(n − 2)(n − 3)(n − 4)`. -/
theorem biclique_planar_family' (r : Nat) :
    Complexity.PlanarGraph (biclique r) ∧
      ∀ ps, ValidChoices ((cycles (biclique r) 4).map selectedOptions) ps →
        r * (r - 1) * (r - 3) ≤ 4 * cost ps ∧ cost ps ≤ r * (r - 1) * (r - 2) :=
  ⟨(biclique_planar_family r).1, (biclique_planar_family r).2.2.2⟩

end STACS2027.Paper

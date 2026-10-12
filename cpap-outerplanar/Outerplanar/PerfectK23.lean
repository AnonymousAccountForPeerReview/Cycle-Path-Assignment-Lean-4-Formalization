module

public import Outerplanar.BlockConn
public import Outerplanar.DFS
public import Outerplanar.Degenerate
public import MinorFree.Blocks
public import Outerplanar.TwoConnectedK23Structure
import Mathlib.Tactic

/-!
# Theorem 20 for `K_{2,3}`-minor-free graphs

**Theorem 20**: every `K_{2,3}`-minor-free graph admits a perfect cycle-path assignment
for `k = 4` (`k23_perfect`; the third sentence of Lemma 19 is proved in
`Outerplanar/TwoConnectedK23Structure.lean`; `k23_perfect_of_structure` takes it as a hypothesis).

The proof follows the paper (Appendix E): decompose `g` into its blocks (the blocks of a palm
tree: edge-disjoint, every cycle in one of them, each with a third vertex 2-connected); by
Lemma 19, each block with a cycle is outerplanar (an outerplanar Hamiltonian cycle) or a
`K₄`; an outerplanar block has a degree-two elimination order (2-degeneracy) and, by
Lemma 24, at most two common neighbours of any two vertices, so Lemma 25 (Algorithm 4)
gives it a perfect assignment; `K₄` has one; the blockwise assignments combine.
-/

@[expose] public section

namespace STACS2027

/-! ### `K₄` -/

theorem mem_mapGraph_k4 (t : ℕ → ℕ) (x y : ℕ) :
    edge x y ∈ mapGraph t k4 ↔ edge x y = edge (t 0) (t 1) ∨ edge x y = edge (t 0) (t 2) ∨
      edge x y = edge (t 0) (t 3) ∨ edge x y = edge (t 1) (t 2) ∨ edge x y = edge (t 1) (t 3) ∨
      edge x y = edge (t 2) (t 3) := by
  simp only [mapGraph, k4, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
    mapEdge]

/-- A `K₄` is the graph `k4` renamed. -/
theorem IsK4Graph.relabel {b : Graph} (h : IsK4Graph b) :
    ∃ t : ℕ → ℕ, (∀ i, i < 4 → ∀ j, j < 4 → t i = t j → i = j) ∧
      ∀ x y, x ≠ y → (edge x y ∈ b ↔ edge x y ∈ mapGraph t k4) := by
  obtain ⟨a, b', c, d, hab, hac, had, hbc, hbd, hcd, hadj⟩ := h
  let t : ℕ → ℕ := fun i => if i = 0 then a else if i = 1 then b' else if i = 2 then c else d
  have t0 : t 0 = a := rfl
  have t1 : t 1 = b' := rfl
  have t2 : t 2 = c := rfl
  have t3 : t 3 = d := rfl
  refine ⟨t, ?_, ?_⟩
  · intro i hi j hj hij
    interval_cases i <;> interval_cases j <;> simp_all
  · intro x y hxy
    have h1 : edge x y ∈ b ↔ Adj b x y := ⟨fun h => ⟨hxy, h⟩, fun h => h.2⟩
    rw [h1, hadj, mem_mapGraph_k4, t0, t1, t2, t3]
    simp only [edge_eq_iff]
    constructor
    · rintro ⟨-, hx, hy⟩
      rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;> simp_all
    · intro h
      refine ⟨hxy, ?_⟩
      rcases h with (⟨h1, h2⟩ | ⟨h1, h2⟩) | (⟨h1, h2⟩ | ⟨h1, h2⟩) | (⟨h1, h2⟩ | ⟨h1, h2⟩) |
        (⟨h1, h2⟩ | ⟨h1, h2⟩) | (⟨h1, h2⟩ | ⟨h1, h2⟩) | (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> simp [h1, h2]

/-- `CPAP` on a `K₄` is `CPAP` on `k4`. -/
theorem IsK4Graph.hasAssignment_iff {b : Graph} (h : IsK4Graph b) (k B : ℕ) :
    HasAssignment b k B ↔ HasAssignment k4 k B := by
  obtain ⟨t, ht, he⟩ := h.relabel
  rw [hasAssignment_proper he, hasAssignment_relabel k4_verticesBelow k4_normalized t ht]

/-! ### Outerplanar blocks -/

/-- **Lemma 25 on an outerplanar block**: a `K_{2,3}`-minor-free graph without loops with
an outerplanar Hamiltonian cycle has a perfect assignment for `k = 4`. -/
theorem perfect_of_outerplanarHam {b : Graph} {ham : List ℕ} (h : OuterplanarHam b ham)
    (hk : K23MinorFree b) (hloop : ∀ e ∈ b, e.1 ≠ e.2) : HasAssignment b 4 0 := by
  obtain ⟨rank, hrank⟩ := eliminationOrder_of_degenerate (g := b) (fun U hU hUv =>
    outerplanarHam_degenerate h hU (fun u hu => h.2.1 u (hUv u hu)))
  obtain ⟨hv, hc⟩ := algorithm4_perfect hrank (commonNeighbourBound_of_k23MinorFree hk hloop)
  exact ⟨_, hv, hc.le⟩

/-- A graph without cycles of length `k` has a perfect assignment. -/
theorem hasAssignment_of_no_cycle {b : Graph} {k : ℕ} (h : ∀ c, ¬ IsCycle b k c) :
    HasAssignment b k 0 := by
  have hnil : cycles b k = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro c hc
    exact h c (enumerated_isCycle hc)
  refine ⟨[], ?_, le_rfl⟩
  rw [hnil]; trivial

/-! ### The corollary -/

namespace Palm

variable {g : Graph} (P : Palm g)

open Classical

/-- The heads of the palm tree. -/
noncomputable def heads : List ℕ := (vertices g).filter fun h => decide (P.IsHead h)

theorem heads_nodup : P.heads.Nodup := (List.nodup_range.filter _).filter _

theorem mem_heads {h : ℕ} : h ∈ P.heads ↔ P.IsHead h := by
  simp only [heads, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
  intro hh
  obtain ⟨u, hu⟩ := hh.1
  exact (endpoints_mem_vertices hu.2).2

/-- The blocks. -/
noncomputable def blocks : List Graph := P.heads.map P.block

theorem mem_block_iff {h : ℕ} {e : Edge} :
    e ∈ P.block h ↔ e ∈ g ∧ e.1 < e.2 ∧ P.head (P.lower e.1 e.2) = h := by
  simp [block]

theorem blocks_flatten (a b : ℕ) (hab : a ≠ b) : edge a b ∈ g ↔ edge a b ∈ P.blocks.flatten := by
  constructor
  · intro he
    have hadj : Adj g a b := ⟨hab, he⟩
    have hadj' : Adj g (edge a b).1 (edge a b).2 := by
      rcases Nat.lt_or_gt_of_ne hab with h | h
      · simpa [edge, Nat.min_eq_left h.le, Nat.max_eq_right h.le] using hadj
      · simpa [edge, Nat.min_eq_right h.le, Nat.max_eq_left h.le] using hadj.symm
    obtain ⟨hxv, hxr, -⟩ := P.lower_facts hadj'
    have hh := (P.head_spec hxv hxr).1
    apply List.mem_flatten.mpr
    refine ⟨P.block (P.head (P.lower (edge a b).1 (edge a b).2)), List.mem_map_of_mem
      ((P.mem_heads).mpr hh), ?_⟩
    rw [P.mem_block_iff]
    exact ⟨he, by simp only [edge]; omega, rfl⟩
  · intro he
    obtain ⟨b', hb', heb⟩ := List.mem_flatten.mp he
    obtain ⟨h, -, rfl⟩ := List.mem_map.mp hb'
    exact P.block_sub h _ heb

theorem blocks_edgeDisjoint : EdgeDisjoint P.blocks := by
  unfold EdgeDisjoint blocks
  rw [List.pairwise_map]
  refine P.heads_nodup.imp ?_
  intro h h' hne e he he'
  rw [P.mem_block_iff] at he he'
  exact hne (he.2.2.symm.trans he'.2.2)

theorem blocks_cycles (k : ℕ) : CyclesInBlocks P.blocks k := by
  intro c hc
  have hcg : IsCycle g k c := hc.graph_mono (fun e he => by
    obtain ⟨b', hb', heb⟩ := List.mem_flatten.mp he
    obtain ⟨h, -, rfl⟩ := List.mem_map.mp hb'
    exact P.block_sub h _ heb)
  obtain ⟨e0, he0⟩ := cycleEdges_nonempty hcg
  have hn := pathEdges_normalized _ e0 he0
  have he0' : edge e0.1 e0.2 ∈ cycleEdges c := by rw [hn]; exact he0
  have hall := P.cycle_in_block hcg he0'
  have hadj : Adj g e0.1 e0.2 := ⟨hcg.edge_endpoints_ne he0, by rw [hn]; exact hcg.2.2.2 e0 he0⟩
  obtain ⟨hxv, hxr, -⟩ := P.lower_facts hadj
  have hh := (P.head_spec hxv hxr).1
  exact ⟨_, List.mem_map_of_mem ((P.mem_heads).mpr hh), hall⟩

theorem block_k23MinorFree (hg : K23MinorFree g) (h : ℕ) : K23MinorFree (P.block h) :=
  fun hm => hg (hm.mono (fun _ _ huv => ((P.adj_block).mp huv).1))

theorem block_loopfree (h : ℕ) : ∀ e ∈ P.block h, e.1 ≠ e.2 := by
  intro e he
  rw [P.mem_block_iff] at he
  omega

/-- A block without a third vertex has no cycle. -/
theorem block_no_cycle {h : ℕ} (hh : P.IsHead h) (h3 : ¬ ∃ v, P.InBlock h v ∧ v ≠ h ∧ v ≠ P.par h)
    {k : ℕ} (c : Cycle) : ¬ IsCycle (P.block h) k c := by
  intro hc
  have hsub : c ⊆ [h, P.par h] := by
    intro v hv
    obtain ⟨w, hwv, hw⟩ := hc.vertex_incident hv
    have hadj : Adj (P.block h) v w := ⟨Ne.symm hwv, hc.2.2.2 _ hw⟩
    have hin : P.InBlock h v := (P.isVertex_block hh).mp ⟨w, hadj.symm⟩
    by_contra hnot
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hnot
    exact h3 ⟨v, hin, hnot.1, hnot.2⟩
  have := List.Nodup.length_le_of_subset hc.2.2.1 hsub
  have := hc.1
  have := hc.2.1
  simp at *
  omega

end Palm

/-- **Theorem 20**, from Lemma 19 (third sentence, `TwoConnectedK23Structure`) as a hypothesis: every
`K_{2,3}`-minor-free graph admits a perfect cycle-path assignment for `k = 4`. -/
theorem k23_perfect_of_structure (hL : TwoConnectedK23Structure) {g : Graph} (hg : K23MinorFree g) :
    HasAssignment g 4 0 := by
  classical
  obtain ⟨P⟩ := exists_palm g
  rw [hasAssignment_proper P.blocks_flatten]
  have := hasAssignment_blocks (fun _ => 0) P.blocks_edgeDisjoint (P.blocks_cycles 4) (by
    intro b hb
    obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hb
    have hh' := (P.mem_heads).mp hh
    by_cases h3 : ∃ v, P.InBlock h v ∧ v ≠ h ∧ v ≠ P.par h
    · rcases hL _ (P.twoConnected_block hh' h3) (P.block_k23MinorFree hg h) with hk4 | ⟨ham, hham⟩
      · rw [hk4.hasAssignment_iff]; exact k4_perfect
      · exact perfect_of_outerplanarHam hham (P.block_k23MinorFree hg h) (P.block_loopfree h)
    · exact hasAssignment_of_no_cycle (P.block_no_cycle hh' h3))
  simpa using this

/-- **Theorem 20**: every `K_{2,3}`-minor-free graph admits a perfect cycle-path assignment
for `k = 4` (the third sentence of Lemma 19 is proved: `twoConnectedK23_structure`). -/
theorem k23_perfect {g : Graph} (hg : K23MinorFree g) : HasAssignment g 4 0 :=
  k23_perfect_of_structure twoConnectedK23_structure hg

end STACS2027

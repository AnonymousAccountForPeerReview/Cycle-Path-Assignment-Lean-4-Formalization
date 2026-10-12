module

public import Runtimes.C4.Supersat
import Outerplanar.RAM.R0Spec
import Outerplanar.Algo.Combine
import Outerplanar.Algo.LowPoint
import Mathlib.Tactic

/-!
# Four-cycle listing: the bounds on the number of inserted 2-paths

`N = numV g`, `m = g.length`, `|E| = (idEdges g).length ≤ m`, `t = (cycles g 4).length`:

* **Bound (a)** `numPaths_le_sq`: for any ranking injective on the vertices,
  `numPaths ≤ N² + t` (every insertion opens one of at most `N²` buckets or reports a cycle,
  and exactly `t` cycles are reported);
* **Bound (b)** `numPaths_le_pow43`: for the peeling order, `numPaths ≤ 4 D |E| ≤ 8 X + 18 t`
  with `X = ⌈m^{4/3}⌉ = pow43 m` (`numPaths_le_degen`, `degen_bound`);
* **Combined** `numPaths_le`: `numPaths g (peelPos g) ≤ 8 · min (N², ⌈m^{4/3}⌉) + 18 t`, and
  `numPaths_le'`: `numPaths g (peelPos g) ≤ 18 · (t + min (N², ⌈m^{4/3}⌉))`;
* `pow43`: `pow43_mono`, `le_pow43` (`m ≤ ⌈m^{4/3}⌉`), `pow43_le_sq`;
* for the machine's step counts: `sum_length_outL_le` (`Σ_{v<N} |out v| ≤ 2 |E|`),
  `length_outL_le_degen`, `numV_le` (`N ≤ 2m`), `length_idEdges_le` (`|E| ≤ m`), and for a
  simple graph `length_le_sq_of_simple` (`m ≤ N²`; with `le_pow43`, the paper's form).
-/

@[expose] public section

namespace STACS2027.Runtimes.C4

open STACS2027 STACS2027.Algo Finset

/-! ### `pow43` -/

theorem pow43_mono {m m' : ℕ} (h : m ≤ m') : pow43 m ≤ pow43 m' :=
  pow43_min ((Nat.pow_le_pow_left h 4).trans (pow43_spec m'))

/-- `m ≤ ⌈m^{4/3}⌉`. -/
theorem le_pow43 (m : ℕ) : m ≤ pow43 m := by
  by_contra h
  simp only [not_le] at h
  have h1 : pow43 m ^ 3 < m ^ 3 := Nat.pow_lt_pow_left h (by norm_num)
  have h2 : m ^ 3 ≤ m ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have := pow43_spec m
  omega

/-- `⌈m^{4/3}⌉ ≤ m²`. -/
theorem pow43_le_sq (m : ℕ) : pow43 m ≤ m ^ 2 := by
  apply pow43_min
  rcases Nat.eq_zero_or_pos m with h | h
  · simp [h]
  · rw [← pow_mul]; exact Nat.pow_le_pow_right h (by norm_num)

/-! ### Sizes of the graph -/

theorem numV_le (g : Graph) : numV g ≤ 2 * g.length := RAM.R0.numV_le g

theorem length_idEdges_le (g : Graph) : (idEdges g).length ≤ g.length :=
  RAM.R0.length_idEdges_le g

/-- For a simple graph given by its edges (each once, smaller end first), `m ≤ N²`. -/
theorem length_le_sq_of_simple (g : Graph) (hs : g.Nodup ∧ ∀ e ∈ g, e.1 < e.2) :
    g.length ≤ numV g * numV g := by
  have hl : ∀ e ∈ g, e.1 ∈ labels g ∧ e.2 ∈ labels g := fun e he =>
    Comb.mem_labels_of_proper (Comb.mem_proper.mpr ⟨he, hs.2 e he⟩)
  rw [← List.toFinset_card_of_nodup hs.1]
  have h := card_le_card_of_injOn (s := g.toFinset) (t := range (numV g) ×ˢ range (numV g))
    (fun e => (idOf g e.1, idOf g e.2)) ?_ ?_
  · simpa using h
  · intro e he
    have := hl e (List.mem_toFinset.mp he)
    simp [Comb.idOf_lt this.1, Comb.idOf_lt this.2]
  · intro e he e' he' h
    have h1 := hl e (List.mem_toFinset.mp he)
    have h2 := hl e' (List.mem_toFinset.mp he')
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (idOf_inj h1.1 h.1) (idOf_inj h1.2 h.2)

/-- The out-degrees sum to at most `2 |E|`. -/
theorem sum_length_outL_le (g : Graph) (pos : ℕ → ℕ) :
    ∑ v ∈ range (numV g), (outL g pos v).length ≤ 2 * (idEdges g).length := by
  rw [← sum_length_nb]
  exact sum_le_sum fun v _ => length_outL_le g pos v

theorem length_outL_le_degen (g : Graph) {v : ℕ} (hv : v < numV g) :
    (outL g (peelPos g) v).length ≤ degen g :=
  le_sup (f := fun v => (outL g (peelPos g) v).length) (mem_range.mpr hv)

/-! ### Bound (a) -/

/-- **Bound (a)**: for any ranking injective on the vertices, at most `N² + t`
2-paths are inserted. -/
theorem numPaths_le_sq (g : Graph) (pos : ℕ → ℕ) (hpos : Set.InjOn pos (Set.Iio (numV g))) :
    numPaths g pos ≤ numV g * numV g + (cycles g 4).length := by
  have h := length_le_card_keys_add (ins g pos)
  rw [length_reports_ins g pos hpos] at h
  have hk : ((ins g pos).map Prod.fst).toFinset ⊆ range (numV g) ×ˢ range (numV g) := by
    intro k hk
    simp only [List.mem_toFinset, List.mem_map] at hk
    obtain ⟨⟨⟨x, y⟩, z⟩, hm, rfl⟩ := hk
    obtain ⟨-, hx, hy, -⟩ := (mem_ins hpos).mp hm
    simp [hx, hy]
  have := card_le_card hk
  rw [card_product, card_range] at this
  unfold numPaths
  omega

/-! ### Bound (b) and the combination -/

/-- **Bound (b)**: for the peeling order, at most `8 ⌈m^{4/3}⌉ + 18 t` 2-paths
are inserted. -/
theorem numPaths_le_pow43 (g : Graph) :
    numPaths g (peelPos g) ≤ 8 * pow43 g.length + 18 * (cycles g 4).length := by
  have h1 := numPaths_le_degen g (peelPos g) fun v hv => length_outL_le_degen g hv
  have hX : (idEdges g).length ^ 4 ≤ pow43 g.length ^ 3 :=
    (Nat.pow_le_pow_left (length_idEdges_le g) 4).trans (pow43_spec _)
  have h2 := degen_bound g hX
  omega

/-- **Combined bound**. -/
theorem numPaths_le (g : Graph) :
    numPaths g (peelPos g) ≤
      8 * min (numV g * numV g) (pow43 g.length) + 18 * (cycles g 4).length := by
  have ha := numPaths_le_sq g (peelPos g) (peelPos_injOn g)
  have hb := numPaths_le_pow43 g
  rcases le_total (numV g * numV g) (pow43 g.length) with h | h
  · rw [min_eq_left h]; omega
  · rw [min_eq_right h]; omega

/-- The inserted-path count in the form `C · (t + min (N², ⌈m^{4/3}⌉))`, `C = 18`. -/
theorem numPaths_le' (g : Graph) :
    numPaths g (peelPos g) ≤
      18 * ((cycles g 4).length + min (numV g * numV g) (pow43 g.length)) := by
  have := numPaths_le g
  omega

end STACS2027.Runtimes.C4

module

public import Approximation.Greedy

/-!
Lemma 13 and Theorem 14: the sum of squared loads of a greedy run is at most
`(3 + 2√2)` times that of any assignment, and the greedy cost is at most
`(3 + 2√2) OPT + (1 + √2)(k − 2) t`. Both are stated without square roots, as
`(S − S')² ≤ 4 S S'`, which for `S ≥ S'` is `S/S' ≤ (1 + √2)² = 3 + 2√2`.
-/

@[expose] public section
namespace STACS2027

/-- The option lists of the `k`-cycles of `g`: the instance of Algorithms 1 and 2. -/
theorem cycleOptions_nonempty (g : Graph) (k : Nat) :
    ∀ opts ∈ (cycles g k).map selectedOptions, opts ≠ [] := by
  intro opts ho
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ho
  have hk := (enumerated_isCycle hc).1
  have hl := (enumerated_isCycle hc).2.1
  intro h
  have : (selectedOptions c).length = 0 := by rw [h]; rfl
  simp only [selectedOptions, List.length_map, List.length_range] at this
  omega

theorem greedy_cycles_run (g : Graph) (k : Nat) :
    GreedyRun [] ((cycles g k).map selectedOptions) (greedy ((cycles g k).map selectedOptions)) :=
  greedy_run _ (cycleOptions_nonempty g k)

theorem load_le_sq (es : List Edge) (ps : List (List Edge)) :
    (es.map (load ps)).sum ≤ (es.map fun e => load ps e * load ps e).sum :=
  sum_map_le es _ _ (fun _ _ => Nat.le_mul_self _)

/-- Lemma 13 on the graph `g`: for a run `ps` of Algorithm 1 on the `k`-cycles of `g` and any
assignment `qs`, with `S = ∑_e l(e)²` and `S' = ∑_e l'(e)²`, `(S − S')² ≤ 4 S S'`. -/
theorem greedy_sq_load_bound {g : Graph} {k : Nat} (hg : g.Nodup) {ps qs : List (List Edge)}
    (hrun : GreedyRun [] ((cycles g k).map selectedOptions) ps)
    (hq : ValidChoices ((cycles g k).map selectedOptions) qs) :
    ((g.map fun e => load ps e * load ps e).sum - (g.map fun e => load qs e * load qs e).sum) *
      ((g.map fun e => load ps e * load ps e).sum - (g.map fun e => load qs e * load qs e).sum) ≤
    4 * ((g.map fun e => load ps e * load ps e).sum * (g.map fun e => load qs e * load qs e).sum) := by
  obtain ⟨hlen, hpn, hpl, hps⟩ := enumerated_choices_properties hrun.valid
  obtain ⟨hlen', hqn, hql, hqs⟩ := enumerated_choices_properties hq
  have hS := sum_sq_load hg ps hpn hps
  have hQ : (g.map (load ps)).sum = (g.map (load qs)).sum := by
    rw [total_load hg hpl hps, total_load hg hql hqs, hlen, hlen']
  have hQ' := load_le_sq g qs
  have hc : cost ps ≤ (g.map fun e => load qs e * load ps e).sum := by
    have h := hrun.cost_le hq
    simp only [List.nil_append, cost, Nat.zero_add] at h
    rw [sum_pathLoad_eq hg ps qs hqs] at h
    exact h
  have hP : (g.map fun e => load qs e * load ps e).sum * (g.map fun e => load qs e * load ps e).sum ≤
      (g.map fun e => load ps e * load ps e).sum * (g.map fun e => load qs e * load qs e).sum := by
    exact Nat.le_trans (cauchy_schwarz g (load qs) (load ps)) (Nat.le_of_eq (Nat.mul_comm _ _))
  exact quadratic_bound hS.symm (hQ ▸ hQ') hc hP

/-- Theorem 14 on the graph `g`, with `Q = (k − 2) t` the total load, `A = 2 ALG + Q` and
`B = 2 c(qs) + Q`: `(A − B)² ≤ 4 A B`, i.e. `A ≤ (3 + 2√2) B`, which rearranges to
`ALG ≤ (3 + 2√2) c(qs) + (1 + √2)(k − 2) t`; with `qs` optimal, `c(qs) = OPT`. -/
theorem greedy_cost_bound {g : Graph} {k : Nat} (hg : g.Nodup) {ps qs : List (List Edge)}
    (hrun : GreedyRun [] ((cycles g k).map selectedOptions) ps)
    (hq : ValidChoices ((cycles g k).map selectedOptions) qs) :
    (2 * cost ps + (k - 2) * (cycles g k).length - (2 * cost qs + (k - 2) * (cycles g k).length)) *
      (2 * cost ps + (k - 2) * (cycles g k).length - (2 * cost qs + (k - 2) * (cycles g k).length)) ≤
    4 * ((2 * cost ps + (k - 2) * (cycles g k).length) *
      (2 * cost qs + (k - 2) * (cycles g k).length)) := by
  obtain ⟨hlen, hpn, hpl, hps⟩ := enumerated_choices_properties hrun.valid
  obtain ⟨hlen', hqn, hql, hqs⟩ := enumerated_choices_properties hq
  have h := greedy_sq_load_bound hg hrun hq
  rw [sum_sq_load_assignment hg hpn hpl hps, sum_sq_load_assignment hg hqn hql hqs, hlen, hlen'] at h
  exact h

/-- An integer form of Theorem 14: `2 ALG ≤ 12 c(qs) + 5 (k − 2) t` (as `3 + 2√2 < 6`). -/
theorem greedy_cost_integer_bound {g : Graph} {k : Nat} (hg : g.Nodup) {ps qs : List (List Edge)}
    (hrun : GreedyRun [] ((cycles g k).map selectedOptions) ps)
    (hq : ValidChoices ((cycles g k).map selectedOptions) qs) :
    2 * cost ps ≤ 12 * cost qs + 5 * ((k - 2) * (cycles g k).length) := by
  have h := le_six_of_quadratic (greedy_cost_bound hg hrun hq)
  omega

end STACS2027

module

public import Approximation.Expectation
public import Approximation.GreedyBound

/-!
Theorems 16 and 17 on a graph: the rounding bounds instantiated on the
`k`-cycles of `g`, whose option lists form a `CycleInstance`.
-/

@[expose] public section
namespace STACS2027

theorem cycleEdges_length {c : Cycle} (hc : c ≠ []) : (cycleEdges c).length = c.length := by
  unfold cycleEdges
  rw [pathEdges_length, List.length_append]
  cases c with
  | nil => exact absurd rfl hc
  | cons a c => simp

/-- The option lists of the `k`-cycles of `g`, with any weights, form a cycle instance with paths
of `k − 2` edges. -/
theorem cycleInstance_of_cycles {g : Graph} {k : Nat} {R : List (List (List Edge) × List Nat)}
    (hR : R.map Prod.fst = (cycles g k).map selectedOptions) : CycleInstance g (k - 2) R := by
  intro r hr
  have hmem : r.1 ∈ (cycles g k).map selectedOptions := by
    rw [← hR]; exact List.mem_map.mpr ⟨r, hr, rfl⟩
  obtain ⟨c, hc, hopts⟩ := List.mem_map.mp hmem
  have hcyc := enumerated_isCycle hc
  have hk := hcyc.1
  have hlen := hcyc.2.1
  have hne : c ≠ [] := by intro h; subst h; simp at hlen; omega
  refine ⟨cycleEdges c, ?_, fun e he => hcyc.2.2.2 e he, ?_⟩
  · rw [cycleEdges_length hne, hlen]; omega
  · intro p hp
    rw [← hopts] at hp
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hp
    exact ⟨selected_nodup hcyc.2.2.1 i, by rw [selected_length, hlen],
      fun e he => selected_mem_cycleEdges he⟩

theorem rounding_options_nonempty {g : Graph} {k : Nat} {R : List (List (List Edge) × List Nat)}
    (hR : R.map Prod.fst = (cycles g k).map selectedOptions) : ∀ r ∈ R, r.1 ≠ [] := by
  intro r hr
  have hmem : r.1 ∈ (cycles g k).map selectedOptions := by
    rw [← hR]; exact List.mem_map.mpr ⟨r, hr, rfl⟩
  exact cycleOptions_nonempty g k r.1 hmem

theorem fractional_length {g : Graph} {k : Nat} {R : List (List (List Edge) × List Nat)}
    (hR : R.map Prod.fst = (cycles g k).map selectedOptions) : R.length = (cycles g k).length := by
  have := congrArg List.length hR
  simpa using this

theorem cycles_k_ge {g : Graph} {k : Nat} (h : cycles g k ≠ []) : 3 ≤ k := by
  cases hc : cycles g k with
  | nil => exact absurd hc h
  | cons c cs => exact (enumerated_isCycle (hc ▸ List.mem_cons_self)).1

/-- Theorem 18 on the graph `g`: a run `ps` of Algorithm 2 on an optimal fractional solution of
the relaxation for the `k`-cycles of `g` has cost at most `c(qs) + (k − 2) t / k` for every
assignment `qs`, with `t` the number of `k`-cycles; with `qs` optimal, `c(ps) ≤ OPT + (k − 2) t / k`. -/
theorem conditional_rounding_cost_bound {g : Graph} {k D : Nat} (hg : g.Nodup)
    {R : List (List (List Edge) × List Nat)}
    (hR : R.map Prod.fst = (cycles g k).map selectedOptions) (hopt : OptimalFractional g D R)
    {ps qs : List (List Edge)} (hrun : RoundingRun D [] R ps)
    (hq : ValidChoices ((cycles g k).map selectedOptions) qs) :
    k * cost ps ≤ k * cost qs + (k - 2) * (cycles g k).length := by
  by_cases hnil : cycles g k = []
  · have hRnil : R = [] := by
      rw [hnil] at hR
      simpa using hR
    subst hRnil
    cases ps with
    | nil => simp [cost]
    | cons _ _ => exact False.elim hrun
  · have hk := cycles_k_ge hnil
    have h := roundingRun_cost_bound hg (cycleInstance_of_cycles hR) hopt hrun (hR ▸ hq)
    rw [fractional_length hR] at h
    have hk' : k - 2 + 2 = k := by omega
    rw [hk'] at h
    exact h

/-- Theorem 17 on the graph `g`: independent randomized rounding of an optimal fractional
solution has expected cost at most `c(qs) + (k − 2) t / k` for every assignment `qs`
(`D^t E[c(τ)] = expectedCost R`). -/
theorem randomized_rounding_cost_bound {g : Graph} {k D : Nat} (hg : g.Nodup)
    {R : List (List (List Edge) × List Nat)}
    (hR : R.map Prod.fst = (cycles g k).map selectedOptions) (hopt : OptimalFractional g D R)
    {qs : List (List Edge)} (hq : ValidChoices ((cycles g k).map selectedOptions) qs) :
    k * expectedCost R ≤
      D ^ (cycles g k).length * (k * cost qs + (k - 2) * (cycles g k).length) := by
  by_cases hnil : cycles g k = []
  · have hRnil : R = [] := by
      rw [hnil] at hR
      simpa using hR
    subst hRnil
    simp [hnil, expectedCost, rounded_nil, cost]
  · have hk := cycles_k_ge hnil
    have h := expectedCost_bound hg (cycleInstance_of_cycles hR) hopt (hR ▸ hq)
    rw [fractional_length hR] at h
    have hk' : k - 2 + 2 = k := by omega
    rw [hk'] at h
    exact h

/-- Algorithm 2's output on the `k`-cycles of `g` is a run of Algorithm 2. -/
theorem conditionalRounding_cycles_run {g : Graph} {k D : Nat}
    {R : List (List (List Edge) × List Nat)}
    (hR : R.map Prod.fst = (cycles g k).map selectedOptions) :
    RoundingRun D [] R (conditionalRounding D R) :=
  conditionalRounding_run D R (rounding_options_nonempty hR)

/-- A run of Algorithm 2 on the `k`-cycles of `g` is a cycle-path assignment. -/
theorem RoundingRun.valid_cycles {g : Graph} {k D : Nat} {R : List (List (List Edge) × List Nat)}
    (hR : R.map Prod.fst = (cycles g k).map selectedOptions) {ps : List (List Edge)}
    (hrun : RoundingRun D [] R ps) : ValidChoices ((cycles g k).map selectedOptions) ps :=
  hR ▸ hrun.valid

/-- Algorithm 1 on the `k`-cycles of `g` is a run of Algorithm 1, and every run of Algorithm 1
is a cycle-path assignment. -/
theorem greedy_is_assignment (g : Graph) (k : Nat) :
    GreedyRun [] ((cycles g k).map selectedOptions) (greedy ((cycles g k).map selectedOptions)) ∧
      ∀ ps, GreedyRun [] ((cycles g k).map selectedOptions) ps →
        ValidChoices ((cycles g k).map selectedOptions) ps :=
  ⟨greedy_cycles_run g k, fun _ h => h.valid⟩

/-- Algorithm 2 on a fractional solution for the `k`-cycles of `g` is a run of Algorithm 2, and
every run of Algorithm 2 is a cycle-path assignment. -/
theorem rounding_is_assignment {g : Graph} {k : Nat} (D : Nat)
    {R : List (List (List Edge) × List Nat)}
    (hR : R.map Prod.fst = (cycles g k).map selectedOptions) :
    RoundingRun D [] R (conditionalRounding D R) ∧
      ∀ ps, RoundingRun D [] R ps → ValidChoices ((cycles g k).map selectedOptions) ps :=
  ⟨conditionalRounding_cycles_run hR, fun _ h => h.valid_cycles hR⟩

end STACS2027

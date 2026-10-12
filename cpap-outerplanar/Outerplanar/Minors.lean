module

public import Outerplanar.Polygon
import Mathlib.Tactic

/-!
# Minors and Lemma 24

* Walks and connectivity are monotone in the graph, so minors of a subgraph are minors of
  the graph (`HasMinor.mono`); a `K₄` has a `K₄` minor (`IsK4Graph.hasMinor`).
* **Lemma 24**: in a `K_{2,3}`-minor-free graph, two distinct vertices have at most two
  common neighbours — three common neighbours `a, b, c` of `u ≠ w` give the `K_{2,3}`
  subgraph with sides `{u, w}` and `{a, b, c}`, a minor with singleton branch sets
  (`common_neighbours_le_two`). For an edge list without loops this is Section 8's `CommonNeighbourBound`
  (`commonNeighbourBound_of_k23MinorFree`), the hypothesis of Lemma 25.
-/

@[expose] public section

namespace STACS2027

/-- Lemma 24's conclusion on the simple graph: two distinct vertices have at most two common
neighbours. -/
def CommonNeighbours2 (g : Graph) : Prop :=
  ∀ u w a b c, u ≠ w → Adj g u a → Adj g w a → Adj g u b → Adj g w b → Adj g u c → Adj g w c →
    a = b ∨ a = c ∨ b = c

theorem WalkWithin.mono {g h : Graph} {S T : ℕ → Prop} (hg : ∀ u v, Adj g u v → Adj h u v)
    (hS : ∀ v, S v → T v) : ∀ {w : List ℕ}, WalkWithin g S w → WalkWithin h T w
  | [], _ => trivial
  | [a], hw => hS a hw
  | a :: b :: _, ⟨ha, hab, hw⟩ => ⟨hS a ha, hg a b hab, WalkWithin.mono hg hS hw⟩

theorem ConnectedWithin.mono {g h : Graph} {S : ℕ → Prop} (hg : ∀ u v, Adj g u v → Adj h u v)
    (hc : ConnectedWithin g S) : ConnectedWithin h S := by
  intro u v hu hv
  obtain ⟨w, h1, h2, hw⟩ := hc u v hu hv
  exact ⟨w, h1, h2, hw.mono hg (fun _ h => h)⟩

/-- Minors of a subgraph are minors of the graph. -/
theorem HasMinor.mono {g h : Graph} (hg : ∀ u v, Adj g u v → Adj h u v) {size : ℕ} {H : Graph}
    (hm : HasMinor g size H) : HasMinor h size H := by
  obtain ⟨branch, h1, h2, h3, h4⟩ := hm
  refine ⟨branch, h1, h2, fun i hi => (h3 i hi).mono hg, ?_⟩
  intro e he
  obtain ⟨u, v, hu, hv, huv⟩ := h4 e he
  exact ⟨u, v, hu, hv, hg u v huv⟩

theorem connectedWithin_singleton (g : Graph) (x : ℕ) : ConnectedWithin g (fun v => v ∈ [x]) := by
  intro u v hu hv
  simp only [List.mem_singleton] at hu hv
  exact ⟨[x], by simp [hu], by simp [hv], by simp [WalkWithin]⟩

/-- A minor given by singleton branch sets: a subgraph. -/
theorem hasMinor_of_embedding {g : Graph} {size : ℕ} {H : Graph} (t : ℕ → ℕ)
    (hinj : ∀ i j, i < size → j < size → t i = t j → i = j)
    (hedges : ∀ e ∈ H, Adj g (t e.1) (t e.2)) : HasMinor g size H := by
  refine ⟨fun i => [t i], fun i _ => by simp, ?_, fun i _ => connectedWithin_singleton g (t i), ?_⟩
  · intro i j hi hj hij v hv hv'
    simp only [List.mem_singleton] at hv hv'
    exact hij (hinj i j hi hj (hv.symm.trans hv'))
  · intro e he
    exact ⟨t e.1, t e.2, by simp, by simp, hedges e he⟩

/-- **Lemma 24**: in a `K_{2,3}`-minor-free graph, any two distinct vertices have at most two
common neighbours. -/
theorem common_neighbours_le_two {g : Graph} (hg : K23MinorFree g) : CommonNeighbours2 g := by
  intro u w a b c huw hua hwa hub hwb huc hwc
  by_contra hne
  simp only [not_or] at hne
  obtain ⟨hab, hac, hbc⟩ := hne
  apply hg
  let t : ℕ → ℕ := fun i => if i = 0 then u else if i = 1 then w else if i = 2 then a
    else if i = 3 then b else c
  have hua' := hua.1
  have hwa' := hwa.1
  have hub' := hub.1
  have hwb' := hwb.1
  have huc' := huc.1
  have hwc' := hwc.1
  refine hasMinor_of_embedding t ?_ ?_
  · intro i j hi hj hij
    simp only [t] at hij
    interval_cases i <;> interval_cases j <;> simp_all
  · intro e he
    simp only [k23, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [t, hua, hub, huc, hwa, hwb, hwc]

/-- For an edge list without loops, Lemma 24 is Section 8's `CommonNeighbourBound`. -/
theorem commonNeighbourBound_of_k23MinorFree {g : Graph} (hg : K23MinorFree g)
    (hloop : ∀ e ∈ g, e.1 ≠ e.2) : CommonNeighbourBound g := by
  have hadj : ∀ x y, edge x y ∈ g → Adj g x y := by
    intro x y h
    refine ⟨?_, h⟩
    intro hxy; subst hxy
    have := hloop _ h
    simp [edge] at this
  intro u w a b c huw hua hwa hub hwb huc hwc
  exact common_neighbours_le_two hg u w a b c huw (hadj _ _ hua) (hadj _ _ hwa) (hadj _ _ hub) (hadj _ _ hwb)
    (hadj _ _ huc) (hadj _ _ hwc)

/-- A `K₄` has a `K₄` minor. -/
theorem IsK4Graph.hasMinor {g : Graph} (h : IsK4Graph g) : HasMinor g 4 k4 := by
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, hadj⟩ := h
  let t : ℕ → ℕ := fun i => if i = 0 then a else if i = 1 then b else if i = 2 then c else d
  refine hasMinor_of_embedding t ?_ ?_
  · intro i j hi hj hij
    simp only [t] at hij
    interval_cases i <;> interval_cases j <;> simp_all
  · intro e he
    simp only [k4, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [t, hadj] <;> omega

/-- An outerplanar graph is `K_{2,3}`-minor-free. -/
theorem Outerplanar.k23MinorFree {g : Graph} (h : Outerplanar g) : K23MinorFree g := h.2

end STACS2027

module

public import NPHardness.GlobalCost
public import NPHardness.VariableExpansionCost

/-! Relabelling reflects cycles and preserves the full assignment objective. -/

@[expose] public section
namespace STACS2027

theorem mapEdge_injective_on {g : Graph} {n : Nat} (hb : VerticesBelow g n)
    (hn : ∀ e ∈ g, edge e.1 e.2 = e) (t : Nat → Nat)
    (hi : ∀ a, a < n → ∀ b, b < n → t a = t b → a = b)
    {e d : Edge} (he : e ∈ g) (hd : d ∈ g) (heq : mapEdge t e = mapEdge t d) : e = d := by
  obtain ⟨he1,he2⟩ := hb e he
  obtain ⟨hd1,hd2⟩ := hb d hd
  rcases (edge_eq_iff ..).mp heq with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · exact Prod.ext (hi _ he1 _ hd1 h1) (hi _ he2 _ hd2 h2)
  · have h1' := hi _ he1 _ hd2 h1
    have h2' := hi _ he2 _ hd1 h2
    rw [← hn e he,← hn d hd,h1',h2',edge_comm]

theorem count_map_on {α β : Type} [DecidableEq α] [DecidableEq β]
    (t : α → β) {es : List α} {e : α}
    (hi : ∀ d ∈ es, t d = t e → d = e) : (es.map t).count (t e) = es.count e := by
  induction es with
  | nil => rfl
  | cons d es ih =>
    have ht := ih (fun q hq => hi q (by simp [hq]))
    have heq : t d = t e ↔ d = e :=
      ⟨fun h => hi d (by simp) h,fun h => congrArg t h⟩
    simp only [List.map_cons,List.count_cons,ht]
    simp [heq]

theorem overlap_map_on {g : List Edge} (t : Edge → Edge)
    (hi : ∀ e ∈ g, ∀ d ∈ g, t e = t d → e = d)
    {p q : List Edge} (hp : p ⊆ g) (hq : q ⊆ g) :
    overlap (p.map t) (q.map t) = overlap p q := by
  unfold overlap
  simp only [List.map_map]
  congr 1
  apply List.map_congr_left
  intro e he
  exact count_map_on t (fun d hd heq => hi d (hq hd) e (hp he) heq)

theorem cost_relabel {g : Graph} {n : Nat} (hb : VerticesBelow g n)
    (hn : ∀ e ∈ g, edge e.1 e.2 = e) (t : Nat → Nat)
    (hi : ∀ a, a < n → ∀ b, b < n → t a = t b → a = b)
    {ps : List (List Edge)} (hs : ∀ p ∈ ps, p ⊆ g) :
    cost (ps.map (List.map (mapEdge t))) = cost ps := by
  have heinj : ∀ e ∈ g, ∀ d ∈ g, mapEdge t e = mapEdge t d → e = d :=
    fun _ he _ hd heq => mapEdge_injective_on hb hn t hi he hd heq
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    have ht := ih (fun q hq => hs q (by simp [hq]))
    simp only [List.map_cons,cost,List.map_map,ht]
    congr 1
    congr 1
    apply List.map_congr_left
    intro q hq
    exact overlap_map_on (mapEdge t) heinj (hs p (by simp)) (hs q (by simp [hq]))

noncomputable def boundedInverse (t : Nat → Nat) (n x : Nat) : Nat :=
  if h : ∃ a, a < n ∧ t a = x then Classical.choose h else 0

theorem boundedInverse_left (t : Nat → Nat) {n : Nat}
    (hi : ∀ a, a < n → ∀ b, b < n → t a = t b → a = b) {u : Nat} (hu : u < n) :
    boundedInverse t n (t u) = u := by
  have h : ∃ a, a < n ∧ t a = t u := ⟨u,hu,rfl⟩
  rw [boundedInverse,dite_eq_left h]
  exact hi _ (Classical.choose_spec h).1 u hu (Classical.choose_spec h).2

theorem boundedInverse_right (t : Nat → Nat) {n x : Nat}
    (h : ∃ a, a < n ∧ x = t a) : t (boundedInverse t n x) = x := by
  have h' : ∃ a, a < n ∧ t a = x := by obtain ⟨a,ha,he⟩ := h; exact ⟨a,ha,he.symm⟩
  rw [boundedInverse,dite_eq_left h']
  exact (Classical.choose_spec h').2

theorem mapGraph_inverse {g : Graph} {n : Nat} (hb : VerticesBelow g n)
    (hn : ∀ e ∈ g, edge e.1 e.2 = e) (t inv : Nat → Nat)
    (hi : ∀ a, a < n → inv (t a) = a) : mapGraph inv (mapGraph t g) = g := by
  unfold mapGraph
  rw [List.map_map]
  apply Eq.trans (b := g.map id) ?_ (List.map_id g)
  apply List.map_congr_left
  intro e he
  change mapEdge inv (edge (t e.1) (t e.2)) = e
  rw [mapEdge_edge,hi _ (hb e he).1,hi _ (hb e he).2,hn e he]

theorem IsCycle.unmap {g : Graph} {n r : Nat} (hb : VerticesBelow g n)
    (hn : ∀ e ∈ g, edge e.1 e.2 = e) (t : Nat → Nat)
    (hi : ∀ a, a < n → ∀ b, b < n → t a = t b → a = b)
    {c : Cycle} (hc : IsCycle (mapGraph t g) r c) :
    ∃ d, IsCycle g r d ∧ c = d.map t := by
  let inv := boundedInverse t n
  have hr : ∀ x ∈ c, t (inv x) = x := by
    intro x hx
    obtain ⟨y,_,he⟩ := hc.vertex_incident hx
    exact boundedInverse_right t (mapGraph_edge_endpoints hb t (hc.2.2.2 _ he)).1
  have hmap := hc.map inv (fun x hx y hy he => (hr x hx).symm.trans ((congrArg t he).trans (hr y hy)))
  rw [mapGraph_inverse hb hn t inv (fun _ hu => boundedInverse_left t hi hu)] at hmap
  refine ⟨c.map inv,hmap,?_⟩
  rw [List.map_map]
  exact (List.map_congr_left hr).trans (List.map_id c) |>.symm

theorem selectedAt_map {g : Graph} {r : Nat} {c : Cycle} (_hc : IsCycle g r c)
    (t : Nat → Nat) (hi : ∀ a ∈ c, ∀ b ∈ c, t a = t b → a = b)
    {v : Nat} (hv : v ∈ c) :
    selectedAt (c.map t) (t v) = (selectedAt c v).map (mapEdge t) := by
  unfold selectedAt
  rw [cycleEdges_map,List.filter_map]
  congr 1
  apply List.filter_congr
  intro e he
  have hm := cycleEdges_endpoints he
  have ha : t e.1 ≠ t v ↔ e.1 ≠ v := ⟨fun h he => h (congrArg t he),fun h he => h (hi _ hm.1 v hv he)⟩
  have hb : t e.2 ≠ t v ↔ e.2 ≠ v := ⟨fun h he => h (congrArg t he),fun h he => h (hi _ hm.2 v hv he)⟩
  apply Bool.eq_iff_iff.mpr
  change avoidsVertex (t v) (edge (t e.1) (t e.2)) = true ↔ avoidsVertex v e = true
  rw [avoidsVertex_edge,ha,hb]
  simp only [avoidsVertex,Bool.and_eq_true,bne_iff_ne]

end STACS2027

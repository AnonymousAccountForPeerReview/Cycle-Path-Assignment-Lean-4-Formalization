module

public import Outerplanar.Algo.Solve
public import Outerplanar.Algo.LowPoint
public import Outerplanar.Transfer
import Mathlib.Tactic

/-!
# Correctness of the algorithm of Theorem 21

`solve_correct`: given Lemma 19, the correctness of the dynamic program on polygons
(`hpoly`: `Poly.polyOut` writes an optimal output of every polygon) and of the ear
elimination (`hear`: `Ear.earHam` finds an outerplanar Hamiltonian cycle of every graph on
`0, …, N - 1` that has one), the algorithm `solve k g` writes an optimal cycle-path
assignment of every `K_{2,3}`-minor-free graph `g`.

* **Vertices of a block** (`blockVerts`): no repetitions (`blockVerts_nodup`), the ends of
  the edges (`mem_blockVerts`), i.e. the vertices of the simple graph when the edges are
  written smaller end first (`isVertex_iff_mem_blockVerts`).
* **Local ids** (`localEdges vs E`, the ends renamed to their positions in `vs`): edges
  smaller end first below `vs.length` (`localEdges_lt`), without repetitions
  (`localEdges_nodup`), adjacency of the renamed vertices (`adj_localEdges`); renamed back
  by `vs`, an optimal output of the local graph is one of `E`
  (`optimalAssignmentOutput_ofLocal`).
* **Transport**: outerplanar Hamiltonian cycles transport along renamings injective on the
  vertices and preserving adjacency (`OuterplanarHam.relabel`), and depend only on the
  simple graph (`OuterplanarHam.of_adj_iff`); the positions on an outerplanar Hamiltonian
  cycle form a polygon (`isPolygon_localEdges`).
* **Blocks** (`optimalAssignmentOutput_solveBlock`): at most two vertices — no cycle,
  nothing to write (`optimalAssignmentOutput_small`); four vertices and six edges — a `K₄`
  (`optimalAssignmentOutput_k4Block`); otherwise, the block being 2-connected and
  `K_{2,3}`-minor-free, Lemma 19 gives an outerplanar Hamiltonian cycle (a `K₄` has four
  vertices and six edges, `IsK4Graph.counts`), so the ear elimination succeeds on the local
  graph and the dynamic program on its polygon (`optimalAssignmentOutput_outerBlock`).
* **The whole algorithm** (`solve_correct`): the blocks of the palm tree of the search of the
  id graph (`blocksOf_eq`), each 2-connected when it has three vertices
  (`idBlock_twoConnected`), combine (`optimalAssignmentOutput_blocks`); ids are replaced by
  labels (`optimalAssignmentOutput_labels`).
-/

@[expose] public section

namespace STACS2027.Algo

/-! ### Generalities (in `SolveAux`, opened below) -/

namespace SolveAux

theorem edge_of_lt {e : Edge} (h : e.1 < e.2) : edge e.1 e.2 = e := by
  simp [edge, Nat.min_eq_left h.le, Nat.max_eq_right h.le]

theorem adj_of_mem_lt {E : Graph} {e : Edge} (he : e ∈ E) (h : e.1 < e.2) : Adj E e.1 e.2 :=
  ⟨Nat.ne_of_lt h, by rw [edge_of_lt h]; exact he⟩

theorem edge_cases (a b : ℕ) : edge a b = (a, b) ∨ edge a b = (b, a) := by
  rcases le_total a b with h | h
  · left; simp [edge, Nat.min_eq_left h, Nat.max_eq_right h]
  · right; simp [edge, Nat.min_eq_right h, Nat.max_eq_left h]

/-- The vertices of a cycle are vertices of the graph. -/
theorem isVertex_of_mem_cycle {g : Graph} {k : ℕ} {c : Cycle} (hc : IsCycle g k c) {v : ℕ}
    (hv : v ∈ c) : IsVertex g v := by
  obtain ⟨w, hwv, hw⟩ := hc.vertex_incident hv
  exact ⟨w, hwv, by rw [edge_comm]; exact hc.2.2.2 _ hw⟩

theorem getD_eq_getElem' {vs : List ℕ} {i : ℕ} (hi : i < vs.length) : vs.getD i 0 = vs[i] := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

theorem getD_idxOf {vs : List ℕ} {a : ℕ} (ha : a ∈ vs) : vs.getD (vs.idxOf a) 0 = a := by
  rw [getD_eq_getElem' (List.idxOf_lt_length_of_mem ha), List.getElem_idxOf]

theorem idxOf_getD {vs : List ℕ} (hnd : vs.Nodup) {i : ℕ} (hi : i < vs.length) :
    vs.idxOf (vs.getD i 0) = i := by
  rw [getD_eq_getElem' hi, hnd.idxOf_getElem]

theorem getD_mem {vs : List ℕ} {i : ℕ} (hi : i < vs.length) : vs.getD i 0 ∈ vs := by
  rw [getD_eq_getElem' hi]
  exact List.getElem_mem hi

theorem getD_inj {vs : List ℕ} (hnd : vs.Nodup) :
    ∀ a, a < vs.length → ∀ b, b < vs.length → vs.getD a 0 = vs.getD b 0 → a = b := by
  intro a ha b hb h
  rw [← idxOf_getD hnd ha, ← idxOf_getD hnd hb, h]

end SolveAux

open SolveAux

/-! ### The vertices of a block -/

theorem mem_blockVerts {E : List Edge} {v : ℕ} :
    v ∈ blockVerts E ↔ ∃ e ∈ E, v = e.1 ∨ v = e.2 := by
  simp only [blockVerts, List.mem_eraseDups, List.mem_flatMap, List.mem_cons, List.not_mem_nil,
    or_false]

/-- The vertices of a block are listed without repetitions. -/
theorem blockVerts_nodup (E : List Edge) : (blockVerts E).Nodup := nodup_eraseDups _

theorem ends_mem_blockVerts {E : List Edge} : ∀ e ∈ E, e.1 ∈ blockVerts E ∧ e.2 ∈ blockVerts E :=
  fun e he => ⟨mem_blockVerts.mpr ⟨e, he, Or.inl rfl⟩, mem_blockVerts.mpr ⟨e, he, Or.inr rfl⟩⟩

/-- With edges written smaller end first, the vertices of a block are those of its simple
graph. -/
theorem isVertex_iff_mem_blockVerts {E : Graph} (hE : ∀ e ∈ E, e.1 < e.2) {v : ℕ} :
    IsVertex E v ↔ v ∈ blockVerts E := by
  rw [mem_blockVerts]
  constructor
  · rintro ⟨u, -, he⟩
    exact ⟨_, he, by simp only [edge]; omega⟩
  · rintro ⟨e, he, rfl | rfl⟩
    · exact ⟨e.2, (adj_of_mem_lt he (hE e he)).symm⟩
    · exact ⟨e.1, adj_of_mem_lt he (hE e he)⟩

/-! ### Local ids -/

section Local

variable {vs : List ℕ} {E : Graph}

theorem mem_localEdges {f : Edge} :
    f ∈ localEdges vs E ↔ ∃ e ∈ E, edge (vs.idxOf e.1) (vs.idxOf e.2) = f := by
  simp only [localEdges, List.mem_map]

theorem localEdges_normalized : ∀ f ∈ localEdges vs E, edge f.1 f.2 = f := by
  intro f hf
  obtain ⟨e, -, rfl⟩ := mem_localEdges.mp hf
  exact Comb.edge_edge _ _

theorem localEdges_below (hvs : ∀ e ∈ E, e.1 ∈ vs ∧ e.2 ∈ vs) :
    VerticesBelow (localEdges vs E) vs.length := by
  intro f hf
  obtain ⟨e, he, rfl⟩ := mem_localEdges.mp hf
  exact (edge_below _ _ _).mpr ⟨List.idxOf_lt_length_of_mem (hvs e he).1,
    List.idxOf_lt_length_of_mem (hvs e he).2⟩

/-- The local edges are written smaller end first, between local ids below `vs.length`. -/
theorem localEdges_lt (hE : ∀ e ∈ E, e.1 < e.2) (hvs : ∀ e ∈ E, e.1 ∈ vs ∧ e.2 ∈ vs) :
    ∀ f ∈ localEdges vs E, f.1 < f.2 ∧ f.2 < vs.length := by
  intro f hf
  obtain ⟨e, he, rfl⟩ := mem_localEdges.mp hf
  have h1 := List.idxOf_lt_length_of_mem (hvs e he).1
  have h2 := List.idxOf_lt_length_of_mem (hvs e he).2
  have hne : vs.idxOf e.1 ≠ vs.idxOf e.2 := fun h =>
    Nat.ne_of_lt (hE e he) ((List.idxOf_inj (hvs e he).1).mp h)
  simp only [edge]
  omega

/-- The local edges have no repetitions. -/
theorem localEdges_nodup (hE : ∀ e ∈ E, e.1 < e.2) (hvs : ∀ e ∈ E, e.1 ∈ vs ∧ e.2 ∈ vs)
    (hnd : E.Nodup) : (localEdges vs E).Nodup := by
  refine hnd.map_on fun x hx y hy hxy => ?_
  rcases (edge_eq_iff _ _ _ _).mp hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Prod.ext ((List.idxOf_inj (hvs x hx).1).mp h1) ((List.idxOf_inj (hvs x hx).2).mp h2)
  · have := (List.idxOf_inj (hvs x hx).1).mp h1
    have := (List.idxOf_inj (hvs x hx).2).mp h2
    have := hE x hx
    have := hE y hy
    omega

/-- Adjacency between local ids is adjacency between the vertices. -/
theorem adj_localEdges (hvs : ∀ e ∈ E, e.1 ∈ vs ∧ e.2 ∈ vs) (hn : ∀ e ∈ E, edge e.1 e.2 = e)
    {a b : ℕ} (ha : a ∈ vs) :
    Adj (localEdges vs E) (vs.idxOf a) (vs.idxOf b) ↔ Adj E a b := by
  constructor
  · rintro ⟨hne, he⟩
    obtain ⟨e, heE, heq⟩ := mem_localEdges.mp he
    refine ⟨fun h => hne (by rw [h]), ?_⟩
    obtain ⟨h1, h2⟩ := hvs e heE
    rcases (edge_eq_iff _ _ _ _).mp heq with ⟨x, y⟩ | ⟨x, y⟩
    · rw [← (List.idxOf_inj h1).mp x, ← (List.idxOf_inj h2).mp y, hn e heE]
      exact heE
    · rw [← (List.idxOf_inj h2).mp y, ← (List.idxOf_inj h1).mp x, edge_comm, hn e heE]
      exact heE
  · rintro ⟨hab, he⟩
    refine ⟨fun h => hab ((List.idxOf_inj ha).mp h), mem_localEdges.mpr ⟨_, he, ?_⟩⟩
    rcases edge_cases a b with h | h <;> simp only [h, edge_comm]

/-- The ends of a local edge are local ids of vertices. -/
theorem adj_localEdges_cases (hvs : ∀ e ∈ E, e.1 ∈ vs ∧ e.2 ∈ vs) {x y : ℕ}
    (h : Adj (localEdges vs E) x y) : ∃ a ∈ vs, ∃ b ∈ vs, x = vs.idxOf a ∧ y = vs.idxOf b := by
  obtain ⟨e, he, heq⟩ := mem_localEdges.mp h.2
  obtain ⟨h1, h2⟩ := hvs e he
  rcases (edge_eq_iff _ _ _ _).mp heq with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · exact ⟨_, h1, _, h2, hx.symm, hy.symm⟩
  · exact ⟨_, h2, _, h1, hy.symm, hx.symm⟩

/-- Renaming the local ids back by `vs` gives back `E`. -/
theorem mapGraph_localEdges (hvs : ∀ e ∈ E, e.1 ∈ vs ∧ e.2 ∈ vs)
    (hn : ∀ e ∈ E, edge e.1 e.2 = e) : mapGraph (fun p => vs.getD p 0) (localEdges vs E) = E := by
  unfold mapGraph localEdges
  rw [List.map_map]
  conv_rhs => rw [← List.map_id E]
  refine List.map_congr_left fun e he => ?_
  simp only [Function.comp_apply, mapEdge_edge, id]
  rw [getD_idxOf (hvs e he).1, getD_idxOf (hvs e he).2, hn e he]

/-- **Back from local ids**: an optimal output of the local graph, renamed by `vs`, is an
optimal output of `E`. -/
theorem optimalAssignmentOutput_ofLocal (hnd : vs.Nodup) (hvs : ∀ e ∈ E, e.1 ∈ vs ∧ e.2 ∈ vs)
    (hn : ∀ e ∈ E, edge e.1 e.2 = e) {k : ℕ} {out : List ℕ}
    (h : OptimalAssignmentOutput (localEdges vs E) k out) :
    OptimalAssignmentOutput E k (out.map fun p => vs.getD p 0) :=
  optimalAssignmentOutput_relabel (localEdges_below hvs) localEdges_normalized _ (getD_inj hnd)
    (fun _ _ _ => by rw [mapGraph_localEdges hvs hn]) h

end Local

/-! ### Transporting outerplanar Hamiltonian cycles -/

/-- **Transport**: an outerplanar Hamiltonian cycle of `g`, renamed by `t` injective on the
vertices of `g`, is one of every graph `g'` in which renamed vertices are adjacent exactly
when they are in `g`, and whose vertices are renamed vertices of `g`. -/
theorem OuterplanarHam.relabel {g g' : Graph} {ham : List ℕ} (h : OuterplanarHam g ham)
    (t : ℕ → ℕ) (ht : ∀ a b, IsVertex g a → IsVertex g b → t a = t b → a = b)
    (hadj : ∀ a b, IsVertex g a → IsVertex g b → (Adj g' (t a) (t b) ↔ Adj g a b))
    (hvert : ∀ v, IsVertex g' v → ∃ u, IsVertex g u ∧ t u = v) :
    OuterplanarHam g' (ham.map t) := by
  have hc := h.1
  have hV : ∀ v ∈ ham, IsVertex g v := fun v hv => isVertex_of_mem_cycle hc hv
  have hget : ∀ m, m < ham.length → (ham.map t).getD m 0 = t (ham.getD m 0) := by
    intro m hm
    rw [getD_eq_getElem' (by simpa using hm), getD_eq_getElem' hm, List.getElem_map]
  have hgetV : ∀ m, m < ham.length → IsVertex g (ham.getD m 0) := fun m hm => hV _ (getD_mem hm)
  refine ⟨⟨by simpa using hc.1, rfl, hc.2.2.1.map_on fun x hx y hy hxy =>
    ht x y (hV x hx) (hV y hy) hxy, ?_⟩, ?_, ?_⟩
  · intro f hf
    rw [cycleEdges_map] at hf
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hf
    have hn := pathEdges_normalized _ e he
    have hadjg : Adj g e.1 e.2 := ⟨hc.edge_endpoints_ne he, by rw [hn]; exact hc.2.2.2 e he⟩
    exact ((hadj _ _ ⟨_, hadjg.symm⟩ ⟨_, hadjg⟩).mpr hadjg).2
  · intro v hv
    obtain ⟨u, hu, rfl⟩ := hvert v hv
    exact List.mem_map_of_mem (h.2.1 u hu)
  · intro i j k l hij hjk hkl hl hcross
    rw [List.length_map] at hl
    rw [hget i (by omega), hget j (by omega), hget k (by omega), hget l hl] at hcross
    exact h.2.2 i j k l hij hjk hkl hl
      ⟨(hadj _ _ (hgetV i (by omega)) (hgetV k (by omega))).mp hcross.1,
        (hadj _ _ (hgetV j (by omega)) (hgetV l hl)).mp hcross.2⟩

/-- Outerplanar Hamiltonian cycles depend only on the simple graph. -/
theorem OuterplanarHam.of_adj_iff {g g' : Graph} {ham : List ℕ} (h : OuterplanarHam g ham)
    (hadj : ∀ a b, Adj g' a b ↔ Adj g a b) : OuterplanarHam g' ham := by
  simpa using OuterplanarHam.relabel h id (fun _ _ _ _ h => h) (fun a b _ _ => hadj a b)
    fun v ⟨u, hu⟩ => ⟨v, ⟨u, (hadj u v).mp hu⟩, rfl⟩

/-! ### Positions on an outerplanar Hamiltonian cycle -/

/-- A Hamiltonian cycle of a graph whose vertices are `0, …, N - 1` has length `N`. -/
theorem length_of_outerplanarHam {L : Graph} {N : ℕ} (hV : ∀ v, IsVertex L v ↔ v < N)
    {ham : List ℕ} (h : OuterplanarHam L ham) : ham.length = N := by
  apply le_antisymm
  · simpa using h.1.2.2.1.length_le_of_subset (l₂ := List.range N) fun v hv =>
      List.mem_range.mpr ((hV v).mp (isVertex_of_mem_cycle h.1 hv))
  · simpa using List.nodup_range.length_le_of_subset (l₂ := ham) fun v hv =>
      h.2.1 v ((hV v).mpr (List.mem_range.mp hv))

theorem ends_mem_ham {L : Graph} (hL : ∀ e ∈ L, e.1 < e.2) {ham : List ℕ}
    (h : OuterplanarHam L ham) : ∀ e ∈ L, e.1 ∈ ham ∧ e.2 ∈ ham := fun e he =>
  ⟨h.2.1 _ ⟨_, (adj_of_mem_lt he (hL e he)).symm⟩, h.2.1 _ ⟨_, adj_of_mem_lt he (hL e he)⟩⟩

/-- **The polygon**: the vertices of a graph renamed by their positions on an outerplanar
Hamiltonian cycle form a polygon. -/
theorem isPolygon_localEdges {L : Graph} (hL : ∀ e ∈ L, e.1 < e.2) {ham : List ℕ}
    (h : OuterplanarHam L ham) : IsPolygon (localEdges ham L) ham.length := by
  have hnd := h.1.2.2.1
  have hvs := ends_mem_ham hL h
  have hn : ∀ e ∈ L, edge e.1 e.2 = e := fun e he => edge_of_lt (hL e he)
  refine OuterplanarHam.of_adj_iff (isPolygon_posGraph h) fun i j => ?_
  rw [adj_posGraph]
  constructor
  · intro hij
    obtain ⟨a, ha, b, hb, rfl, rfl⟩ := adj_localEdges_cases hvs hij
    refine ⟨List.idxOf_lt_length_of_mem ha, List.idxOf_lt_length_of_mem hb, ?_⟩
    rw [getD_idxOf ha, getD_idxOf hb]
    exact (adj_localEdges hvs hn ha).mp hij
  · rintro ⟨hi, hj, hadj⟩
    rw [← idxOf_getD hnd hi, ← idxOf_getD hnd hj]
    exact (adj_localEdges hvs hn (getD_mem hi)).mpr hadj

/-! ### Small blocks -/

/-- A block with at most two vertices has no cycle: nothing to write. -/
theorem optimalAssignmentOutput_small {E : Graph} (hE : ∀ e ∈ E, e.1 < e.2)
    (h2 : (blockVerts E).length ≤ 2) (k : ℕ) : OptimalAssignmentOutput E k [] := by
  refine Comb.optimalAssignmentOutput_of_cost_zero (cs := []) (by simp) (by simp)
    (fun c hc => ?_) rfl
  exfalso
  have := hc.2.2.1.length_le_of_subset fun v hv =>
    (isVertex_iff_mem_blockVerts hE).mp (isVertex_of_mem_cycle hc hv)
  have := hc.1
  have := hc.2.1
  omega

/-! ### `K₄` blocks -/

/-- The six edges of the `K₄` on `a, b, c, d`. -/
def k4Edges (a b c d : ℕ) : Graph := [edge a b, edge a c, edge a d, edge b c, edge b d, edge c d]

theorem edge_mem_k4Edges {a b c d u v : ℕ} (huv : u ≠ v) (hu : u = a ∨ u = b ∨ u = c ∨ u = d)
    (hv : v = a ∨ v = b ∨ v = c ∨ v = d) : edge u v ∈ k4Edges a b c d := by
  rcases hu with rfl | rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl | rfl <;>
    simp_all [k4Edges, edge_eq_iff]

theorem k4Edges_nodup {a b c d : ℕ} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) : (k4Edges a b c d).Nodup := by
  simp [k4Edges, edge_eq_iff, hab, hac, had, hbc, hbd, hcd, hab.symm, hac.symm,
    hbc.symm, hbd.symm, hcd.symm]

theorem k4Edges_sub {B : Graph} (hB : ∀ e ∈ B, e.1 < e.2) {a b c d : ℕ}
    (hV : ∀ v, IsVertex B v → v = a ∨ v = b ∨ v = c ∨ v = d) : B ⊆ k4Edges a b c d := by
  intro e he
  have hadj := adj_of_mem_lt he (hB e he)
  rw [← edge_of_lt (hB e he)]
  exact edge_mem_k4Edges hadj.1 (hV _ ⟨_, hadj.symm⟩) (hV _ ⟨_, hadj⟩)

/-- A `K₄` (each edge once, smaller end first) has four vertices and six edges. -/
theorem IsK4Graph.counts {B : Graph} (hB : ∀ e ∈ B, e.1 < e.2) (hnd : B.Nodup)
    (h : IsK4Graph B) : (blockVerts B).length = 4 ∧ B.length = 6 := by
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, hadj⟩ := h
  have hV : ∀ v, v ∈ blockVerts B ↔ v ∈ [a, b, c, d] := by
    intro v
    rw [← isVertex_iff_mem_blockVerts hB]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro ⟨u, huv⟩
      exact ((hadj u v).mp huv).2.2
    · intro hv
      by_cases hva : v = a
      · exact ⟨b, (hadj b v).mpr ⟨by rw [hva]; exact hab.symm, Or.inr (Or.inl rfl), hv⟩⟩
      · exact ⟨a, (hadj a v).mpr ⟨Ne.symm hva, Or.inl rfl, hv⟩⟩
  have h4 : [a, b, c, d].Nodup := by simp [hab, hac, had, hbc, hbd, hcd]
  have hsup : k4Edges a b c d ⊆ B := by
    have key : ∀ u v, u ≠ v → (u = a ∨ u = b ∨ u = c ∨ u = d) →
        (v = a ∨ v = b ∨ v = c ∨ v = d) → edge u v ∈ B :=
      fun u v huv hu hv => ((hadj u v).mpr ⟨huv, hu, hv⟩).2
    intro f hf
    simp only [k4Edges, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact key _ _ (by assumption) (by simp) (by simp)
  refine ⟨le_antisymm ?_ ?_, le_antisymm ?_ ?_⟩
  · simpa using (blockVerts_nodup B).length_le_of_subset fun v hv => (hV v).mp hv
  · simpa using h4.length_le_of_subset fun v hv => (hV v).mpr hv
  · simpa [k4Edges] using hnd.length_le_of_subset (k4Edges_sub hB fun v hv => by
      obtain ⟨u, huv⟩ := hv
      exact ((hadj u v).mp huv).2.2)
  · simpa [k4Edges] using (k4Edges_nodup hab hac had hbc hbd hcd).length_le_of_subset hsup

/-- **`K₄` blocks**: a block with four vertices and six edges (each once, smaller end
first) is the `K₄` on its vertices, and `k4Out` writes an optimal output of it. -/
theorem optimalAssignmentOutput_k4Block {B : Graph} (hB : ∀ e ∈ B, e.1 < e.2) (hnd : B.Nodup)
    (h46 : (blockVerts B).length = 4 ∧ B.length = 6) (k : ℕ) :
    OptimalAssignmentOutput B k (k4Out k (blockVerts B)).flatten := by
  obtain ⟨a, b, c, d, hv⟩ := List.length_eq_four.mp h46.1
  have hvnd := blockVerts_nodup B
  have hV : ∀ v, IsVertex B v ↔ v = a ∨ v = b ∨ v = c ∨ v = d := by
    intro v
    rw [isVertex_iff_mem_blockVerts hB, hv]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
  rw [hv] at hvnd ⊢
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, not_false_eq_true, and_true] at hvnd
  obtain ⟨⟨hab, hac, had⟩, ⟨hbc, hbd⟩, hcd⟩ := hvnd
  have hperm := (List.subperm_of_subset hnd (k4Edges_sub hB fun v => (hV v).mp)).perm_of_length_le
    (by simp [k4Edges, h46.2])
  refine optimalAssignmentOutput_k4Out hab hac had hbc hbd hcd (fun u v => ⟨fun huv =>
    ⟨huv.1, (hV u).mp ⟨v, huv.symm⟩, (hV v).mp ⟨u, huv⟩⟩, fun ⟨huv, hu, hv'⟩ =>
    ⟨huv, hperm.symm.subset (edge_mem_k4Edges huv hu hv')⟩⟩) k

/-! ### Outerplanar blocks -/

/-- The vertices of the local graph of a block are the local ids. -/
theorem isVertex_localEdges {B : Graph} (hB : ∀ e ∈ B, e.1 < e.2) {v : ℕ} :
    IsVertex (localEdges (blockVerts B) B) v ↔ v < (blockVerts B).length := by
  constructor
  · rintro ⟨u, huv⟩
    have := localEdges_lt hB ends_mem_blockVerts _ huv.2
    simp only [edge] at this
    omega
  · intro hv
    have hm : (blockVerts B).getD v 0 ∈ blockVerts B := getD_mem hv
    obtain ⟨u, hu⟩ := (isVertex_iff_mem_blockVerts hB).mpr hm
    have hu' : u ∈ blockVerts B := (isVertex_iff_mem_blockVerts hB).mp ⟨_, hu.symm⟩
    refine ⟨(blockVerts B).idxOf u, ?_⟩
    have := (adj_localEdges ends_mem_blockVerts (fun e he => edge_of_lt (hB e he)) hu').mpr hu
    rwa [idxOf_getD (blockVerts_nodup B) hv] at this

/-- **Outerplanar blocks**: given an outerplanar Hamiltonian cycle `ham` of the local graph
of a block, the output of the dynamic program on the polygon of the positions on `ham`,
renamed back to local ids and then to ids, is an optimal output of the block. -/
theorem optimalAssignmentOutput_outerBlock {k : ℕ}
    (hpoly : ∀ {pg : Graph} {n : ℕ}, IsPolygon pg n →
      OptimalAssignmentOutput pg k (Poly.polyOut pg n k).flatten)
    {B : Graph} (hB : ∀ e ∈ B, e.1 < e.2) {ham : List ℕ}
    (hham : OuterplanarHam (localEdges (blockVerts B) B) ham) :
    OptimalAssignmentOutput B k
      ((Poly.polyOut (localEdges ham (localEdges (blockVerts B) B)) (blockVerts B).length k).map
        (List.map fun p => (blockVerts B).getD (ham.getD p 0) 0)).flatten := by
  have hL := localEdges_lt hB ends_mem_blockVerts
  have hLlt : ∀ e ∈ localEdges (blockVerts B) B, e.1 < e.2 := fun e he => (hL e he).1
  have hP := isPolygon_localEdges hLlt hham
  rw [length_of_outerplanarHam (fun _ => isVertex_localEdges hB) hham] at hP
  have h1 := optimalAssignmentOutput_ofLocal hham.1.2.2.1 (ends_mem_ham hLlt hham)
    localEdges_normalized (hpoly hP)
  have h2 := optimalAssignmentOutput_ofLocal (blockVerts_nodup B) ends_mem_blockVerts
    (fun e he => edge_of_lt (hB e he)) h1
  rw [List.map_map] at h2
  rw [← List.map_flatten]
  exact h2

/-! ### The block solver -/

/-- **The block solver is correct**: on a block (edges smaller end first, each once,
`K_{2,3}`-minor-free, 2-connected when it has three vertices), `solveBlock k` writes an
optimal output. -/
theorem optimalAssignmentOutput_solveBlock (hL : TwoConnectedK23Structure) {k : ℕ}
    (hpoly : ∀ {pg : Graph} {n : ℕ}, IsPolygon pg n →
      OptimalAssignmentOutput pg k (Poly.polyOut pg n k).flatten)
    (hear : ∀ {N : ℕ} {L : List Edge}, (∀ e ∈ L, e.1 < e.2 ∧ e.2 < N) → L.Nodup → 3 ≤ N →
      ∀ {ham0 : List ℕ}, OuterplanarHam L ham0 → (∀ v, v < N → v ∈ ham0) →
      OuterplanarHam L (Ear.earHam N L))
    {B : Graph} (hB : ∀ e ∈ B, e.1 < e.2) (hnd : B.Nodup) (hK : K23MinorFree B)
    (h2c : 3 ≤ (blockVerts B).length → TwoConnected B) :
    OptimalAssignmentOutput B k (solveBlock k B).flatten := by
  by_cases h2 : (blockVerts B).length ≤ 2
  · rw [show solveBlock k B = [] by simp [solveBlock, h2]]
    exact optimalAssignmentOutput_small hB h2 k
  by_cases h46 : (blockVerts B).length = 4 ∧ B.length = 6
  · rw [show solveBlock k B = k4Out k (blockVerts B) by simp [solveBlock, h46]]
    exact optimalAssignmentOutput_k4Block hB hnd h46 k
  have h3 : 3 ≤ (blockVerts B).length := by omega
  obtain ⟨ham, hham⟩ : ∃ ham, OuterplanarHam B ham := by
    rcases hL B (h2c h3) hK with hk4 | hh
    · exact absurd (IsK4Graph.counts hB hnd hk4) h46
    · exact hh
  have hvs : ∀ e ∈ B, e.1 ∈ blockVerts B ∧ e.2 ∈ blockVerts B := ends_mem_blockVerts
  have hn : ∀ e ∈ B, edge e.1 e.2 = e := fun e he => edge_of_lt (hB e he)
  have hmem : ∀ {v}, IsVertex B v → v ∈ blockVerts B := (isVertex_iff_mem_blockVerts hB).mp
  have hham0 : OuterplanarHam (localEdges (blockVerts B) B)
      (ham.map fun a => (blockVerts B).idxOf a) := by
    refine OuterplanarHam.relabel hham _ (fun a b ha _ hab => (List.idxOf_inj (hmem ha)).mp hab)
      (fun a b ha _ => adj_localEdges hvs hn (hmem ha)) fun v ⟨u, huv⟩ => ?_
    obtain ⟨-, -, b, hb, -, rfl⟩ := adj_localEdges_cases hvs huv
    exact ⟨b, (isVertex_iff_mem_blockVerts hB).mpr hb, rfl⟩
  have hall : ∀ v, v < (blockVerts B).length → v ∈ ham.map fun a => (blockVerts B).idxOf a :=
    fun v hv => List.mem_map.mpr ⟨_, hham.2.1 _ ((isVertex_iff_mem_blockVerts hB).mpr
      (getD_mem hv)), idxOf_getD (blockVerts_nodup B) hv⟩
  have hear' := hear (localEdges_lt hB hvs) (localEdges_nodup hB hvs hnd) h3 hham0 hall
  have hsol : solveBlock k B =
      (Poly.polyOut (localEdges (Ear.earHam (blockVerts B).length (localEdges (blockVerts B) B))
        (localEdges (blockVerts B) B)) (blockVerts B).length k).map
        (List.map fun p => (blockVerts B).getD
          ((Ear.earHam (blockVerts B).length (localEdges (blockVerts B) B)).getD p 0) 0) := by
    simp only [solveBlock, h2, h46, ↓reduceIte]
  rw [hsol]
  exact optimalAssignmentOutput_outerBlock hpoly hB hear'

/-! ### The whole algorithm -/

section Blocks

variable {g : Graph} (P : Palm (idEdges g))

/-- The edges of a block of the id graph are written smaller end first. -/
theorem idBlock_lt (h : ℕ) : ∀ e ∈ P.block h, e.1 < e.2 :=
  fun _ he => (P.mem_block_iff.mp he).2.1

/-- A block of the id graph has no repeated edge. -/
theorem idBlock_nodup (h : ℕ) : (P.block h).Nodup :=
  (idEdges_nodup g).filter _

/-- A block of the id graph with three vertices is 2-connected. -/
theorem idBlock_twoConnected {h : ℕ} (h3 : 3 ≤ (blockVerts (P.block h)).length) :
    TwoConnected (P.block h) := by
  set vs := blockVerts (P.block h) with hvs
  have hnd : vs.Nodup := blockVerts_nodup _
  have hmem : ∀ i (hi : i < vs.length), IsVertex (P.block h) (vs[i]'hi) :=
    fun i hi => (isVertex_iff_mem_blockVerts (idBlock_lt P h)).mpr (List.getElem_mem hi)
  obtain ⟨u, hu⟩ := hmem 0 (by omega)
  obtain ⟨hadj, hhd⟩ := P.adj_block.mp hu
  obtain ⟨hxv, hxr, -⟩ := P.lower_facts hadj
  have hh : P.IsHead h := by
    rw [← hhd]
    exact (P.head_spec hxv hxr).1
  refine P.twoConnected_block hh ?_
  have hin : ∀ i (hi : i < vs.length), P.InBlock h (vs[i]'hi) :=
    fun i hi => (P.isVertex_block hh).mp (hmem i hi)
  have hne : ∀ i j (hi : i < vs.length) (hj : j < vs.length), i ≠ j → vs[i]'hi ≠ vs[j]'hj :=
    fun i j hi hj hij heq => hij (hnd.getElem_inj_iff.mp heq)
  have h01 := hne 0 1 (by omega) (by omega) (by omega)
  have h02 := hne 0 2 (by omega) (by omega) (by omega)
  have h12 := hne 1 2 (by omega) (by omega) (by omega)
  by_cases a0 : vs[0]'(by omega) ≠ h ∧ vs[0]'(by omega) ≠ P.par h
  · exact ⟨_, hin 0 (by omega), a0⟩
  by_cases a1 : vs[1]'(by omega) ≠ h ∧ vs[1]'(by omega) ≠ P.par h
  · exact ⟨_, hin 1 (by omega), a1⟩
  refine ⟨_, hin 2 (by omega), ?_⟩
  simp only [ne_eq, not_and_or, not_not] at a0 a1
  omega

end Blocks

/-- **Correctness of the algorithm of Theorem 21**: given Lemma 19, the correctness of the
dynamic program on polygons and that of the ear elimination, `solve k g` writes an optimal
cycle-path assignment of every `K_{2,3}`-minor-free graph `g`. -/
theorem solve_correct (hL : TwoConnectedK23Structure) {k : ℕ} (hk : 3 ≤ k) {g : Graph} (hg : K23MinorFree g)
    (hpoly : ∀ {pg : Graph} {n : ℕ}, IsPolygon pg n →
      OptimalAssignmentOutput pg k (Poly.polyOut pg n k).flatten)
    (hear : ∀ {N : ℕ} {L : List Edge}, (∀ e ∈ L, e.1 < e.2 ∧ e.2 < N) → L.Nodup → 3 ≤ N →
      ∀ {ham0 : List ℕ}, OuterplanarHam L ham0 → (∀ v, v < N → v ∈ ham0) →
      OuterplanarHam L (Ear.earHam N L)) :
    OptimalAssignmentOutput g k (solve k g) := by
  have _ := hk  -- not needed: every step holds for all `k`
  obtain ⟨P, -, -, hbl⟩ := blocksOf_eq g
  have hK := k23MinorFree_idEdges hg
  rw [solve, solveWith_eq_map, hbl, List.flatMap_map,
    ← Comb.flatMap_flatten_eq _ (fun h => (solveBlock k (P.block h)).flatten) _ fun _ _ => rfl]
  refine optimalAssignmentOutput_labels (optimalAssignmentOutput_blocks P List.nodup_range
    (fun _ hh => mem_range_of_isVertex hh.1) fun h _ => ?_)
  exact optimalAssignmentOutput_solveBlock hL hpoly hear (idBlock_lt P h) (idBlock_nodup P h)
    (P.block_k23MinorFree hK h) (idBlock_twoConnected P)

end STACS2027.Algo

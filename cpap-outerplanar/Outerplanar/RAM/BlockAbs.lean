module

public import Outerplanar.RAM.Iface
import Outerplanar.Algo.PolyOut
import Outerplanar.Algo.PolyPool
import Mathlib.Tactic

/-!
# The block solver, abstract side

Facts about the specification `solveBlock k E` used by the block solver of the machine
(`Outerplanar/RAM/Block.lean`):

* **Vertices.** The vertices `blockVerts (E.take j)` of the first `j` edges grow by `R0.ext`
  (append if new) at both ends of the next edge (`blockVerts_take_succ`); there are at most
  `2 j` of them (`length_blockVerts_take_le`), all ids below `numV g`.
* **The three cases** of `solveBlock` and their outputs as label lists (`out_small`,
  `out_k4`, `out_poly`).
* **The polygon case.** When the positions on `ham` of a local graph `L` (edges smaller end
  first, ends below `N`) form a polygon on `N` positions, `ham` (of length `N`) is a
  permutation of `0, …, N - 1` (`HamFacts`): every entry is below `N`, `ham.idxOf ham[p] = p`,
  no repetitions, every `x < N` occurs. Hence the polygon is written smaller end first and has
  no repetitions (`pg_lt`, `pg_nodup`), and the outputs of the polygon solver are positions
  below `N` (`polyOut_lt`), so the output map `p ↦ label (vs[ham[p]])` stored for `p < N`
  gives the right labels (`out_poly_omap`).
-/

@[expose] public section

namespace STACS2027.RAM.Block

open STACS2027.Algo

/-! ### Lists -/

theorem map_take_succ {α β : Type} (f : α → β) (l : List α) {j : ℕ} (hj : j < l.length) :
    (l.take (j + 1)).map f = (l.take j).map f ++ [f l[j]] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, List.map_append,
    List.map_singleton]

theorem take_succ_eq {α : Type} (l : List α) {j : ℕ} (hj : j < l.length) :
    l.take (j + 1) = l.take j ++ [l[j]] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some]

/-! ### The vertices of a block, edge by edge -/

/-- The vertices after one more edge. -/
theorem blockVerts_take_succ (E : List Edge) {j : ℕ} (hj : j < E.length) :
    blockVerts (E.take (j + 1)) = R0.ext (R0.ext (blockVerts (E.take j)) E[j].1) E[j].2 := by
  unfold blockVerts
  rw [take_succ_eq E hj, List.flatMap_append, List.flatMap_singleton,
    show ∀ l : List ℕ, ∀ a b : ℕ, l ++ [a, b] = (l ++ [a]) ++ [b] by simp,
    R0.eraseDups_append_singleton, R0.eraseDups_append_singleton]

theorem length_blockVerts_take_le (E : List Edge) (j : ℕ) :
    (blockVerts (E.take j)).length ≤ 2 * j := by
  have h1 := R0.length_eraseDups_le ((E.take j).flatMap fun e => [e.1, e.2])
  have h2 := length_flatMap_pair (E.take j)
  have h3 : (E.take j).length ≤ j := List.length_take_le _ _
  unfold blockVerts; omega

/-- A block has at most `2 |E|` vertices. -/
theorem length_blockVerts_le (E : List Edge) : (blockVerts E).length ≤ 2 * E.length := by
  simpa using length_blockVerts_take_le E E.length

theorem mem_blockVerts_of_take {E : List Edge} {j v : ℕ} (hv : v ∈ blockVerts (E.take j)) :
    v ∈ blockVerts E := by
  obtain ⟨e, he, hv⟩ := mem_blockVerts.mp hv
  exact mem_blockVerts.mpr ⟨e, List.mem_of_mem_take he, hv⟩

/-- The vertices are ids below `n` when the edges are. -/
theorem lt_of_mem_blockVerts {E : List Edge} {n : ℕ} (hE : ∀ e ∈ E, e.1 < e.2 ∧ e.2 < n) {v : ℕ}
    (hv : v ∈ blockVerts E) : v < n := by
  obtain ⟨e, he, rfl | rfl⟩ := mem_blockVerts.mp hv
  · have := hE e he; omega
  · exact (hE e he).2

theorem dictOf_of_mem {L : List ℕ} {a : ℕ} (ha : a ∈ L) : R0.dictOf L a = L.idxOf a + 1 := by
  simp [R0.dictOf, ha]

/-! ### The local graph -/

/-- The local graph is written smaller end first, with ends below `N`. -/
theorem localEdges_bounds {E : List Edge} (hE : ∀ e ∈ E, e.1 < e.2) :
    ∀ f ∈ localEdges (blockVerts E) E, f.1 < f.2 ∧ f.2 < (blockVerts E).length :=
  localEdges_lt hE ends_mem_blockVerts

theorem localEdges_nodup' {E : List Edge} (hE : ∀ e ∈ E, e.1 < e.2) (hnd : E.Nodup) :
    (localEdges (blockVerts E) E).Nodup :=
  localEdges_nodup hE ends_mem_blockVerts hnd

theorem length_localEdges (vs : List ℕ) (E : List Edge) : (localEdges vs E).length = E.length := by
  simp [localEdges]

theorem getElem_localEdges (vs : List ℕ) (E : List Edge) {j : ℕ} (hj : j < (localEdges vs E).length) :
    (localEdges vs E)[j] = edge (vs.idxOf (E[j]'(by simpa [length_localEdges] using hj)).1)
      (vs.idxOf (E[j]'(by simpa [length_localEdges] using hj)).2) := by
  simp [localEdges]

/-! ### The three cases of `solveBlock` -/

/-- At most two vertices: nothing. -/
theorem out_small {k : ℕ} {E : List Edge} (h : (blockVerts E).length ≤ 2) (f : ℕ → ℕ) :
    (solveBlock k E).flatten.map f = [] := by
  simp [solveBlock, h]

/-- A `K₄`: the fixed patterns. -/
theorem out_k4 {k : ℕ} {E : List Edge} (h4 : (blockVerts E).length = 4) (h6 : E.length = 6)
    (f : ℕ → ℕ) :
    (solveBlock k E).flatten.map f = (k4Base k).flatten.map fun i => f ((blockVerts E).getD i 0) := by
  simp [solveBlock, h4, h6, k4Out, List.map_flatten, List.map_map, Function.comp_def]

/-- The polygon case. -/
theorem out_poly {k : ℕ} {E : List Edge} (h2 : ¬ (blockVerts E).length ≤ 2)
    (h46 : ¬ ((blockVerts E).length = 4 ∧ E.length = 6)) (f : ℕ → ℕ) :
    (solveBlock k E).flatten.map f =
      (Poly.polyOut (localEdges (Ear.earHam (blockVerts E).length (localEdges (blockVerts E) E))
          (localEdges (blockVerts E) E)) (blockVerts E).length k).flatten.map fun p =>
        f ((blockVerts E).getD
          ((Ear.earHam (blockVerts E).length (localEdges (blockVerts E) E)).getD p 0) 0) := by
  simp only [solveBlock, h2, h46, ↓reduceIte, List.map_flatten, List.map_map,
    Function.comp_def]

/-- The `K₄` patterns index four vertices. -/
theorem k4Base_lt (k : ℕ) : ∀ i ∈ (k4Base k).flatten, i < 4 := by
  unfold k4Base
  split_ifs <;> decide

/-! ### The Hamiltonian cycle in the polygon case -/

theorem length_walk (succ : ℕ → ℕ) : ∀ m x, (Ear.walk succ m x).length = m
  | 0, _ => rfl
  | m + 1, x => by simp [Ear.walk, length_walk succ m]

/-- The ear elimination returns `N` vertices. -/
theorem length_earHam (N : ℕ) (L : List Edge) : (Ear.earHam N L).length = N :=
  length_walk _ _ _

section Ham

variable {N : ℕ} {L : List Edge} {ham : List ℕ}

/-- Every position of the polygon is the position of an end of an edge. -/
theorem ham_pos (hlen : ham.length = N) (hL : ∀ f ∈ L, f.1 < f.2 ∧ f.2 < N)
    (hP : IsPolygon (localEdges ham L) N) {p : ℕ} (hp : p < N) :
    ∃ x, x < N ∧ x ∈ ham ∧ ham.idxOf x = p := by
  have hv : IsVertex (localEdges ham L) p :=
    SolveAux.isVertex_of_mem_cycle hP.1 (List.mem_range.mpr hp)
  obtain ⟨u, -, he⟩ := hv
  obtain ⟨e, heL, heq⟩ := mem_localEdges.mp he
  have hb := hL e heL
  rcases (edge_eq_iff _ _ _ _).mp heq with ⟨-, h2⟩ | ⟨h1, -⟩
  · exact ⟨e.2, hb.2, List.idxOf_lt_length_iff.mp (by rw [h2, hlen]; exact hp), h2⟩
  · exact ⟨e.1, by omega, List.idxOf_lt_length_iff.mp (by rw [h1, hlen]; exact hp), h1⟩

/-- The facts about `ham` in the polygon case: a permutation of `0, …, N - 1`. -/
structure HamFacts (N : ℕ) (ham : List ℕ) : Prop where
  len : ham.length = N
  lt : ∀ p (hp : p < ham.length), ham[p] < N
  idx : ∀ p (hp : p < ham.length), ham.idxOf ham[p] = p
  nodup : ham.Nodup
  mem : ∀ x, x < N → x ∈ ham

theorem hamFacts (hlen : ham.length = N) (hL : ∀ f ∈ L, f.1 < f.2 ∧ f.2 < N)
    (hP : IsPolygon (localEdges ham L) N) : HamFacts N ham := by
  have key : ∀ p (hp : p < ham.length), ham[p] < N ∧ ham.idxOf ham[p] = p := by
    intro p hp
    obtain ⟨x, hx, hxm, rfl⟩ := ham_pos hlen hL hP (hlen ▸ hp)
    rw [List.getElem_idxOf]
    exact ⟨hx, rfl⟩
  have hnd : ham.Nodup := by
    rw [List.nodup_iff_injective_get]
    intro ⟨i, hi⟩ ⟨j, hj⟩ h
    simp only [List.get_eq_getElem] at h
    have h1 := (key i hi).2
    have h2 := (key j hj).2
    rw [h] at h1
    exact Fin.ext (h1.symm.trans h2)
  have hsub : ham ⊆ List.range N := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem hx
    exact List.mem_range.mpr (key p hp).1
  have hperm := (List.subperm_of_subset hnd hsub).perm_of_length_le (by simp [hlen])
  exact ⟨hlen, fun p hp => (key p hp).1, fun p hp => (key p hp).2, hnd,
    fun x hx => hperm.symm.subset (List.mem_range.mpr hx)⟩

theorem HamFacts.ends (hH : HamFacts N ham) (hL : ∀ f ∈ L, f.1 < f.2 ∧ f.2 < N) :
    ∀ e ∈ L, e.1 ∈ ham ∧ e.2 ∈ ham := fun e he =>
  ⟨hH.mem _ (by have := hL e he; omega), hH.mem _ (hL e he).2⟩

/-- The polygon is written smaller end first. -/
theorem pg_lt (hH : HamFacts N ham) (hL : ∀ f ∈ L, f.1 < f.2 ∧ f.2 < N) :
    ∀ e ∈ localEdges ham L, e.1 < e.2 := fun e he =>
  (localEdges_lt (fun f hf => (hL f hf).1) (hH.ends hL) e he).1

/-- The polygon has no repetitions. -/
theorem pg_nodup (hH : HamFacts N ham) (hL : ∀ f ∈ L, f.1 < f.2 ∧ f.2 < N) (hnd : L.Nodup) :
    (localEdges ham L).Nodup :=
  localEdges_nodup (fun f hf => (hL f hf).1) (hH.ends hL) hnd

/-- The position of a vertex `u < N` on `ham`. -/
theorem HamFacts.idxOf_lt (hH : HamFacts N ham) {u : ℕ} (hu : u < N) : ham.idxOf u < N := by
  have := List.idxOf_lt_length_iff.mpr (hH.mem u hu)
  rwa [hH.len] at this

/-- **The polygon case gives the hypothesis of the ear elimination** (`EarSpec`): `ham` is an
outerplanar Hamiltonian cycle of `L` (rename the polygon back by `p ↦ ham[p]`). -/
theorem HamFacts.outerplanarHam (hH : HamFacts N ham) (hL : ∀ f ∈ L, f.1 < f.2 ∧ f.2 < N)
    (hP : IsPolygon (localEdges ham L) N) : OuterplanarHam L ham := by
  have hvs := hH.ends hL
  have hn : ∀ e ∈ L, edge e.1 e.2 = e := fun e he => SolveAux.edge_of_lt (hL e he).1
  have hvN : ∀ a, IsVertex (localEdges ham L) a → a < ham.length := fun a ha => by
    rw [hH.len]; exact List.mem_range.mp (hP.2.1 a ha)
  have hmap : (List.range N).map (fun p => ham.getD p 0) = ham := by
    refine List.ext_getElem (by simp [hH.len]) fun i h1 h2 => ?_
    simp only [List.getElem_map, List.getElem_range]
    exact SolveAux.getD_eq_getElem' h2
  have hmemL : ∀ w v, Adj L w v → v ∈ ham := fun w v h => by
    have := (hL _ h.2).2
    simp only [edge] at this
    exact hH.mem v (by omega)
  have := OuterplanarHam.relabel hP (fun p => ham.getD p 0)
    (fun a b ha hb h => SolveAux.getD_inj hH.nodup a (hvN a ha) b (hvN b hb) h)
    (fun a b ha hb => by
      have hxa : ham.getD a 0 ∈ ham := SolveAux.getD_mem (hvN a ha)
      have h := adj_localEdges (b := ham.getD b 0) hvs hn hxa
      rw [SolveAux.idxOf_getD hH.nodup (hvN a ha), SolveAux.idxOf_getD hH.nodup (hvN b hb)] at h
      exact h.symm)
    (fun v ⟨w, hwv⟩ => ⟨ham.idxOf v, ⟨ham.idxOf w,
      (adj_localEdges hvs hn (hmemL v w hwv.symm)).mpr hwv⟩, SolveAux.getD_idxOf (hmemL w v hwv)⟩)
  rwa [hmap] at this

end Ham

/-! ### The output of the polygon solver -/

/-- The outputs of the polygon solver are positions. -/
theorem polyOut_lt {pg : Graph} {n k : ℕ} (hP : IsPolygon pg n) (hk : 3 ≤ k) :
    ∀ p ∈ (Poly.polyOut pg n k).flatten, p < n := by
  obtain ⟨cs, hout, hcyc, -⟩ := Poly.optimalAssignmentOutput_polyOut hP hk (Poly.polyFacts hP hk)
  intro p hp
  rw [hout, List.mem_flatten] at hp
  obtain ⟨c, hc, hpc⟩ := hp
  exact List.mem_range.mp (hP.2.1 p (SolveAux.isVertex_of_mem_cycle (hcyc c hc) hpc))

/-- An output map stored for the positions `p < n` maps the outputs as the function. -/
theorem map_omap {l : List ℕ} {n : ℕ} (hl : ∀ p ∈ l, p < n) (f : ℕ → ℕ) :
    l.map (fun p => ((List.range n).map f).getD p 0) = l.map f := by
  refine List.map_congr_left fun p hp => ?_
  have := hl p hp
  simp [List.getD_eq_getElem?_getD, this]

/-- The output map of the polygon case. -/
def omapOf (g : Graph) (E : List Edge) : List ℕ :=
  (List.range (blockVerts E).length).map fun p =>
    labelOf g ((blockVerts E).getD ((Ear.earHam (blockVerts E).length
      (localEdges (blockVerts E) E)).getD p 0) 0)

/-- **The polygon case through the output map.** -/
theorem out_poly_omap {k : ℕ} (hk : 3 ≤ k) {g : Graph} {E : List Edge}
    (h2 : ¬ (blockVerts E).length ≤ 2) (h46 : ¬ ((blockVerts E).length = 4 ∧ E.length = 6))
    (hP : IsPolygon (localEdges (Ear.earHam (blockVerts E).length (localEdges (blockVerts E) E))
      (localEdges (blockVerts E) E)) (blockVerts E).length) :
    (solveBlock k E).flatten.map (labelOf g) =
      (Poly.polyOut (localEdges (Ear.earHam (blockVerts E).length (localEdges (blockVerts E) E))
          (localEdges (blockVerts E) E)) (blockVerts E).length k).flatten.map
        fun p => (omapOf g E).getD p 0 := by
  rw [out_poly h2 h46, omapOf, map_omap (polyOut_lt hP hk)]

end STACS2027.RAM.Block

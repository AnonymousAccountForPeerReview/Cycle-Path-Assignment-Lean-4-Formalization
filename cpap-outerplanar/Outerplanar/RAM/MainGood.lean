module

public import Outerplanar.RAM.Iface
public import Outerplanar.Algo.EarCorrect
import Mathlib.Tactic

/-!
# The blocks satisfy the hypotheses of the block solver

The block solver's specification `BlockSpec` (`Outerplanar/RAM/Iface.lean`) applies to a block
`E` whose edges are written smaller end first between ids below `numV g`, without
repetitions, and which satisfies `BlockGood E` (the polygon branch receives a polygon). This
file proves these hypotheses for every block `E ∈ blocksOf g`:

* `blocksOf_ends`, `blocksOf_nodup`: the blocks are sublists of the id edges `idEdges g`
  (`idEdges_lt`, `idEdges_nodup`);
* `blockGood_of`: a block that is 2-connected when it has three vertices, `K_{2,3}`-minor-free,
  written smaller end first, without repetitions, is `BlockGood`, given Lemma 19: when it has
  at least three vertices and is not a `K₄` (four vertices and six edges, `IsK4Graph.counts`),
  Lemma 19 gives an outerplanar Hamiltonian cycle, which transported to the local ids
  (`OuterplanarHam.relabel`) makes the ear elimination succeed (`Ear.earHam_correct`); the
  positions on its cycle form a polygon (`isPolygon_localEdges`) on `|blockVerts E|` positions
  (`length_of_outerplanarHam`). This is the polygon branch of
  `optimalAssignmentOutput_solveBlock` (`Outerplanar/Algo/SolveCorrect.lean`);
* `blockGood_blocksOf`: hence, for a `K_{2,3}`-minor-free graph, every block of
  `blocksOf g` is `BlockGood` (the blocks are those of a palm tree of the id graph,
  `Algo.blocksOf_eq`: `idBlock_lt`, `idBlock_nodup`, `idBlock_twoConnected`,
  `Palm.block_k23MinorFree`).
-/

@[expose] public section

namespace STACS2027.RAM.Main

open STACS2027.Algo STACS2027.Algo.SolveAux

/-! ### Ends and repetitions -/

/-- The edges of a block are id edges. -/
theorem mem_idEdges_of_blocksOf {g : Graph} {E : List Edge} (hE : E ∈ blocksOf g) :
    ∀ e ∈ E, e ∈ idEdges g := by
  simp only [blocksOf, List.mem_map] at hE
  obtain ⟨h, -, rfl⟩ := hE
  exact fun e he => (List.mem_filter.mp he).1

/-- The edges of a block are written smaller end first, between ids below `numV g`. -/
theorem blocksOf_ends {g : Graph} {E : List Edge} (hE : E ∈ blocksOf g) :
    ∀ e ∈ E, e.1 < e.2 ∧ e.2 < numV g :=
  fun e he => idEdges_lt (mem_idEdges_of_blocksOf hE e he)

/-- A block has no repeated edge. -/
theorem blocksOf_nodup {g : Graph} {E : List Edge} (hE : E ∈ blocksOf g) : E.Nodup := by
  simp only [blocksOf, List.mem_map] at hE
  obtain ⟨h, -, rfl⟩ := hE
  exact (idEdges_nodup g).filter _

/-! ### The polygon branch receives a polygon -/

/-- **`BlockGood` from Lemma 19**: a block (edges smaller end first, each once,
`K_{2,3}`-minor-free, 2-connected when it has three vertices) with at least three vertices
that is not a `K₄` has an outerplanar Hamiltonian cycle (Lemma 19); hence the ear elimination
finds one on the local graph (`Ear.earHam_correct`), and the positions on it form a polygon. -/
theorem blockGood_of (hL : TwoConnectedK23Structure) {B : Graph} (hB : ∀ e ∈ B, e.1 < e.2) (hnd : B.Nodup)
    (hK : K23MinorFree B) (h2c : 3 ≤ (blockVerts B).length → TwoConnected B) :
    BlockGood B := by
  intro h3 h46
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
  have hear := Ear.earHam_correct (localEdges_lt hB hvs) (localEdges_nodup hB hvs hnd) h3 hham0
    hall
  have hLlt : ∀ e ∈ localEdges (blockVerts B) B, e.1 < e.2 :=
    fun e he => (localEdges_lt hB hvs e he).1
  have hP := isPolygon_localEdges hLlt hear
  rwa [length_of_outerplanarHam (fun _ => isVertex_localEdges hB) hear] at hP

/-- **Every block of a `K_{2,3}`-minor-free graph is `BlockGood`** (given Lemma 19). -/
theorem blockGood_blocksOf (hL : TwoConnectedK23Structure) {g : Graph} (hg : K23MinorFree g) :
    ∀ E ∈ blocksOf g, BlockGood E := by
  obtain ⟨P, -, -, hbl⟩ := Algo.blocksOf_eq g
  intro E hE
  rw [hbl, List.mem_map] at hE
  obtain ⟨h, -, rfl⟩ := hE
  exact blockGood_of hL (idBlock_lt P h) (idBlock_nodup P h)
    (P.block_k23MinorFree (k23MinorFree_idEdges hg) h) (idBlock_twoConnected P)

end STACS2027.RAM.Main

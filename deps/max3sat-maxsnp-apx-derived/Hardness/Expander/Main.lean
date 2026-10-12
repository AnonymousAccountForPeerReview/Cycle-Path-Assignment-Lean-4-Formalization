module

public import Hardness.Expander.Table
public import Bridge.Total
public import OAI.Computability.UniqueGames.Machines.MachinePaddedOverlayRuntimeLemmas

/-!
# An explicit polynomial-time family of constant-degree expanders

`exists_expanderFamily`: there are constants `D`, `c` and a polynomial-time computable family
`G : Nat → List (List Nat)` of `D`-regular symmetric multigraphs in neighbour-list form, `G k`
having between `k` and `c * k` vertices, with edge expansion at least `1` (in fact `2`) on sets
of at most half the vertices.

The family is the zig-zag family of the vendored development
(`ExpanderTables.family H (boundedLevel k)` on `paddedSize k` vertices, of degree
`internalDegree = baseDegree ^ 2`). It is computed as

`k ↦ extract 4096 1 internalDegree (parseWords (F (unaryWords (inputWords 4096 k))))`,

where `F` is the total polynomial-time word function that `Bridge.exists_polyTime_of_tm2`
extracts from the vendored padded-overlay machine
(`MachinePaddedOverlayRuntime.computableInPolyTime H 1`), run on the port table with `k`
vertices and a single self-reversing port per vertex; the machine overlays the expander table
on the padded input, and `extract` reads the expander ports off the output table.
-/

@[expose] public section

namespace Complexity

open OAI.UniqueGamesTheorem.Foundations OAI.UniqueGamesTheorem.Foundations.PCP
open Complexity.Expander Complexity.PT

/-- The vendored family is polynomial-time computable in list form. -/
theorem Expander.pt_familyGraph (H : PreprocessingStageMaps.BaseTable) :
    PT (Expander.familyGraph H) := by
  obtain ⟨F, hF, hFa⟩ := Bridge.exists_polyTime_of_tm2
    (OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedOverlayRuntime.computableInPolyTime H 1 Nat.one_pos)
    (OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedOverlayRuntime.finite_alphabet H 1 Nat.one_pos)
  have hF' : PT F := PT.of_polyTime hF
  have h : PT (fun k : Nat => extract 4096 1 PreprocessingRegularTables.internalDegree
      (parseWords (F (unaryWords (inputWords 4096 k))))) :=
    (PT.extract 4096 1 PreprocessingRegularTables.internalDegree).comp
      (PT.parseWords.comp (hF'.comp (PT.unaryWords.comp (PT.inputWords 4096))))
  refine h.of_eq fun k => ?_
  rw [← inputBits_selfInput, hFa (selfInput k), familyGraph_eq_extract]
  change extract 4096 1 PreprocessingRegularTables.internalDegree (parseWords
    (OAI.UniqueGamesTheorem.Foundations.Complexity.encodeWords (PortTables.tableWords _))) = _
  rw [encodeWords_eq, parseWords_unaryWords]

/-- **An explicit polynomial-time family of constant-degree expanders**, with the expansion
bound `2 * S.length ≤ …` and `8 ≤ D`. -/
theorem exists_expanderFamily_strong : ∃ (D c : Nat) (G : Nat → List (List Nat)),
    PT G ∧ IsExpanderFamily D c G ∧ 8 ≤ D ∧
      ∀ k (S : List Nat), S.Nodup → (∀ v ∈ S, v < (G k).length) →
        2 * S.length ≤ (G k).length →
        2 * S.length ≤
          (S.flatMap fun v => ((G k).getD v []).filter fun u => decide (u ∉ S)).length := by
  obtain ⟨H, hH⟩ := ExpanderTables.exists_base_table
  obtain ⟨h1, h2⟩ := isExpanderFamily_familyGraph H hH
  exact ⟨PreprocessingRegularTables.internalDegree, ExpanderFamily.growth, familyGraph H,
    pt_familyGraph H, h1, PreprocessingRegularSoundness.internalDegree_ge_eight, h2⟩

/-- **An explicit polynomial-time family of constant-degree expanders.** -/
theorem exists_expanderFamily :
    ∃ (D c : Nat) (G : Nat → List (List Nat)), PT G ∧ IsExpanderFamily D c G := by
  obtain ⟨D, c, G, hG, h, -, -⟩ := exists_expanderFamily_strong
  exact ⟨D, c, G, hG, h⟩

end Complexity

module

public import Hardness.Expander.Words
public import Hardness.Expander.Graph
public import OAI.Computability.UniqueGames.PCP.PreprocessingTablesLemmas

/-!
# The vendored expander tables in list form

* `selfTable k`: the port table with `k` vertices and one self-reversing port per vertex, whose
  serialisation is `unaryWords (inputWords 4096 k)`;
* `extract_overlay`: the neighbour lists of an expander table `T` can be read off the
  serialisation of any overlay `PreprocessingOverlayTables.overlay G T`;
* `familyGraph H k`: the neighbour lists of the vendored zig-zag table
  `family H (boundedLevel k)` on `paddedSize k` vertices, and `isExpanderFamily_familyGraph`.
-/

@[expose] public section

namespace Complexity.Expander

open OAI.UniqueGamesTheorem.Foundations OAI.UniqueGamesTheorem.Foundations.PCP
open OAI.UniqueGamesTheorem.Foundations.Complexity (encodeWords encodeWord)

theorem encodeWords_eq (ws : List Nat) : encodeWords ws = unaryWords ws := by
  induction ws with
  | nil => rfl
  | cons n ws ih =>
    simp [encodeWords, ih, unaryWords, unaryWord, encodeWord]

/-! ### The input table -/

/-- The empty relation. -/
def zeroRelation : GraphTables.RelationTable := Vector.replicate 4096 false

theorem relationWords_zeroRelation :
    GraphTables.relationWords zeroRelation = List.replicate 4096 0 := by
  have hbit : GraphTables.bitWord false = 0 := rfl
  rw [GraphTables.relationWords, zeroRelation, Vector.toList_replicate, List.map_replicate, hbit]

/-- `k` vertices, one self-reversing port per vertex, all relations empty. -/
def selfTable (k : Nat) : PortTables.Table k 1 where
  reverseIndex := Vector.ofFn id
  relations := Vector.replicate (k * 1) zeroRelation
  involutive := by
    intro i
    simp
  transpose := by
    intro i a b
    simp [GraphTables.relationAt, zeroRelation]

theorem rowWords_flatRows_selfTable (k i : Nat) (h : i < k * 1) :
    GraphTables.rowWords ((PortTables.flatRows (selfTable k))[i]'h) =
      [i, i] ++ List.replicate 4096 0 := by
  rw [← relationWords_zeroRelation]
  have h1 : ((PortTables.rowIndex k 1).symm ⟨i, h⟩).1.val = i := by
    simp [PortTables.rowIndex, finProdFinEquiv, Fin.divNat]
  have h2 : (selfTable k).reverseIndex[i]'h = ⟨i, h⟩ := by simp [selfTable]
  have h3 : (selfTable k).relations[i]'h = zeroRelation := by simp [selfTable]
  simp only [PortTables.flatRows, Vector.getElem_ofFn, GraphTables.rowWords, Fin.getElem_fin,
    h1, h2, h3]

theorem tableWords_selfTable (k : Nat) :
    PortTables.tableWords (selfTable k) = inputWords 4096 k := by
  rw [PortTables.tableWords_eq, inputWords]
  congr 1
  rw [List.flatMap_def, List.flatMap_def]
  congr 1
  apply List.ext_getElem
  · rw [List.length_map, List.length_map, Vector.length_toList, List.length_range, Nat.mul_one]
  · intro i h1 h2
    rw [List.length_map, List.length_range] at h2
    rw [List.getElem_map, List.getElem_map, Vector.getElem_toList, List.getElem_range]
    exact rowWords_flatRows_selfTable k i (by omega)

/-- The input of the overlay machine. -/
def selfInput (k : Nat) : PortTables.Input 1 := ⟨k, selfTable k⟩

theorem inputBits_selfInput (k : Nat) :
    PortTables.inputBits (selfInput k) = unaryWords (inputWords 4096 k) := by
  change encodeWords (PortTables.tableWords (selfTable k)) = _
  rw [encodeWords_eq, tableWords_selfTable]

/-! ### Reading an expander table off an overlay -/

theorem reverseIndex_val {n d : Nat} (table : PortTables.Table n d) (e : Fin n × Fin d)
    (h : e.2.val + d * e.1.val < n * d) :
    (table.reverseIndex[e.2.val + d * e.1.val]'h).val =
      (PortTables.rotation table e).2.val + d * (PortTables.rotation table e).1.val := by
  have h1 := congrArg Fin.val (PortTables.rowIndex_rotation table e)
  rw [PortTables.rowIndex_val] at h1
  rw [h1]
  rfl

theorem length_rowWords {n m : Nat} (row : GraphTables.DartRow n m) :
    (GraphTables.rowWords row).length = 4096 + 2 := by
  simp [GraphTables.rowWords]

theorem extract_overlay {n d q : Nat} (G : PortTables.Table n d)
    (T : ExpanderTables.Table n q) :
    extract 4096 d q (PortTables.tableWords (PreprocessingOverlayTables.overlay G T)) =
      nbrs (ExpanderTables.lookup T) := by
  rw [PortTables.tableWords_eq]
  let g : Nat → Nat → Nat := fun v i =>
    if h : v < n ∧ i < q then (ExpanderTables.lookup T (⟨v, h.1⟩, ⟨i, h.2⟩)).1.val else 0
  rw [nbrs_eq_range (ExpanderTables.lookup T) g (fun v i => by simp [g])]
  refine extract_flatMap 4096 d q n _ _ _ (fun x _ => length_rowWords x) g ?_
  intro v hv i hi
  let e : Fin n × Fin (d + q) :=
    (⟨v, hv⟩, PreprocessingOverlayTables.overlayPorts d q (Sum.inr ⟨i, hi⟩))
  have hlt : d + i + (d + q) * v < n * (d + q) := (PortTables.rowIndex n (d + q) e).isLt
  have hrot := PreprocessingOverlayTables.overlay_rotation_expander G T ⟨v, hv⟩ ⟨i, hi⟩
  refine ⟨by simpa using hlt, d + (ExpanderTables.lookup T (⟨v, hv⟩, ⟨i, hi⟩)).2.val,
    by omega, ?_⟩
  have hrev := reverseIndex_val (PreprocessingOverlayTables.overlay G T) e hlt
  rw [show PortTables.rotation (PreprocessingOverlayTables.overlay G T) e = _ from hrot] at hrev
  simp only [Vector.getElem_toList, PortTables.flatRows, Vector.getElem_ofFn,
    GraphTables.rowWords, List.cons_append, List.nil_append, g, hv, hi, and_self, dite_true]
  exact hrev

/-! ### The family -/

/-- Neighbour lists of the vendored expander table on `paddedSize k` vertices. -/
noncomputable def familyGraph (H : PreprocessingStageMaps.BaseTable) (k : Nat) :
    List (List Nat) :=
  nbrs (ExpanderTables.lookup (PreprocessingStageMaps.familyAt H k))

/-- The family is read off the output table of the vendored padded-overlay stage. -/
theorem familyGraph_eq_extract (H : PreprocessingStageMaps.BaseTable) (k : Nat) :
    familyGraph H k = extract 4096 1 PreprocessingRegularTables.internalDegree
      (PortTables.tableWords (PreprocessingStageMaps.paddedOverlay H 1 (selfInput k)).2) :=
  (extract_overlay _ _).symm

theorem familyAt_certificate (H : PreprocessingStageMaps.BaseTable)
    (hH : SpectralReturn.SpectralCertificate (ExpanderTables.graph H) (1 / 100 : ℝ))
    (k : Nat) :
    SpectralReturn.SpectralCertificate
      (ExpanderTables.graph (PreprocessingStageMaps.familyAt H k)) (1 / 2 : ℝ) := by
  let : NeZero Expanders.baseDegree := ⟨PreprocessingRegularSoundness.baseDegree_ne_zero⟩
  unfold PreprocessingStageMaps.familyAt
  apply PreprocessingRegularSoundness.resizeTable_certificate
  exact ExpanderTables.family_certificate H hH _

theorem isExpanderFamily_familyGraph (H : PreprocessingStageMaps.BaseTable)
    (hH : SpectralReturn.SpectralCertificate (ExpanderTables.graph H) (1 / 100 : ℝ)) :
    IsExpanderFamily PreprocessingRegularTables.internalDegree ExpanderFamily.growth
        (familyGraph H) ∧
      ∀ k (S : List Nat), S.Nodup → (∀ v ∈ S, v < (familyGraph H k).length) →
        2 * S.length ≤ (familyGraph H k).length →
        2 * S.length ≤ (S.flatMap fun v =>
          ((familyGraph H k).getD v []).filter fun u => decide (u ∉ S)).length := by
  refine isExpanderFamily_nbrs PreprocessingRegularTables.internalDegree ExpanderFamily.growth
    PreprocessingLevels.paddedSize
    (fun k => ExpanderTables.lookup (PreprocessingStageMaps.familyAt H k))
    (fun k hk => (PreprocessingLevels.paddedSize_bounds hk).1)
    (fun k hk => (PreprocessingLevels.paddedSize_bounds hk).2)
    (fun k => ExpanderTables.lookup_involutive _) ?_
  intro k S hsmall
  have h := SpectralCut.cut_card_ge_twice
    (ExpanderTables.graph (PreprocessingStageMaps.familyAt H k)) (familyAt_certificate H hH k)
    (by simpa only [Fintype.card_fin] using PreprocessingRegularSoundness.internalDegree_ge_eight)
    S (by simpa only [Fintype.card_fin] using hsmall)
  exact h

end Complexity.Expander

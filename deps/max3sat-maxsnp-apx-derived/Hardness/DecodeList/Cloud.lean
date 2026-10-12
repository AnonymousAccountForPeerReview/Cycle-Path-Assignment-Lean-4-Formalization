module

public import Hardness.DecodeList.CloudDef
public import Hardness.Decode.Cloud

/-!
# List form of the cloud-majority decoder: correctness

`cloudList_spec`: on the tail column `tailList t` of a table `t` and the list of a labeling of
the preprocessed table, the list program `cloudList` of `Hardness/DecodeList/CloudDef.lean`
returns the list of `Decode.roundPreprocessed t labels`.

The proof identifies, in this order,

* the constant `cloudGrowth` with `ExpanderFamily.growth` (`cloudGrowth_eq`, by unfolding
  `growth = baseDegree ^ 4`, `baseDegree = initialDegree ^ basePower`, `initialDegree = 2 ^ 16`,
  `basePower = 7`; the numbers are never evaluated);
* the padded-size search `paddedSizeG` with `PreprocessingLevels.cloudPaddedSize` (the loop
  `levelLoop` carries `(padStep g k)^[fuel] s` in its second component, `levelLoop_snd`);
* `tails.count v` with `PreprocessingCloudIndex.cloudSize t v` and hence `cloudPadding` with
  `PreprocessingRegularTables.padding t` (`count_tailList`, `cloudPadding_eq`);
* the owner list `cloudOwners` with the list of `regularOwner t z` for `z < regularVertices t`
  (`cloudOwners_eq`): the original darts are owned by their tails (`regularOwner_original`), and
  the dummy part of the list is the list `paddingList (padding t)` of dummy coordinates, numbered
  by `paddingOrder` (`regularOwner_dummy`);
* the `List.countP` of `cloudCountList` with the `Finset.card` of `cloudCount`
  (`cloudCountList_eq`).
-/

@[expose] public section

set_option linter.dupNamespace false

namespace Complexity.DecodeList

open OAI.UniqueGamesTheorem.Foundations.PCP
open OAI.UniqueGamesTheorem.Foundations.PCP.Decode
open PreprocessingRegularTables

/-- The tail column of a table: entry `e` is the tail of the dart `e`. -/
def tailList (t : GraphTables.Table) : List Nat :=
  List.ofFn fun e : Fin t.darts => (t.rows[e].tail).val

@[simp] theorem tailList_length (t : GraphTables.Table) : (tailList t).length = t.darts := by
  simp [tailList]

/-! ### The constants -/

/-- `cloudGrowth` is the growth factor of the cloud expander family (symbolic unfolding only). -/
theorem cloudGrowth_eq : cloudGrowth = ExpanderFamily.growth := by
  unfold cloudGrowth ExpanderFamily.growth Expanders.baseDegree Expanders.initialDegree
    Expanders.basePower
  rfl

theorem padStep_iterate_fixed {g k s : Nat} (h : k ≤ s) (n : Nat) :
    (padStep g k)^[n] s = s :=
  Function.iterate_fixed (by simp only [padStep, h, ↓reduceIte]) n

/-- The second component of the vendored search loop is the iteration of `padStep`. -/
theorem levelLoop_snd (g k : Nat) : ∀ fuel e s,
    (PreprocessingLevels.levelLoop g k fuel e s).2 = (padStep g k)^[fuel] s
  | 0, _, _ => rfl
  | fuel + 1, e, s => by
    rw [Function.iterate_succ_apply]
    unfold PreprocessingLevels.levelLoop
    by_cases h : k ≤ s
    · have hs : padStep g k s = s := by simp only [padStep, h, ↓reduceIte]
      simp only [h, ↓reduceIte]
      rw [hs, padStep_iterate_fixed h]
    · have hs : padStep g k s = s * g := by simp only [padStep, h, ↓reduceIte]
      simp only [h, ↓reduceIte]
      rw [hs]
      exact levelLoop_snd g k fuel (e + 1) (s * g)

/-- `paddedSizeG cloudGrowth` is the vendored `cloudPaddedSize`. -/
theorem paddedSizeG_eq (c : Nat) :
    paddedSizeG cloudGrowth c = PreprocessingLevels.cloudPaddedSize c := by
  unfold paddedSizeG PreprocessingLevels.cloudPaddedSize PreprocessingLevels.paddedSize
    PreprocessingLevels.searchResult
  rw [levelLoop_snd, cloudGrowth_eq]

/-! ### Cloud sizes and padding -/

theorem count_tailList (t : GraphTables.Table) (v : Fin t.vertices) :
    (tailList t).count v.val = PreprocessingCloudIndex.cloudSize t v := by
  unfold tailList PreprocessingCloudIndex.cloudSize PreprocessingCloudIndex.cloudDarts
  rw [List.ofFn_eq_map, List.count, List.countP_map, List.countP_eq_length_filter]
  congr 1

theorem cloudPadding_eq (t : GraphTables.Table) (v : Fin t.vertices) :
    cloudPadding cloudGrowth (tailList t) v.val = padding t v := by
  unfold cloudPadding PreprocessingRegularTables.padding
  rw [count_tailList, paddedSizeG_eq]

/-! ### Owners -/

/-- The dummy part of the owner list is the list of owners of the dummy coordinates. -/
theorem flatMap_replicate_eq {n : Nat} (p : Fin n → Nat) (q : Nat → Nat)
    (hq : ∀ v : Fin n, q v.val = p v) :
    (List.range n).flatMap (fun v => List.replicate (q v) v) =
      (paddingList p).map (fun s => s.1.val) := by
  rw [← List.map_coe_finRange_eq_range, List.flatMap_map]
  unfold paddingList
  rw [List.sigma, List.map_flatMap]
  congr 1
  funext v
  rw [List.map_map, hq v]
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp

/-- The dummy coordinate at position `w` of `paddingList` has the number `w`. -/
theorem paddingOrder_getElem {n : Nat} (p : Fin n → Nat) (w : Nat)
    (hw : w < (paddingList p).length) :
    (paddingOrder p (paddingList p)[w]).val = w := by
  have h : (paddingList p)[w] = (paddingListOrder p).symm ⟨w, hw⟩ := rfl
  rw [h]
  show ((paddingListOrder p) ((paddingListOrder p).symm ⟨w, hw⟩)).val = w
  rw [Equiv.apply_symm_apply]

theorem regularOwner_inr (t : GraphTables.Table) (s : Σ v : Fin t.vertices, Fin (padding t v)) :
    regularOwner t (vertexOrder t (padding t) (Sum.inr s)) = s.1 := by
  obtain ⟨v, k⟩ := s
  exact regularOwner_dummy t v k

/-- The owner list of the program is the list of `regularOwner`. -/
theorem cloudOwners_eq (t : GraphTables.Table) :
    cloudOwners cloudGrowth t.vertices (tailList t) =
      List.ofFn fun z : Fin (vertexCount t (padding t)) => (regularOwner t z).val := by
  unfold cloudOwners
  rw [flatMap_replicate_eq (padding t) _ (cloudPadding_eq t)]
  apply List.ext_getElem
  · simp [vertexCount, paddingList_length]
  · intro z h1 h2
    rw [List.getElem_ofFn]
    by_cases hz : z < t.darts
    · rw [List.getElem_append_left (by rw [tailList_length]; exact hz)]
      have he : (⟨z, by simpa using h2⟩ : Fin (vertexCount t (padding t))) =
          vertexOrder t (padding t) (Sum.inl ⟨z, hz⟩) := Fin.ext rfl
      rw [he, regularOwner_original]
      simp [tailList]
    · have hz' : (tailList t).length ≤ z := by rw [tailList_length]; omega
      rw [List.getElem_append_right hz', List.getElem_map]
      have hw : z - (tailList t).length < (paddingList (padding t)).length := by
        rw [paddingList_length, tailList_length]
        have := h2
        simp only [List.length_ofFn, vertexCount] at this
        omega
      have he : (⟨z, by simpa using h2⟩ : Fin (vertexCount t (padding t))) =
          vertexOrder t (padding t) (Sum.inr (paddingList (padding t))[z - (tailList t).length]) := by
        apply Fin.ext
        rw [vertexOrder_dummy, paddingOrder_getElem]
        show z = t.darts + (z - (tailList t).length)
        rw [tailList_length]
        omega
      rw [he, regularOwner_inr]

/-! ### Counting -/

theorem countP_ofFn_eq_card {α : Type*} {n : Nat} (f : Fin n → α) (p : α → Bool) :
    (List.ofFn f).countP p = (Finset.univ.filter fun i => p (f i) = true).card := by
  rw [List.ofFn_eq_map, List.countP_map, List.countP_eq_length_filter,
    ← List.toFinset_card_of_nodup ((List.nodup_finRange n).filter _)]
  congr 1
  ext i
  simp

theorem zip_ofFn_ofFn {α β : Type*} {m n : Nat} (f : Fin m → α) (g : Fin n → β) (h : m ≤ n) :
    (List.ofFn f).zip (List.ofFn g) = List.ofFn fun i : Fin m => (f i, g (i.castLE h)) := by
  apply List.ext_getElem
  · simp [h]
  · intro i h1 h2
    simp [List.getElem_zip]

/-- The list count of the program is the cloud count of the decoder. -/
theorem cloudCountList_eq (t : GraphTables.Table)
    (labels : Fin (PreprocessingTables.vertices t) → GraphTables.Label)
    (v : Fin t.vertices) (a : GraphTables.Label) :
    cloudCountList (cloudOwners cloudGrowth t.vertices (tailList t)) (labelList labels)
        v.val a.val =
      cloudCount t (PreprocessingGuarantees.restrictedLabel t labels) v a := by
  unfold cloudCountList cloudCount labelList
  have hle : vertexCount t (padding t) ≤ PreprocessingTables.vertices t :=
    PreprocessingLevels.le_paddedSize (PreprocessingTables.regularVertices t)
  rw [cloudOwners_eq, zip_ofFn_ofFn _ _ hle, countP_ofFn_eq_card]
  congr 1

private theorem argMaxUpTo_congr' {f g : Nat → Nat} (k : Nat) (h : ∀ i, i ≤ k → f i = g i) :
    argMaxUpTo f k = argMaxUpTo g k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have ih' := ih fun i hi => h i (Nat.le_succ_of_le hi)
    simp only [argMaxUpTo]
    rw [← ih', h (k + 1) (Nat.le_refl _),
      h (argMaxUpTo f k) (Nat.le_succ_of_le (argMaxUpTo_le f k))]

/-! ### Specification -/

/-- **Correctness of the list form of the cloud-majority decoder.** -/
theorem cloudList_spec (t : GraphTables.Table)
    (labels : Fin (PreprocessingTables.vertices t) → GraphTables.Label) :
    cloudList t.vertices (tailList t) (labelList labels) =
      labelList (roundPreprocessed t labels) := by
  apply List.ext_getElem
  · rw [cloudList_length, labelList_length]
  · intro v h1 h2
    have hv : v < t.vertices := by
      rw [cloudList_length] at h1
      exact h1
    have hl : (cloudList t.vertices (tailList t) (labelList labels))[v] =
        argMaxUpTo (cloudCountList (cloudOwners cloudGrowth t.vertices (tailList t))
          (labelList labels) v) 63 := by
      simp only [cloudList, cloudListG, List.getElem_map, List.getElem_range]
    have hr : (labelList (roundPreprocessed t labels))[v] =
        argMaxUpTo (extendCount (cloudCount t (PreprocessingGuarantees.restrictedLabel t labels)
          ⟨v, hv⟩)) (64 - 1) := by
      simp only [labelList, List.getElem_ofFn]
      rfl
    have h63 : (64 - 1 : Nat) = 63 := rfl
    rw [hl, hr, h63]
    apply argMaxUpTo_congr'
    intro a ha
    have ha' : a < 64 := Nat.lt_succ_of_le ha
    rw [show extendCount (cloudCount t (PreprocessingGuarantees.restrictedLabel t labels)
      ⟨v, hv⟩) a = cloudCount t (PreprocessingGuarantees.restrictedLabel t labels)
      ⟨v, hv⟩ ⟨a, ha'⟩ from extendCount_val _ ⟨a, ha'⟩]
    exact cloudCountList_eq t labels ⟨v, hv⟩ ⟨a, ha'⟩

end Complexity.DecodeList

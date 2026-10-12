module

public import Outerplanar.Algo.Combine
public import Outerplanar.RAM.Layout
import Mathlib.Tactic

/-!
# Phase R0 (parsing), abstract side: prefix versions of `labels` and `idEdges`

The parsing phase reads the input pairs in order. After `j` pairs it has computed
* the labels `labels (g.take j)` (a dictionary `dictOf L` maps a label to its id `+ 1`),
* the edges `edgesPre g j` between the ids (with respect to the final ids `idOf g`),
and both grow by `ext` (append if new) at every proper pair (`labels_take_succ`,
`edgesPre_succ`), because `(l ++ [x]).eraseDups = ext l.eraseDups x`
(`eraseDups_append_singleton`). The largest label `maxLab g` bounds all labels
(`labelBound g = maxLab g + 1`, `labelBound_eq`). The id edges are the `eraseDups` of the id
pairs `idPairs g` of the proper input pairs (`idEdges_eq`), which R0 writes in input order
(`pairsPre_succ`) and deduplicates by the module `PairIds` (no `N × N` matrix).
-/

@[expose] public section

namespace STACS2027.RAM.R0

open STACS2027.Algo

/-! ### Appending a new element -/

/-- `L` extended by `x` when `x` is new. -/
def ext {α : Type} [BEq α] [LawfulBEq α] (L : List α) (x : α) : List α := if x ∈ L then L else L ++ [x]

theorem eraseDups_append_singleton {α : Type} [BEq α] [LawfulBEq α] (l : List α) (x : α) :
    (l ++ [x]).eraseDups = ext l.eraseDups x := by
  rw [List.eraseDups_append]
  by_cases hx : x ∈ l
  · have : [x].removeAll l = [] := by simp [List.removeAll, hx]
    simp [ext, this, hx]
  · have : [x].removeAll l = [x] := by simp [List.removeAll, hx]
    simp [ext, this, hx, List.eraseDups_cons]

theorem mem_ext {α : Type} [BEq α] [LawfulBEq α] {L : List α} {x y : α} : y ∈ ext L x ↔ y ∈ L ∨ y = x := by
  unfold ext
  by_cases hx : x ∈ L
  · simp only [hx, ↓reduceIte]
    exact ⟨Or.inl, fun h => h.elim id (fun h' => h' ▸ hx)⟩
  · simp [hx]

theorem length_ext_le {α : Type} [BEq α] [LawfulBEq α] (L : List α) (x : α) :
    (ext L x).length ≤ L.length + 1 := by
  unfold ext; split <;> simp

theorem length_eraseDups_le {α : Type} [BEq α] [LawfulBEq α] (l : List α) :
    l.eraseDups.length ≤ l.length := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l x ih =>
    rw [eraseDups_append_singleton]
    have := length_ext_le l.eraseDups x
    simp only [List.length_append, List.length_singleton]; omega

/-! ### The entries and the largest label -/

/-- The input entries: the ends of the input pairs, in order. -/
def ents (g : Graph) : List ℕ := g.flatMap fun e => [e.1, e.2]

/-- The largest entry of the input (`0` for the empty input). -/
def maxLab (g : Graph) : ℕ := (ents g).foldl max 0

@[simp] theorem length_ents (g : Graph) : (ents g).length = 2 * g.length := length_flatMap_pair g

theorem graphInput_eq (g : Graph) : graphInput g = g.length :: ents g := rfl

theorem foldl_max_take_succ (l : List ℕ) (k : ℕ) (hk : k < l.length) :
    (l.take (k + 1)).foldl max 0 = max ((l.take k).foldl max 0) l[k] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, List.foldl_append]
  rfl

theorem le_foldl_max_init (l : List ℕ) (a : ℕ) : a ≤ l.foldl max a := by
  induction l generalizing a with
  | nil => simp
  | cons z l ih => simp only [List.foldl_cons]; exact le_trans (le_max_left _ _) (ih _)

theorem le_foldl_max {l : List ℕ} {x : ℕ} (hx : x ∈ l) (a : ℕ) : x ≤ l.foldl max a := by
  induction l generalizing a with
  | nil => simp at hx
  | cons y l ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hx with rfl | hx
    · exact le_trans (le_max_right _ _) (le_foldl_max_init _ _)
    · exact ih hx _

theorem le_maxLab {g : Graph} {x : ℕ} (hx : x ∈ ents g) : x ≤ maxLab g := le_foldl_max hx 0

theorem mem_ents_of_proper {g : Graph} {e : Edge} (he : e ∈ proper g) : e.1 ∈ ents g ∧ e.2 ∈ ents g := by
  have := (Comb.mem_proper.mp he).1
  simp only [ents, List.mem_flatMap]
  exact ⟨⟨e, this, by simp⟩, ⟨e, this, by simp⟩⟩

theorem pair_mem_ents (g : Graph) (j : ℕ) (hj : j < g.length) : g[j].1 ∈ ents g ∧ g[j].2 ∈ ents g := by
  simp only [ents, List.mem_flatMap]
  exact ⟨⟨g[j], List.getElem_mem hj, by simp⟩, ⟨g[j], List.getElem_mem hj, by simp⟩⟩

theorem labels_le_maxLab {g : Graph} {x : ℕ} (hx : x ∈ labels g) : x ≤ maxLab g := by
  simp only [labels, List.mem_eraseDups, List.mem_flatMap] at hx
  obtain ⟨e, he, hx⟩ := hx
  have := mem_ents_of_proper he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact le_maxLab this.1
  · exact le_maxLab this.2

/-- The `k`-th entry of the input is in memory cell `k + 1`. -/
theorem graphInput_getD_succ (g : Graph) (k : ℕ) (hk : k < 2 * g.length) :
    (graphInput g).getD (k + 1) 0 = (ents g)[k]'(by simpa using hk) := by
  rw [graphInput_eq, List.getD_cons_succ, getD_eq_getElem']

/-- The ends of the `j`-th pair are the entries `2j` and `2j + 1`. -/
theorem ents_pair (g : Graph) (j : ℕ) (hj : j < g.length) :
    (ents g)[2 * j]'(by simp; omega) = g[j].1 ∧ (ents g)[2 * j + 1]'(by simp; omega) = g[j].2 := by
  have h := getD_flatMap_pair g j hj
  rw [getD_eq_getElem' (by simp; omega), getD_eq_getElem' (by simp; omega)] at h
  exact h

/-- The ends of the `j`-th pair in a memory holding the input. -/
theorem input_pair {m : ℕ → ℕ} {g : Graph} (h : Arr m 0 (graphInput g)) {j : ℕ} (hj : j < g.length) :
    m (2 * j + 1) = g[j].1 ∧ m (2 * j + 2) = g[j].2 := by
  have h1 := h.getD (i := 2 * j + 1) (by simp; omega)
  have h2 := h.getD (i := 2 * j + 2) (by simp; omega)
  simp only [Nat.zero_add] at h1 h2
  rw [h1, h2, graphInput_getD_succ g (2 * j) (by omega), graphInput_getD_succ g (2 * j + 1) (by omega)]
  exact ents_pair g j hj

theorem length_le_ext {α : Type} [BEq α] [LawfulBEq α] (L : List α) (x : α) :
    L.length ≤ (ext L x).length := by
  unfold ext; split <;> simp

/-! ### Prefixes of the input -/

theorem proper_take_succ (g : Graph) (j : ℕ) (hj : j < g.length) :
    proper (g.take (j + 1)) = proper (g.take j) ++ (if g[j].1 < g[j].2 then [g[j]] else []) := by
  simp only [proper, List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some,
    List.filter_append, List.filter_singleton]
  split <;> simp_all

/-- The labels after one more pair. -/
theorem labels_take_succ (g : Graph) (j : ℕ) (hj : j < g.length) :
    labels (g.take (j + 1)) = if g[j].1 < g[j].2 then ext (ext (labels (g.take j)) g[j].1) g[j].2
      else labels (g.take j) := by
  unfold labels
  rw [proper_take_succ g j hj]
  split
  · rw [List.flatMap_append, List.flatMap_singleton, show ∀ l : List ℕ, ∀ a b : ℕ,
      l ++ [a, b] = (l ++ [a]) ++ [b] by simp, eraseDups_append_singleton, eraseDups_append_singleton]
  · simp

theorem labels_take_length (g : Graph) : labels (g.take g.length) = labels g := by
  rw [List.take_length]

theorem length_labels_take_le (g : Graph) (j : ℕ) : (labels (g.take j)).length ≤ 2 * j := by
  have h1 := length_eraseDups_le ((proper (g.take j)).flatMap fun e => [e.1, e.2])
  have h2 : ((proper (g.take j)).flatMap fun e => [e.1, e.2]).length = 2 * (proper (g.take j)).length :=
    length_flatMap_pair _
  have h3 : (proper (g.take j)).length ≤ (g.take j).length := List.length_filter_le _ _
  have h4 : (g.take j).length ≤ j := List.length_take_le _ _
  unfold labels; omega

theorem numV_le (g : Graph) : numV g ≤ 2 * g.length := by
  have := length_labels_take_le g g.length
  rwa [labels_take_length] at this

/-- The id edges of the first `j` pairs (with respect to the final ids). -/
def edgesPre (g : Graph) (j : ℕ) : List Edge :=
  ((proper (g.take j)).map fun e => edge (idOf g e.1) (idOf g e.2)).eraseDups

/-- The id edges after one more pair. -/
theorem edgesPre_succ (g : Graph) (j : ℕ) (hj : j < g.length) :
    edgesPre g (j + 1) = if g[j].1 < g[j].2 then ext (edgesPre g j) (edge (idOf g g[j].1) (idOf g g[j].2))
      else edgesPre g j := by
  unfold edgesPre
  rw [proper_take_succ g j hj]
  split
  · rw [List.map_append, List.map_singleton, eraseDups_append_singleton]
  · simp

theorem edgesPre_zero (g : Graph) : edgesPre g 0 = [] := by simp [edgesPre, proper]

theorem edgesPre_length (g : Graph) : edgesPre g g.length = idEdges g := by
  rw [edgesPre, List.take_length]; rfl

theorem length_edgesPre_le (g : Graph) (j : ℕ) : (edgesPre g j).length ≤ j := by
  have h1 := length_eraseDups_le ((proper (g.take j)).map fun e => edge (idOf g e.1) (idOf g e.2))
  have h3 : (proper (g.take j)).length ≤ (g.take j).length := List.length_filter_le _ _
  have h4 : (g.take j).length ≤ j := List.length_take_le _ _
  unfold edgesPre; simp only [List.length_map] at h1; omega

theorem length_idEdges_le (g : Graph) : (idEdges g).length ≤ g.length := by
  have := length_edgesPre_le g g.length
  rwa [edgesPre_length] at this

/-- An edge of a prefix joins two ids below `numV g`. -/
theorem edgesPre_below {g : Graph} {j : ℕ} {e : Edge} (he : e ∈ edgesPre g j) :
    e.1 < numV g ∧ e.2 < numV g := by
  simp only [edgesPre, List.mem_eraseDups, List.mem_map] at he
  obtain ⟨d, hd, rfl⟩ := he
  have hd' : d ∈ proper g := by
    simp only [proper, List.mem_filter] at hd ⊢
    exact ⟨List.mem_of_mem_take hd.1, hd.2⟩
  have hl := Comb.mem_labels_of_proper hd'
  have h1 := Comb.idOf_lt hl.1
  have h2 := Comb.idOf_lt hl.2
  simp only [edge]; constructor <;> omega

/-! ### The dictionary -/

/-- The dictionary of a label list: a label maps to its position plus one, others to `0`. -/
def dictOf (L : List ℕ) (x : ℕ) : ℕ := if x ∈ L then L.idxOf x + 1 else 0

theorem dictOf_eq_zero_iff {L : List ℕ} {x : ℕ} : dictOf L x = 0 ↔ x ∉ L := by
  unfold dictOf; split <;> simp_all

@[simp] theorem dictOf_nil : dictOf [] = fun _ => 0 := by funext x; simp [dictOf]

theorem dictOf_snoc {L : List ℕ} {a : ℕ} (ha : a ∉ L) :
    dictOf (L ++ [a]) = Function.update (dictOf L) a (L.length + 1) := by
  funext x
  by_cases hx : x = a
  · subst hx; simp [dictOf, ha, List.idxOf_append]
  · rw [Function.update_of_ne hx]
    by_cases hxL : x ∈ L
    · simp [dictOf, hxL, List.idxOf_append]
    · simp [dictOf, hxL, hx]

theorem dictOf_ext_of_mem {L : List ℕ} {a : ℕ} (ha : a ∈ L) : ext L a = L := by simp [ext, ha]
theorem ext_of_not_mem {α : Type} [BEq α] [LawfulBEq α] {L : List α} {a : α} (ha : a ∉ L) :
    ext L a = L ++ [a] := by simp [ext, ha]
theorem ext_of_mem {α : Type} [BEq α] [LawfulBEq α] {L : List α} {a : α} (ha : a ∈ L) :
    ext L a = L := by simp [ext, ha]

theorem dictOf_labels {g : Graph} {x : ℕ} (hx : x ∈ labels g) : dictOf (labels g) x = idOf g x + 1 := by
  simp [dictOf, hx, idOf]

/-- The label bound is one more than the largest entry. -/
theorem labelBound_eq (g : Graph) : labelBound g = maxLab g + 1 := rfl

/-! ### The id pairs of the proper input pairs -/

/-- The id pairs of the proper input pairs, in input order, with repetitions (with respect to
the final ids): `idEdges g` is their `eraseDups`. -/
def idPairs (g : Graph) : List Edge := (proper g).map fun e => edge (idOf g e.1) (idOf g e.2)

theorem idEdges_eq (g : Graph) : idEdges g = (idPairs g).eraseDups := rfl

/-- The id pairs of the first `j` input pairs. -/
def pairsPre (g : Graph) (j : ℕ) : List Edge :=
  (proper (g.take j)).map fun e => edge (idOf g e.1) (idOf g e.2)

theorem pairsPre_zero (g : Graph) : pairsPre g 0 = [] := by simp [pairsPre, proper]

/-- One more input pair: its id pair is appended if it is proper. -/
theorem pairsPre_succ (g : Graph) (j : ℕ) (hj : j < g.length) :
    pairsPre g (j + 1) = pairsPre g j ++
      if g[j].1 < g[j].2 then [edge (idOf g g[j].1) (idOf g g[j].2)] else [] := by
  unfold pairsPre
  rw [proper_take_succ g j hj]
  split <;> simp

theorem pairsPre_length (g : Graph) : pairsPre g g.length = idPairs g := by
  rw [pairsPre, List.take_length]; rfl

theorem length_pairsPre_le (g : Graph) (j : ℕ) : (pairsPre g j).length ≤ j := by
  have h3 : (proper (g.take j)).length ≤ (g.take j).length := List.length_filter_le _ _
  have h4 : (g.take j).length ≤ j := List.length_take_le _ _
  simp only [pairsPre, List.length_map]; omega

theorem length_idPairs_le (g : Graph) : (idPairs g).length ≤ g.length := by
  have := length_pairsPre_le g g.length
  rwa [pairsPre_length] at this

/-- The id pairs join two ids below `numV g`. -/
theorem idPairs_below (g : Graph) : ∀ e ∈ idPairs g, e.1 < numV g ∧ e.2 < numV g := by
  intro e he
  have : e ∈ edgesPre g g.length := by
    rw [edgesPre_length]; exact List.mem_eraseDups.mpr he
  exact edgesPre_below this

end STACS2027.RAM.R0

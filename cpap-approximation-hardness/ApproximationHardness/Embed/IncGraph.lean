module

public import ApproximationHardness.Embed.DFSRun
public import Complexity.Planar.CombBasic
public import Complexity.Planar.Incidence
import Lean.Elab.Tactic.Omega

/-!
# The incidence graph as a graph to search

The darts of the incidence graph of `f` are `2i` (the variable end of occurrence `i`) and `2i + 1`
(its clause end). The vertex of a dart is its least dart with the same end (`incRep`): `2` times the
first occurrence of the variable, or `2` times the first occurrence of the clause plus one. Two darts
have the same vertex iff they have the same end in `halfEdgeEnd` (`incRep_eq_iff`); for a
Definition 7 formula the graph satisfies the hypotheses of the search (`incOk`).
-/

@[expose] public section

namespace STACS2027.Embed

open Complexity Complexity.SAT Complexity.Planar Complexity.Planar.Comb

/-- The variable of occurrence `i`. -/
def varAt (f : CNF) (i : Nat) : Nat := (f.flatten.getD i ⟨0, true⟩).var

/-- The first occurrence of the variable `v`. -/
def firstOcc (f : CNF) (v : Nat) : Nat := f.flatten.findIdx fun l => l.var == v

/-- The vertex of a dart of the incidence graph. -/
def incRep (f : CNF) (d : Nat) : Nat :=
  if d % 2 = 0 then 2 * firstOcc f (varAt f (d / 2)) else 2 * off f (oj f (d / 2)) + 1

/-- The incidence graph of `f`, as a graph to search. -/
def incDG (f : CNF) : DG := ⟨f.flatten.length, incRep f⟩

theorem flatten_length_nM (f : CNF) : f.flatten.length = nM f := by
  unfold nM Comb.lens; exact length_flatten' f

theorem incidence_length (f : CNF) : (incidenceGraph f).length = f.flatten.length := by
  rw [incidenceGraph_length, flatten_length_nM]; rfl

/-- The edge of occurrence `i`. -/
theorem incidence_getElem? (f : CNF) {i : Nat} (hi : i < f.flatten.length) :
    (incidenceGraph f)[i]? = some (Sum.inl (varAt f i), Sum.inr (oj f i)) := by
  rw [flatten_length_nM] at hi
  obtain ⟨hj, ht, he⟩ := occ_spec f i hi
  have hj' : oj f i < f.length := hj
  have ht' : ot f i < f[oj f i].length := by rw [← kl_of_lt f _ hj']; exact ht
  have h1 := incidenceGraph_getElem? f (oj f i) (ot f i) hj' ht'
  have hoff : ((f.map List.length).take (oj f i)).sum = off f (oj f i) := rfl
  rw [hoff, he] at h1
  rw [h1]
  have h2 := getElem?_flatten_offset f (oj f i) (ot f i) hj' ht'
  rw [hoff, he] at h2
  have hvar : f[oj f i][ot f i].var = varAt f i := by
    unfold varAt
    rw [List.getD_eq_getElem?_getD, h2, List.getElem?_eq_getElem ht']
    rfl
  rw [hvar]

theorem halfEdgeEnd_even (f : CNF) {i : Nat} (hi : i < f.flatten.length) :
    halfEdgeEnd (incidenceGraph f) (2 * i) = some (Sum.inl (varAt f i)) := by
  unfold halfEdgeEnd
  rw [show 2 * i / 2 = i by omega, incidence_getElem? f hi]
  simp

theorem halfEdgeEnd_odd (f : CNF) {i : Nat} (hi : i < f.flatten.length) :
    halfEdgeEnd (incidenceGraph f) (2 * i + 1) = some (Sum.inr (oj f i)) := by
  unfold halfEdgeEnd
  rw [show (2 * i + 1) / 2 = i by omega, incidence_getElem? f hi]
  simp [show (2 * i + 1) % 2 = 1 by omega]

/-! ### First occurrences -/

theorem varAt_eq (f : CNF) {i : Nat} (hi : i < f.flatten.length) : varAt f i = (f.flatten[i]'hi).var := by
  unfold varAt; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl

theorem firstOcc_spec (f : CNF) {i : Nat} (hi : i < f.flatten.length) :
    firstOcc f (varAt f i) ≤ i ∧ firstOcc f (varAt f i) < f.flatten.length ∧
      varAt f (firstOcc f (varAt f i)) = varAt f i := by
  generalize hvv : varAt f i = v
  have hp : ((f.flatten[i]'hi).var == v) = true := by rw [← hvv, varAt_eq f hi]; simp
  have hle : firstOcc f v ≤ i := by
    apply Classical.byContradiction; intro h
    have := List.not_of_lt_findIdx (p := fun l => l.var == v) (xs := f.flatten) (i := i)
      (by unfold firstOcc at h; omega)
    rw [hp] at this; simp at this
  have hlt : firstOcc f v < f.flatten.length := by omega
  refine ⟨hle, hlt, ?_⟩
  have hlt' : List.findIdx (fun l : Literal => l.var == v) f.flatten < f.flatten.length := hlt
  have := List.findIdx_getElem (xs := f.flatten) (p := fun l : Literal => l.var == v) (w := hlt')
  rw [varAt_eq f hlt]
  simp at this
  exact this

theorem firstOcc_inj (f : CNF) {i i' : Nat} (hi : i < f.flatten.length) (hi' : i' < f.flatten.length)
    (h : firstOcc f (varAt f i) = firstOcc f (varAt f i')) : varAt f i = varAt f i' := by
  rw [← (firstOcc_spec f hi).2.2, ← (firstOcc_spec f hi').2.2, h]

/-! ### Clauses -/

/-- Nonempty clauses. -/
def NonemptyClauses (f : CNF) : Prop := ∀ c ∈ f, c ≠ []

theorem kl_pos {f : CNF} (hf : NonemptyClauses f) {j : Nat} (hj : j < f.length) : 0 < kl f j := by
  rw [kl_of_lt f j hj]
  have := hf _ (List.getElem_mem hj)
  cases h : f[j] with
  | nil => exact absurd h this
  | cons a l => simp

theorem off_strict {f : CNF} (hf : NonemptyClauses f) {j j' : Nat} (hj' : j' < f.length) (h : j < j') :
    off f j < off f j' := by
  have h1 := off_mono f (show j + 1 ≤ j' by omega)
  have h2 := off_succ f j (by omega)
  have h3 := kl_pos hf (show j < f.length by omega)
  omega

theorem off_inj {f : CNF} (hf : NonemptyClauses f) {j j' : Nat} (hj : j < f.length) (hj' : j' < f.length)
    (h : off f j = off f j') : j = j' := by
  rcases Nat.lt_trichotomy j j' with hl | he | hl
  · have := off_strict hf hj' hl; omega
  · exact he
  · have := off_strict hf hj hl; omega

theorem oj_off {f : CNF} (hf : NonemptyClauses f) {j : Nat} (hj : j < f.length) : oj f (off f j) = j := by
  have := (occ_eq f j 0 hj (kl_pos hf hj)).1
  simpa using this

theorem occ_lt (f : CNF) {i : Nat} (hi : i < f.flatten.length) :
    oj f i < f.length ∧ off f (oj f i) ≤ i := by
  rw [flatten_length_nM] at hi
  obtain ⟨h1, _, h3⟩ := occ_spec f i hi
  exact ⟨h1, by omega⟩

/-! ### The vertices -/

theorem incRep_even (f : CNF) (i : Nat) : incRep f (2 * i) = 2 * firstOcc f (varAt f i) := by
  unfold incRep; rw [ite_eq_left (by omega), show 2 * i / 2 = i by omega]

theorem incRep_odd (f : CNF) (i : Nat) : incRep f (2 * i + 1) = 2 * off f (oj f i) + 1 := by
  unfold incRep; rw [ite_eq_right (by omega), show (2 * i + 1) / 2 = i by omega]

theorem dart_cases (d : Nat) : (∃ i, d = 2 * i) ∨ (∃ i, d = 2 * i + 1) := by
  rcases Nat.mod_two_eq_zero_or_one d with h | h
  · exact Or.inl ⟨d / 2, by omega⟩
  · exact Or.inr ⟨d / 2, by omega⟩

/-- **Two darts have the same vertex iff they have the same end.** -/
theorem incRep_eq_iff {f : CNF} (hf : NonemptyClauses f) {d d' : Nat} (hd : d < 2 * f.flatten.length)
    (hd' : d' < 2 * f.flatten.length) :
    incRep f d = incRep f d' ↔ halfEdgeEnd (incidenceGraph f) d = halfEdgeEnd (incidenceGraph f) d' := by
  rcases dart_cases d with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;> rcases dart_cases d' with ⟨i', rfl⟩ | ⟨i', rfl⟩
  · rw [incRep_even, incRep_even, halfEdgeEnd_even f (by omega), halfEdgeEnd_even f (by omega)]
    constructor
    · intro h; rw [firstOcc_inj f (i := i) (i' := i') (by omega) (by omega) (by omega)]
    · intro h; simp at h; rw [h]
  · rw [incRep_even, incRep_odd, halfEdgeEnd_even f (by omega), halfEdgeEnd_odd f (by omega)]
    constructor
    · intro h; omega
    · intro h; simp at h
  · rw [incRep_odd, incRep_even, halfEdgeEnd_odd f (by omega), halfEdgeEnd_even f (by omega)]
    constructor
    · intro h; omega
    · intro h; simp at h
  · rw [incRep_odd, incRep_odd, halfEdgeEnd_odd f (by omega), halfEdgeEnd_odd f (by omega)]
    constructor
    · intro h
      have := off_inj hf (occ_lt f (show i < f.flatten.length by omega)).1
        (occ_lt f (show i' < f.flatten.length by omega)).1 (by omega)
      rw [this]
    · intro h; simp at h; rw [h]

/-! ### Counting the darts at a vertex -/

theorem length_le_of_sub : ∀ (l l' : List Nat), l.Nodup → (∀ x ∈ l, x ∈ l') → l.length ≤ l'.length
  | [], _, _, _ => by simp
  | a :: t, l', hnd, h => by
    obtain ⟨h1, h2⟩ := List.nodup_cons.mp hnd
    have ha := h a (List.mem_cons_self ..)
    have := length_le_of_sub t (l'.erase a) h2 (fun x hx => by
      rw [List.mem_erase_of_ne (fun e => h1 (by rw [← e]; exact hx))]; exact h x (List.mem_cons_of_mem _ hx))
    rw [List.length_erase_of_mem ha] at this
    have : 0 < l'.length := List.length_pos_of_mem ha
    simp; omega

theorem countP_range_getD {α : Type} (P : α → Bool) (x : α) :
    ∀ l : List α, (List.range l.length).countP (fun i => P (l.getD i x)) = l.countP P
  | [] => by simp
  | a :: l => by
    rw [List.length_cons, List.range_succ_eq_map, List.countP_cons, List.countP_map, List.countP_cons]
    have := countP_range_getD P x l
    simp only [Function.comp_def, List.getD_cons_succ, List.getD_cons_zero] at this ⊢
    rw [this]

theorem countP_var (l : List Literal) (v : Nat) :
    l.countP (fun x => x.var == v) =
      (l.filter fun x => x.var == v && x.positive == true).length +
      (l.filter fun x => x.var == v && x.positive == false).length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.countP_cons, ih]
    by_cases hv : a.var = v <;> cases hp : a.positive <;> simp [hv, hp] <;> omega

theorem filter_length_map {l : List Nat} (hnd : l.Nodup) (g : Nat → Nat)
    (hg : ∀ a ∈ l, ∀ b ∈ l, g a = g b → a = b) {l' : List Nat} (h : ∀ x ∈ l, g x ∈ l') :
    l.length ≤ l'.length := by
  have hnd' : (l.map g).Nodup := nodup_map_of_injOn' g hnd hg
  have := length_le_of_sub (l.map g) l' hnd' (fun y hy => by
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy; exact h x hx)
  simpa using this

/-- **Every vertex of the incidence graph of a Definition 7 formula has at most three darts.** -/
theorem incDeg {f : CNF} (hf : BoundedOccurrence f) (r : Nat) : ((incDG f).darts r).length ≤ 3 := by
  have hne : NonemptyClauses f := fun c hc e => by rcases hf.1 c hc with h | h <;> rw [e] at h <;> simp at h
  obtain ⟨L, hLdef⟩ : ∃ L, L = (incDG f).darts r := ⟨_, rfl⟩
  rw [← hLdef]
  have hL : ∀ d ∈ L, d < 2 * f.flatten.length ∧ incRep f d = r := fun d hd => DG.mem_darts.mp (hLdef ▸ hd)
  have hnd : L.Nodup := hLdef ▸ DG.darts_nodup r
  rcases Nat.mod_two_eq_zero_or_one r with hr | hr
  · -- a variable vertex
    by_cases hex : ∃ d ∈ L, True
    · obtain ⟨d0, hd0, -⟩ := hex
      obtain ⟨hd0l, hd0r⟩ := hL d0 hd0
      have hd0e : d0 % 2 = 0 := by
        rcases dart_cases d0 with ⟨i, rfl⟩ | ⟨i, rfl⟩
        · omega
        · rw [incRep_odd] at hd0r; omega
      obtain ⟨i0, rfl⟩ : ∃ i0, d0 = 2 * i0 := ⟨d0 / 2, by omega⟩
      obtain ⟨v, hvdef⟩ : ∃ v, v = varAt f i0 := ⟨_, rfl⟩
      obtain ⟨I, hIdef⟩ : ∃ I, I = (List.range f.flatten.length).filter fun i => varAt f i == v := ⟨_, rfl⟩
      have hbound : L.length ≤ I.length := by
        refine filter_length_map hnd (fun d => d / 2) (fun a ha b hb h => ?_) (fun d hd => ?_)
        · obtain ⟨hal, har⟩ := hL a ha
          obtain ⟨hbl, hbr⟩ := hL b hb
          have hae : a % 2 = 0 := by
            rcases dart_cases a with ⟨i, rfl⟩ | ⟨i, rfl⟩
            · omega
            · rw [incRep_odd] at har; omega
          have hbe : b % 2 = 0 := by
            rcases dart_cases b with ⟨i, rfl⟩ | ⟨i, rfl⟩
            · omega
            · rw [incRep_odd] at hbr; omega
          omega
        · obtain ⟨hdl, hdr⟩ := hL d hd
          rcases dart_cases d with ⟨i, rfl⟩ | ⟨i, rfl⟩
          · rw [show 2 * i / 2 = i by omega]
            rw [hIdef]
            refine List.mem_filter.mpr ⟨List.mem_range.mpr (by omega), ?_⟩
            rw [incRep_even] at hdr hd0r
            have := firstOcc_inj f (show i < f.flatten.length by omega) (show i0 < f.flatten.length by omega)
              (by omega)
            simp [hvdef, this]
          · rw [incRep_odd] at hdr; omega
      have hI : I.length = (f.flatten.filter fun x => x.var == v && x.positive == true).length +
          (f.flatten.filter fun x => x.var == v && x.positive == false).length := by
        rw [hIdef, ← countP_var, ← countP_range_getD (fun x : Literal => x.var == v) ⟨0, true⟩ f.flatten,
          List.countP_eq_length_filter]
        rfl
      have h1 := hf.2.1 v
      have h2 := hf.2.2 v
      unfold occurrences at h1 h2
      omega
    · have : L = [] := List.eq_nil_iff_forall_not_mem.mpr fun d hd => hex ⟨d, hd, trivial⟩
      rw [this]; simp
  · -- a clause vertex
    by_cases hex : ∃ d ∈ L, True
    · obtain ⟨d0, hd0, -⟩ := hex
      obtain ⟨hd0l, hd0r⟩ := hL d0 hd0
      have hd0o : d0 % 2 = 1 := by
        rcases dart_cases d0 with ⟨i, rfl⟩ | ⟨i, rfl⟩
        · rw [incRep_even] at hd0r; omega
        · omega
      obtain ⟨i0, rfl⟩ : ∃ i0, d0 = 2 * i0 + 1 := ⟨d0 / 2, by omega⟩
      obtain ⟨j, hjdef⟩ : ∃ j, j = oj f i0 := ⟨_, rfl⟩
      have hj : j < f.length := hjdef ▸ (occ_lt f (show i0 < f.flatten.length by omega)).1
      have hbound : L.length ≤ (List.range (kl f j)).length := by
        refine filter_length_map hnd (fun d => d / 2 - off f j) (fun a ha b hb h => ?_) (fun d hd => ?_)
        · obtain ⟨hal, har⟩ := hL a ha
          obtain ⟨hbl, hbr⟩ := hL b hb
          rcases dart_cases a with ⟨ia, rfl⟩ | ⟨ia, rfl⟩
          · rw [incRep_even] at har; omega
          rcases dart_cases b with ⟨ib, rfl⟩ | ⟨ib, rfl⟩
          · rw [incRep_even] at hbr; omega
          rw [incRep_odd] at har hbr hd0r
          rw [← hjdef] at hd0r
          have ha' := off_inj hne (occ_lt f (show ia < f.flatten.length by omega)).1 hj (by omega)
          have hb' := off_inj hne (occ_lt f (show ib < f.flatten.length by omega)).1 hj (by omega)
          have h1 := (occ_lt f (show ia < f.flatten.length by omega)).2
          have h2 := (occ_lt f (show ib < f.flatten.length by omega)).2
          rw [ha'] at h1; rw [hb'] at h2
          rw [show (2 * ia + 1) / 2 = ia by omega, show (2 * ib + 1) / 2 = ib by omega] at h
          omega
        · obtain ⟨hdl, hdr⟩ := hL d hd
          rcases dart_cases d with ⟨i, rfl⟩ | ⟨i, rfl⟩
          · rw [incRep_even] at hdr; omega
          rw [incRep_odd] at hdr hd0r
          rw [← hjdef] at hd0r
          have hi := occ_lt f (show i < f.flatten.length by omega)
          have hij := off_inj hne hi.1 hj (by omega)
          rw [show (2 * i + 1) / 2 = i by omega]
          apply List.mem_range.mpr
          have := occ_spec f i (by rw [← flatten_length_nM]; omega)
          rw [hij] at this
          omega
      have h3 : kl f j ≤ 3 := by
        rw [kl_of_lt f j hj]
        rcases hf.1 _ (List.getElem_mem hj) with h | h <;> omega
      simp at hbound; omega
    · have : L = [] := List.eq_nil_iff_forall_not_mem.mpr fun d hd => hex ⟨d, hd, trivial⟩
      rw [this]; simp

/-- **The incidence graph of a Definition 7 formula satisfies the hypotheses of the search.** -/
theorem incOk {f : CNF} (hf : BoundedOccurrence f) : (incDG f).Ok := by
  have hne : NonemptyClauses f := fun c hc e => by rcases hf.1 c hc with h | h <;> rw [e] at h <;> simp at h
  refine ⟨?_, ?_, ?_, ?_, incDeg hf⟩
  · intro d hd
    show incRep f d < 2 * f.flatten.length
    have hd' : d < 2 * f.flatten.length := hd
    rcases dart_cases d with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · rw [incRep_even]; have := (firstOcc_spec f (show i < f.flatten.length by omega)).2.1; omega
    · rw [incRep_odd]; have := (occ_lt f (show i < f.flatten.length by omega)).2; omega
  · intro d hd
    show incRep f (incRep f d) = incRep f d
    have hd' : d < 2 * f.flatten.length := hd
    rcases dart_cases d with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · rw [incRep_even, incRep_even, (firstOcc_spec f (show i < f.flatten.length by omega)).2.2]
    · rw [incRep_odd, incRep_odd, oj_off hne (occ_lt f (show i < f.flatten.length by omega)).1]
  · intro d hd
    show incRep f d ≤ d
    have hd' : d < 2 * f.flatten.length := hd
    rcases dart_cases d with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · rw [incRep_even]; have := (firstOcc_spec f (show i < f.flatten.length by omega)).1; omega
    · rw [incRep_odd]; have := (occ_lt f (show i < f.flatten.length by omega)).2; omega
  · intro d hd
    show incRep f (pair d) ≠ incRep f d
    rcases dart_cases d with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · rw [show pair (2 * i) = 2 * i + 1 by unfold pair; rw [ite_eq_left (by omega)], incRep_odd, incRep_even]; omega
    · rw [show pair (2 * i + 1) = 2 * i by unfold pair; rw [ite_eq_right (by omega)]; omega, incRep_even, incRep_odd]
      omega

end STACS2027.Embed

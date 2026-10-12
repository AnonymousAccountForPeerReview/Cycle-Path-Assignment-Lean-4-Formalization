module

public import Outerplanar.OuterplanarConstructPolyRot
import Mathlib.Data.List.GetD
import Mathlib.Tactic

/-!
# The polygon embedding is a spherical outerplanar embedding

For a polygon with non-crossing chords (`PolyHyp es N`), the rotation system `polyRot` gives
a spherical outerplanar embedding (`PolyHyp.sphOuter`). The outer face is
`PolyHyp.outerFaceCond`; it remains to count:

* the faces, from below: a half-edge going up from `t` to `h` (`t < h`) lies on the face just
  above the chord `{t, h}`, a half-edge going down on the face just below its chord; the set
  of chords containing the chord of a half-edge (strictly above, resp. including it) is
  `chordLabel`, constant along the faces away from the outer face (`chordLabel_step`: the
  only argument where non-crossing is used). Labelling the outer half-edges by `none`, the
  label `polyLabel` is invariant under `face` (`polyLabel_face`), and the downward half-edges
  of the chords `{a, b}` with `b ≥ a + 2` have pairwise different labels: at least
  `1 + (|es| - (N - 1))` faces;
* the nodes: every vertex has a neighbour (`N` nodes);
* the components: the polygon sides connect every half-edge to the half-edge `0` (one
  component).

Then `2 · 1 + |es| ≤ N + (1 + |es| - (N - 1))` is the spherical inequality.
-/

@[expose] public section

namespace STACS2027

open Complexity Complexity.Planar PlanarGluing

/-- The chords (pairs `a < b` of neighbours) whose interval contains that of the half-edge
from `t` to `h`: strictly if the half-edge goes up (`t < h`), including itself otherwise. -/
def chordLabel (es : List (ℕ × ℕ)) (t h : ℕ) : ℕ → ℕ → Prop := fun a b =>
  Adjs es a b ∧ a < b ∧
    (if t < h then a ≤ t ∧ h ≤ b ∧ ¬ (a = t ∧ b = h) else a ≤ h ∧ t ≤ b)

/-- The half-edge from `t` to `h` lies on the outer face of the polygon. -/
def PolyOuter (N t h : ℕ) : Prop := t = h + 1 ∨ (t = 0 ∧ h = N - 1)

open Classical in
/-- The face label of a half-edge of the polygon. -/
noncomputable def polyLabel (es : List (ℕ × ℕ)) (N : ℕ) (d : Fin (2 * es.length)) :
    Option (ℕ → ℕ → Prop) :=
  if PolyOuter N (dtail es d.val) (dhead es d.val) then none
  else some (chordLabel es (dtail es d.val) (dhead es d.val))

/-- A chord whose ends differ by at least two (not a side of the polygon). -/
def isLong (e : ℕ × ℕ) : Bool := decide (e.1 + 2 ≤ e.2 ∨ e.2 + 2 ≤ e.1)

/-- The half-edge of edge `i` from its larger to its smaller end. -/
def downDart (es : List (ℕ × ℕ)) (i : Fin es.length) : Fin (2 * es.length) :=
  ⟨if es[i.val].2 < es[i.val].1 then 2 * i.val else 2 * i.val + 1, by split_ifs <;> omega⟩

theorem downDart_ends (es : List (ℕ × ℕ)) (i : Fin es.length) :
    dtail es (downDart es i).val = max es[i.val].1 es[i.val].2 ∧
      dhead es (downDart es i).val = min es[i.val].1 es[i.val].2 := by
  have hg : es.getD i.val (0, 0) = es[i.val] := List.getD_eq_getElem _ _ i.isLt
  have hv : (downDart es i).val =
      if es[i.val].2 < es[i.val].1 then 2 * i.val else 2 * i.val + 1 := rfl
  rw [hv]
  split_ifs with hc
  · rw [dtail_even es (by omega), dhead_even es (by omega), show 2 * i.val / 2 = i.val by omega,
      hg]
    omega
  · rw [dtail_odd es (by omega), dhead_odd es (by omega),
      show (2 * i.val + 1) / 2 = i.val by omega, hg]
    omega

namespace PolyHyp

variable {es : List (ℕ × ℕ)} {N : ℕ} (h : PolyHyp es N)
include h

/-- **The face step away from the outer face keeps the chord label.** The half-edge from `u`
to `w` is followed on its face by the half-edge from `w` to `x`, the neighbour of `w` just
before `u` in the counterclockwise order at `w`. -/
theorem chordLabel_step {u w x : ℕ} (hu : Adjs es w u) (hx : Adjs es w x)
    (hlt : pkey N w x < pkey N w u)
    (hbetween : ∀ z, Adjs es w z → pkey N w x < pkey N w z → pkey N w z < pkey N w u → False) :
    chordLabel es w x = chordLabel es u w := by
  obtain ⟨hw, hu', hwu⟩ := h.adjs_bounds hu
  obtain ⟨-, hx', hwx⟩ := h.adjs_bounds hx
  have hnc := h.noncross
  have hzb : ∀ z, Adjs es w z → z < N := fun z hz => (h.adjs_bounds hz).2.1
  funext a b
  apply propext
  unfold chordLabel
  rcases Nat.lt_or_gt_of_ne hwu with hwu' | hwu'
  · -- the half-edge goes down, from `u > w` to `w`
    have hkx : w < x ∧ x < u := by unfold pkey at hlt; split_ifs at hlt <;> omega
    have hb : ∀ z, Adjs es w z → x < z → z < u → False := fun z hz h1 h2 =>
      hbetween z hz (by unfold pkey; split_ifs <;> omega)
        (by unfold pkey; split_ifs <;> omega)
    simp only [hkx.1, show ¬ u < w by omega, ↓reduceIte]
    constructor
    · rintro ⟨hab, hab', ha, hb', hne⟩
      refine ⟨hab, hab', ha, ?_⟩
      by_contra hbu
      rcases Nat.lt_or_ge a w with haw | haw
      · exact hnc a w b u haw (by omega) (by omega) ⟨hab, hu⟩
      · have haw' : a = w := by omega
        subst haw'
        exact hb b hab (by omega) (by omega)
    · rintro ⟨hab, hab', ha, hb'⟩
      exact ⟨hab, hab', ha, by omega, by omega⟩
  · -- the half-edge goes up, from `u < w` to `w`
    rcases Nat.lt_or_gt_of_ne hwx with hwx' | hwx'
    · -- the next half-edge goes up, to `x > w`
      have hb1 : ∀ z, Adjs es w z → x < z → False := fun z hz h1 =>
        hbetween z hz (by unfold pkey; split_ifs <;> omega)
          (by have := hzb z hz; unfold pkey; split_ifs <;> omega)
      have hb2 : ∀ z, Adjs es w z → z < u → False := fun z hz h1 =>
        hbetween z hz (by unfold pkey; split_ifs <;> omega)
          (by unfold pkey; split_ifs <;> omega)
      simp only [show w < x by omega, show u < w by omega, ↓reduceIte]
      constructor
      · rintro ⟨hab, hab', ha, hb', hne⟩
        refine ⟨hab, hab', ?_, by omega, by omega⟩
        by_contra hau
        rcases Nat.lt_or_ge a w with haw | haw
        · exact hnc u a w b (by omega) haw (by omega) ⟨hu.symm, hab⟩
        · have haw' : a = w := by omega
          subst haw'
          exact hb1 b hab (by omega)
      · rintro ⟨hab, hab', ha, hb', hne⟩
        refine ⟨hab, hab', by omega, ?_, by omega⟩
        by_contra hbx
        rcases Nat.lt_or_ge w b with hwb | hwb
        · exact hnc a w b x (by omega) hwb (by omega) ⟨hab, hx⟩
        · have hbw : b = w := by omega
          subst hbw
          exact hb2 a hab.symm (by omega)
    · -- the next half-edge goes down, to `x < u`
      have hxu : x < u := by unfold pkey at hlt; split_ifs at hlt <;> omega
      have hb : ∀ z, Adjs es w z → x < z → z < u → False := fun z hz h1 h2 =>
        hbetween z hz (by unfold pkey; split_ifs <;> omega)
          (by unfold pkey; split_ifs <;> omega)
      simp only [show ¬ w < x by omega, show u < w by omega, ↓reduceIte]
      constructor
      · rintro ⟨hab, hab', ha, hb'⟩
        exact ⟨hab, hab', by omega, hb', by omega⟩
      · rintro ⟨hab, hab', ha, hb', hne⟩
        refine ⟨hab, hab', ?_, hb'⟩
        by_contra hax
        rcases Nat.lt_or_ge w b with hwb | hwb
        · exact hnc x a w b (by omega) (by omega) hwb ⟨hx.symm, hab⟩
        · have hbw : b = w := by omega
          subst hbw
          exact hb a hab.symm (by omega) (by omega)

theorem pkey_succ {w : ℕ} (hw : w < N) {u : ℕ} (hu : PolyOuter N u w) : pkey N w u = 1 := by
  have := h.two_le
  unfold PolyOuter at hu
  unfold pkey
  split_ifs <;> omega

omit h in
theorem polyOuter_of_key {w u : ℕ} (hw : w < N) (hu : u < N) (hk : pkey N w u = 1) :
    PolyOuter N u w := by
  unfold PolyOuter
  unfold pkey at hk
  split_ifs at hk <;> omega

theorem key_of_polyOuter {w x : ℕ} (hw : w < N) (hx : PolyOuter N w x) :
    pkey N w x = N - 1 := by
  have := h.two_le
  unfold PolyOuter at hx
  unfold pkey
  split_ifs <;> omega

/-- **The face labels are invariant.** -/
theorem polyLabel_face (d : Fin (2 * es.length)) :
    polyLabel es N (h.polyMap.face d) = polyLabel es N d := by
  have hd := adjs_dart es d.isLt
  have hwu : Adjs es (dhead es d.val) (dtail es d.val) := hd.symm
  obtain ⟨hw, hu, -⟩ := h.adjs_bounds hwu
  have hk := h.pkey_mem hwu
  have hpm := rprev_mem (nbrKeys_nodup es N _) hk
  have ht : dtail es (h.polyMap.face d).val = dhead es d.val := RotSystem.dtail_face _ _ d
  have hh : dhead es (h.polyMap.face d).val =
      pdec N (dhead es d.val) (rprev (nbrKeys es N (dhead es d.val))
        (pkey N (dhead es d.val) (dtail es d.val))) := RotSystem.dhead_face _ _ d
  have hxk : pkey N (dhead es d.val) (dhead es (h.polyMap.face d).val) =
      rprev (nbrKeys es N (dhead es d.val)) (pkey N (dhead es d.val) (dtail es d.val)) := by
    rw [hh, pkey_pdec_mem hw hpm]
  have hxadj : Adjs es (dhead es d.val) (dhead es (h.polyMap.face d).val) := by
    rw [hh]; exact pdec_adjs hpm
  unfold polyLabel
  rw [ht]
  by_cases ho : PolyOuter N (dtail es d.val) (dhead es d.val)
  · have h1 := h.pkey_succ hw ho
    have hfo : PolyOuter N (dhead es d.val) (dhead es (h.polyMap.face d).val) := by
      rw [hh, h1, h.rprev_one hw]
      have := h.two_le
      unfold PolyOuter pdec
      split_ifs <;> omega
    simp only [ho, hfo, ↓reduceIte]
  · have hk1 : pkey N (dhead es d.val) (dtail es d.val) ≠ 1 :=
      fun he => ho (polyOuter_of_key hw hu he)
    obtain ⟨-, hlt, hmax⟩ := h.rprev_nonwrap hw hk hk1
    have hfo : ¬ PolyOuter N (dhead es d.val) (dhead es (h.polyMap.face d).val) := by
      intro hfo
      have hkx := h.key_of_polyOuter hw hfo
      rw [hxk] at hkx
      have := rnext_rprev (nbrKeys_nodup es N _) hk
      rw [hkx, h.rnext_last hw] at this
      exact hk1 this.symm
    simp only [ho, hfo, ↓reduceIte]
    rw [h.chordLabel_step hwu hxadj (by rw [hxk]; exact hlt) (fun z hz h1 h2 => by
      rw [hxk] at h1
      have := hmax _ (h.pkey_mem hz) h2
      omega)]

/-! ### Counting -/

/-- The short edges are sides of the polygon: at most `N - 1` of them. -/
theorem short_count :
    ((List.finRange es.length).filter fun i => !isLong es[i.val]).length ≤ N - 1 := by
  have hm : ∀ i : Fin es.length, i ∈ (List.finRange es.length).filter (fun i => !isLong es[i.val]) →
      es[i.val].1 ≠ es[i.val].2 ∧ es[i.val].1 < N ∧ es[i.val].2 < N ∧
        ¬ (es[i.val].1 + 2 ≤ es[i.val].2 ∨
        es[i.val].2 + 2 ≤ es[i.val].1) := by
    intro i hi
    have hl := (List.mem_filter.mp hi).2
    simp only [isLong, Bool.not_eq_true', decide_eq_false_iff_not] at hl
    have hmem := List.getElem_mem i.isLt
    exact ⟨h.simple.1 _ hmem, (h.lt _ hmem).1, (h.lt _ hmem).2, hl⟩
  have hnd : (((List.finRange es.length).filter fun i => !isLong es[i.val]).map
      fun i => min es[i.val].1 es[i.val].2).Nodup := by
    apply List.Nodup.map_on _ ((List.nodup_finRange _).filter _)
    intro i hi j hj he
    obtain ⟨hi1, -, -, hi2⟩ := hm i hi
    obtain ⟨hj1, -, -, hj2⟩ := hm j hj
    apply Fin.ext
    apply h.simple.2 _ _ i.isLt j.isLt
    rw [List.getD_eq_getElem _ _ i.isLt, List.getD_eq_getElem _ _ j.isLt]
    have hi' : es[i.val] = (es[i.val].1, es[i.val].2) := rfl
    have hj' : es[j.val] = (es[j.val].1, es[j.val].2) := rfl
    rw [hi', hj']
    simp only [Prod.mk.injEq]
    omega
  have hsub : ∀ x ∈ (((List.finRange es.length).filter fun i => !isLong es[i.val]).map
      fun i => min es[i.val].1 es[i.val].2), x ∈ List.range (N - 1) := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    obtain ⟨h1, h2, h3, h4⟩ := hm i hi
    rw [List.mem_range]
    omega
  have := hnd.length_le_of_subset hsub
  simpa using this

omit h in
theorem long_add_short :
    ((List.finRange es.length).filter fun i => isLong es[i.val]).length +
      ((List.finRange es.length).filter fun i => !isLong es[i.val]).length = es.length := by
  have := List.length_eq_length_filter_add (l := List.finRange es.length)
    (fun i => isLong es[i.val])
  rw [List.length_finRange] at this
  exact this.symm

omit h in
theorem downDart_label {i : Fin es.length} (hi : isLong es[i.val] = true) :
    polyLabel es N (downDart es i) = some (chordLabel es (max es[i.val].1 es[i.val].2)
      (min es[i.val].1 es[i.val].2)) := by
  obtain ⟨h1, h2⟩ := downDart_ends es i
  simp only [isLong, decide_eq_true_eq] at hi
  have hno : ¬ PolyOuter N (max es[i.val].1 es[i.val].2) (min es[i.val].1 es[i.val].2) := by
    unfold PolyOuter; omega
  unfold polyLabel
  rw [h1, h2]
  simp only [hno, ↓reduceIte]

/-- **The faces.** -/
theorem faces_ge : 1 + ((List.finRange es.length).filter fun i => isLong es[i.val]).length ≤
    cycleCount h.polyMap.face := by
  have h2 := h.two_le
  set L := (List.finRange es.length).filter fun i => isLong es[i.val]
  have hout : polyLabel es N (h.outerDart 0 (by omega)) = none := by
    have : PolyOuter N (dtail es (h.outerDart 0 (by omega)).val)
        (dhead es (h.outerDart 0 (by omega)).val) := by
      rw [dtail_outerDart, dhead_outerDart]
      unfold PolyOuter polySucc pdec
      split_ifs <;> omega
    unfold polyLabel
    simp only [this, ↓reduceIte]
  have hinj : ∀ i ∈ L, ∀ j ∈ L, polyLabel es N (downDart es i) =
      polyLabel es N (downDart es j) → i = j := by
    intro i hi j hj he
    have hi' := (List.mem_filter.mp hi).2
    have hj' := (List.mem_filter.mp hj).2
    rw [downDart_label hi', downDart_label hj', Option.some.injEq] at he
    have hai := adjs_dart es (downDart es i).isLt
    have haj := adjs_dart es (downDart es j).isLt
    obtain ⟨hti, hhi⟩ := downDart_ends es i
    obtain ⟨htj, hhj⟩ := downDart_ends es j
    rw [hti, hhi] at hai
    rw [htj, hhj] at haj
    have hn1 := h.simple.1 _ (List.getElem_mem i.isLt)
    have hn2 := h.simple.1 _ (List.getElem_mem j.isLt)
    have e1 := iff_of_eq <| congrFun (congrFun he (min es[i.val].1 es[i.val].2))
      (max es[i.val].1 es[i.val].2)
    have e2 := iff_of_eq <| congrFun (congrFun he (min es[j.val].1 es[j.val].2))
      (max es[j.val].1 es[j.val].2)
    unfold chordLabel at e1 e2
    simp only [show ¬ max es[i.val].1 es[i.val].2 < min es[i.val].1 es[i.val].2 by omega,
      show ¬ max es[j.val].1 es[j.val].2 < min es[j.val].1 es[j.val].2 by omega,
      ↓reduceIte] at e1 e2
    have f1 := e1.mp ⟨hai.symm, by omega, le_refl _, le_refl _⟩
    have f2 := e2.mpr ⟨haj.symm, by omega, le_refl _, le_refl _⟩
    apply Fin.ext
    apply h.simple.2 _ _ i.isLt j.isLt
    rw [List.getD_eq_getElem _ _ i.isLt, List.getD_eq_getElem _ _ j.isLt]
    have hi'' : es[i.val] = (es[i.val].1, es[i.val].2) := rfl
    have hj'' : es[j.val] = (es[j.val].1, es[j.val].2) := rfl
    rw [hi'', hj'']
    simp only [Prod.mk.injEq]
    omega
  have hnd : ((h.outerDart 0 (by omega) :: L.map (downDart es)).map (polyLabel es N)).Nodup := by
    rw [List.map_cons, List.nodup_cons, List.map_map]
    refine ⟨?_, List.Nodup.map_on hinj ((List.nodup_finRange _).filter _)⟩
    rw [hout]
    intro hm
    obtain ⟨i, hi, he⟩ := List.mem_map.mp hm
    rw [Function.comp_apply, downDart_label (List.mem_filter.mp hi).2] at he
    exact Option.some_ne_none _ he
  have := cycleCount_ge h.polyMap.face (polyLabel es N) h.polyLabel_face _ hnd
  simpa [Nat.add_comm] using this

/-- The half-edge from `v` to the next vertex on the circle. -/
noncomputable def succDart (v : ℕ) (hv : v < N) : Fin (2 * es.length) :=
  ⟨findDart es v (polySucc N v), (findDart_spec (h.polySucc_adjs hv).symm).1⟩

/-- **The nodes.** -/
theorem nodes_ge : N ≤ cycleCount h.polyMap.node := by
  have hnd : (((List.finRange N).map fun v => h.succDart v.val v.isLt).map
      fun d => dtail es d.val).Nodup := by
    rw [List.map_map]
    have he : ((fun d : Fin (2 * es.length) => dtail es d.val) ∘
        fun v : Fin N => h.succDart v.val v.isLt) = Fin.val := by
      funext v
      exact (findDart_spec (h.polySucc_adjs v.isLt).symm).2.1
    rw [he]
    exact (List.nodup_finRange N).map Fin.val_injective
  have := h.polyRot.nodes_ge h.simple _ hnd
  rw [List.length_map, List.length_finRange] at this
  exact this

/-- The half-edge from `v` to the previous vertex on the circle. -/
noncomputable def predDart (v : ℕ) (hv : v < N) : Fin (2 * es.length) :=
  ⟨findDart es v (polyPred N v), (findDart_spec (pdec_adjs (h.last_mem hv))).1⟩

theorem linked_predDart : ∀ v (hv : v < N) (d : Fin (2 * es.length)), dtail es d.val = v →
    LinkedPath h.polyMap d (h.predDart 0 (by omega)) := by
  have h2 := h.two_le
  have hsame : ∀ d d' : Fin (2 * es.length), dtail es d.val = dtail es d'.val →
      LinkedPath h.polyMap d d' := fun d d' he =>
    nodeOrbit_linked _ ((h.polyRot.nodeCond h.simple d d').mpr (by
      rw [halfEdgeEnd_eq_dtail es d.isLt, halfEdgeEnd_eq_dtail es d'.isLt, he]))
  intro v
  induction v with
  | zero =>
    intro hv d hd
    exact hsame _ _ (by rw [hd]; exact (findDart_spec (pdec_adjs (h.last_mem hv))).2.1.symm)
  | succ v ih =>
    intro hv d hd
    have hp : dtail es (h.predDart (v + 1) hv).val = v + 1 :=
      (findDart_spec (pdec_adjs (h.last_mem hv))).2.1
    have hq : dhead es (h.predDart (v + 1) hv).val = v := by
      show dhead es (findDart es (v + 1) (pdec N (v + 1) (N - 1))) = v
      rw [(findDart_spec (pdec_adjs (h.last_mem hv))).2.2]
      unfold pdec; split_ifs <;> omega
    have h1 := hsame d (h.predDart (v + 1) hv) (hd.trans hp.symm)
    have h2 : LinkedPath h.polyMap (h.predDart (v + 1) hv)
        (h.polyMap.edge (h.predDart (v + 1) hv)) := LinkedPath.step _ (Or.inl rfl)
    have h3 := ih (by omega) (h.polyMap.edge (h.predDart (v + 1) hv))
      (by rw [polyMap, RotSystem.dtail_edge, hq])
    exact h1.trans (h2.trans h3)

/-- **One component.** -/
theorem components_le : h.polyMap.componentCount ≤ 1 := by
  have h2 := h.two_le
  have hm : 0 < es.length := by
    obtain ⟨d, hd, -⟩ := h.cyc 0 (by omega)
    omega
  have hc := componentCount_le h.polyMap (fun x => x.val == 0) (by
    intro x hx
    have hx0 : x.val ≠ 0 := by simpa using hx
    refine ⟨⟨0, by omega⟩, by simp only; omega, ?_⟩
    have h1 := h.linked_predDart _ (h.adjs_bounds (adjs_dart es x.isLt)).1 x rfl
    have h0 := h.linked_predDart (dtail es 0)
      (h.adjs_bounds (adjs_dart es (d := 0) (by omega))).1 ⟨0, by omega⟩ rfl
    exact h1.trans h0.symm)
  refine hc.trans ?_
  rw [countP_finRange_val (fun d => d == 0)]
  have := List.nodup_iff_count_le_one.mp (List.nodup_range (n := 2 * es.length)) 0
  rwa [List.count] at this

/-- **The polygon embedding.** A polygon with non-crossing chords has a spherical
outerplanar embedding. -/
theorem sphOuter : SphOuter es := by
  have hs := h.short_count
  have hl := long_add_short (es := es)
  have h2 := h.two_le
  exact h.polyRot.sphOuter h.simple N _ 1 h.nodes_ge h.faces_ge h.components_le (by omega)
    h.outerFaceCond

end PolyHyp

end STACS2027

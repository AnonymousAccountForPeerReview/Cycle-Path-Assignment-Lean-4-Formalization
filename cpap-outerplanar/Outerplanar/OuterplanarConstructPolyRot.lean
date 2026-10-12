module

public import Outerplanar.OuterplanarConstructRot
public import Complexity.Planar.Rot
import Mathlib.Tactic

/-!
# The rotation system of a polygon with chords

The vertices `0, …, N - 1` are placed counterclockwise on a circle, the edges drawn as
straight chords (`PolyHyp`: every polygon side `{i, i + 1}`, `{0, N - 1}` is an edge, and no
two edges cross). At a vertex `w` the neighbours are ordered counterclockwise, by their
offset `pkey N w z` (`z - w` modulo `N`); `nbrKeys es N w` is the sorted list of the offsets
of the neighbours of `w`, and the rotation `polyRot` takes the next offset in it
(`rnext`, `rprev` of the foundation).

At every vertex the smallest offset is `1` (the next vertex `polySucc N w` on the circle)
and the largest is `N - 1` (the previous vertex `polyPred N w`); hence the half-edges
`outerDart w` from `polySucc N w` to `w` form one face, `w ↦ polyPred N w`
(`face_outerDart`), which passes through every vertex: the outer face. Away from this
corner the face step `rprev` is the predecessor in the sorted list, with no offset strictly
between (`rprev_nonwrap`).
-/

@[expose] public section

namespace STACS2027

open Complexity Complexity.Planar PlanarGluing

/-! ### Offsets on the circle -/

/-- The counterclockwise offset of `z` seen from `w`, on a circle of `N` vertices. -/
def pkey (N w z : ℕ) : ℕ := if w < z then z - w else z + N - w

/-- The vertex at offset `r` from `w`. -/
def pdec (N w r : ℕ) : ℕ := if w + r < N then w + r else w + r - N

theorem pdec_pkey {N w z : ℕ} (hw : w < N) (hz : z < N) :
    pdec N w (pkey N w z) = z := by
  unfold pkey pdec; split_ifs <;> omega

theorem pkey_pdec {N w r : ℕ} (hw : w < N) (hr0 : 0 < r) (hr : r < N) :
    pkey N w (pdec N w r) = r := by
  unfold pkey pdec; split_ifs <;> omega

theorem pkey_pos {N w z : ℕ} (hw : w < N) : 0 < pkey N w z := by
  unfold pkey; split_ifs <;> omega

theorem pkey_lt {N w z : ℕ} (hw : w < N) (hz : z < N) (hne : z ≠ w) : pkey N w z < N := by
  unfold pkey; split_ifs <;> omega

theorem pdec_lt {N w r : ℕ} (hw : w < N) (hr : r < N) : pdec N w r < N := by
  unfold pdec; split_ifs <;> omega

/-! ### Polygons with non-crossing chords -/

/-- The hypotheses of the polygon embedding: `N ≥ 2` vertices `0, …, N - 1`, a simple edge
list on them containing every side of the polygon, and no two crossing edges. -/
structure PolyHyp (es : List (ℕ × ℕ)) (N : ℕ) : Prop where
  two_le : 2 ≤ N
  lt : ∀ e ∈ es, e.1 < N ∧ e.2 < N
  simple : SimpleList es
  cyc : ∀ i, i + 1 < N → Adjs es i (i + 1)
  close : Adjs es 0 (N - 1)
  noncross : ∀ a b c d, a < b → b < c → c < d → ¬ (Adjs es a c ∧ Adjs es b d)

open Classical in
/-- The sorted list of the offsets of the neighbours of `w`. -/
noncomputable def nbrKeys (es : List (ℕ × ℕ)) (N w : ℕ) : List ℕ :=
  (List.range N).filter fun r => decide (0 < r ∧ Adjs es w (pdec N w r))

/-- The next vertex on the circle. -/
def polySucc (N w : ℕ) : ℕ := pdec N w 1

/-- The previous vertex on the circle. -/
def polyPred (N w : ℕ) : ℕ := pdec N w (N - 1)

theorem mem_nbrKeys {es : List (ℕ × ℕ)} {N w r : ℕ} :
    r ∈ nbrKeys es N w ↔ r < N ∧ 0 < r ∧ Adjs es w (pdec N w r) := by
  simp [nbrKeys]

theorem nbrKeys_sorted (es : List (ℕ × ℕ)) (N w : ℕ) : (nbrKeys es N w).Pairwise (· < ·) :=
  List.Pairwise.filter _ List.pairwise_lt_range

theorem nbrKeys_nodup (es : List (ℕ × ℕ)) (N w : ℕ) : (nbrKeys es N w).Nodup :=
  (nbrKeys_sorted es N w).imp (fun hab => Nat.ne_of_lt hab)

theorem pdec_adjs {es : List (ℕ × ℕ)} {N w r : ℕ} (hr : r ∈ nbrKeys es N w) :
    Adjs es w (pdec N w r) :=
  (mem_nbrKeys.mp hr).2.2

theorem pkey_pdec_mem {es : List (ℕ × ℕ)} {N w r : ℕ} (hw : w < N) (hr : r ∈ nbrKeys es N w) :
    pkey N w (pdec N w r) = r :=
  pkey_pdec hw (mem_nbrKeys.mp hr).2.1 (mem_nbrKeys.mp hr).1

theorem key_bounds {es : List (ℕ × ℕ)} {N w r : ℕ} (hr : r ∈ nbrKeys es N w) :
    1 ≤ r ∧ r ≤ N - 1 := by
  have := mem_nbrKeys.mp hr; omega

/-- In a strictly increasing list, positions are ordered as the entries. -/
theorem sorted_index_lt {l : List ℕ} (hl : l.Pairwise (· < ·)) {i j : ℕ} (hi : i < l.length)
    (hj : j < l.length) (hlt : l[i] < l[j]) : i < j := by
  rcases Nat.lt_trichotomy i j with h' | h' | h'
  · exact h'
  · subst h'; omega
  · have := List.pairwise_iff_getElem.mp hl j i hj hi h'; omega

namespace PolyHyp

variable {es : List (ℕ × ℕ)} {N : ℕ} (h : PolyHyp es N)
include h

theorem adjs_bounds {u v : ℕ} (huv : Adjs es u v) : u < N ∧ v < N ∧ u ≠ v := by
  rcases (adjs_iff es u v).mp huv with hm | hm
  · exact ⟨(h.lt _ hm).1, (h.lt _ hm).2, h.simple.1 _ hm⟩
  · exact ⟨(h.lt _ hm).2, (h.lt _ hm).1, fun he => h.simple.1 _ hm he.symm⟩

theorem pkey_mem {w z : ℕ} (hz : Adjs es w z) : pkey N w z ∈ nbrKeys es N w := by
  obtain ⟨hw, hz', hne⟩ := h.adjs_bounds hz
  rw [mem_nbrKeys, pdec_pkey hw hz']
  exact ⟨pkey_lt hw hz' (Ne.symm hne), pkey_pos hw, hz⟩

theorem one_mem {w : ℕ} (hw : w < N) : 1 ∈ nbrKeys es N w := by
  have h2 := h.two_le
  rw [mem_nbrKeys]
  refine ⟨by omega, by omega, ?_⟩
  unfold pdec
  split_ifs with hc
  · exact h.cyc w hc
  · rw [show w + 1 - N = 0 by omega, show w = N - 1 by omega]; exact h.close.symm

theorem last_mem {w : ℕ} (hw : w < N) : N - 1 ∈ nbrKeys es N w := by
  have h2 := h.two_le
  rw [mem_nbrKeys]
  refine ⟨by omega, by omega, ?_⟩
  unfold pdec
  split_ifs with hc
  · rw [show w = 0 by omega, Nat.zero_add]; exact h.close
  · rw [show w + (N - 1) - N = w - 1 by omega]
    have := h.cyc (w - 1) (by omega)
    rw [show w - 1 + 1 = w by omega] at this
    exact this.symm

theorem nbrKeys_pos (w : ℕ) (hw : w < N) : 0 < (nbrKeys es N w).length :=
  List.length_pos_of_mem (h.one_mem hw)

theorem first_eq {w : ℕ} (hw : w < N) : (nbrKeys es N w)[0]'(h.nbrKeys_pos w hw) = 1 := by
  obtain ⟨p, hp, he⟩ := List.getElem_of_mem (h.one_mem hw)
  have hb := key_bounds (List.getElem_mem (h.nbrKeys_pos w hw))
  rcases Nat.eq_zero_or_pos p with h0 | h0
  · subst h0; exact he
  · have := List.pairwise_iff_getElem.mp (nbrKeys_sorted es N w) 0 p (h.nbrKeys_pos w hw) hp h0
    omega

theorem last_eq {w : ℕ} (hw : w < N) :
    (nbrKeys es N w)[(nbrKeys es N w).length - 1]'(by have := h.nbrKeys_pos w hw; omega) =
      N - 1 := by
  have hpos := h.nbrKeys_pos w hw
  obtain ⟨p, hp, he⟩ := List.getElem_of_mem (h.last_mem hw)
  have hb := key_bounds (List.getElem_mem
    (show (nbrKeys es N w).length - 1 < (nbrKeys es N w).length by omega))
  rcases Nat.lt_or_ge p ((nbrKeys es N w).length - 1) with hlt | hge
  · have := List.pairwise_iff_getElem.mp (nbrKeys_sorted es N w) p _ hp (by omega) hlt
    omega
  · have : p = (nbrKeys es N w).length - 1 := by omega
    subst this; exact he

/-- At the smallest offset the face step wraps around to the largest. -/
theorem rprev_one {w : ℕ} (hw : w < N) : rprev (nbrKeys es N w) 1 = N - 1 := by
  have hpos := h.nbrKeys_pos w hw
  conv => lhs; rw [← h.first_eq hw]
  rw [rprev_getElem (nbrKeys_nodup es N w)]
  have he : (0 + (nbrKeys es N w).length - 1) % (nbrKeys es N w).length =
      (nbrKeys es N w).length - 1 := by
    rw [Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
  simp only [he]
  exact h.last_eq hw

/-- At the largest offset the node step wraps around to the smallest. -/
theorem rnext_last {w : ℕ} (hw : w < N) : rnext (nbrKeys es N w) (N - 1) = 1 := by
  have hpos := h.nbrKeys_pos w hw
  conv => lhs; rw [← h.last_eq hw]
  rw [rnext_getElem (nbrKeys_nodup es N w)]
  have he : ((nbrKeys es N w).length - 1 + 1) % (nbrKeys es N w).length = 0 := by
    rw [Nat.sub_add_cancel (by omega), Nat.mod_self]
  simp only [he]
  exact h.first_eq hw

/-- Away from the smallest offset, `rprev` is the next smaller offset of a neighbour. -/
theorem rprev_nonwrap {w r : ℕ} (hw : w < N) (hr : r ∈ nbrKeys es N w) (h1 : r ≠ 1) :
    rprev (nbrKeys es N w) r ∈ nbrKeys es N w ∧ rprev (nbrKeys es N w) r < r ∧
      ∀ t ∈ nbrKeys es N w, t < r → t ≤ rprev (nbrKeys es N w) r := by
  have hs := nbrKeys_sorted es N w
  have hpos := h.nbrKeys_pos w hw
  obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem hr
  have hp0 : 0 < p := by
    rcases Nat.eq_zero_or_pos p with h0 | h0
    · subst h0; exact absurd (h.first_eq hw) h1
    · exact h0
  rw [rprev_getElem (nbrKeys_nodup es N w)]
  have he : (p + (nbrKeys es N w).length - 1) % (nbrKeys es N w).length = p - 1 := by
    rw [show p + (nbrKeys es N w).length - 1 = (p - 1) + (nbrKeys es N w).length by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  simp only [he]
  refine ⟨List.getElem_mem _, List.pairwise_iff_getElem.mp hs _ _ _ hp (by omega), ?_⟩
  intro t ht htl
  obtain ⟨q, hq, rfl⟩ := List.getElem_of_mem ht
  have hqp := sorted_index_lt hs hq hp htl
  rcases Nat.lt_or_ge q (p - 1) with hlt | hge
  · exact Nat.le_of_lt (List.pairwise_iff_getElem.mp hs _ _ hq (by omega) hlt)
  · have hq' : q = p - 1 := by omega
    subst hq'
    exact Nat.le_refl _

/-- The rotation system of the polygon: neighbours in counterclockwise order. -/
noncomputable def polyRot : RotSystem es where
  rot w u := pdec N w (rnext (nbrKeys es N w) (pkey N w u))
  rotInv w u := pdec N w (rprev (nbrKeys es N w) (pkey N w u))
  rot_adj w u hu := pdec_adjs (rnext_mem (nbrKeys_nodup es N w) (h.pkey_mem hu))
  rotInv_adj w u hu := pdec_adjs (rprev_mem (nbrKeys_nodup es N w) (h.pkey_mem hu))
  rot_rotInv w u hu := by
    obtain ⟨hw, hu', hne⟩ := h.adjs_bounds hu
    have hm := rprev_mem (nbrKeys_nodup es N w) (h.pkey_mem hu)
    rw [pkey_pdec_mem hw hm, rnext_rprev (nbrKeys_nodup es N w) (h.pkey_mem hu),
      pdec_pkey hw hu']
  reach w u u' hu hu' := by
    obtain ⟨hw, hu1, hne⟩ := h.adjs_bounds hu
    obtain ⟨-, hu1', hne'⟩ := h.adjs_bounds hu'
    have key : ∀ j r, r ∈ nbrKeys es N w →
        iterate (fun u => pdec N w (rnext (nbrKeys es N w) (pkey N w u))) j (pdec N w r) =
          pdec N w (iterate (rnext (nbrKeys es N w)) j r) := by
      intro j
      induction j with
      | zero => intro r _; rfl
      | succ j ih =>
        intro r hr
        simp only [iterate]
        rw [pkey_pdec_mem hw hr]
        exact ih _ (rnext_mem (nbrKeys_nodup es N w) hr)
    obtain ⟨j, hj⟩ := rnext_reach (nbrKeys_nodup es N w) (h.pkey_mem hu) (h.pkey_mem hu')
    refine ⟨j, ?_⟩
    have := key j _ (h.pkey_mem hu)
    rw [pdec_pkey hw hu1] at this
    rw [this, hj, pdec_pkey hw hu1']

theorem polyRot_rot (w u : ℕ) :
    h.polyRot.rot w u = pdec N w (rnext (nbrKeys es N w) (pkey N w u)) := rfl

theorem polyRot_rotInv (w u : ℕ) :
    h.polyRot.rotInv w u = pdec N w (rprev (nbrKeys es N w) (pkey N w u)) := rfl

/-- The hypermap of the polygon. -/
noncomputable def polyMap : Hypermap (2 * es.length) := h.polyRot.hypermap h.simple

theorem polySucc_adjs {w : ℕ} (hw : w < N) : Adjs es (polySucc N w) w :=
  (pdec_adjs (h.one_mem hw)).symm

theorem polySucc_lt {w : ℕ} (hw : w < N) : polySucc N w < N :=
  pdec_lt hw (by have := h.two_le; omega)

theorem polyPred_lt {w : ℕ} (hw : w < N) : polyPred N w < N :=
  pdec_lt hw (by have := h.two_le; omega)

theorem polySucc_polyPred {w : ℕ} (hw : w < N) : polySucc N (polyPred N w) = w := by
  have := h.two_le
  unfold polySucc polyPred pdec; split_ifs <;> omega

/-- The outer half-edge into `w`: from the next vertex on the circle to `w`. -/
noncomputable def outerDart (w : ℕ) (hw : w < N) : Fin (2 * es.length) :=
  ⟨findDart es (polySucc N w) w, (findDart_spec (h.polySucc_adjs hw)).1⟩

theorem dtail_outerDart {w : ℕ} (hw : w < N) : dtail es (h.outerDart w hw).val = polySucc N w :=
  (findDart_spec (h.polySucc_adjs hw)).2.1

theorem dhead_outerDart {w : ℕ} (hw : w < N) : dhead es (h.outerDart w hw).val = w :=
  (findDart_spec (h.polySucc_adjs hw)).2.2

/-- The outer face: from the outer half-edge into `w` to the one into `polyPred N w`. -/
theorem face_outerDart {w : ℕ} (hw : w < N) :
    h.polyMap.face (h.outerDart w hw) = h.outerDart (polyPred N w) (h.polyPred_lt hw) := by
  apply fin_dart_inj h.simple
  · rw [polyMap, RotSystem.dtail_face, dtail_outerDart, dhead_outerDart, h.polySucc_polyPred hw]
  · rw [polyMap, RotSystem.dhead_face, dtail_outerDart, dhead_outerDart, polyRot_rotInv,
      polySucc, pkey_pdec hw (by omega) (by have := h.two_le; omega), h.rprev_one hw,
      dhead_outerDart]
    rfl

theorem iterate_face_outerDart (j : ℕ) {w : ℕ} (hw : w < N) (hj : j ≤ w) :
    iterate h.polyMap.face j (h.outerDart w hw) = h.outerDart (w - j) (by omega) := by
  induction j generalizing w with
  | zero => rfl
  | succ j ih =>
    simp only [iterate]
    rw [h.face_outerDart hw]
    have hp : polyPred N w = w - 1 := by
      have := h.two_le
      unfold polyPred pdec; split_ifs <;> omega
    have := ih (w := polyPred N w) (h.polyPred_lt hw) (by omega)
    rw [this]
    congr 1
    omega

/-- Every outer half-edge is on the face of the outer half-edge into `0`. -/
theorem outerDart_reach {t : ℕ} (ht : t < N) :
    ∃ j, iterate h.polyMap.face j (h.outerDart 0 (by have := h.two_le; omega)) =
      h.outerDart t ht := by
  have h2 := h.two_le
  rcases Nat.eq_zero_or_pos t with h0 | h0
  · subst h0; exact ⟨0, rfl⟩
  · refine ⟨1 + (N - 1 - t), ?_⟩
    rw [iterate_add]
    simp only [iterate]
    rw [h.face_outerDart]
    have hp : polyPred N 0 = N - 1 := by unfold polyPred pdec; split_ifs <;> omega
    have := h.iterate_face_outerDart (N - 1 - t) (w := polyPred N 0) (h.polyPred_lt (by omega))
      (by omega)
    rw [this]
    congr 1
    omega

/-- **The outer face** of the polygon passes through every vertex. -/
theorem outerFaceCond : OuterFaceCond h.polyMap := by
  have h2 := h.two_le
  intro _
  refine ⟨h.outerDart 0 (by omega), fun d' _ => ?_⟩
  have hv := (h.adjs_bounds (adjs_dart es d'.isLt)).1
  obtain ⟨j, hj⟩ := h.outerDart_reach (h.polyPred_lt hv)
  have hn := (h.polyRot.nodeCond h.simple d' (h.outerDart _ (h.polyPred_lt hv))).mpr (by
    rw [halfEdgeEnd_eq_dtail es d'.isLt, halfEdgeEnd_eq_dtail es (Fin.isLt _),
      dtail_outerDart, h.polySucc_polyPred hv])
  obtain ⟨k, hk⟩ := hn
  exact ⟨j, k, hj.trans hk.symm⟩

end PolyHyp

end STACS2027

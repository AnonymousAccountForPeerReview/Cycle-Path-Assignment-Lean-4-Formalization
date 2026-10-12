module

public import ApproximationHardness.Embed.Bridge
public import ApproximationHardness.Embed.Count
public import NPHardness.PlanarAssemblyComponents
public import NPHardness.PlanarGluingCut
import Lean.Elab.Tactic.Omega

/-!
# Planarity of the embedding of a choice of bits

**Theorem** (`planar_iff`). The hypermap of the bits `β` is planar iff the chord word of every tree
is well nested.

The proof counts: the hypermap has `E` edges, one node per vertex, and one component per tree; the
forest has `2 (V - c)` darts; the forest rotation has one cycle per tree; and the faces of the
hypermap and of the chord diagram differ by the same number as the tours. The excess theorem for
chord diagrams then turns the Euler criterion into the absence of crossings.
-/

@[expose] public section

namespace STACS2027.Embed

open Complexity Complexity.Planar STACS2027.PlanarGluing STACS2027.PlanarAssembly

theorem countP_le_of_inj {n m : Nat} (P : Fin n → Bool) (Q : Fin m → Bool) (f : Fin n → Fin m)
    (hinj : ∀ a b, P a = true → P b = true → f a = f b → a = b) (hmap : ∀ a, P a = true → Q (f a) = true) :
    (List.finRange n).countP P ≤ (List.finRange m).countP Q := by
  rw [List.countP_eq_length_filter, List.countP_eq_length_filter]
  have hnd : (((List.finRange n).filter P).map f).Nodup :=
    nodup_map_of_injOn' f ((List.nodup_finRange n).filter _) (fun a ha b hb h =>
      hinj a b (List.mem_filter.mp ha).2 (List.mem_filter.mp hb).2 h)
  have := hnd.length_le_of_subset (l₂ := (List.finRange m).filter Q) (by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    exact List.mem_filter.mpr ⟨List.mem_finRange _, hmap x (List.mem_filter.mp hx).2⟩)
  simpa using this

namespace ForestData

variable {F : ForestData} (hF : F.Valid)
include hF

/-! ### Nodes -/

theorem rotInv_cyc (β : Nat → Bool) {v : Nat} (hv : F.IsVertex v) :
    Cyc (natp (rotInv hF β)) (cycOf hF β v).reverse := by
  have hnd : (cycOf hF β v).reverse.Nodup := ((List.reverse_perm _).nodup_iff).mpr (cycOf_nodup hF hv)
  apply cyc_congr _ (cyc_cnext hnd)
  intro x hx
  have hx' := (mem_cycOf hF hv).mp (List.mem_reverse.mp hx)
  simp only [natp, hx'.1, dite_eq_left, rotInv, rotInvN]
  rw [hx'.2]

theorem rotN_rotInvN {β : Nat → Bool} {d : Nat} (hd : d < 2 * F.E) : rotN hF β (rotInvN hF β d) = d := by
  have hr := (rotInvN_lt hF (β := β) hd).2
  unfold rotN
  rw [hr]
  unfold rotInvN
  have hv := isVertex_rep hF hd
  have hnd := cycOf_nodup hF (β := β) hv
  have := cnext_reverse (l := (cycOf hF β (F.rep d)).reverse)
    (((List.reverse_perm _).nodup_iff).mpr hnd)
    (List.mem_reverse.mpr ((mem_cycOf hF hv).mpr ⟨hd, rfl⟩))
  rw [List.reverse_reverse] at this
  exact this

theorem node_reaches (β : Nat → Bool) (d d' : Fin (2 * F.E)) :
    Reaches (rotInv hF β) d d' ↔ F.rep d'.val = F.rep d.val := by
  have hv := isVertex_rep hF d.isLt
  have hd : d.val ∈ (cycOf hF β (F.rep d.val)).reverse := List.mem_reverse.mpr ((mem_cycOf hF hv).mpr ⟨d.isLt, rfl⟩)
  rw [reaches_iff_mem (rotInv_cyc hF β hv) hd, List.mem_reverse, mem_cycOf hF hv]
  exact ⟨fun h => h.2, fun h => ⟨d'.isLt, h⟩⟩

/-- The number of vertices. -/
def numV (F : ForestData) : Nat := (List.finRange (2 * F.E)).countP fun d => decide (F.rep d.val = d.val)

theorem node_count (β : Nat → Bool) : cycleCount (rotInv hF β) = F.numV := by
  have hinj : ∀ a b, rotInv hF β a = rotInv hF β b → a = b := by
    intro a b h
    have h' : rotInvN hF β a.val = rotInvN hF β b.val := congrArg Fin.val h
    apply Fin.ext
    have ha := (rotInvN_lt hF (β := β) a.isLt)
    have hb := (rotInvN_lt hF (β := β) b.isLt)
    -- the inverse rotation is injective: it is the rotation of the reversed order
    have hc := rotInv_cyc hF β (isVertex_rep hF a.isLt)
    have hc' := rotInv_cyc hF β (isVertex_rep hF b.isLt)
    have e1 := rotN_rotInvN hF (β := β) a.isLt
    have e2 := rotN_rotInvN hF (β := β) b.isLt
    rw [← e1, h', e2]
  rw [cycleCount_eq]
  unfold numV
  apply countP_congr'
  intro d _
  apply Bool.eq_iff_iff.mpr
  rw [cycleMin_iff_reach hinj, decide_eq_true_iff]
  constructor
  · intro h
    have hr : F.rep (F.rep d.val) = F.rep d.val := hF.rep_rep _ d.isLt
    have := h ⟨F.rep d.val, hF.rep_lt _ d.isLt⟩ ((node_reaches hF β d _).mpr hr)
    have := hF.rep_le _ d.isLt
    simp only at *; omega
  · intro h y hy
    have e := (node_reaches hF β d y).mp hy
    have := hF.rep_le _ y.isLt
    rw [e, h] at this; exact this

/-! ### Trees -/

theorem rootOf_eq {u R : Nat} (hu : F.IsVertex u) (hR : F.IsVertex R) (hroot : F.IsRoot R)
    (h : F.Desc R u) : F.rootOf u = R := by
  obtain ⟨h1, h2, h3⟩ := rootOf_spec hF hu
  exact desc_unique hF hu h3 h (by rw [hF.depth_root _ h1 h2, hF.depth_root _ hR hroot])

theorem rootOf_root {r : Nat} (hr : F.IsVertex r) (hroot : F.IsRoot r) : F.rootOf r = r :=
  rootOf_eq hF hr hr hroot (desc_refl r)

theorem rootOf_pair {d : Nat} (hd : d < 2 * F.E) : F.rootOf (F.rep (pair d)) = F.rootOf (F.rep d) := by
  have hv := isVertex_rep hF hd
  have hpv := isVertex_rep hF (pair_lt hd)
  obtain ⟨h1, h2, h3⟩ := rootOf_spec hF hv
  apply rootOf_eq hF hpv h1 h2
  apply desc_root_of_rel hF h1 h2 hv hpv h3
  by_cases ht : F.IsTree d
  · rcases ht with hu | hdn
    · obtain ⟨_, _, hc⟩ := down_child hF (pair_lt hd) (isDown_pair.mpr hu)
      rw [pair_pair] at hc
      exact Or.inr ⟨1, hc⟩
    · obtain ⟨_, _, hc⟩ := down_child hF hd hdn
      exact Or.inl ⟨1, hc⟩
  · exact (hF.back d hd ht).symm

/-- The number of trees. -/
def numC (F : ForestData) : Nat :=
  (List.finRange (2 * F.E)).countP fun d => decide (F.IsVertex d.val ∧ F.IsRoot d.val)

theorem sig_reaches_root (β : Nat → Bool) (x : Fin (2 * F.E)) :
    Reaches (sigF hF β) x ⟨F.rootOf (F.rep x.val), (rootOf_spec hF (isVertex_rep hF x.isLt)).1.1⟩ := by
  obtain ⟨h1, h2, h3⟩ := rootOf_spec hF (isVertex_rep hF x.isLt)
  have hlt := lt_of_Ftour_top hF (β := β) h1 h2
  have hc : Cyc (natp (sigF hF β)) (Ftour hF β (F.top (F.rootOf (F.rep x.val)))) :=
    cyc_congr (fun y hy => (natp_sigF hF β (hlt y hy)).symm) (top_cyc hF β h1 h2)
  rw [reaches_iff_mem hc ((mem_Ftour_top hF β h1 h2 _).mpr ⟨x.isLt, h3⟩)]
  exact (mem_Ftour_top hF β h1 h2 _).mpr ⟨h1.1, by rw [h1.2]; exact desc_refl _⟩

theorem sig_count (β : Nat → Bool) : cycleCount (sigF hF β) = F.numC := by
  apply Nat.le_antisymm
  · let xs := (List.finRange (2 * F.E)).filter fun d => decide (F.IsVertex d.val ∧ F.IsRoot d.val)
    have := STACS2027.PlanarSource.Embedding.cycleCount_le_representatives (sigF_inj hF β)
      (fun x => ⟨F.rootOf (F.rep x.val), (rootOf_spec hF (isVertex_rep hF x.isLt)).1.1⟩) xs
      (sig_reaches_root hF β) (fun x => by
        obtain ⟨h1, h2, _⟩ := rootOf_spec hF (isVertex_rep hF x.isLt)
        exact List.mem_filter.mpr ⟨List.mem_finRange _, by simp [h1, h2]⟩)
    unfold numC; rw [List.countP_eq_length_filter]; exact this
  · let xs := (List.finRange (2 * F.E)).filter fun d => decide (F.IsVertex d.val ∧ F.IsRoot d.val)
    have hφ : ∀ x, F.rootOf (F.rep (sigF hF β x).val) = F.rootOf (F.rep x.val) := by
      intro x
      obtain ⟨h1, h2, h3⟩ := rootOf_spec hF (isVertex_rep hF x.isLt)
      have hlt := lt_of_Ftour_top hF (β := β) h1 h2
      have hc : Cyc (natp (sigF hF β)) (Ftour hF β (F.top (F.rootOf (F.rep x.val)))) :=
        cyc_congr (fun y hy => (natp_sigF hF β (hlt y hy)).symm) (top_cyc hF β h1 h2)
      have hm := cyc_maps hc _ ((mem_Ftour_top hF β h1 h2 _).mpr ⟨x.isLt, h3⟩)
      rw [natp_val] at hm
      exact rootOf_eq hF (isVertex_rep hF (sigF hF β x).isLt) h1 h2 ((mem_Ftour_top hF β h1 h2 _).mp hm).2
    have := cycleCount_ge (sigF hF β) (fun x => F.rootOf (F.rep x.val)) hφ xs (by
      have : xs.map (fun x => F.rootOf (F.rep x.val)) = xs.map Fin.val := by
        apply List.map_congr_left
        intro x hx
        have h := (List.mem_filter.mp hx).2
        simp only [decide_eq_true_eq] at h
        rw [h.1.2, rootOf_root hF h.1 h.2]
      rw [this]
      exact nodup_map_of_injOn' _ ((List.nodup_finRange _).filter _) (fun a _ b _ h => Fin.ext h))
    unfold numC; rw [List.countP_eq_length_filter]; exact this

/-! ### Darts of the forest -/

/-- The number of darts of the forest. -/
def numT (F : ForestData) : Nat := (List.finRange (2 * F.E)).countP fun d => decide (F.IsTree d.val)

theorem tree_count : F.numT + 2 * F.numC = 2 * F.numV := by
  let cUp := (List.finRange (2 * F.E)).countP fun d => decide (F.IsUp d.val)
  let cDown := (List.finRange (2 * F.E)).countP fun d => decide (F.IsDown d.val)
  let cNR := (List.finRange (2 * F.E)).countP fun d => decide (F.IsVertex d.val ∧ ¬ F.IsRoot d.val)
  have hT : F.numT = cUp + cDown := by
    unfold numT
    rw [countP_split _ _ (fun d => decide (F.IsUp d.val))]
    congr 1
    · apply countP_congr'; intro d _
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      unfold IsTree; exact ⟨fun h => h.2, fun h => ⟨Or.inl h, h⟩⟩
    · apply countP_congr'; intro d _
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]
      unfold IsTree
      constructor
      · rintro ⟨h1 | h1, h2⟩
        · exact absurd h1 h2
        · exact h1
      · intro h; exact ⟨Or.inr h, fun hu => not_up_and_down hF d.isLt hu h⟩
  have hV : F.numV = cNR + F.numC := by
    unfold numV numC
    rw [countP_split _ _ (fun d => decide (F.IsRoot d.val)), Nat.add_comm]
    congr 1
    · apply countP_congr'; intro d _
      simp only [IsVertex, d.isLt, true_and]
      apply Bool.eq_iff_iff.mpr; simp
    · apply countP_congr'; intro d _
      simp only [IsVertex, d.isLt, true_and]
      apply Bool.eq_iff_iff.mpr; simp
  have h1 : cUp ≤ cNR := countP_le_of_inj _ _ (fun d => ⟨F.rep d.val, hF.rep_lt _ d.isLt⟩)
    (fun a b ha hb h => by
      simp only [decide_eq_true_eq] at ha hb
      apply Fin.ext
      have h' : F.rep a.val = F.rep b.val := congrArg Fin.val h
      rw [← ha.2, ← hb.2, h'])
    (fun a ha => by
      simp only [decide_eq_true_eq] at ha ⊢
      exact ⟨isVertex_rep hF a.isLt, ha.1⟩)
  have h2 : cNR ≤ cUp := countP_le_of_inj _ _
    (fun d => if h : F.IsVertex d.val ∧ ¬ F.IsRoot d.val then ⟨F.par d.val, hF.par_lt _ h.1 h.2⟩ else d)
    (fun a b ha hb h => by
      simp only [decide_eq_true_eq] at ha hb
      simp only [dite_eq_left ha, dite_eq_left hb] at h
      apply Fin.ext
      have h' : F.par a.val = F.par b.val := congrArg Fin.val h
      rw [← hF.par_rep _ ha.1 ha.2, h', hF.par_rep _ hb.1 hb.2])
    (fun a ha => by
      simp only [decide_eq_true_eq] at ha ⊢
      simp only [dite_eq_left ha]
      exact par_isUp hF ha.1 ha.2)
  have h3 : cUp ≤ cDown := countP_le_of_inj _ _ F.pairF
    (fun a b _ _ h => Fin.ext (pair_inj (congrArg Fin.val h)))
    (fun a ha => by
      simp only [decide_eq_true_eq] at ha ⊢
      exact isDown_pair.mpr ha)
  have h4 : cDown ≤ cUp := countP_le_of_inj _ _ F.pairF
    (fun a b _ _ h => Fin.ext (pair_inj (congrArg Fin.val h)))
    (fun a ha => by
      simp only [decide_eq_true_eq] at ha ⊢
      exact ha)
  omega

omit hF in
theorem back_count : (List.finRange (2 * F.E)).countP F.backS + F.numT = 2 * F.E := by
  have := countP_add_not (List.finRange (2 * F.E)) F.backS
  rw [List.length_finRange] at this
  have e : F.numT = (List.finRange (2 * F.E)).countP (fun z => !F.backS z) := by
    unfold numT
    apply countP_congr'; intro d _
    simp [backS, IsBack, d.isLt]
  omega

/-! ### Components -/

theorem connected_sig {β : Nat → Bool} (x : Fin (2 * F.E)) :
    Connected (hyp hF β) x (sigF hF β x) := by
  have hface : ∀ y, Connected (hyp hF β) y ((hyp hF β).face y) :=
    fun y => ⟨1, Linked.linked_step _ (Linked.linked_refl _ 0 y) (Or.inr (Or.inr rfl))⟩
  have hedge : ∀ y, Connected (hyp hF β) y ((hyp hF β).edge y) :=
    fun y => ⟨1, Linked.linked_step _ (Linked.linked_refl _ 0 y) (Or.inl rfl)⟩
  by_cases ht : F.IsTree x.val
  · have : sigF hF β x = (hyp hF β).face x := by
      apply Fin.ext
      show rotN hF β (if F.IsTree x.val then pair x.val else x.val) = rotN hF β (pair x.val)
      rw [ite_eq_left ht]
    rw [this]; exact hface x
  · have : sigF hF β x = (hyp hF β).face ((hyp hF β).edge x) := by
      apply Fin.ext
      show rotN hF β (if F.IsTree x.val then pair x.val else x.val) = rotN hF β (pair (pair x.val))
      rw [ite_eq_right ht, pair_pair]
    rw [this]; exact (hedge x).trans (hface _)

theorem connected_iterate {β : Nat → Bool} : ∀ k (x : Fin (2 * F.E)),
    Connected (hyp hF β) x (iterate (sigF hF β) k x) := by
  intro k
  induction k with
  | zero => intro x; exact Connected.refl _ _
  | succ k ih => intro x; exact (connected_sig hF x).trans (ih _)

theorem component_count (β : Nat → Bool) : (hyp hF β).componentCount = F.numC := by
  let xs := (List.finRange (2 * F.E)).filter fun d => decide (F.IsVertex d.val ∧ F.IsRoot d.val)
  have hlen : xs.length = F.numC := by unfold numC; rw [List.countP_eq_length_filter]
  apply Nat.le_antisymm
  · rw [← hlen]
    apply componentCount_le_cover
    intro d
    obtain ⟨h1, h2, _⟩ := rootOf_spec hF (isVertex_rep hF d.isLt)
    refine ⟨⟨F.rootOf (F.rep d.val), h1.1⟩, List.mem_filter.mpr ⟨List.mem_finRange _, by simp [h1, h2]⟩, ?_⟩
    obtain ⟨k, hk⟩ := sig_reaches_root hF β d
    rw [← hk]
    exact connected_iterate hF k d
  · rw [← hlen]
    apply componentCount_ge (hyp hF β) (fun x => F.rootOf (F.rep x.val))
    · intro x y hs
      rcases hs with h | h | h
      · rw [← h]; exact rootOf_pair hF x.isLt
      · rw [← h]
        show F.rootOf (F.rep (rotInvN hF β x.val)) = _
        rw [(rotInvN_lt hF x.isLt).2]
      · rw [← h]
        show F.rootOf (F.rep (rotN hF β (pair x.val))) = _
        rw [(rotN_lt hF (pair_lt x.isLt)).2, rootOf_pair hF x.isLt]
    · have : xs.map (fun x => F.rootOf (F.rep x.val)) = xs.map Fin.val := by
        apply List.map_congr_left
        intro x hx
        have h := (List.mem_filter.mp hx).2
        simp only [decide_eq_true_eq] at h
        rw [h.1.2, rootOf_root hF h.1 h.2]
      rw [this]
      exact nodup_map_of_injOn' _ ((List.nodup_finRange _).filter _) (fun a _ b _ h => Fin.ext h)

/-! ### Faces -/

theorem face_eq (β : Nat → Bool) (x : Fin (2 * F.E)) :
    (hyp hF β).face x = sigF hF β ((diag hF β).chord x) := by
  apply Fin.ext
  show rotN hF β (pair x.val) = sigN hF β ((if F.backS x = true then F.pairF x else x).val)
  by_cases hb : F.backS x = true
  · rw [ite_eq_left hb]
    have hb' : F.IsBack x.val := by simpa [backS] using hb
    have hnt : ¬ F.IsTree (pair x.val) := (isBack_pair hb').2
    show _ = rotN hF β (if F.IsTree (pair x.val) then _ else _)
    rw [ite_eq_right hnt]; rfl
  · rw [ite_eq_right hb]
    have ht : F.IsTree x.val := by
      apply Classical.byContradiction
      intro h; exact hb (by simp [backS, IsBack, x.isLt, h])
    show _ = rotN hF β (if F.IsTree x.val then _ else _)
    rw [ite_eq_left ht]

theorem face_inj (β : Nat → Bool) : ∀ a b, (hyp hF β).face a = (hyp hF β).face b → a = b := by
  intro a b h
  have h1 := rot_inj hF β _ _ h
  exact Fin.ext (pair_inj (congrArg Fin.val h1))

theorem face_firstReturn (β : Nat → Bool) :
    firstReturn (hyp hF β).face F.backS = (diag hF β).faces := by
  have hagree : ∀ u, F.backS u = false → (hyp hF β).face u = sigF hF β u := by
    intro u hu
    rw [face_eq hF β u]
    show sigF hF β (if F.backS u = true then F.pairF u else u) = _
    rw [ite_eq_right (by simp [hu])]
  funext z
  by_cases hz : F.backS z = true
  · rw [firstReturn_eq_nextIn (face_inj hF β) hz]
    show _ = firstReturn (sigF hF β) F.backS ((diag hF β).chord z)
    have hcz : F.backS ((diag hF β).chord z) = true := by
      show F.backS (if F.backS z = true then F.pairF z else z) = true
      rw [ite_eq_left hz]; exact backS_pair hz
    rw [firstReturn_eq_nextIn (sigF_inj hF β) hcz, ← face_eq hF β z]
    exact (nextIn_congr hagree _ (meetsFrom_of_meets (meets_of_perm (face_inj hF β) _ hz))).2
  · have hz' : F.backS z = false := by simpa using hz
    rw [firstReturn_of_not hz']
    show z = firstReturn (sigF hF β) F.backS (if F.backS z = true then F.pairF z else z)
    rw [ite_eq_right hz, firstReturn_of_not hz']

omit hF in
theorem pairF_graphEdge : IsGraphEdge F.pairF := by
  intro d
  show pair d.val = _
  unfold pair
  by_cases h : d.val % 2 = 0
  · rw [ite_eq_left h]; simp [h]
  · rw [ite_eq_right h]
    have : d.val % 2 = 1 := by omega
    simp [this]

/-- **Planarity of the embedding of the bits.** The hypermap of the bits `β` is planar iff the chord
word of every tree is well nested. -/
theorem hyp_planar_iff (β : Nat → Bool) :
    (hyp hF β).Planar ↔ ∀ r, F.IsVertex r → F.IsRoot r → WN pair ((F.plan hF).W β (F.top r)) := by
  rw [← diag_noncrossing_iff hF β]
  have hA1 := cycleCount_firstReturn_avoid (face_inj hF β) F.backS
  have hA2 := cycleCount_firstReturn_avoid (sigF_inj hF β) F.backS
  have hav : avoidCount (hyp hF β).face F.backS = avoidCount (sigF hF β) F.backS :=
    avoidCount_congr (face_inj hF β) (sigF_inj hF β) (fun u hu => by
      rw [face_eq hF β u]
      show sigF hF β (if F.backS u = true then F.pairF u else u) = _
      rw [ite_eq_right (by simp [hu])])
  rw [face_firstReturn hF β] at hA1
  have hD := Diagram.chord_excess (diag hF β)
  have htour : (diag hF β).tour = firstReturn (sigF hF β) F.backS := rfl
  have hS : (diag hF β).S = F.backS := rfl
  rw [← htour] at hA2
  rw [hS] at hD
  have hsig := sig_count hF β
  have hnode := node_count hF β
  have hcomp := component_count hF β
  have hbc := back_count (F := F)
  have htc := tree_count hF
  have he1 := cycleCount_graphEdge_ge (pairF_graphEdge (F := F))
  have he2 := cycleCount_graphEdge_le (pairF_graphEdge (F := F))
  rw [Complexity.Planar.planar_iff]
  unfold Hypermap.eulerRhs
  have hedge : (hyp hF β).edge = F.pairF := rfl
  have hnd : (hyp hF β).node = rotInv hF β := rfl
  rw [hedge, hnd, hcomp, hnode]
  constructor
  · intro hp
    apply Classical.byContradiction
    intro hnc
    have := hD.2 hnc
    omega
  · intro hnc
    have := hD.1 hnc
    omega

end ForestData

end STACS2027.Embed

module

public import ApproximationHardness.Embed.Euler
import Lean.Elab.Tactic.Omega

/-!
# The embedding of a choice of bits, and its chord diagram

For bits `β`, the hypermap `hyp β` has the edge involution `pair`, the node permutation the inverse
rotation of the bits, and the face permutation `rot β ∘ pair`. Contracting the forest turns it into
the chord diagram `diag β`: the darts outside the forest, the first return of the forest rotation
to them, and the edge involution. Its tour runs along the chord words of the tops of the trees.
-/

@[expose] public section

namespace STACS2027.Embed

open Complexity Complexity.Planar STACS2027.PlanarGluing

theorem cyc_congr {f g : Nat → Nat} {l : List Nat} (h : ∀ x ∈ l, f x = g x) (hc : Cyc f l) : Cyc g l := by
  have hch : ∀ l', (∀ x ∈ l', f x = g x) → Chain f l' → Chain g l' := by
    intro l'
    induction l' with
    | nil => intro _ _; exact Chain.nil
    | cons a l' ih =>
      intro h' hc'
      obtain ⟨h1, h2⟩ := chain_cons_iff.mp hc'
      exact chain_cons_iff.mpr ⟨ih (fun x hx => h' x (List.mem_cons_of_mem _ hx)) h1,
        fun b hb => by rw [← h' a (List.mem_cons_self ..)]; exact h2 b hb⟩
  refine ⟨hch l h hc.1, fun a b ha hb => ?_⟩
  rw [← h a (List.mem_of_getLast? ha)]
  exact hc.2 a b ha hb

namespace ForestData

variable {F : ForestData} (hF : F.Valid)

/-- The edge involution on darts. -/
def pairF (F : ForestData) (d : Fin (2 * F.E)) : Fin (2 * F.E) := ⟨pair d.val, pair_lt d.isLt⟩

/-- The hypermap of the bits `β`. -/
def hyp (β : Nat → Bool) : Hypermap (2 * F.E) where
  edge := F.pairF
  node := rotInv hF β
  face := fun d => rot hF β (F.pairF d)
  edgeK := by
    intro x
    apply Fin.ext
    show rotInvN hF β (rotN hF β (pair (pair x.val))) = x.val
    rw [pair_pair, rotInvN_rotN hF x.isLt]

include hF

theorem rotN_inj {β : Nat → Bool} {a b : Nat} (ha : a < 2 * F.E) (hb : b < 2 * F.E)
    (h : rotN hF β a = rotN hF β b) : a = b := by
  rw [← rotInvN_rotN hF ha, h, rotInvN_rotN hF hb]

/-- The edge involution on forest darts, the identity elsewhere. -/
def alphaT (F : ForestData) (d : Nat) : Nat := if F.IsTree d then pair d else d

omit hF in
theorem alphaT_lt {d : Nat} (hd : d < 2 * F.E) : F.alphaT d < 2 * F.E := by
  unfold alphaT; split
  · exact pair_lt hd
  · exact hd

omit hF in
theorem alphaT_alphaT (d : Nat) : F.alphaT (F.alphaT d) = d := by
  unfold alphaT
  by_cases h : F.IsTree d
  · rw [ite_eq_left h, ite_eq_left (isTree_pair.mpr h), pair_pair]
  · rw [ite_eq_right h, ite_eq_right h]

theorem sigN_lt {β : Nat → Bool} {d : Nat} (hd : d < 2 * F.E) : sigN hF β d < 2 * F.E :=
  (rotN_lt hF (alphaT_lt hd)).1

/-- The forest rotation on darts. -/
def sigF (β : Nat → Bool) (d : Fin (2 * F.E)) : Fin (2 * F.E) := ⟨sigN hF β d.val, sigN_lt hF d.isLt⟩

theorem sigF_inj (β : Nat → Bool) : ∀ a b, sigF hF β a = sigF hF β b → a = b := by
  intro a b h
  apply Fin.ext
  have h' : rotN hF β (F.alphaT a.val) = rotN hF β (F.alphaT b.val) := congrArg Fin.val h
  have := rotN_inj hF (alphaT_lt a.isLt) (alphaT_lt b.isLt) h'
  rw [← alphaT_alphaT a.val, this, alphaT_alphaT]

theorem natp_sigF (β : Nat → Bool) {d : Nat} (hd : d < 2 * F.E) : natp (sigF hF β) d = sigN hF β d := by
  simp [natp, hd, sigF]

/-- The darts outside the forest. -/
def backS (F : ForestData) (d : Fin (2 * F.E)) : Bool := decide (F.IsBack d.val)

omit hF in
theorem natS_backS {d : Nat} (hd : d < 2 * F.E) : natS F.backS d = decide (F.IsBack d) := by
  simp [natS, hd, backS]

omit hF in
theorem backS_pair {d : Fin (2 * F.E)} (h : F.backS d = true) : F.backS (F.pairF d) = true := by
  simp only [backS, decide_eq_true_eq] at h ⊢
  exact isBack_pair h

/-- The root of the tree of a vertex. -/
def rootOf (F : ForestData) (u : Nat) : Nat := iterate F.up (F.depth u) u

theorem rootOf_spec {u : Nat} (hu : F.IsVertex u) :
    F.IsVertex (F.rootOf u) ∧ F.IsRoot (F.rootOf u) ∧ F.Desc (F.rootOf u) u := by
  refine ⟨iterate_up_vertex hF hu _, ?_, ⟨_, rfl⟩⟩
  have h := depth_iterate hF hu (F.depth u) (Nat.le_refl _)
  apply Classical.byContradiction
  intro hn
  have := hF.depth_up _ (iterate_up_vertex hF hu _) hn
  unfold rootOf at hn this
  omega

theorem mem_W_top (β : Nat → Bool) {r : Nat} (hr : F.IsVertex r) (hroot : F.IsRoot r) (e : Nat) :
    e ∈ (F.plan hF).W β (F.top r) ↔ F.IsBack e ∧ F.Desc r (F.rep e) := by
  rw [(F.plan hF).mem_W_D]; exact mem_D_top hF hr hroot e

theorem lt_of_Ftour_top {β : Nat → Bool} {r : Nat} (hr : F.IsVertex r) (hroot : F.IsRoot r) :
    ∀ x ∈ Ftour hF β (F.top r), x < 2 * F.E := fun x hx => ((mem_Ftour_top hF β hr hroot x).mp hx).1

/-- **The tour of the diagram runs along the chord word of every tree.** -/
theorem tau_cyc (β : Nat → Bool) {r : Nat} (hr : F.IsVertex r) (hroot : F.IsRoot r) :
    Cyc (natp (firstReturn (sigF hF β) F.backS)) ((F.plan hF).W β (F.top r)) := by
  have hlt := lt_of_Ftour_top hF (β := β) hr hroot
  have h1 : Cyc (natp (sigF hF β)) (Ftour hF β (F.top r)) :=
    cyc_congr (fun x hx => (natp_sigF hF β (hlt x hx)).symm) (top_cyc hF β hr hroot)
  have h2 := cyc_firstReturn (sigF_inj hF β) (S := F.backS) h1 (top_nodup hF β hr hroot) hlt
  have hf : (Ftour hF β (F.top r)).filter (natS F.backS) = (F.plan hF).W β (F.top r) := by
    rw [← Ftour_filter hF β]
    apply List.filter_congr
    intro x hx; exact natS_backS (hlt x hx)
  rw [hf] at h2; exact h2

theorem pair_same_tree {d : Nat} (hb : F.IsBack d) : F.Desc (F.rootOf (F.rep d)) (F.rep (pair d)) := by
  have hv := isVertex_rep hF hb.1
  obtain ⟨h1, h2, h3⟩ := rootOf_spec hF hv
  exact desc_root_of_rel hF h1 h2 hv (isVertex_rep hF (pair_lt hb.1)) h3 (hF.back d hb.1 hb.2).symm

/-- The chord diagram of the bits `β`. -/
noncomputable def diag (β : Nat → Bool) : Diagram (2 * F.E) where
  S := F.backS
  tour := firstReturn (sigF hF β) F.backS
  chord := fun d => if F.backS d = true then F.pairF d else d
  tour_inj := firstReturn_injective (sigF_inj hF β) _
  tour_fix := fun _ h => firstReturn_of_not h
  chord_invol := by
    intro d
    by_cases h : F.backS d = true
    · simp only [h, ite_true, backS_pair h]
      apply Fin.ext; exact pair_pair _
    · simp [h]
  chord_fix := fun d h => by simp [h]
  chord_ne := fun d h => by
    simp only [h, ite_true]
    intro e; exact pair_ne d.val (congrArg Fin.val e)
  chord_reach := by
    intro d
    by_cases h : F.backS d = true
    · simp only [h, ite_true]
      have hb : F.IsBack d.val := by simpa [backS] using h
      have hv := isVertex_rep hF hb.1
      obtain ⟨h1, h2, h3⟩ := rootOf_spec hF hv
      have hc := tau_cyc hF β h1 h2
      have hdW : d.val ∈ (F.plan hF).W β (F.top (F.rootOf (F.rep d.val))) := (mem_W_top hF β h1 h2 _).mpr ⟨hb, h3⟩
      exact (reaches_iff_mem hc hdW).mpr ((mem_W_top hF β h1 h2 _).mpr ⟨isBack_pair hb, pair_same_tree hF hb⟩)
    · simp only [h]; exact Reaches.refl _ _

/-! ### Crossings and nesting -/

/-- The roots, as a list. -/
def roots (F : ForestData) : List Nat := (List.range (2 * F.E)).filter fun r => decide (F.IsVertex r ∧ F.IsRoot r)

omit hF in
theorem mem_roots {r : Nat} : r ∈ F.roots ↔ F.IsVertex r ∧ F.IsRoot r := by
  unfold roots
  rw [List.mem_filter, List.mem_range, decide_eq_true_eq]
  exact ⟨fun h => h.2, fun h => ⟨h.1.1, h⟩⟩

/-- **Crossings of the diagram.** The diagram of the bits is non-crossing iff the chord word of
every tree is well nested. -/
theorem diag_noncrossing_iff (β : Nat → Bool) :
    (diag hF β).NonCrossing ↔ ∀ r, F.IsVertex r → F.IsRoot r → WN pair ((F.plan hF).W β (F.top r)) := by
  have hk := kind hF
  let Ws := F.roots.map fun r => (F.plan hF).W β (F.top r)
  have hmemWs : ∀ w, w ∈ Ws ↔ ∃ r, F.IsVertex r ∧ F.IsRoot r ∧ w = (F.plan hF).W β (F.top r) := by
    intro w
    simp only [Ws, List.mem_map, mem_roots]
    constructor
    · rintro ⟨r, ⟨h1, h2⟩, rfl⟩; exact ⟨r, h1, h2, rfl⟩
    · rintro ⟨r, h1, h2, rfl⟩; exact ⟨r, ⟨h1, h2⟩, rfl⟩
  have hchord : ∀ r, F.IsVertex r → F.IsRoot r → ∀ u ∈ (F.plan hF).W β (F.top r),
      natp (diag hF β).chord u = pair u := by
    intro r h1 h2 u hu
    have hb := ((mem_W_top hF β h1 h2 u).mp hu).1
    have hS : F.backS ⟨u, hb.1⟩ = true := by simp [backS, hb]
    show natp (fun d => if F.backS d = true then F.pairF d else d) u = pair u
    simp [natp, hb.1, hS, pairF]
  have main := noncrossing_iff_wn (diag hF β) Ws
    (fun w hw => by obtain ⟨r, h1, h2, rfl⟩ := (hmemWs w).mp hw; exact tau_cyc hF β h1 h2)
    (fun w hw => by obtain ⟨r, h1, h2, rfl⟩ := (hmemWs w).mp hw; exact (F.plan hF).W_nodup hk β _)
    (fun w hw u hu => by
      obtain ⟨r, h1, h2, rfl⟩ := (hmemWs w).mp hw; exact ((mem_W_top hF β h1 h2 u).mp hu).1.1)
    (fun w hw u hu => by
      obtain ⟨r, h1, h2, rfl⟩ := (hmemWs w).mp hw
      have hb := ((mem_W_top hF β h1 h2 u).mp hu).1
      show natS F.backS u = true
      rw [natS_backS hb.1]; simpa using hb)
    (fun w hw u hu => by
      obtain ⟨r, h1, h2, rfl⟩ := (hmemWs w).mp hw
      rw [hchord r h1 h2 u hu]
      obtain ⟨hb, hd⟩ := (mem_W_top hF β h1 h2 u).mp hu
      have hv := isVertex_rep hF hb.1
      refine (mem_W_top hF β h1 h2 _).mpr ⟨isBack_pair hb, ?_⟩
      exact desc_root_of_rel hF h1 h2 hv (isVertex_rep hF (pair_lt hb.1)) hd (hF.back u hb.1 hb.2).symm)
    (fun x hx => by
      have hb : F.IsBack x.val := by simpa [diag, backS] using hx
      obtain ⟨h1, h2, h3⟩ := rootOf_spec hF (isVertex_rep hF hb.1)
      exact ⟨_, (hmemWs _).mpr ⟨_, h1, h2, rfl⟩, (mem_W_top hF β h1 h2 _).mpr ⟨hb, h3⟩⟩)
  rw [main]
  constructor
  · intro h r h1 h2
    exact (wn_congr (hchord r h1 h2)).mp (h _ ((hmemWs _).mpr ⟨r, h1, h2, rfl⟩))
  · intro h w hw
    obtain ⟨r, h1, h2, rfl⟩ := (hmemWs w).mp hw
    exact (wn_congr (hchord r h1 h2)).mpr (h r h1 h2)

end ForestData

end STACS2027.Embed

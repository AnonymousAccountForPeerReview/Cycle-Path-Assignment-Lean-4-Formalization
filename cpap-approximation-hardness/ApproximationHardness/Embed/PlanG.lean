module

public import ApproximationHardness.Embed.Forest
import Lean.Elab.Tactic.Omega

/-!
# The plan of a depth-first forest

The nodes of the plan are the vertices of the graph and, for every root `r`, a virtual top node
`top r = 2E + r`. A non-root vertex has as parts its darts other than its parent dart; a root has
as parts its darts other than its distinguished dart `zOf r` (for a root with three darts: its
largest dart outside the forest if there is one, else its largest dart); the top of `r` has the
parts `r` and the distinguished dart. A dart leading to a child is the part `.node child`; any
other dart is the part `.dart d`.
-/

@[expose] public section

namespace STACS2027.Embed

open Complexity Complexity.Planar

namespace ForestData

variable (F : ForestData)

/-- A dart outside the forest. -/
def IsBack (d : Nat) : Prop := d < 2 * F.E ∧ ¬ F.IsTree d

instance (d : Nat) : Decidable (F.IsBack d) := inferInstanceAs (Decidable (_ ∧ _))

/-- The distinguished dart of a root with three darts (`2E` if none). -/
def zOf (r : Nat) : Nat :=
  if (F.dartsAt r).length = 3 then
    match ((F.dartsAt r).filter fun d => !decide (F.IsTree d)).getLast? with
    | some d => d
    | none => (F.dartsAt r).getLastD 0
  else 2 * F.E

/-- The part of a dart. -/
def item (d : Nat) : Item := if F.IsDown d then .node (F.rep (pair d)) else .dart d

/-- The top node of the tree of the root `r`. -/
def top (r : Nat) : Nat := 2 * F.E + r

/-- `t` is the top node of a tree. -/
def IsTop (t : Nat) : Prop := 2 * F.E ≤ t ∧ F.IsVertex (t - 2 * F.E) ∧ F.IsRoot (t - 2 * F.E)

instance (r : Nat) : Decidable (F.IsVertex r) := inferInstanceAs (Decidable (_ ∧ _))
instance (t : Nat) : Decidable (F.IsTop t) := inferInstanceAs (Decidable (_ ∧ _))

/-- The parts of a node. -/
def parts (v : Nat) : List Item :=
  if F.IsVertex v then
    if F.IsRoot v then ((F.dartsAt v).erase (F.zOf v)).map F.item
    else ((F.dartsAt v).erase (F.par v)).map F.item
  else if F.IsTop v then
    .node (v - 2 * F.E) ::
      (if F.zOf (v - 2 * F.E) < 2 * F.E then [F.item (F.zOf (v - 2 * F.E))] else [])
  else []

/-- The height of a node. -/
def ht (v : Nat) : Nat :=
  if F.IsVertex v then F.H - F.depth v else if F.IsTop v then F.H + 1 else 0

/-- The node closing a dart. -/
def tgt (d : Nat) : Nat :=
  if F.IsRoot (F.rep d) ∧ d = F.zOf (F.rep d) then F.top (F.rep d) else F.rep d

instance (d : Nat) : Decidable (F.IsRoot (F.rep d) ∧ d = F.zOf (F.rep d)) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The key of an open end: the depth of the node closing its partner. -/
def key (e : Nat) : Nat :=
  if F.IsRoot (F.rep (pair e)) ∧ pair e = F.zOf (F.rep (pair e)) then 0 else F.depth (F.rep (pair e)) + 1

variable {F}

theorem isDown_iff {d : Nat} : F.IsDown d ↔ ¬ F.IsRoot (F.rep (pair d)) ∧ F.par (F.rep (pair d)) = pair d :=
  Iff.rfl

section valid

variable (hF : F.Valid)
include hF

/-- The child reached through a down dart. -/
theorem down_child {d : Nat} (hd : d < 2 * F.E) (h : F.IsDown d) :
    F.IsVertex (F.rep (pair d)) ∧ ¬ F.IsRoot (F.rep (pair d)) ∧ F.up (F.rep (pair d)) = F.rep d := by
  refine ⟨isVertex_rep hF (pair_lt hd), h.1, ?_⟩
  unfold up; rw [ite_eq_right h.1, h.2, pair_pair]

theorem ht_lt (v c : Nat) (h : Item.node c ∈ F.parts v) : F.ht c < F.ht v := by
  have hdown : ∀ d, d ∈ F.dartsAt v → F.item d = .node c → F.IsVertex c ∧ F.depth c = F.depth v + 1 := by
    intro d hd he
    obtain ⟨hdl, hdr⟩ := mem_dartsAt.mp hd
    unfold item at he
    split at he
    · rename_i hdn
      cases he
      obtain ⟨hv, hr, hu⟩ := down_child hF hdl hdn
      refine ⟨hv, ?_⟩
      rw [hF.depth_up _ hv hr, hu, hdr]
    · cases he
  unfold parts at h
  by_cases hv : F.IsVertex v
  · rw [ite_eq_left hv] at h
    have hm : ∃ d ∈ F.dartsAt v, F.item d = .node c := by
      split at h <;> obtain ⟨d, hd, he⟩ := List.mem_map.mp h <;> exact ⟨d, List.mem_of_mem_erase hd, he⟩
    obtain ⟨d, hd, he⟩ := hm
    obtain ⟨hc, hdc⟩ := hdown d hd he
    have := hF.depth_lt c hc
    unfold ht; rw [ite_eq_left hc, ite_eq_left hv]; omega
  · rw [ite_eq_right hv] at h
    by_cases ht' : F.IsTop v
    · rw [ite_eq_left ht'] at h
      have htv : F.ht v = F.H + 1 := by unfold ht; rw [ite_eq_right hv, ite_eq_left ht']
      have hle : ∀ c, F.IsVertex c → F.ht c ≤ F.H := by intro c hc; unfold ht; rw [ite_eq_left hc]; omega
      rw [htv]
      obtain ⟨_, hr, hroot⟩ := ht'
      rcases List.mem_cons.mp h with he | he
      · cases he; have := hle _ hr; omega
      · split at he
        · rw [List.mem_singleton] at he
          unfold item at he
          split at he
          · rename_i hz hdn
            cases he
            obtain ⟨hcv, _, _⟩ := down_child hF hz hdn
            have := hle _ hcv; omega
          · cases he
        · simp at he
    · rw [ite_eq_right ht'] at h; simp at h

end valid

/-- The plan of a valid forest. -/
def plan (hF : F.Valid) : Plan where
  parts := F.parts
  ht := F.ht
  tgt := F.tgt
  ht_lt := ht_lt hF

/-! ### Darts of the forest -/

section darts

variable {F : ForestData}

theorem isUp_pair {d : Nat} : F.IsUp (pair d) ↔ F.IsDown d := Iff.rfl
theorem isDown_pair {d : Nat} : F.IsDown (pair d) ↔ F.IsUp d := by
  unfold IsDown; rw [pair_pair]

theorem isTree_pair {d : Nat} : F.IsTree (pair d) ↔ F.IsTree d := by
  unfold IsTree; rw [isUp_pair, isDown_pair]; exact Or.comm

/-- A dart closing a chord at its own vertex: its partner lies below. -/
def InEnd (F : ForestData) (d : Nat) : Prop := F.IsBack d ∧ F.Desc (F.rep d) (F.rep (pair d))

/-- A dart opening a chord: its partner lies above. -/
def OutEnd (F : ForestData) (d : Nat) : Prop := F.IsBack d ∧ F.Desc (F.rep (pair d)) (F.rep d)

variable (hF : F.Valid)
include hF

theorem not_up_and_down {d : Nat} (hd : d < 2 * F.E) (hu : F.IsUp d) (hdn : F.IsDown d) : False := by
  have h1 := down_child hF hd hdn
  have h2 := down_child hF (pair_lt hd) (isDown_pair.mpr hu)
  rw [pair_pair] at h2
  have e1 := hF.depth_up _ h1.1 h1.2.1
  have e2 := hF.depth_up _ h2.1 h2.2.1
  rw [h1.2.2] at e1; rw [h2.2.2] at e2
  omega

omit hF in
theorem isBack_pair {d : Nat} (h : F.IsBack d) : F.IsBack (pair d) :=
  ⟨pair_lt h.1, fun ht => h.2 (isTree_pair.mp ht)⟩

theorem back_in_or_out {d : Nat} (h : F.IsBack d) : F.InEnd d ∨ F.OutEnd d := by
  rcases hF.back d h.1 h.2 with h1 | h1
  · exact Or.inr ⟨h, h1⟩
  · exact Or.inl ⟨h, h1⟩

theorem not_in_and_out {d : Nat} (h1 : F.InEnd d) (h2 : F.OutEnd d) : False := by
  have := desc_antisymm hF (isVertex_rep hF h1.1.1) h2.2 h1.2
  exact hF.noloop d h1.1.1 this

omit hF in
theorem outEnd_pair {d : Nat} : F.OutEnd d ↔ F.InEnd (pair d) := by
  unfold OutEnd InEnd
  rw [pair_pair]
  constructor
  · rintro ⟨hb, h⟩; exact ⟨isBack_pair hb, h⟩
  · rintro ⟨hb, h⟩; refine ⟨?_, h⟩
    have := isBack_pair hb; rwa [pair_pair] at this

theorem rep_ne_pair {d : Nat} (hd : d < 2 * F.E) : F.rep (pair d) ≠ F.rep d := hF.noloop d hd

/-- The down dart to a child. -/
theorem child_down {v c : Nat} (hc : F.IsVertex c) (hroot : ¬ F.IsRoot c) (hup : F.up c = v) :
    pair (F.par c) ∈ F.dartsAt v ∧ F.IsDown (pair (F.par c)) ∧ F.rep (pair (pair (F.par c))) = c := by
  have hpl := hF.par_lt c hc hroot
  have hpr := hF.par_rep c hc hroot
  refine ⟨mem_dartsAt.mpr ⟨pair_lt hpl, ?_⟩, ?_, by rw [pair_pair, hpr]⟩
  · rw [← hup]; unfold up; rw [ite_eq_right hroot]
  · show F.IsUp (pair (pair (F.par c)))
    rw [pair_pair]; exact ⟨by rw [hpr]; exact hroot, by rw [hpr]⟩

/-- The darts of a vertex are distinct elements of a list of at most three. -/
theorem four_darts {a x y z w : Nat} (hx : x ∈ F.dartsAt a) (hy : y ∈ F.dartsAt a) (hz : z ∈ F.dartsAt a)
    (hw : w ∈ F.dartsAt a) (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w) (hyz : y ≠ z) (hyw : y ≠ w)
    (hzw : z ≠ w) : False := by
  have hnd : [x, y, z, w].Nodup := by simp [hxy, hxz, hxw, hyz, hyw, hzw]
  have := hnd.length_le_of_subset (l₂ := F.dartsAt a) (by
    intro u hu; simp at hu; rcases hu with rfl | rfl | rfl | rfl <;> assumption)
  have := hF.deg a
  simp at *; omega

theorem only_three {a x y z u : Nat} (hx : x ∈ F.dartsAt a) (hy : y ∈ F.dartsAt a) (hz : z ∈ F.dartsAt a)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (hu : u ∈ F.dartsAt a) : u = x ∨ u = y ∨ u = z := by
  apply Classical.byContradiction
  intro h
  have h1 : u ≠ x := fun e => h (Or.inl e)
  have h2 : u ≠ y := fun e => h (Or.inr (Or.inl e))
  have h3 : u ≠ z := fun e => h (Or.inr (Or.inr e))
  exact four_darts hF hu hx hy hz h1 h2 h3 hxy hxz hyz

/-- A vertex with a closing dart has a child below which the partner lies. -/
theorem inEnd_child {d : Nat} (h : F.InEnd d) :
    ∃ c, F.IsVertex c ∧ ¬ F.IsRoot c ∧ F.up c = F.rep d ∧ F.Desc c (F.rep (pair d)) :=
  desc_child hF (isVertex_rep hF (pair_lt h.1.1)) h.2 (rep_ne_pair hF h.1.1)

omit hF in
theorem tree_not_back {d : Nat} (h : F.IsTree d) : ¬ F.IsBack d := fun hb => hb.2 h

theorem par_isUp {r : Nat} (hr : F.IsVertex r) (hroot : ¬ F.IsRoot r) : F.IsUp (F.par r) := by
  have := hF.par_rep r hr hroot
  exact ⟨by rw [this]; exact hroot, by rw [this]⟩

/-- A non-root vertex closes at most one chord. -/
theorem inEnd_unique {a d1 d2 : Nat} (hroot : ¬ F.IsRoot a) (h1 : F.InEnd d1) (h2 : F.InEnd d2)
    (r1 : F.rep d1 = a) (r2 : F.rep d2 = a) : d1 = d2 := by
  apply Classical.byContradiction
  intro hne
  have ha : F.IsVertex a := by rw [← r1]; exact isVertex_rep hF h1.1.1
  obtain ⟨c, hc, hcr, hcu, _⟩ := inEnd_child hF h1
  rw [r1] at hcu
  obtain ⟨ht, htd, _⟩ := child_down hF hc hcr hcu
  have hp : F.par a ∈ F.dartsAt a := mem_dartsAt.mpr ⟨hF.par_lt a ha hroot, hF.par_rep a ha hroot⟩
  have hpu := par_isUp hF ha hroot
  have m1 : d1 ∈ F.dartsAt a := mem_dartsAt.mpr ⟨h1.1.1, r1⟩
  have m2 : d2 ∈ F.dartsAt a := mem_dartsAt.mpr ⟨h2.1.1, r2⟩
  have b1 := h1.1; have b2 := h2.1
  exact four_darts hF m1 m2 ht hp hne
    (fun e => b1.2 (e ▸ Or.inr htd)) (fun e => b1.2 (e ▸ Or.inl hpu))
    (fun e => b2.2 (e ▸ Or.inr htd)) (fun e => b2.2 (e ▸ Or.inl hpu))
    (fun e => not_up_and_down hF (mem_dartsAt.mp ht).1 (e ▸ hpu) htd)

omit hF in
theorem zOf_mem {r : Nat} (h : F.zOf r < 2 * F.E) : F.zOf r ∈ F.dartsAt r ∧ (F.dartsAt r).length = 3 := by
  unfold zOf at h ⊢
  by_cases h3 : (F.dartsAt r).length = 3
  · rw [ite_eq_left h3] at h ⊢
    refine ⟨?_, h3⟩
    split
    · rename_i d hd
      exact (List.mem_filter.mp (List.mem_of_getLast? hd)).1
    · cases hl : F.dartsAt r with
      | nil => rw [hl] at h3; simp at h3
      | cons a l => simp [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast]
  · rw [ite_eq_right h3] at h; omega

omit hF in
theorem zOf_ge {r : Nat} (h : (F.dartsAt r).length ≠ 3) : F.zOf r = 2 * F.E := by
  unfold zOf; rw [ite_eq_right h]

omit hF in
/-- If a root of degree three has a dart outside the forest, its distinguished dart is one. -/
theorem zOf_back {r d : Nat} (h3 : (F.dartsAt r).length = 3) (hd : d ∈ F.dartsAt r) (hb : ¬ F.IsTree d) :
    F.zOf r ∈ (F.dartsAt r).filter (fun d => !decide (F.IsTree d)) := by
  unfold zOf; rw [ite_eq_left h3]
  split
  · rename_i z hz; exact List.mem_of_getLast? hz
  · rename_i hz
    rw [List.getLast?_eq_none_iff] at hz
    have : d ∈ (F.dartsAt r).filter (fun d => !decide (F.IsTree d)) := List.mem_filter.mpr ⟨hd, by simp [hb]⟩
    rw [hz] at this; simp at this

/-- A root closes at most one chord besides its distinguished dart. -/
theorem inEnd_unique_root {a d1 d2 : Nat} (_hroot : F.IsRoot a) (h1 : F.InEnd d1) (h2 : F.InEnd d2)
    (r1 : F.rep d1 = a) (r2 : F.rep d2 = a) (z1 : d1 ≠ F.zOf a) (z2 : d2 ≠ F.zOf a) : d1 = d2 := by
  apply Classical.byContradiction
  intro hne
  obtain ⟨c, hc, hcr, hcu, _⟩ := inEnd_child hF h1
  rw [r1] at hcu
  obtain ⟨ht, htd, _⟩ := child_down hF hc hcr hcu
  have m1 : d1 ∈ F.dartsAt a := mem_dartsAt.mpr ⟨h1.1.1, r1⟩
  have m2 : d2 ∈ F.dartsAt a := mem_dartsAt.mpr ⟨h2.1.1, r2⟩
  have n1 : d1 ≠ pair (F.par c) := fun e => h1.1.2 (e ▸ Or.inr htd)
  have n2 : d2 ≠ pair (F.par c) := fun e => h2.1.2 (e ▸ Or.inr htd)
  have h3 : (F.dartsAt a).length = 3 := by
    have hnd : [d1, d2, pair (F.par c)].Nodup := by simp [hne, n1, n2]
    have hl1 := hnd.length_le_of_subset (l₂ := F.dartsAt a) (by
      intro u hu; simp at hu; rcases hu with rfl | rfl | rfl <;> assumption)
    have hl2 := hF.deg a
    simp only [List.length_cons, List.length_nil] at hl1; omega
  have hz := zOf_back h3 m1 h1.1.2
  obtain ⟨hzm, _⟩ := List.mem_filter.mp hz
  rcases only_three hF m1 m2 ht hne n1 n2 hzm with e | e | e
  · exact z1 e.symm
  · exact z2 e.symm
  · have := (List.mem_filter.mp hz).2
    rw [e] at this; simp [Or.inr htd, IsTree] at this

end darts

/-! ### The darts below a node -/

section below

variable {F : ForestData}

/-- The darts of a root outside its distinguished dart and the subtree of that dart. -/
def ZExcl (F : ForestData) (r e : Nat) : Prop :=
  e ≠ F.zOf r ∧ ¬ (F.zOf r < 2 * F.E ∧ F.IsDown (F.zOf r) ∧ F.Desc (F.rep (pair (F.zOf r))) (F.rep e))

variable (hF : F.Valid)
include hF

omit hF in
theorem parts_vertex {v : Nat} (hv : F.IsVertex v) :
    F.parts v = ((F.dartsAt v).erase (if F.IsRoot v then F.zOf v else F.par v)).map F.item := by
  unfold parts; rw [ite_eq_left hv]; split <;> rfl

theorem id_item {d e : Nat} : e ∈ (F.plan hF).ID (F.item d) ↔
    (F.IsDown d ∧ e ∈ (F.plan hF).D (F.rep (pair d))) ∨ (¬ F.IsDown d ∧ e = d) := by
  unfold item
  split
  · rename_i h; simp [Plan.ID, Plan.partW, Plan.D, h]
  · rename_i h; simp [Plan.ID, Plan.partW, h]

omit hF in
theorem not_up_root {d : Nat} (h : F.IsRoot (F.rep d)) : ¬ F.IsUp d := fun hu => hu.1 h

omit hF in
theorem back_of_not_tree_part {v q : Nat} (_hv : F.IsVertex v) (hq : q ∈ F.dartsAt v)
    (hX : q ≠ (if F.IsRoot v then F.zOf v else F.par v)) (hd : ¬ F.IsDown q) : F.IsBack q := by
  obtain ⟨hql, hqr⟩ := mem_dartsAt.mp hq
  refine ⟨hql, fun ht => ?_⟩
  rcases ht with hu | hdn
  · by_cases hroot : F.IsRoot v
    · exact hu.1 (by rw [hqr]; exact hroot)
    · rw [ite_eq_right hroot] at hX
      exact hX (by rw [← hu.2, hqr])
  · exact hd hdn

/-- **The darts below a vertex**: the darts outside the forest at its descendants (for a root,
outside its distinguished dart and that dart's subtree). -/
theorem mem_D_vertex : ∀ v, F.IsVertex v → ∀ e, e ∈ (F.plan hF).D v ↔
    F.IsBack e ∧ F.Desc v (F.rep e) ∧ (F.IsRoot v → F.ZExcl v e) := by
  have main : ∀ k v, F.IsVertex v → F.H - F.depth v = k → ∀ e, e ∈ (F.plan hF).D v ↔
      F.IsBack e ∧ F.Desc v (F.rep e) ∧ (F.IsRoot v → F.ZExcl v e) := by
    intro k
    induction k using Nat.strongRecOn with
    | _ k ih =>
      intro v hv hk e
      have hdl := hF.depth_lt v hv
      have IHc : ∀ c, F.IsVertex c → ¬ F.IsRoot c → F.up c = v →
          (e ∈ (F.plan hF).D c ↔ F.IsBack e ∧ F.Desc c (F.rep e)) := by
        intro c hc hcr hcu
        have hdc := hF.depth_up c hc hcr
        rw [hcu] at hdc
        have := hF.depth_lt c hc
        rw [ih (F.H - F.depth c) (by omega) c hc rfl e]
        exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, fun h' => absurd h' hcr⟩⟩
      let X := if F.IsRoot v then F.zOf v else F.par v
      have hpv : (F.plan hF).parts v = ((F.dartsAt v).erase X).map F.item := parts_vertex hv
      have hmemL : ∀ q, q ∈ (F.dartsAt v).erase X ↔ q ∈ F.dartsAt v ∧ q ≠ X := by
        intro q; rw [(dartsAt_nodup v).mem_erase_iff]; exact And.comm
      rw [Plan.mem_D]
      show (∃ it ∈ F.parts v, e ∈ (F.plan hF).ID it) ↔ _
      rw [parts_vertex hv]
      constructor
      · rintro ⟨it, hit, he⟩
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hit
        obtain ⟨hqd, hqX⟩ := (hmemL q).mp hq
        obtain ⟨hql, hqr⟩ := mem_dartsAt.mp hqd
        rcases (id_item hF).mp he with ⟨hdn, he'⟩ | ⟨hdn, rfl⟩
        · obtain ⟨hc, hcr, hcu⟩ := down_child hF hql hdn
          rw [hqr] at hcu
          obtain ⟨hb, hdesc⟩ := (IHc _ hc hcr hcu).mp he'
          refine ⟨hb, desc_trans ⟨1, hcu⟩ hdesc, fun hroot => ⟨?_, ?_⟩⟩
          · intro hez
            have hd := desc_depth hF (isVertex_rep hF hb.1) hdesc
            have hzl : F.zOf v < 2 * F.E := by rw [← hez]; exact hb.1
            have := (mem_dartsAt.mp (zOf_mem hzl).1).2
            rw [← hez] at this
            rw [this] at hd
            have := hF.depth_up _ hc hcr; rw [hcu] at this; omega
          · rintro ⟨hzl, hzd, hz⟩
            obtain ⟨hc3, hc3r, hc3u⟩ := down_child hF hzl hzd
            rw [(mem_dartsAt.mp (zOf_mem hzl).1).2] at hc3u
            have e1 := hF.depth_up _ hc hcr
            have e2 := hF.depth_up _ hc3 hc3r
            rw [hcu] at e1; rw [hc3u] at e2
            have hcc := desc_unique hF (isVertex_rep hF hb.1) hdesc hz (by omega)
            apply hqX
            have q1 := hdn.2
            have q2 := hzd.2
            rw [← hcc] at q2
            have : pair q = pair (F.zOf v) := q1.symm.trans q2
            have := pair_inj this
            simp only [X, ite_eq_left hroot]; exact this
        · have hb := back_of_not_tree_part hv hqd hqX hdn
          refine ⟨hb, by rw [hqr]; exact desc_refl _, fun hroot => ⟨?_, ?_⟩⟩
          · simp only [X, ite_eq_left hroot] at hqX; exact hqX
          · rintro ⟨hzl, hzd, hz⟩
            obtain ⟨hc3, hc3r, hc3u⟩ := down_child hF hzl hzd
            rw [(mem_dartsAt.mp (zOf_mem hzl).1).2] at hc3u
            rw [hqr] at hz
            have := desc_depth hF hv hz
            have := hF.depth_up _ hc3 hc3r; rw [hc3u] at this; omega
      · rintro ⟨hb, hdesc, hz⟩
        by_cases hev : F.rep e = v
        · refine ⟨F.item e, List.mem_map.mpr ⟨e, (hmemL e).mpr ⟨mem_dartsAt.mpr ⟨hb.1, hev⟩, ?_⟩, rfl⟩,
            (id_item hF).mpr (Or.inr ⟨fun h => hb.2 (Or.inr h), rfl⟩)⟩
          by_cases hroot : F.IsRoot v
          · simp only [X, ite_eq_left hroot]; exact (hz hroot).1
          · simp only [X, ite_eq_right hroot]
            intro he
            exact hb.2 (Or.inl (he ▸ par_isUp hF hv hroot))
        · obtain ⟨c, hc, hcr, hcu, hce⟩ := desc_child hF (isVertex_rep hF hb.1) hdesc hev
          obtain ⟨ht, htd, htc⟩ := child_down hF hc hcr hcu
          refine ⟨F.item (pair (F.par c)), List.mem_map.mpr ⟨_, (hmemL _).mpr ⟨ht, ?_⟩, rfl⟩,
            (id_item hF).mpr (Or.inl ⟨htd, by rw [htc]; exact (IHc c hc hcr hcu).mpr ⟨hb, hce⟩⟩)⟩
          by_cases hroot : F.IsRoot v
          · simp only [X, ite_eq_left hroot]
            intro he
            apply (hz hroot).2
            refine ⟨by rw [← he]; exact (mem_dartsAt.mp ht).1, by rw [← he]; exact htd, ?_⟩
            rw [← he, htc]; exact hce
          · simp only [X, ite_eq_right hroot]
            intro he
            exact not_up_and_down hF (mem_dartsAt.mp ht).1 (he ▸ par_isUp hF hv hroot) htd
  exact fun v hv e => main _ v hv rfl e

omit hF in
theorem top_isTop {r : Nat} (hr : F.IsVertex r) (hroot : F.IsRoot r) :
    ¬ F.IsVertex (F.top r) ∧ F.IsTop (F.top r) ∧ F.top r - 2 * F.E = r := by
  unfold top IsTop IsVertex
  refine ⟨fun h => by omega, ⟨by omega, ?_, ?_⟩, by omega⟩ <;> rw [show 2 * F.E + r - 2 * F.E = r by omega]
  · exact hr
  · exact hroot

omit hF in
theorem parts_top {r : Nat} (hr : F.IsVertex r) (hroot : F.IsRoot r) :
    F.parts (F.top r) = .node r :: (if F.zOf r < 2 * F.E then [F.item (F.zOf r)] else []) := by
  obtain ⟨h1, h2, h3⟩ := top_isTop hr hroot
  unfold parts; rw [ite_eq_right h1, ite_eq_left h2, h3]

/-- An outgoing dart at a root does not exist: back darts at a root close chords. -/
theorem back_root_inEnd {d : Nat} (hb : F.IsBack d) (hroot : F.IsRoot (F.rep d)) : F.InEnd d := by
  rcases back_in_or_out hF hb with h | h
  · exact h
  · exfalso
    have hv := isVertex_rep hF hb.1
    have := desc_depth hF hv h.2
    rw [hF.depth_root _ hv hroot] at this
    have hpv := isVertex_rep hF (pair_lt hb.1)
    have hd0 : F.depth (F.rep (pair d)) = 0 := by omega
    have := desc_unique hF hv h.2 (desc_refl _) (by rw [hd0, hF.depth_root _ hv hroot])
    exact rep_ne_pair hF hb.1 this

/-- The vertices of the tree of a root. -/
theorem desc_root_of_rel {r u u' : Nat} (hr : F.IsVertex r) (hroot : F.IsRoot r) (hu : F.IsVertex u)
    (_hu' : F.IsVertex u') (h : F.Desc r u) (hrel : F.Desc u u' ∨ F.Desc u' u) : F.Desc r u' := by
  rcases hrel with h1 | h1
  · exact desc_trans h h1
  · apply desc_of_desc hF hu h h1
    rw [hF.depth_root r hr hroot]; omega

/-- **The darts below a top node**: all darts outside the forest in the tree. -/
theorem mem_D_top {r : Nat} (hr : F.IsVertex r) (hroot : F.IsRoot r) (e : Nat) :
    e ∈ (F.plan hF).D (F.top r) ↔ F.IsBack e ∧ F.Desc r (F.rep e) := by
  rw [Plan.mem_D]
  show (∃ it ∈ F.parts (F.top r), e ∈ (F.plan hF).ID it) ↔ _
  rw [parts_top hr hroot]
  have hDr := mem_D_vertex hF r hr e
  constructor
  · rintro ⟨it, hit, he⟩
    rcases List.mem_cons.mp hit with rfl | hit
    · have := hDr.mp he; exact ⟨this.1, this.2.1⟩
    · split at hit
      · rename_i hzl
        rw [List.mem_singleton] at hit; subst hit
        rcases (id_item hF).mp he with ⟨hdn, he'⟩ | ⟨hdn, rfl⟩
        · obtain ⟨hc, hcr, hcu⟩ := down_child hF hzl hdn
          rw [(mem_dartsAt.mp (zOf_mem hzl).1).2] at hcu
          have := (mem_D_vertex hF _ hc e).mp he'
          exact ⟨this.1, desc_trans ⟨1, hcu⟩ this.2.1⟩
        · have hzr := (mem_dartsAt.mp (zOf_mem hzl).1).2
          refine ⟨⟨hzl, fun ht => ?_⟩, by rw [hzr]; exact desc_refl _⟩
          rcases ht with hu | hd
          · exact hu.1 (by rw [hzr]; exact hroot)
          · exact hdn hd
      · simp at hit
  · rintro ⟨hb, hdesc⟩
    by_cases hz : F.ZExcl r e
    · exact ⟨.node r, List.mem_cons_self .., hDr.mpr ⟨hb, hdesc, fun _ => hz⟩⟩
    · have hzl : F.zOf r < 2 * F.E := by
        apply Classical.byContradiction
        intro hzl
        apply hz
        exact ⟨fun he => hzl (he ▸ hb.1), fun h => hzl h.1⟩
      refine ⟨F.item (F.zOf r), List.mem_cons_of_mem _ (by rw [ite_eq_left hzl]; exact List.mem_singleton_self _), ?_⟩
      apply (id_item hF).mpr
      by_cases hez : e = F.zOf r
      · refine Or.inr ⟨fun hd => hb.2 (Or.inr (hez ▸ hd)), hez⟩
      · have hd : F.IsDown (F.zOf r) ∧ F.Desc (F.rep (pair (F.zOf r))) (F.rep e) := by
          apply Classical.byContradiction
          intro h
          exact hz ⟨hez, fun ⟨_, h1, h2⟩ => h ⟨h1, h2⟩⟩
        obtain ⟨hc, hcr, _⟩ := down_child hF hzl hd.1
        exact Or.inl ⟨hd.1, (mem_D_vertex hF _ hc e).mpr ⟨hb, hd.2, fun h => absurd h hcr⟩⟩

end below

/-! ### Kinds of the nodes -/

section kinds

variable {F : ForestData} (hF : F.Valid)
include hF

theorem part_in_D {v q e : Nat} (hq : F.item q ∈ F.parts v) (he : e ∈ (F.plan hF).ID (F.item q)) :
    e ∈ (F.plan hF).D v :=
  (Plan.mem_D _).mpr ⟨_, hq, he⟩

/-- The partner of an open end below a non-root vertex lies strictly above it. -/
theorem open_partner {v e : Nat} (hv : F.IsVertex v) (hroot : ¬ F.IsRoot v)
    (he : e ∈ (F.plan hF).D v) (hpe : pair e ∉ (F.plan hF).D v) :
    F.Desc (F.rep (pair e)) v ∧ F.rep (pair e) ≠ v := by
  obtain ⟨hb, hd, _⟩ := (mem_D_vertex hF v hv e).mp he
  have hpb := isBack_pair hb
  have hev := isVertex_rep hF hb.1
  have hpv := isVertex_rep hF hpb.1
  have notin : ¬ F.Desc v (F.rep (pair e)) := fun h =>
    hpe ((mem_D_vertex hF v hv _).mpr ⟨hpb, h, fun h' => absurd h' hroot⟩)
  rcases hF.back e hb.1 hb.2 with h | h
  · rcases Nat.lt_or_ge (F.depth (F.rep (pair e))) (F.depth v) with hl | hl
    · exact ⟨desc_of_desc hF hev h hd (by omega), fun e' => by rw [e'] at hl; omega⟩
    · exact absurd (desc_of_desc hF hev hd h hl) notin
  · exact absurd (desc_trans hd h) notin

/-- The partner of an open end below a root is its distinguished dart. -/
theorem open_partner_root {v e : Nat} (hv : F.IsVertex v) (hroot : F.IsRoot v)
    (he : e ∈ (F.plan hF).D v) (hpe : pair e ∉ (F.plan hF).D v) : pair e = F.zOf v := by
  obtain ⟨hb, hd, hz⟩ := (mem_D_vertex hF v hv e).mp he
  have hpb := isBack_pair hb
  have hev := isVertex_rep hF hb.1
  have hpv := isVertex_rep hF hpb.1
  have hdp : F.Desc v (F.rep (pair e)) := desc_root_of_rel hF hv hroot hev hpv hd (hF.back e hb.1 hb.2).symm
  apply Classical.byContradiction
  intro hne
  have hz' : ¬ F.ZExcl v (pair e) := fun h => hpe ((mem_D_vertex hF v hv _).mpr ⟨hpb, hdp, fun _ => h⟩)
  have hz2 : F.zOf v < 2 * F.E ∧ F.IsDown (F.zOf v) ∧ F.Desc (F.rep (pair (F.zOf v))) (F.rep (pair e)) := by
    apply Classical.byContradiction
    intro h; exact hz' ⟨hne, h⟩
  obtain ⟨hzl, hzd, hzc⟩ := hz2
  obtain ⟨hc3, hc3r, hc3u⟩ := down_child hF hzl hzd
  have hzm := zOf_mem hzl
  rw [(mem_dartsAt.mp hzm.1).2] at hc3u
  have hd3 := hF.depth_up _ hc3 hc3r
  rw [hc3u, hF.depth_root v hv hroot] at hd3
  have hne3 : ¬ F.Desc (F.rep (pair (F.zOf v))) (F.rep e) := fun h => (hz hroot).2 ⟨hzl, hzd, h⟩
  rcases hF.back e hb.1 hb.2 with h | h
  · exact hne3 (desc_trans hzc h)
  · -- `e` lies above the subtree of `zOf v`, hence at the root
    have hde : F.depth (F.rep e) = 0 := by
      apply Classical.byContradiction
      intro h0
      exact hne3 (desc_of_desc hF hpv hzc h (by omega))
    have hev' : F.rep e = v := desc_unique hF hev (desc_refl _) hd (by rw [hde, hF.depth_root v hv hroot])
    have := zOf_back hzm.2 (mem_dartsAt.mpr ⟨hb.1, hev'⟩) hb.2
    have := (List.mem_filter.mp this).2
    simp only [Bool.not_eq_true', decide_eq_false_iff_not] at this
    exact this (Or.inr hzd)

theorem key_of_open {v e : Nat} (hv : F.IsVertex v) (hroot : ¬ F.IsRoot v)
    (he : e ∈ (F.plan hF).D v) (hpe : pair e ∉ (F.plan hF).D v) :
    F.key e ≤ F.depth v ∧ (F.key e = 0 ∨ F.key e = F.depth (F.rep (pair e)) + 1) := by
  obtain ⟨h1, h2⟩ := open_partner hF hv hroot he hpe
  have hpv := isVertex_rep hF (pair_lt ((mem_D_vertex hF v hv e).mp he).1.1)
  have hdl := desc_depth hF hv h1
  have : F.depth (F.rep (pair e)) ≠ F.depth v := fun hd => h2 (desc_unique hF hv h1 (desc_refl _) hd)
  unfold key
  split <;> omega

/-- Open ends below a vertex have distinct keys. -/
theorem open_key_inj {v e f : Nat} (hv : F.IsVertex v)
    (he : e ∈ (F.plan hF).D v) (hpe : pair e ∉ (F.plan hF).D v)
    (hf : f ∈ (F.plan hF).D v) (hpf : pair f ∉ (F.plan hF).D v) (hk : F.key e = F.key f) : e = f := by
  by_cases hroot : F.IsRoot v
  · exact pair_inj ((open_partner_root hF hv hroot he hpe).trans (open_partner_root hF hv hroot hf hpf).symm)
  · obtain ⟨hea, hea'⟩ := open_partner hF hv hroot he hpe
    obtain ⟨hfb, hfb'⟩ := open_partner hF hv hroot hf hpf
    obtain ⟨heb, hed, _⟩ := (mem_D_vertex hF v hv e).mp he
    obtain ⟨hfbk, hfd, _⟩ := (mem_D_vertex hF v hv f).mp hf
    have hav := isVertex_rep hF (pair_lt heb.1)
    have hbv := isVertex_rep hF (pair_lt hfbk.1)
    have inE : F.InEnd (pair e) := ⟨isBack_pair heb, by rw [pair_pair]; exact desc_trans hea hed⟩
    have inF : F.InEnd (pair f) := ⟨isBack_pair hfbk, by rw [pair_pair]; exact desc_trans hfb hfd⟩
    unfold key at hk
    split at hk <;> split at hk
    · rename_i h1 h2
      have hd1 := hF.depth_root _ hav h1.1
      have hd2 := hF.depth_root _ hbv h2.1
      have hab := desc_unique hF hv hea hfb (by rw [hd1, hd2])
      exact pair_inj (h1.2.trans (by rw [hab]; exact h2.2.symm))
    · omega
    · omega
    · rename_i h1 h2
      have hab := desc_unique hF hv hea hfb (by omega)
      by_cases har : F.IsRoot (F.rep (pair e))
      · have z1 : pair e ≠ F.zOf (F.rep (pair e)) := fun h => h1 ⟨har, h⟩
        have z2 : pair f ≠ F.zOf (F.rep (pair e)) := fun h => h2 ⟨hab ▸ har, by rw [← hab]; exact h⟩
        exact pair_inj (inEnd_unique_root hF har inE inF rfl hab.symm z1 z2)
      · exact pair_inj (inEnd_unique hF har inE inF rfl hab.symm)

end kinds

end ForestData

end STACS2027.Embed

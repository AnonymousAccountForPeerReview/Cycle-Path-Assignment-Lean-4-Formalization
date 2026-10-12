module

public import ApproximationHardness.Embed.PlanKind
import Lean.Elab.Tactic.Omega

/-!
# Rotations from bits and the Euler tour of the forest

The bits of the plan give every vertex a cyclic order of its darts (`cycOf`): after the parent dart
come the darts of the parts in the order the bit chooses; at a root, the darts of the parts and
then the distinguished dart. `rotN` is the next dart in this order.
-/

@[expose] public section

namespace STACS2027.Embed

open Complexity Complexity.Planar

/-- The element after `d` in `l`, cyclically (the head if `d` is last or absent). -/
def cnext (l : List Nat) (d : Nat) : Nat :=
  match l.dropWhile (fun x => decide (x ≠ d)) with
  | _ :: y :: _ => y
  | _ => l.headD d

theorem dropWhile_ne_append {A B : List Nat} {d : Nat} (h : d ∉ A) :
    (A ++ d :: B).dropWhile (fun x => decide (x ≠ d)) = d :: B := by
  induction A with
  | nil => simp
  | cons a A ih =>
    have had : a ≠ d := fun e => h (e ▸ List.mem_cons_self ..)
    simp only [List.cons_append, List.dropWhile_cons, ne_eq, had, not_false_eq_true, decide_true,
      ite_true]
    exact ih (fun hd => h (List.mem_cons_of_mem _ hd))

theorem cnext_rot {A B : List Nat} {d : Nat} (hnd : (A ++ d :: B).Nodup) :
    cnext (A ++ d :: B) d = (B ++ A ++ [d]).headD 0 := by
  have hdA : d ∉ A := fun hd => (List.nodup_append.mp hnd).2.2 d hd d (by simp) rfl
  unfold cnext
  rw [dropWhile_ne_append hdA]
  cases B with
  | nil => cases A <;> simp
  | cons y B => simp

theorem cyc_cnext {l : List Nat} (hnd : l.Nodup) : Cyc (cnext l) l :=
  cyc_of_rot fun A x B h => by rw [h]; exact cnext_rot (h ▸ hnd)

theorem cnext_mem {l : List Nat} (hnd : l.Nodup) {d : Nat} (hd : d ∈ l) : cnext l d ∈ l :=
  cyc_maps (cyc_cnext hnd) d hd

/-- The element before `d` in `l` is the element after `d` in the reversed list. -/
theorem cnext_reverse {l : List Nat} (hnd : l.Nodup) {d : Nat} (hd : d ∈ l) :
    cnext l.reverse (cnext l d) = d := by
  obtain ⟨A, B, rfl⟩ := List.append_of_mem hd
  rw [cnext_rot hnd]
  have hr : (A ++ d :: B).reverse = B.reverse ++ d :: A.reverse := by simp
  have hndr : (B.reverse ++ d :: A.reverse).Nodup := by rw [← hr]; exact ((List.reverse_perm _).nodup_iff).mpr hnd
  cases B with
  | cons y B =>
    simp only [List.cons_append, List.headD_cons]
    have : (A ++ d :: y :: B).reverse = B.reverse ++ y :: (d :: A.reverse) := by simp
    rw [this, cnext_rot (by rw [← this]; exact ((List.reverse_perm _).nodup_iff).mpr hnd)]
    simp
  | nil =>
    cases A with
    | nil => simp [cnext]
    | cons a A =>
      simp only [List.nil_append, List.cons_append, List.headD_cons]
      have e2 : (a :: (A ++ [d])).reverse = (d :: A.reverse) ++ a :: [] := by simp
      rw [e2, cnext_rot (by rw [← e2]; exact ((List.reverse_perm _).nodup_iff).mpr hnd)]
      simp

namespace ForestData

variable {F : ForestData}

/-- The dart of a part at its vertex. -/
def itemDart (F : ForestData) : Item → Nat
  | .node c => pair (F.par c)
  | .dart d => d

theorem itemDart_item {q : Nat} : F.itemDart (F.item q) = q := by
  unfold item
  split
  · rename_i h; simp only [itemDart]; rw [h.2, pair_pair]
  · rfl

variable (hF : F.Valid)

/-- The darts of `v` in the cyclic order chosen by the bits. -/
def cycOf (β : Nat → Bool) (v : Nat) : List Nat :=
  if F.IsRoot v then ((F.plan hF).ord β v).map F.itemDart ++ (if F.zOf v < 2 * F.E then [F.zOf v] else [])
  else F.par v :: ((F.plan hF).ord β v).map F.itemDart

/-- The rotation chosen by the bits: the next dart around its vertex. -/
def rotN (β : Nat → Bool) (d : Nat) : Nat := cnext (cycOf hF β (F.rep d)) d

include hF

theorem ord_map_itemDart {β : Nat → Bool} {v : Nat} (hv : F.IsVertex v) :
    ((F.plan hF).ord β v).map F.itemDart =
      if β v then ((F.dartsAt v).erase (if F.IsRoot v then F.zOf v else F.par v)).reverse
      else (F.dartsAt v).erase (if F.IsRoot v then F.zOf v else F.par v) := by
  show (if β v then (F.parts v).reverse else F.parts v).map F.itemDart = _
  rw [parts_vertex hv]
  have : ∀ l : List Nat, (l.map F.item).map F.itemDart = l := by
    intro l
    induction l with
    | nil => rfl
    | cons q l ih => simp only [List.map_cons, itemDart_item, ih]
  split
  · rw [List.map_reverse, this]
  · rw [this]

/-- The cyclic order of a vertex lists its darts, each once. -/
theorem cycOf_perm {β : Nat → Bool} {v : Nat} (hv : F.IsVertex v) :
    (cycOf hF β v).Perm (F.dartsAt v) := by
  unfold cycOf
  rw [ord_map_itemDart hF hv]
  by_cases hroot : F.IsRoot v
  · rw [ite_eq_left hroot]
    simp only [ite_eq_left hroot]
    have hp : ∀ l : List Nat, (if β v then l.reverse else l).Perm l := by
      intro l; split
      · exact List.reverse_perm l
      · exact List.Perm.refl l
    by_cases hz : F.zOf v < 2 * F.E
    · rw [ite_eq_left hz]
      have hm := (zOf_mem hz).1
      exact ((hp _).append_right _).trans ((List.perm_append_comm).trans (List.perm_cons_erase hm).symm)
    · rw [ite_eq_right hz, List.append_nil]
      have : F.zOf v ∉ F.dartsAt v := fun h => hz (mem_dartsAt.mp h).1
      rw [List.erase_of_not_mem this]
      exact hp _
  · rw [ite_eq_right hroot]
    simp only [ite_eq_right hroot]
    have hm : F.par v ∈ F.dartsAt v := mem_dartsAt.mpr ⟨hF.par_lt v hv hroot, hF.par_rep v hv hroot⟩
    have hp : (if β v then ((F.dartsAt v).erase (F.par v)).reverse else (F.dartsAt v).erase (F.par v)).Perm
        ((F.dartsAt v).erase (F.par v)) := by
      split
      · exact List.reverse_perm _
      · exact List.Perm.refl _
    exact (hp.cons _).trans (List.perm_cons_erase hm).symm

theorem cycOf_nodup {β : Nat → Bool} {v : Nat} (hv : F.IsVertex v) : (cycOf hF β v).Nodup :=
  (cycOf_perm hF hv).nodup_iff.mpr (dartsAt_nodup v)

theorem mem_cycOf {β : Nat → Bool} {v d : Nat} (hv : F.IsVertex v) :
    d ∈ cycOf hF β v ↔ d < 2 * F.E ∧ F.rep d = v := by
  rw [(cycOf_perm hF hv).mem_iff, mem_dartsAt]

theorem rotN_lt {β : Nat → Bool} {d : Nat} (hd : d < 2 * F.E) :
    rotN hF β d < 2 * F.E ∧ F.rep (rotN hF β d) = F.rep d := by
  have hv := isVertex_rep hF hd
  have hm : d ∈ cycOf hF β (F.rep d) := (mem_cycOf hF hv).mpr ⟨hd, rfl⟩
  exact (mem_cycOf hF hv).mp (cnext_mem (cycOf_nodup hF hv) hm)

/-- The rotation as a map of the darts. -/
def rot (β : Nat → Bool) (d : Fin (2 * F.E)) : Fin (2 * F.E) := ⟨rotN hF β d.val, (rotN_lt hF d.isLt).1⟩

/-- The inverse rotation (the node permutation of the embedding). -/
def rotInvN (β : Nat → Bool) (d : Nat) : Nat := cnext (cycOf hF β (F.rep d)).reverse d

theorem rotInvN_rotN {β : Nat → Bool} {d : Nat} (hd : d < 2 * F.E) : rotInvN hF β (rotN hF β d) = d := by
  unfold rotInvN
  rw [(rotN_lt hF hd).2]
  have hv := isVertex_rep hF hd
  exact cnext_reverse (cycOf_nodup hF hv) ((mem_cycOf hF hv).mpr ⟨hd, rfl⟩)

theorem rotInvN_lt {β : Nat → Bool} {d : Nat} (hd : d < 2 * F.E) :
    rotInvN hF β d < 2 * F.E ∧ F.rep (rotInvN hF β d) = F.rep d := by
  have hv := isVertex_rep hF hd
  have hnd := cycOf_nodup hF (β := β) hv
  have hm : d ∈ (cycOf hF β (F.rep d)).reverse := List.mem_reverse.mpr ((mem_cycOf hF hv).mpr ⟨hd, rfl⟩)
  have := cnext_mem (((List.reverse_perm _).nodup_iff).mpr hnd) hm
  exact (mem_cycOf hF hv).mp (List.mem_reverse.mp this)

def rotInv (β : Nat → Bool) (d : Fin (2 * F.E)) : Fin (2 * F.E) :=
  ⟨rotInvN hF β d.val, (rotInvN_lt hF d.isLt).1⟩

theorem rot_inj (β : Nat → Bool) : ∀ a b, rot hF β a = rot hF β b → a = b := by
  intro a b h
  apply Fin.ext
  have := congrArg (fun x : Fin (2 * F.E) => rotInvN hF β x.val) h
  simp only [rot] at this
  rwa [rotInvN_rotN hF a.isLt, rotInvN_rotN hF b.isLt] at this

theorem rotN_cyc (β : Nat → Bool) {v : Nat} (hv : F.IsVertex v) : Cyc (rotN hF β) (cycOf hF β v) := by
  have hc := cyc_cnext (cycOf_nodup hF (β := β) hv)
  have heq : ∀ d ∈ cycOf hF β v, rotN hF β d = cnext (cycOf hF β v) d := by
    intro d hd
    unfold rotN; rw [((mem_cycOf hF hv).mp hd).2]
  apply cyc_of_rot
  intro A x B h
  rw [heq x (by rw [h]; simp), h]
  exact cnext_rot (h ▸ cycOf_nodup hF hv)

/-! ### The Euler tour -/

/-- The parent dart of a non-root vertex, as a list. -/
def upL (F : ForestData) (v : Nat) : List Nat := if F.IsVertex v ∧ ¬ F.IsRoot v then [F.par v] else []

/-- The dart from the parent of a non-root vertex, as a list. -/
def downL (F : ForestData) (c : Nat) : List Nat :=
  if F.IsVertex c ∧ ¬ F.IsRoot c then [pair (F.par c)] else []

/-- The Euler tour of the subtree of a node: all its darts in the order of the walk around it. -/
def Ftour (β : Nat → Bool) (v : Nat) : List Nat :=
  ((F.plan hF).ord β v).flatMap (fun it => match it with
    | .node c => if _h : F.ht c < F.ht v then F.downL c ++ Ftour β c else []
    | .dart d => [d]) ++ F.upL v
termination_by F.ht v

/-- The tour of a part. -/
def expandT (β : Nat → Bool) : Item → List Nat
  | .node c => F.downL c ++ Ftour hF β c
  | .dart d => [d]

include hF in
theorem Ftour_eq (β : Nat → Bool) (v : Nat) :
    Ftour hF β v = ((F.plan hF).ord β v).flatMap (expandT hF β) ++ F.upL v := by
  rw [Ftour]
  congr 1
  apply flatMap_congr'
  intro it hit
  cases it with
  | node c => simp only [expandT]; rw [dite_eq_left (ht_lt hF v c ((F.plan hF).mem_ord.mp hit))]
  | dart d => rfl

omit hF in
theorem upL_root {v : Nat} (h : F.IsRoot v) : F.upL v = [] := by simp [upL, h]
omit hF in
theorem upL_nonroot {v : Nat} (hv : F.IsVertex v) (h : ¬ F.IsRoot v) : F.upL v = [F.par v] := by
  simp [upL, hv, h]
omit hF in
theorem downL_root {v : Nat} (h : F.IsRoot v) : F.downL v = [] := by simp [downL, h]
omit hF in
theorem downL_nonroot {v : Nat} (hv : F.IsVertex v) (h : ¬ F.IsRoot v) : F.downL v = [pair (F.par v)] := by
  simp [downL, hv, h]

include hF in
theorem expandT_item {β : Nat → Bool} {q : Nat} (hq : q < 2 * F.E) :
    (F.IsDown q → expandT hF β (F.item q) = q :: Ftour hF β (F.rep (pair q))) ∧
    (¬ F.IsDown q → expandT hF β (F.item q) = [q]) := by
  refine ⟨fun h => ?_, fun h => by rw [item_back h]; rfl⟩
  rw [item_down h]
  obtain ⟨hc, hcr, _⟩ := down_child hF hq h
  show F.downL _ ++ _ = _
  rw [downL_nonroot hc hcr, h.2, pair_pair]; rfl

/-- **The darts of the tour of a vertex**: the darts at its descendants (for a root, outside its
distinguished dart and that dart's subtree). -/
theorem mem_Ftour_vertex (β : Nat → Bool) : ∀ v, F.IsVertex v → ∀ e, e ∈ Ftour hF β v ↔
    e < 2 * F.E ∧ F.Desc v (F.rep e) ∧ (F.IsRoot v → F.ZExcl v e) := by
  have main : ∀ k v, F.IsVertex v → F.H - F.depth v = k → ∀ e, e ∈ Ftour hF β v ↔
      e < 2 * F.E ∧ F.Desc v (F.rep e) ∧ (F.IsRoot v → F.ZExcl v e) := by
    intro k
    induction k using Nat.strongRecOn with
    | _ k ih =>
      intro v hv hk e
      have hdl := hF.depth_lt v hv
      have IHc : ∀ c, F.IsVertex c → ¬ F.IsRoot c → F.up c = v →
          (e ∈ Ftour hF β c ↔ e < 2 * F.E ∧ F.Desc c (F.rep e)) := by
        intro c hc hcr hcu
        have hdc := hF.depth_up c hc hcr
        rw [hcu] at hdc
        have := hF.depth_lt c hc
        rw [ih (F.H - F.depth c) (by omega) c hc rfl e]
        exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, fun h' => absurd h' hcr⟩⟩
      let X := if F.IsRoot v then F.zOf v else F.par v
      have hmemL : ∀ q, q ∈ (F.dartsAt v).erase X ↔ q ∈ F.dartsAt v ∧ q ≠ X := by
        intro q; rw [(dartsAt_nodup v).mem_erase_iff]; exact And.comm
      have hexp : ∀ it, it ∈ (F.plan hF).ord β v ↔ ∃ q ∈ (F.dartsAt v).erase X, F.item q = it := by
        intro it
        rw [(F.plan hF).mem_ord]
        show it ∈ F.parts v ↔ _
        rw [parts_vertex hv, List.mem_map]
      rw [Ftour_eq hF β v, List.mem_append, List.mem_flatMap]
      constructor
      · rintro (⟨it, hit, he⟩ | he)
        · obtain ⟨q, hq, rfl⟩ := (hexp it).mp hit
          obtain ⟨hqd, hqX⟩ := (hmemL q).mp hq
          obtain ⟨hql, hqr⟩ := mem_dartsAt.mp hqd
          by_cases hdn : F.IsDown q
          · rw [(expandT_item hF hql).1 hdn] at he
            obtain ⟨hc, hcr, hcu⟩ := down_child hF hql hdn
            rw [hqr] at hcu
            have hdepth := hF.depth_up _ hc hcr
            rw [hcu] at hdepth
            rcases List.mem_cons.mp he with rfl | he'
            · refine ⟨hql, by rw [hqr]; exact desc_refl _, fun hroot => ⟨?_, ?_⟩⟩
              · simp only [X, ite_eq_left hroot] at hqX; exact hqX
              · rintro ⟨hzl, hzd, hz⟩
                rw [hqr] at hz
                obtain ⟨hc3, hc3r, hc3u⟩ := down_child hF hzl hzd
                rw [(mem_dartsAt.mp (zOf_mem hzl).1).2] at hc3u
                exact not_desc_child_parent hF hc3 hc3r hc3u hv hz
            · obtain ⟨hel, hdesc⟩ := (IHc _ hc hcr hcu).mp he'
              refine ⟨hel, desc_trans ⟨1, hcu⟩ hdesc, fun hroot => ⟨?_, ?_⟩⟩
              · intro hez
                have hzl : F.zOf v < 2 * F.E := by rw [← hez]; exact hel
                have := (mem_dartsAt.mp (zOf_mem hzl).1).2
                rw [← hez] at this
                rw [this] at hdesc
                exact not_desc_child_parent hF hc hcr hcu hv hdesc
              · rintro ⟨hzl, hzd, hz⟩
                obtain ⟨hc3, hc3r, hc3u⟩ := down_child hF hzl hzd
                rw [(mem_dartsAt.mp (zOf_mem hzl).1).2] at hc3u
                have e2 := hF.depth_up _ hc3 hc3r
                rw [hc3u] at e2
                have hcc := desc_unique hF (isVertex_rep hF hel) hdesc hz (by omega)
                apply hqX
                have q2 := hzd.2
                rw [← hcc] at q2
                have := pair_inj (hdn.2.symm.trans q2)
                simp only [X, ite_eq_left hroot]; exact this
          · rw [(expandT_item hF hql).2 hdn, List.mem_singleton] at he
            subst he
            refine ⟨hql, by rw [hqr]; exact desc_refl _, fun hroot => ⟨?_, ?_⟩⟩
            · simp only [X, ite_eq_left hroot] at hqX; exact hqX
            · rintro ⟨hzl, hzd, hz⟩
              rw [hqr] at hz
              obtain ⟨hc3, hc3r, hc3u⟩ := down_child hF hzl hzd
              rw [(mem_dartsAt.mp (zOf_mem hzl).1).2] at hc3u
              exact not_desc_child_parent hF hc3 hc3r hc3u hv hz
        · by_cases hroot : F.IsRoot v
          · rw [upL_root hroot] at he; simp at he
          · rw [upL_nonroot hv hroot, List.mem_singleton] at he
            subst he
            refine ⟨hF.par_lt v hv hroot, by rw [hF.par_rep v hv hroot]; exact desc_refl _,
              fun h => absurd h hroot⟩
      · rintro ⟨hel, hdesc, hz⟩
        by_cases hev : F.rep e = v
        · by_cases heX : e = X
          · by_cases hroot : F.IsRoot v
            · simp only [X, ite_eq_left hroot] at heX; exact absurd heX (hz hroot).1
            · simp only [X, ite_eq_right hroot] at heX
              right; rw [upL_nonroot hv hroot, heX]; simp
          · left
            refine ⟨F.item e, (hexp _).mpr ⟨e, (hmemL e).mpr ⟨mem_dartsAt.mpr ⟨hel, hev⟩, heX⟩, rfl⟩, ?_⟩
            by_cases hdn : F.IsDown e
            · rw [(expandT_item hF hel).1 hdn]; simp
            · rw [(expandT_item hF hel).2 hdn]; simp
        · obtain ⟨c, hc, hcr, hcu, hce⟩ := desc_child hF (isVertex_rep hF hel) hdesc hev
          obtain ⟨ht, htd, htc⟩ := child_down hF hc hcr hcu
          have htX : pair (F.par c) ≠ X := by
            by_cases hroot : F.IsRoot v
            · simp only [X, ite_eq_left hroot]
              intro he
              apply (hz hroot).2
              refine ⟨by rw [← he]; exact (mem_dartsAt.mp ht).1, by rw [← he]; exact htd, ?_⟩
              rw [← he, htc]; exact hce
            · simp only [X, ite_eq_right hroot]
              intro he
              exact not_up_and_down hF (mem_dartsAt.mp ht).1 (he ▸ par_isUp hF hv hroot) htd
          left
          refine ⟨F.item (pair (F.par c)), (hexp _).mpr ⟨_, (hmemL _).mpr ⟨ht, htX⟩, rfl⟩, ?_⟩
          rw [(expandT_item hF (mem_dartsAt.mp ht).1).1 htd, htc]
          exact List.mem_cons_of_mem _ ((IHc c hc hcr hcu).mpr ⟨hel, hce⟩)
  exact fun v hv e => main _ v hv rfl e

include hF in
theorem Ftour_top {β : Nat → Bool} {r : Nat} (hr : F.IsVertex r) (hroot : F.IsRoot r) :
    Ftour hF β (F.top r) = ((F.plan hF).ord β (F.top r)).flatMap (expandT hF β) := by
  rw [Ftour_eq]
  have : F.upL (F.top r) = [] := by
    simp [upL, (top_isTop hr hroot).1]
  rw [this, List.append_nil]

include hF in
theorem expandT_root {β : Nat → Bool} {r : Nat} (hroot : F.IsRoot r) :
    expandT hF β (.node r) = Ftour hF β r := by
  simp [expandT, downL_root hroot]

/-- **The darts of the tour of a tree**: all darts of the tree. -/
theorem mem_Ftour_top (β : Nat → Bool) {r : Nat} (hr : F.IsVertex r) (hroot : F.IsRoot r) (e : Nat) :
    e ∈ Ftour hF β (F.top r) ↔ e < 2 * F.E ∧ F.Desc r (F.rep e) := by
  rw [Ftour_top hF hr hroot, List.mem_flatMap]
  have hord : ∀ it, it ∈ (F.plan hF).ord β (F.top r) ↔
      it = .node r ∨ (F.zOf r < 2 * F.E ∧ it = F.item (F.zOf r)) := by
    intro it
    rw [(F.plan hF).mem_ord]
    show it ∈ F.parts (F.top r) ↔ _
    rw [parts_top hr hroot]
    split
    · rename_i h; simp [h]
    · rename_i h
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      constructor
      · intro h1; exact Or.inl h1
      · rintro (h1 | ⟨h2, _⟩)
        · exact h1
        · exact absurd h2 h
  have hDr := mem_Ftour_vertex hF β r hr e
  constructor
  · rintro ⟨it, hit, he⟩
    rcases (hord it).mp hit with rfl | ⟨hzl, rfl⟩
    · rw [expandT_root hF hroot] at he
      have := hDr.mp he; exact ⟨this.1, this.2.1⟩
    · have hzr := (mem_dartsAt.mp (zOf_mem hzl).1).2
      by_cases hdn : F.IsDown (F.zOf r)
      · rw [(expandT_item hF hzl).1 hdn] at he
        rcases List.mem_cons.mp he with rfl | he'
        · exact ⟨hzl, by rw [hzr]; exact desc_refl _⟩
        · obtain ⟨hc, hcr, hcu⟩ := down_child hF hzl hdn
          rw [hzr] at hcu
          have := (mem_Ftour_vertex hF β _ hc e).mp he'
          exact ⟨this.1, desc_trans ⟨1, hcu⟩ this.2.1⟩
      · rw [(expandT_item hF hzl).2 hdn, List.mem_singleton] at he
        subst he
        exact ⟨hzl, by rw [hzr]; exact desc_refl _⟩
  · rintro ⟨hel, hdesc⟩
    by_cases hz : F.ZExcl r e
    · exact ⟨.node r, (hord _).mpr (Or.inl rfl), by rw [expandT_root hF hroot]; exact hDr.mpr ⟨hel, hdesc, fun _ => hz⟩⟩
    · have hzl : F.zOf r < 2 * F.E := by
        apply Classical.byContradiction
        intro hzl
        exact hz ⟨fun he => hzl (he ▸ hel), fun h => hzl h.1⟩
      refine ⟨F.item (F.zOf r), (hord _).mpr (Or.inr ⟨hzl, rfl⟩), ?_⟩
      by_cases hez : e = F.zOf r
      · subst hez
        by_cases hdn : F.IsDown (F.zOf r)
        · rw [(expandT_item hF hzl).1 hdn]; simp
        · rw [(expandT_item hF hzl).2 hdn]; simp
      · have hd : F.IsDown (F.zOf r) ∧ F.Desc (F.rep (pair (F.zOf r))) (F.rep e) := by
          apply Classical.byContradiction
          intro h
          exact hz ⟨hez, fun ⟨_, h1, h2⟩ => h ⟨h1, h2⟩⟩
        obtain ⟨hc, hcr, _⟩ := down_child hF hzl hd.1
        rw [(expandT_item hF hzl).1 hd.1]
        exact List.mem_cons_of_mem _ ((mem_Ftour_vertex hF β _ hc e).mpr ⟨hel, hd.2, fun h => absurd h hcr⟩)

/-! ### Distinct darts in the tour -/

omit hF in
theorem nodup_flatMap' {α : Type} (l : List α) (f : α → List Nat) (h1 : ∀ x ∈ l, (f x).Nodup)
    (h2 : l.Pairwise (fun a b => ∀ e ∈ f a, e ∉ f b)) : (l.flatMap f).Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons x l ih =>
    rw [List.flatMap_cons]
    obtain ⟨hx, hl⟩ := List.pairwise_cons.mp h2
    refine List.nodup_append.mpr ⟨h1 x (List.mem_cons_self ..), ih (fun y hy => h1 y (List.mem_cons_of_mem _ hy)) hl,
      fun a ha b hb e => ?_⟩
    obtain ⟨y, hy, hb'⟩ := List.mem_flatMap.mp hb
    exact hx y hy a ha (e ▸ hb')

include hF in
theorem ord_vertex {β : Nat → Bool} {v : Nat} (hv : F.IsVertex v) :
    (F.plan hF).ord β v = (((F.plan hF).ord β v).map F.itemDart).map F.item := by
  rw [List.map_map]
  conv => lhs; rw [← List.map_id ((F.plan hF).ord β v)]
  apply List.map_congr_left
  intro it hit
  have : it ∈ F.parts v := (F.plan hF).mem_ord.mp hit
  rw [parts_vertex hv] at this
  obtain ⟨q, _, rfl⟩ := List.mem_map.mp this
  simp [itemDart_item]

theorem Ftour_nodup (β : Nat → Bool) : ∀ v, F.IsVertex v → (Ftour hF β v).Nodup := by
  have main : ∀ k v, F.IsVertex v → F.H - F.depth v = k → (Ftour hF β v).Nodup := by
    intro k
    induction k using Nat.strongRecOn with
    | _ k ih =>
      intro v hv hk
      have hdl := hF.depth_lt v hv
      let X := if F.IsRoot v then F.zOf v else F.par v
      let L := (F.dartsAt v).erase X
      have hmemL : ∀ q, q ∈ L ↔ q ∈ F.dartsAt v ∧ q ≠ X := by
        intro q; show q ∈ (F.dartsAt v).erase X ↔ _
        rw [(dartsAt_nodup v).mem_erase_iff]; exact And.comm
      have hds : ((F.plan hF).ord β v).map F.itemDart = if β v then L.reverse else L :=
        ord_map_itemDart hF hv
      have hndL : L.Nodup := (dartsAt_nodup v).erase X
      -- the darts of the tour of a part
      have hexp : ∀ q ∈ L, ∀ e, e ∈ expandT hF β (F.item q) →
          e = q ∨ (F.IsDown q ∧ F.Desc (F.rep (pair q)) (F.rep e)) := by
        intro q hq e he
        obtain ⟨hql, _⟩ := mem_dartsAt.mp ((hmemL q).mp hq).1
        by_cases hdn : F.IsDown q
        · rw [(expandT_item hF hql).1 hdn] at he
          rcases List.mem_cons.mp he with rfl | he'
          · exact Or.inl rfl
          · obtain ⟨hc, _, _⟩ := down_child hF hql hdn
            exact Or.inr ⟨hdn, ((mem_Ftour_vertex hF β _ hc e).mp he').2.1⟩
        · rw [(expandT_item hF hql).2 hdn, List.mem_singleton] at he; exact Or.inl he
      have hnd1 : ∀ q ∈ L, (expandT hF β (F.item q)).Nodup := by
        intro q hq
        obtain ⟨hql, hqr⟩ := mem_dartsAt.mp ((hmemL q).mp hq).1
        by_cases hdn : F.IsDown q
        · rw [(expandT_item hF hql).1 hdn]
          obtain ⟨hc, hcr, hcu⟩ := down_child hF hql hdn
          rw [hqr] at hcu
          have := hF.depth_up _ hc hcr
          rw [hcu] at this
          have := hF.depth_lt _ hc
          refine List.nodup_cons.mpr ⟨fun h => ?_, ih (F.H - F.depth (F.rep (pair q))) (by omega) _ hc rfl⟩
          have := ((mem_Ftour_vertex hF β _ hc q).mp h).2.1
          rw [hqr] at this
          exact not_desc_child_parent hF hc hcr hcu hv this
        · rw [(expandT_item hF hql).2 hdn]; exact nodup_one q
      have hdisj : ∀ q1 ∈ L, ∀ q2 ∈ L, q1 ≠ q2 → ∀ e ∈ expandT hF β (F.item q1), e ∉ expandT hF β (F.item q2) := by
        intro q1 h1 q2 h2 hne e he1 he2
        obtain ⟨hl1, hr1⟩ := mem_dartsAt.mp ((hmemL q1).mp h1).1
        obtain ⟨hl2, hr2⟩ := mem_dartsAt.mp ((hmemL q2).mp h2).1
        rcases hexp q1 h1 e he1 with rfl | ⟨d1, a1⟩ <;> rcases hexp q2 h2 _ he2 with rfl | ⟨d2, a2⟩
        · exact hne rfl
        · obtain ⟨hc, hcr, hcu⟩ := down_child hF hl2 d2
          rw [hr2] at hcu; rw [hr1] at a2
          exact not_desc_child_parent hF hc hcr hcu hv a2
        · obtain ⟨hc, hcr, hcu⟩ := down_child hF hl1 d1
          rw [hr1] at hcu; rw [hr2] at a1
          exact not_desc_child_parent hF hc hcr hcu hv a1
        · obtain ⟨hc1, hcr1, hcu1⟩ := down_child hF hl1 d1
          obtain ⟨hc2, hcr2, hcu2⟩ := down_child hF hl2 d2
          rw [hr1] at hcu1; rw [hr2] at hcu2
          have hcc := desc_unique hF (isVertex_rep hF (by
            rcases hexp q1 h1 e he1 with h | h
            · exact (h ▸ hl1)
            · exact (mem_Ftour_vertex hF β _ hc1 e).mp (by
                rw [(expandT_item hF hl1).1 d1] at he1
                rcases List.mem_cons.mp he1 with h' | h'
                · exfalso; rw [h'] at a1; rw [hr1] at a1; exact not_desc_child_parent hF hc1 hcr1 hcu1 hv a1
                · exact h') |>.1)) a1 a2
            (by rw [child_depth hF hc1 hcr1 hcu1, child_depth hF hc2 hcr2 hcu2])
          exact hne (pair_inj (by rw [← d1.2, ← d2.2, hcc]))
      rw [Ftour_eq, ord_vertex hF hv, List.flatMap_map, hds]
      have hpar : ∀ q ∈ L, ∀ e ∈ expandT hF β (F.item q), e ∉ F.upL v := by
        intro q hq e he hu
        by_cases hroot : F.IsRoot v
        · rw [upL_root hroot] at hu; simp at hu
        · rw [upL_nonroot hv hroot, List.mem_singleton] at hu
          subst hu
          rcases hexp q hq _ he with h | ⟨d, a⟩
          · exact ((hmemL q).mp hq).2 (by simp only [X, ite_eq_right hroot]; exact h.symm)
          · obtain ⟨hql, hqr⟩ := mem_dartsAt.mp ((hmemL q).mp hq).1
            obtain ⟨hc, hcr, hcu⟩ := down_child hF hql d
            rw [hqr] at hcu
            rw [hF.par_rep v hv hroot] at a
            exact not_desc_child_parent hF hc hcr hcu hv a
      have hupnd : (F.upL v).Nodup := by
        unfold upL; split
        · exact nodup_one _
        · exact List.nodup_nil
      have hpw : ∀ M : List Nat, (∀ q ∈ M, q ∈ L) → M.Nodup →
          M.Pairwise (fun a b => ∀ e ∈ expandT hF β (F.item a), e ∉ expandT hF β (F.item b)) := by
        intro M hM hnd
        exact List.Pairwise.imp_of_mem (fun {a b} ha hb hab => hdisj a (hM a ha) b (hM b hb) hab) hnd
      split
      · refine List.nodup_append.mpr ⟨nodup_flatMap' _ _ (fun q hq => hnd1 q (List.mem_reverse.mp hq))
          (hpw _ (fun q hq => List.mem_reverse.mp hq) (((List.reverse_perm _).nodup_iff).mpr hndL)), hupnd,
          fun a ha b hb e => ?_⟩
        obtain ⟨q, hq, ha'⟩ := List.mem_flatMap.mp ha
        exact hpar q (List.mem_reverse.mp hq) a ha' (e ▸ hb)
      · refine List.nodup_append.mpr ⟨nodup_flatMap' _ _ hnd1 (hpw _ (fun q hq => hq) hndL), hupnd,
          fun a ha b hb e => ?_⟩
        obtain ⟨q, hq, ha'⟩ := List.mem_flatMap.mp ha
        exact hpar q hq a ha' (e ▸ hb)
  exact fun v hv => main _ v hv rfl

/-! ### The Euler tour is a cycle of the forest rotation -/

/-- The rotation composed with the edge involution on the darts of the forest. -/
def sigN (β : Nat → Bool) (d : Nat) : Nat := rotN hF β (if F.IsTree d then pair d else d)

/-- The facts the Euler tour of a part needs. -/
theorem part_facts {β : Nat → Bool} {q : Nat} (hq : q < 2 * F.E) (hb : ¬ F.IsDown q → F.IsBack q)
    (hc : F.IsDown q → Chain (sigN hF β) (Ftour hF β (F.rep (pair q))) ∧
      (Ftour hF β (F.rep (pair q))).head? = some (rotN hF β (F.par (F.rep (pair q)))) ∧
      (Ftour hF β (F.rep (pair q))).getLast? = some (F.par (F.rep (pair q)))) :
    Chain (sigN hF β) (expandT hF β (F.item q)) ∧ (expandT hF β (F.item q)).head? = some q ∧
      ∀ l, (expandT hF β (F.item q)).getLast? = some l → sigN hF β l = rotN hF β q := by
  by_cases hdn : F.IsDown q
  · rw [(expandT_item hF hq).1 hdn]
    obtain ⟨h1, h2, h3⟩ := hc hdn
    have hpar : F.par (F.rep (pair q)) = pair q := hdn.2
    rw [hpar] at h2 h3
    have hqt : F.IsTree q := Or.inr hdn
    have hpt : F.IsTree (pair q) := Or.inl hdn
    refine ⟨chain_cons_iff.mpr ⟨h1, fun b hb' => ?_⟩, rfl, fun l hl => ?_⟩
    · rw [h2] at hb'; simp at hb'; rw [← hb']
      unfold sigN; rw [ite_eq_left hqt]
    · have hne : Ftour hF β (F.rep (pair q)) ≠ [] := by intro h; rw [h] at h2; simp at h2
      have : (q :: Ftour hF β (F.rep (pair q))).getLast? = (Ftour hF β (F.rep (pair q))).getLast? := by
        cases h' : Ftour hF β (F.rep (pair q)) with
        | nil => exact absurd h' hne
        | cons x xs => rw [List.getLast?_cons_cons]
      rw [this, h3] at hl; simp at hl; rw [← hl]
      unfold sigN; rw [ite_eq_left hpt, pair_pair]
  · rw [(expandT_item hF hq).2 hdn]
    have hnt : ¬ F.IsTree q := (hb hdn).2
    refine ⟨Chain.one q, rfl, fun l hl => ?_⟩
    simp at hl; rw [← hl]
    unfold sigN; rw [ite_eq_right hnt]

/-- **Euler tour of a non-root vertex**: the forest rotation walks along it, starting with the dart
after the parent dart and ending with the parent dart. -/
theorem euler (β : Nat → Bool) : ∀ v, F.IsVertex v → ¬ F.IsRoot v →
    Chain (sigN hF β) (Ftour hF β v) ∧ (Ftour hF β v).head? = some (rotN hF β (F.par v)) ∧
      (Ftour hF β v).getLast? = some (F.par v) := by
  have main : ∀ k v, F.IsVertex v → ¬ F.IsRoot v → F.H - F.depth v = k →
      Chain (sigN hF β) (Ftour hF β v) ∧ (Ftour hF β v).head? = some (rotN hF β (F.par v)) ∧
      (Ftour hF β v).getLast? = some (F.par v) := by
    intro k
    induction k using Nat.strongRecOn with
    | _ k ih =>
      intro v hv hroot hk
      have hdl := hF.depth_lt v hv
      let L := (F.dartsAt v).erase (F.par v)
      have hX : (if F.IsRoot v then F.zOf v else F.par v) = F.par v := ite_eq_right hroot
      have hmemL : ∀ q, q ∈ L ↔ q ∈ F.dartsAt v ∧ q ≠ F.par v := by
        intro q; show q ∈ (F.dartsAt v).erase (F.par v) ↔ _
        rw [(dartsAt_nodup v).mem_erase_iff]; exact And.comm
      have facts : ∀ q ∈ L, Chain (sigN hF β) (expandT hF β (F.item q)) ∧
          (expandT hF β (F.item q)).head? = some q ∧
          ∀ l, (expandT hF β (F.item q)).getLast? = some l → sigN hF β l = rotN hF β q := by
        intro q hq
        obtain ⟨hqd, hqX⟩ := (hmemL q).mp hq
        obtain ⟨hql, hqr⟩ := mem_dartsAt.mp hqd
        refine part_facts hF hql (fun hdn => back_of_not_tree_part hv hqd (by rw [hX]; exact hqX) hdn)
          (fun hdn => ?_)
        obtain ⟨hc, hcr, hcu⟩ := down_child hF hql hdn
        rw [hqr] at hcu
        have := hF.depth_up _ hc hcr
        rw [hcu] at this
        have := hF.depth_lt _ hc
        exact ih (F.H - F.depth (F.rep (pair q))) (by omega) _ hc hcr rfl
      have hds : ((F.plan hF).ord β v).map F.itemDart = if β v then L.reverse else L := by
        have := ord_map_itemDart hF (β := β) hv; rw [hX] at this; exact this
      have hcyc := rotN_cyc hF β hv
      unfold cycOf at hcyc
      rw [ite_eq_right hroot, hds] at hcyc
      rw [Ftour_eq, ord_vertex hF hv, List.flatMap_map, hds, upL_nonroot hv hroot]
      have hlen : L.length ≤ 2 := by
        have := hF.deg v
        have hm : F.par v ∈ F.dartsAt v := mem_dartsAt.mpr ⟨hF.par_lt v hv hroot, hF.par_rep v hv hroot⟩
        show ((F.dartsAt v).erase (F.par v)).length ≤ 2
        rw [List.length_erase_of_mem hm]; omega
      have key : ∀ M : List Nat, (∀ q ∈ M, q ∈ L) → M.length ≤ 2 → Cyc (rotN hF β) (F.par v :: M) →
          Chain (sigN hF β) (M.flatMap (fun q => expandT hF β (F.item q)) ++ [F.par v]) ∧
          (M.flatMap (fun q => expandT hF β (F.item q)) ++ [F.par v]).head? = some (rotN hF β (F.par v)) ∧
          (M.flatMap (fun q => expandT hF β (F.item q)) ++ [F.par v]).getLast? = some (F.par v) := by
        intro M hM hlM hcM
        refine ⟨?_, ?_, by simp⟩
        · rcases M with _ | ⟨a, _ | ⟨b, _ | ⟨c, M⟩⟩⟩
          · exact Chain.one _
          · obtain ⟨f1, f2, f3⟩ := facts a (hM a (by simp))
            obtain ⟨r1, r2⟩ := cyc_two hcM
            simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
            exact chain_append.mpr ⟨f1, Chain.one _, fun x y hx hy => by
              have hyb : y = F.par v := by simpa using hy.symm
              rw [hyb, f3 x hx, r2]⟩
          · obtain ⟨f1, f2, f3⟩ := facts a (hM a (by simp))
            obtain ⟨g1, g2, g3⟩ := facts b (hM b (by simp))
            obtain ⟨r1, r2, r3⟩ := cyc_three hcM
            simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]
            refine chain_append.mpr ⟨f1, chain_append.mpr ⟨g1, Chain.one _, fun x y hx hy => ?_⟩,
              fun x y hx hy => ?_⟩
            · have hyb : y = F.par v := by simpa using hy.symm
              rw [hyb, g3 x hx, r3]
            · have hyb : y = b := by
                rw [List.head?_append, g2] at hy; simp at hy; exact hy.symm
              rw [hyb, f3 x hx, r2]
          · simp at hlM
        · rcases M with _ | ⟨a, M⟩
          · simp [cyc_one hcM]
          · obtain ⟨_, f2, _⟩ := facts a (hM a (by simp))
            have hr : rotN hF β (F.par v) = a := (chain_cons_iff.mp hcM.1).2 a rfl
            simp only [List.flatMap_cons, List.append_assoc, List.head?_append, f2, hr]; rfl
      by_cases hb : β v = true
      · rw [ite_eq_left hb] at hcyc ⊢
        exact key L.reverse (fun q hq => List.mem_reverse.mp hq) (by simp; omega) hcyc
      · rw [ite_eq_right hb] at hcyc ⊢
        exact key L (fun q hq => hq) hlen hcyc
  exact fun v hv hroot => main _ v hv hroot rfl

/-- The tour of a part of a vertex has the facts `part_facts` describes. -/
theorem part_facts_at {β : Nat → Bool} {v q : Nat} (hv : F.IsVertex v) (hq : q ∈ F.dartsAt v)
    (hqX : q ≠ (if F.IsRoot v then F.zOf v else F.par v)) :
    Chain (sigN hF β) (expandT hF β (F.item q)) ∧ (expandT hF β (F.item q)).head? = some q ∧
      ∀ l, (expandT hF β (F.item q)).getLast? = some l → sigN hF β l = rotN hF β q := by
  obtain ⟨hql, hqr⟩ := mem_dartsAt.mp hq
  refine part_facts hF hql (fun hdn => back_of_not_tree_part hv hq hqX hdn) (fun hdn => ?_)
  obtain ⟨hc, hcr, _⟩ := down_child hF hql hdn
  exact euler hF β _ hc hcr

/-- **The Euler tour of a tree is a cycle of the forest rotation.** -/
theorem top_cyc (β : Nat → Bool) {r : Nat} (hr : F.IsVertex r) (hroot : F.IsRoot r) :
    Cyc (sigN hF β) (Ftour hF β (F.top r)) := by
  let L := (F.dartsAt r).erase (F.zOf r)
  have hX : (if F.IsRoot r then F.zOf r else F.par r) = F.zOf r := ite_eq_left hroot
  have hmemL : ∀ q, q ∈ L ↔ q ∈ F.dartsAt r ∧ q ≠ F.zOf r := by
    intro q; show q ∈ (F.dartsAt r).erase (F.zOf r) ↔ _
    rw [(dartsAt_nodup r).mem_erase_iff]; exact And.comm
  have facts : ∀ q ∈ L, Chain (sigN hF β) (expandT hF β (F.item q)) ∧
      (expandT hF β (F.item q)).head? = some q ∧
      ∀ l, (expandT hF β (F.item q)).getLast? = some l → sigN hF β l = rotN hF β q := by
    intro q hq
    obtain ⟨hqd, hqX⟩ := (hmemL q).mp hq
    exact part_facts_at hF hr hqd (by rw [hX]; exact hqX)
  have hds : ((F.plan hF).ord β r).map F.itemDart = if β r then L.reverse else L := by
    have := ord_map_itemDart hF (β := β) hr; rw [hX] at this; exact this
  have hcyc := rotN_cyc hF β hr
  unfold cycOf at hcyc
  rw [ite_eq_left hroot, hds] at hcyc
  have hFr : Ftour hF β r = (if β r then L.reverse else L).flatMap (fun q => expandT hF β (F.item q)) := by
    rw [Ftour_eq, ord_vertex hF hr, List.flatMap_map, hds, upL_root hroot, List.append_nil]
  rw [Ftour_top hF hr hroot]
  have hrL : r ∈ F.dartsAt r := mem_dartsAt.mpr ⟨hr.1, hr.2⟩
  have hdeg := hF.deg r
  -- the darts of the root in the chosen order
  obtain ⟨M, hM, hMd, hMlen⟩ : ∃ M : List Nat, (if β r then L.reverse else L) = M ∧ (∀ q ∈ M, q ∈ L) ∧
      M.length = L.length := by
    refine ⟨_, rfl, fun q hq => ?_, ?_⟩
    · split at hq
      · exact List.mem_reverse.mp hq
      · exact hq
    · split <;> simp
  rw [hM] at hcyc hFr
  by_cases hzl : F.zOf r < 2 * F.E
  · have hzm := zOf_mem hzl
    have hLlen : L.length = 2 := by
      show ((F.dartsAt r).erase (F.zOf r)).length = 2
      rw [List.length_erase_of_mem hzm.1, hzm.2]
    rw [hLlen] at hMlen
    obtain ⟨a, b, rfl⟩ : ∃ a b, M = [a, b] := by
      rcases M with _ | ⟨a, _ | ⟨b, _ | ⟨c, M⟩⟩⟩ <;> simp at hMlen
      exact ⟨a, b, rfl⟩
    rw [ite_eq_left hzl] at hcyc
    obtain ⟨r1, r2, r3⟩ := cyc_three hcyc
    obtain ⟨f1, f2, f3⟩ := facts a (hMd a (by simp))
    obtain ⟨g1, g2, g3⟩ := facts b (hMd b (by simp))
    obtain ⟨h1, h2, h3⟩ := part_facts hF (β := β) hzl (fun hdn => ⟨hzl, fun ht => by
        rcases ht with hu | hd
        · exact hu.1 (by rw [(mem_dartsAt.mp hzm.1).2]; exact hroot)
        · exact hdn hd⟩) (fun hdn => by
        obtain ⟨hc, hcr, _⟩ := down_child hF hzl hdn
        exact euler hF β _ hc hcr)
    have hparts := parts_top hr hroot
    rw [ite_eq_left hzl] at hparts
    have hord : (F.plan hF).ord β (F.top r) = [.node r, F.item (F.zOf r)] ∨
        (F.plan hF).ord β (F.top r) = [F.item (F.zOf r), .node r] := by
      have e : (F.plan hF).ord β (F.top r) =
          if β (F.top r) then [Item.node r, F.item (F.zOf r)].reverse else [.node r, F.item (F.zOf r)] := by
        show (if _ then (F.parts _).reverse else F.parts _) = _
        rw [hparts]
      rw [e]; split
      · exact Or.inr rfl
      · exact Or.inl rfl
    have base : Cyc (sigN hF β) ((expandT hF β (F.item a) ++ expandT hF β (F.item b)) ++
        expandT hF β (F.item (F.zOf r))) := by
      refine ⟨chain_join (chain_join f1 g1 g2 (fun l hl => by rw [f3 l hl, r1]))
        h1 h2 (fun l hl => by rw [g3 l (getLast?_of_head g2 hl), r2]), fun x y hx hy => ?_⟩
      rw [head?_append_of_some (head?_append_of_some f2)] at hy
      cases hy
      rw [h3 x (getLast?_of_head h2 hx), r3]
    rcases hord with ho | ho <;> rw [ho] <;> simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    · rw [expandT_root hF hroot, hFr]; simpa using base
    · rw [expandT_root hF hroot, hFr]; simpa using cyc_append_comm base
  · rw [ite_eq_right hzl, List.append_nil] at hcyc
    have hparts := parts_top hr hroot
    rw [ite_eq_right hzl] at hparts
    have hord : (F.plan hF).ord β (F.top r) = [.node r] := by
      show (if _ then (F.parts _).reverse else F.parts _) = _
      rw [hparts]; split <;> rfl
    rw [hord]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [expandT_root hF hroot, hFr]
    have hzn : F.zOf r ∉ F.dartsAt r := fun h => hzl (mem_dartsAt.mp h).1
    have hLe : L = F.dartsAt r := List.erase_of_not_mem hzn
    have hrM : r ∈ M := by
      rw [← hM]; split
      · exact List.mem_reverse.mpr (by rw [hLe]; exact hrL)
      · rw [hLe]; exact hrL
    have hLlen : L.length ≤ 3 := by rw [hLe]; exact hdeg
    rcases M with _ | ⟨a, _ | ⟨b, _ | ⟨c, M⟩⟩⟩
    · simp at hrM
    · obtain ⟨f1, f2, f3⟩ := facts a (hMd a (by simp))
      have r1 := cyc_one hcyc
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      refine ⟨f1, fun x y hx hy => ?_⟩
      rw [f2] at hy; cases hy
      rw [f3 x hx, r1]
    · obtain ⟨f1, f2, f3⟩ := facts a (hMd a (by simp))
      obtain ⟨g1, g2, g3⟩ := facts b (hMd b (by simp))
      obtain ⟨r1, r2⟩ := cyc_two hcyc
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      refine ⟨chain_join f1 g1 g2 (fun l hl => by rw [f3 l hl, r1]), fun x y hx hy => ?_⟩
      rw [head?_append_of_some f2] at hy; cases hy
      rw [g3 x (getLast?_of_head g2 hx), r2]
    · exfalso
      have h3 : (F.dartsAt r).length = 3 := by
        have := hMlen; rw [← hLe] at hdeg ⊢; simp at this; omega
      exact hzl (zOf_mem_of_three h3 |> fun h => (mem_dartsAt.mp h).1)

theorem top_nodup (β : Nat → Bool) {r : Nat} (hr : F.IsVertex r) (hroot : F.IsRoot r) :
    (Ftour hF β (F.top r)).Nodup := by
  rw [Ftour_top hF hr hroot]
  have hparts := parts_top hr hroot
  have hFr := Ftour_nodup hF β r hr
  by_cases hzl : F.zOf r < 2 * F.E
  · rw [ite_eq_left hzl] at hparts
    have hzr := (mem_dartsAt.mp (zOf_mem hzl).1).2
    have hz1 : (expandT hF β (F.item (F.zOf r))).Nodup := by
      by_cases hdn : F.IsDown (F.zOf r)
      · rw [(expandT_item hF hzl).1 hdn]
        obtain ⟨hc, hcr, hcu⟩ := down_child hF hzl hdn
        rw [hzr] at hcu
        refine List.nodup_cons.mpr ⟨fun h => ?_, Ftour_nodup hF β _ hc⟩
        have := ((mem_Ftour_vertex hF β _ hc _).mp h).2.1
        rw [hzr] at this
        exact not_desc_child_parent hF hc hcr hcu hr this
      · rw [(expandT_item hF hzl).2 hdn]; exact nodup_one _
    have hdisj : ∀ e ∈ Ftour hF β r, e ∉ expandT hF β (F.item (F.zOf r)) := by
      intro e he1 he2
      obtain ⟨_, _, hz⟩ := (mem_Ftour_vertex hF β r hr e).mp he1
      obtain ⟨hz1', hz2'⟩ := hz hroot
      by_cases hdn : F.IsDown (F.zOf r)
      · rw [(expandT_item hF hzl).1 hdn] at he2
        rcases List.mem_cons.mp he2 with h | h
        · exact hz1' h
        · obtain ⟨hc, _, _⟩ := down_child hF hzl hdn
          exact hz2' ⟨hzl, hdn, ((mem_Ftour_vertex hF β _ hc e).mp h).2.1⟩
      · rw [(expandT_item hF hzl).2 hdn, List.mem_singleton] at he2
        exact hz1' he2
    have e : (F.plan hF).ord β (F.top r) =
        if β (F.top r) then [Item.node r, F.item (F.zOf r)].reverse else [.node r, F.item (F.zOf r)] := by
      show (if _ then (F.parts _).reverse else F.parts _) = _
      rw [hparts]
    rw [e]; split <;> simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, expandT_root hF hroot]
    · exact List.nodup_append.mpr ⟨hz1, hFr, fun a ha b hb e => hdisj b hb (e ▸ ha)⟩
    · exact List.nodup_append.mpr ⟨hFr, hz1, fun a ha b hb e => hdisj a ha (e ▸ hb)⟩
  · rw [ite_eq_right hzl] at hparts
    have e : (F.plan hF).ord β (F.top r) = [.node r] := by
      show (if _ then (F.parts _).reverse else F.parts _) = _
      rw [hparts]; split <;> rfl
    rw [e]; simpa [expandT_root hF hroot] using hFr

omit hF in
theorem dart_part_back {v d : Nat} (h : Item.dart d ∈ F.parts v) : F.IsBack d := by
  by_cases hv : F.IsVertex v
  · rw [parts_vertex hv] at h
    obtain ⟨q, hq, he⟩ := List.mem_map.mp h
    have hq' := ((dartsAt_nodup v).mem_erase_iff.mp hq)
    by_cases hdn : F.IsDown q
    · rw [item_down hdn] at he; cases he
    · rw [item_back hdn] at he; cases he
      exact back_of_not_tree_part hv hq'.2 hq'.1 hdn
  · by_cases ht : F.IsTop v
    · obtain ⟨_, hr, hroot⟩ := ht
      have hv' : v = F.top (v - 2 * F.E) := by unfold top; omega
      rw [hv', parts_top hr hroot] at h
      rcases List.mem_cons.mp h with h | h
      · cases h
      · split at h
        · rename_i hzl
          rw [List.mem_singleton] at h
          have hzr := (mem_dartsAt.mp (zOf_mem hzl).1).2
          by_cases hdn : F.IsDown (F.zOf (v - 2 * F.E))
          · rw [item_down hdn] at h; cases h
          · rw [item_back hdn] at h; cases h
            exact ⟨hzl, fun ht => by
              rcases ht with hu | hd
              · exact hu.1 (by rw [hzr]; exact hroot)
              · exact hdn hd⟩
        · simp at h
    · unfold parts at h; rw [ite_eq_right hv, ite_eq_right ht] at h; simp at h

omit hF in
theorem filter_flatMap' {α : Type} (l : List α) (f : α → List Nat) (p : Nat → Bool) :
    (l.flatMap f).filter p = l.flatMap (fun x => (f x).filter p) := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [List.flatMap_cons, List.filter_append, ih]

/-- **The chord word of a node is its Euler tour without the forest darts.** -/
theorem Ftour_filter (β : Nat → Bool) : ∀ v,
    (Ftour hF β v).filter (fun d => decide (F.IsBack d)) = (F.plan hF).W β v := by
  have main : ∀ k v, F.ht v = k →
      (Ftour hF β v).filter (fun d => decide (F.IsBack d)) = (F.plan hF).W β v := by
    intro k
    induction k using Nat.strongRecOn with
    | _ k ih =>
      intro v hv
      rw [Ftour_eq, (F.plan hF).W_eq, List.filter_append, filter_flatMap']
      have hup : (F.upL v).filter (fun d => decide (F.IsBack d)) = [] := by
        unfold upL; split
        · rename_i h
          have := par_isUp hF h.1 h.2
          simp [IsBack, IsTree, this]
        · rfl
      rw [hup, List.append_nil]
      apply flatMap_congr'
      intro it hit
      have hp : it ∈ F.parts v := (F.plan hF).mem_ord.mp hit
      cases it with
      | node c =>
        simp only [expandT, Plan.partW, List.filter_append]
        rw [ih (F.ht c) (by rw [← hv]; exact ht_lt hF v c hp) c rfl]
        have : (F.downL c).filter (fun d => decide (F.IsBack d)) = [] := by
          unfold downL; split
          · rename_i h
            have : F.IsDown (pair (F.par c)) := by
              show F.IsUp (pair (pair (F.par c))); rw [pair_pair]; exact par_isUp hF h.1 h.2
            simp [IsBack, IsTree, this]
          · rfl
        rw [this, List.nil_append]
      | dart d =>
        simp only [expandT, Plan.partW, List.filter_cons, List.filter_nil]
        rw [ite_eq_left (by simpa using dart_part_back hp)]
  exact fun v => main _ v rfl

end ForestData

end STACS2027.Embed

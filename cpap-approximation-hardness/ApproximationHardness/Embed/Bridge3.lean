module

public import ApproximationHardness.Embed.Bridge2
import Lean.Elab.Tactic.Omega

/-!
# Every embedding comes from bits

Every hypermap on the darts whose edge permutation pairs `2i` with `2i + 1` and whose node cycles
are the vertices is the hypermap of some bits (`exists_bits`): at a vertex with three darts, the
cyclic order is one of the two the bits choose between. Hence (`exists_planar_iff`) the graph has a
planar embedding iff some sides make every fork of the plan `ForkOK`.
-/

@[expose] public section

namespace STACS2027.Embed

open Complexity Complexity.Planar STACS2027.PlanarGluing STACS2027.PlanarAssembly

theorem hypermap_ext {n : Nat} {G H : Hypermap n} (he : G.edge = H.edge) (hn : G.node = H.node)
    (hf : G.face = H.face) : G = H := by
  cases G; cases H; simp only at he hn hf; subst he hn hf; rfl

/-- On a list without repetitions, a cycle of `f` is the cyclic successor. -/
theorem cyc_unique {f : Nat → Nat} {l : List Nat} (h : Cyc f l) (hnd : l.Nodup) {x : Nat} (hx : x ∈ l) :
    f x = cnext l x := by
  obtain ⟨A, B, rfl⟩ := List.append_of_mem hx
  have hc := cyc_rot h
  rw [cnext_rot hnd]
  obtain ⟨_, hh⟩ := chain_cons_iff.mp hc
  cases hr : B ++ A ++ [x] with
  | nil => simp at hr
  | cons y R => rw [hr] at hh; exact hh y rfl

theorem iterate_two_cycle {f : Nat → Nat} {a b : Nat} (h1 : f a = b) (h2 : f b = a) :
    ∀ k, iterate f k a = a ∨ iterate f k a = b := by
  intro k
  induction k with
  | zero => exact Or.inl rfl
  | succ k ih =>
    rw [iterate_succ']
    rcases ih with e | e <;> rw [e]
    · exact Or.inr h1
    · exact Or.inl h2

/-- A permutation of three elements with one orbit is the cycle through them. -/
theorem orbit_three {f : Nat → Nat} {x0 x1 x2 : Nat} (hnd : [x0, x1, x2].Nodup)
    (hmap : ∀ y ∈ [x0, x1, x2], f y ∈ [x0, x1, x2]) (hinj : ∀ a ∈ [x0, x1, x2], ∀ b ∈ [x0, x1, x2], f a = f b → a = b)
    (horb : ∃ k, iterate f k x0 = x2) (h0 : f x0 = x1) : Cyc f [x0, x1, x2] := by
  simp at hnd
  obtain ⟨⟨n01, n02⟩, n12⟩ := hnd
  have hm1 := hmap x1 (by simp)
  have hm2 := hmap x2 (by simp)
  simp at hm1 hm2
  have h1 : f x1 = x2 := by
    rcases hm1 with e | e | e
    · exfalso
      obtain ⟨k, hk⟩ := horb
      rcases iterate_two_cycle h0 e k with e' | e' <;> rw [e'] at hk
      · exact n02 hk
      · exact n12 hk
    · exfalso
      obtain ⟨k, hk⟩ := horb
      have hc : ∀ j, iterate f j x0 = x0 ∨ iterate f j x0 = x1 := by
        intro j
        induction j with
        | zero => exact Or.inl rfl
        | succ j ih =>
          rw [iterate_succ']
          rcases ih with e' | e' <;> rw [e']
          · exact Or.inr h0
          · exact Or.inr e
      rcases hc k with e' | e' <;> rw [e'] at hk
      · exact n02 hk
      · exact n12 hk
    · exact e
  have h2 : f x2 = x0 := by
    rcases hm2 with e | e | e
    · exact e
    · exact absurd (hinj x0 (by simp) x2 (by simp) (h0.trans e.symm)) n02
    · exact absurd (hinj x1 (by simp) x2 (by simp) (h1.trans e.symm)) n12
  refine ⟨Chain.cons _ _ _ h0 (Chain.cons _ _ _ h1 (Chain.one _)), fun a b ha hb => ?_⟩
  simp at ha hb; subst ha; subst hb; exact h2

theorem orbit_two {f : Nat → Nat} {x0 x1 : Nat} (hnd : [x0, x1].Nodup)
    (hmap : ∀ y ∈ [x0, x1], f y ∈ [x0, x1]) (hinj : ∀ a ∈ [x0, x1], ∀ b ∈ [x0, x1], f a = f b → a = b)
    (horb : ∃ k, iterate f k x0 = x1) : Cyc f [x0, x1] := by
  simp at hnd
  have hm0 := hmap x0 (by simp)
  have hm1 := hmap x1 (by simp)
  simp at hm0 hm1
  have h0 : f x0 = x1 := by
    rcases hm0 with e | e
    · exfalso
      obtain ⟨k, hk⟩ := horb
      have : ∀ j, iterate f j x0 = x0 := by
        intro j; induction j with
        | zero => rfl
        | succ j ih => rw [iterate_succ', ih, e]
      rw [this] at hk; exact hnd hk
    · exact e
  have h1 : f x1 = x0 := by
    rcases hm1 with e | e
    · exact e
    · exact absurd (hinj x0 (by simp) x1 (by simp) (h0.trans e.symm)) hnd
  exact ⟨Chain.cons _ _ _ h0 (Chain.one _), fun a b ha hb => by simp at ha hb; subst ha; subst hb; exact h1⟩

theorem orbit_one {f : Nat → Nat} {x0 : Nat} (hmap : f x0 ∈ [x0]) : Cyc f [x0] :=
  ⟨Chain.one _, fun a b ha hb => by simp at ha hb hmap; subst ha; subst hb; exact hmap⟩

theorem cyc_small {f : Nat → Nat} {l : List Nat} (hnd : l.Nodup) (hlen : l.length ≤ 3)
    (hmap : ∀ y ∈ l, f y ∈ l) (hinj : ∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b)
    (hor : ∀ a ∈ l, ∀ b ∈ l, ∃ k, iterate f k a = b)
    (h3 : ∀ x0 x1 x2, l = [x0, x1, x2] → f x0 = x1) : Cyc f l := by
  rcases l with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, _ | ⟨x3, l⟩⟩⟩⟩
  · exact ⟨Chain.nil, fun a b ha _ => by simp at ha⟩
  · exact orbit_one (hmap x0 (by simp))
  · exact orbit_two hnd hmap hinj (hor x0 (by simp) x1 (by simp))
  · exact orbit_three hnd hmap hinj (hor x0 (by simp) x2 (by simp)) (h3 x0 x1 x2 rfl)
  · simp at hlen

namespace ForestData

variable {F : ForestData} (hF : F.Valid)
include hF

omit hF in
theorem graphEdge_eq {G : Hypermap (2 * F.E)} (he : IsGraphEdge G.edge) : G.edge = F.pairF := by
  funext d
  apply Fin.ext
  rw [he d]
  show _ = pair d.val
  unfold pair
  by_cases h : d.val % 2 = 0
  · rw [ite_eq_left h]; simp [h]
  · rw [ite_eq_right h]; have : d.val % 2 = 1 := by omega
    simp [this]

/-- The anchor of a vertex: its parent dart, or the distinguished dart of a root. -/
def anchor (F : ForestData) (v : Nat) : Nat := if F.IsRoot v then F.zOf v else F.par v

/-- The bits of a rotation `f`: at a vertex with three darts, whether the image of the anchor is the
second of the other two darts. -/
def bitsOf (F : ForestData) (f : Nat → Nat) (v : Nat) : Bool :=
  decide (f (F.anchor v) ≠ ((F.dartsAt v).erase (F.anchor v)).headD 0)

/-- A rotation of the darts with the vertices as orbits is the rotation of its bits on every
vertex. -/
theorem cyc_bitsOf {f : Nat → Nat} (hfv : ∀ d, d < 2 * F.E → f d < 2 * F.E ∧ F.rep (f d) = F.rep d)
    (hfinj : ∀ a b, a < 2 * F.E → b < 2 * F.E → f a = f b → a = b)
    (horb : ∀ d d', d < 2 * F.E → d' < 2 * F.E → F.rep d' = F.rep d → ∃ k, iterate f k d = d')
    {v : Nat} (hv : F.IsVertex v) : Cyc f (cycOf hF (F.bitsOf f) v) := by
  let β0 := F.bitsOf f
  let a := F.anchor v
  let L := (F.dartsAt v).erase a
  have hX : (if F.IsRoot v then F.zOf v else F.par v) = a := rfl
  have hds := ord_map_itemDart hF (β := β0) hv
  rw [hX] at hds
  -- the darts at `v` and the images of `f`
  have hgen : ∀ l : List Nat, l.Perm (F.dartsAt v) →
      l.Nodup ∧ (∀ y ∈ l, f y ∈ l) ∧ (∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) ∧
        (∀ x ∈ l, ∀ y ∈ l, ∃ k, iterate f k x = y) := by
    intro l hl
    have hm : ∀ d, d ∈ l ↔ d < 2 * F.E ∧ F.rep d = v := fun d => by rw [hl.mem_iff, mem_dartsAt]
    refine ⟨hl.nodup_iff.mpr (dartsAt_nodup v), fun y hy => ?_, fun x hx y hy h =>
      hfinj x y ((hm x).mp hx).1 ((hm y).mp hy).1 h, fun x hx y hy => ?_⟩
    · obtain ⟨h1, h2⟩ := (hm y).mp hy
      obtain ⟨h3, h4⟩ := hfv y h1
      exact (hm _).mpr ⟨h3, h4.trans h2⟩
    · exact horb x y ((hm x).mp hx).1 ((hm y).mp hy).1 (((hm y).mp hy).2.trans ((hm x).mp hx).2.symm)
  -- the head of the ordered parts is the image of the anchor
  have hhead : ∀ p q, L = [p, q] → a ∈ F.dartsAt v →
      (if β0 v then L.reverse else L) = [f a, if f a = p then q else p] := by
    intro p q hLpq ham
    have hpL : p ∈ L := by rw [hLpq]; simp
    have hqL : q ∈ L := by rw [hLpq]; simp
    have hndL : L.Nodup := (dartsAt_nodup v).erase a
    rw [hLpq] at hndL
    have hpq : p ≠ q := by simpa using hndL
    have hpa : p ≠ a := (((dartsAt_nodup v).mem_erase_iff).mp hpL).1
    have hqa : q ≠ a := (((dartsAt_nodup v).mem_erase_iff).mp hqL).1
    have hpd : p ∈ F.dartsAt v := (((dartsAt_nodup v).mem_erase_iff).mp hpL).2
    have hqd : q ∈ F.dartsAt v := (((dartsAt_nodup v).mem_erase_iff).mp hqL).2
    obtain ⟨hal, har⟩ := mem_dartsAt.mp ham
    obtain ⟨hfa1, hfa2⟩ := hfv a hal
    have hfa : f a ∈ F.dartsAt v := mem_dartsAt.mpr ⟨hfa1, hfa2.trans har⟩
    have hb : β0 v = decide (f a ≠ p) := by
      show decide (f (F.anchor v) ≠ L.headD 0) = _
      rw [hLpq]; rfl
    rcases only_three hF ham hpd hqd (Ne.symm hpa) (Ne.symm hqa) hpq hfa with e | e | e
    · exfalso
      obtain ⟨k, hk⟩ := horb a p hal (mem_dartsAt.mp hpd).1 ((mem_dartsAt.mp hpd).2.trans har.symm)
      have : ∀ j, iterate f j a = a := by
        intro j; induction j with
        | zero => rfl
        | succ j ih => rw [iterate_succ', ih, e]
      rw [this] at hk; exact hpa hk.symm
    · rw [hb, e, hLpq]; simp
    · rw [hb, e, hLpq]; simp [Ne.symm hpq]
  have hlenL : ∀ hm : a ∈ F.dartsAt v, L.length + 1 = (F.dartsAt v).length := by
    intro hm; show ((F.dartsAt v).erase a).length + 1 = _
    rw [List.length_erase_of_mem hm]
    have := List.length_pos_of_mem hm; omega
  have hdeg := hF.deg v
  by_cases hroot : F.IsRoot v
  · have ha : a = F.zOf v := by show F.anchor v = _; unfold anchor; rw [ite_eq_left hroot]
    unfold cycOf
    rw [ite_eq_left hroot, hds]
    by_cases hz : F.zOf v < 2 * F.E
    · rw [ite_eq_left hz, ← ha]
      have ham : a ∈ F.dartsAt v := by rw [ha]; exact (zOf_mem hz).1
      have hperm : (a :: (if β0 v then L.reverse else L)).Perm (F.dartsAt v) := by
        have h1 : (if β0 v then L.reverse else L).Perm L := by
          split
          · exact List.reverse_perm _
          · exact List.Perm.refl _
        exact (h1.cons a).trans (List.perm_cons_erase ham).symm
      obtain ⟨g1, g2, g3, g4⟩ := hgen _ hperm
      have hc : Cyc f ([a] ++ (if β0 v then L.reverse else L)) := by
        apply cyc_small g1 (by rw [hperm.length_eq]; exact hdeg) g2 g3 g4
        intro x0 x1 x2 he
        have hL2 : L.length = 2 := by
          have := hlenL ham
          have := (zOf_mem hz).2
          omega
        obtain ⟨p, q, hLpq⟩ : ∃ p q, L = [p, q] := by
          rcases hL : L with _ | ⟨p, _ | ⟨q, _ | ⟨r, L'⟩⟩⟩ <;> rw [hL] at hL2 <;> simp at hL2
          exact ⟨p, q, rfl⟩
        rw [hhead p q hLpq ham] at he
        simp at he
        obtain ⟨rfl, rfl, -⟩ := he
        rfl
      exact cyc_append_comm hc
    · rw [ite_eq_right hz, List.append_nil]
      have hperm : (if β0 v then L.reverse else L).Perm (F.dartsAt v) := by
        have hna : a ∉ F.dartsAt v := fun h => hz (ha ▸ (mem_dartsAt.mp h).1)
        have : L = F.dartsAt v := List.erase_of_not_mem hna
        rw [this]; split
        · exact List.reverse_perm _
        · exact List.Perm.refl _
      obtain ⟨g1, g2, g3, g4⟩ := hgen _ hperm
      apply cyc_small g1 (by rw [hperm.length_eq]; exact hdeg) g2 g3 g4
      intro x0 x1 x2 he
      exfalso
      have := hperm.length_eq
      rw [he] at this
      have h3 : (F.dartsAt v).length = 3 := by simp at this; omega
      exact hz (zOf_mem_of_three h3 |> fun h => (mem_dartsAt.mp h).1)
  · have ha : a = F.par v := by show F.anchor v = _; unfold anchor; rw [ite_eq_right hroot]
    unfold cycOf
    rw [ite_eq_right hroot, hds, ← ha]
    have ham : a ∈ F.dartsAt v := by rw [ha]; exact mem_dartsAt.mpr ⟨hF.par_lt v hv hroot, hF.par_rep v hv hroot⟩
    have hperm : (a :: (if β0 v then L.reverse else L)).Perm (F.dartsAt v) := by
      have h1 : (if β0 v then L.reverse else L).Perm L := by
        split
        · exact List.reverse_perm _
        · exact List.Perm.refl _
      exact (h1.cons a).trans (List.perm_cons_erase ham).symm
    obtain ⟨g1, g2, g3, g4⟩ := hgen _ hperm
    apply cyc_small g1 (by rw [hperm.length_eq]; exact hdeg) g2 g3 g4
    intro x0 x1 x2 he
    have hL2 : L.length = 2 := by
      have := hperm.length_eq; rw [he] at this
      have := hlenL ham
      simp at *; omega
    obtain ⟨p, q, hLpq⟩ : ∃ p q, L = [p, q] := by
      rcases hL : L with _ | ⟨p, _ | ⟨q, _ | ⟨r, L'⟩⟩⟩ <;> rw [hL] at hL2 <;> simp at hL2
      exact ⟨p, q, rfl⟩
    rw [hhead p q hLpq ham] at he
    simp at he
    obtain ⟨rfl, rfl, -⟩ := he
    rfl

/-- **Every embedding comes from bits.** -/
theorem exists_bits (G : Hypermap (2 * F.E)) (he : IsGraphEdge G.edge)
    (hn : ∀ d d', Reaches G.node d d' ↔ F.rep d'.val = F.rep d.val) : ∃ β, G = hyp hF β := by
  have hedge := graphEdge_eq he
  let ρ0 : Fin (2 * F.E) → Fin (2 * F.E) := fun x => G.face (G.edge x)
  have hl : ∀ x, G.node (ρ0 x) = x := G.edgeK
  have hρinj : ∀ a b, ρ0 a = ρ0 b → a = b := fun a b h => by rw [← hl a, h, hl b]
  have hr : ∀ y, ρ0 (G.node y) = y := by
    intro y
    obtain ⟨x, rfl⟩ := surj hρinj y
    rw [hl]
  have hpres : ∀ x, F.rep (ρ0 x).val = F.rep x.val := fun x => ((hn (ρ0 x) x).mp ⟨1, hl x⟩).symm
  have hback : ∀ k (y x : Fin (2 * F.E)), iterate G.node k y = x → iterate ρ0 k x = y := by
    intro k
    induction k with
    | zero => intro y x h; exact h.symm
    | succ k ih =>
      intro y x h
      rw [iterate_succ', ih (G.node y) x h, hr]
  let f := natp ρ0
  have hfv : ∀ d, d < 2 * F.E → f d < 2 * F.E ∧ F.rep (f d) = F.rep d := by
    intro d hd
    have := hpres ⟨d, hd⟩
    exact ⟨by simp [f, natp, hd], by simpa [f, natp, hd] using this⟩
  have hfinj : ∀ a b, a < 2 * F.E → b < 2 * F.E → f a = f b → a = b := by
    intro a b ha hb h
    have : ρ0 ⟨a, ha⟩ = ρ0 ⟨b, hb⟩ := Fin.ext (by simpa [f, natp, ha, hb] using h)
    exact congrArg Fin.val (hρinj _ _ this)
  have horb : ∀ d d', d < 2 * F.E → d' < 2 * F.E → F.rep d' = F.rep d → ∃ k, iterate f k d = d' := by
    intro d d' hd hd' h
    obtain ⟨k, hk⟩ := (hn ⟨d', hd'⟩ ⟨d, hd⟩).mpr h.symm
    refine ⟨k, ?_⟩
    rw [show d = (⟨d, hd⟩ : Fin (2 * F.E)).val from rfl, iterate_natp, hback k _ _ hk]
  let β0 := F.bitsOf f
  have hρ : ∀ d, ρ0 d = rot hF β0 d := by
    intro d
    apply Fin.ext
    have hv := isVertex_rep hF d.isLt
    have hm : d.val ∈ cycOf hF β0 (F.rep d.val) := (mem_cycOf hF hv).mpr ⟨d.isLt, rfl⟩
    have := cyc_unique (cyc_bitsOf hF hfv hfinj horb hv) (cycOf_nodup hF hv) hm
    rw [← natp_val ρ0 d]
    exact this
  refine ⟨β0, hypermap_ext hedge ?_ ?_⟩
  · funext x
    have hx : rot hF β0 (rotInv hF β0 x) = x := Fin.ext (rotN_rotInvN hF x.isLt)
    calc G.node x = G.node (rot hF β0 (rotInv hF β0 x)) := by rw [hx]
      _ = G.node (ρ0 (rotInv hF β0 x)) := by rw [hρ]
      _ = rotInv hF β0 x := hl _
  · funext x
    have hee : G.edge (G.edge x) = x := by rw [hedge]; exact Fin.ext (pair_pair _)
    show G.face x = rot hF β0 (F.pairF x)
    rw [← hedge, ← hρ]
    show G.face x = G.face (G.edge (G.edge x))
    rw [hee]

theorem hyp_valid (β : Nat → Bool) :
    IsGraphEdge (hyp hF β).edge ∧ ∀ d d', Reaches (hyp hF β).node d d' ↔ F.rep d'.val = F.rep d.val :=
  ⟨pairF_graphEdge, node_reaches hF β⟩

/-! ### Nodes below the tops -/

theorem below_top {v : Nat} (hv : F.IsVertex v) : (F.plan hF).Below (F.top (F.rootOf v)) v := by
  have main : ∀ k v, F.IsVertex v → F.depth v = k → (F.plan hF).Below (F.top (F.rootOf v)) v := by
    intro k
    induction k with
    | zero =>
      intro v hv hk
      have hroot : F.IsRoot v := by
        apply Classical.byContradiction
        intro h; have := hF.depth_up v hv h; omega
      rw [rootOf_root hF hv hroot]
      refine Plan.Below.step Plan.Below.refl ?_
      show Item.node v ∈ F.parts (F.top v)
      rw [parts_top hv hroot]; simp
    | succ k ih =>
      intro v hv hk
      have hroot : ¬ F.IsRoot v := fun h => by rw [hF.depth_root v hv h] at hk; omega
      have hu := up_vertex hF hv
      have hdu := hF.depth_up v hv hroot
      have hRu : F.rootOf (F.up v) = F.rootOf v := by
        obtain ⟨h1, h2, h3⟩ := rootOf_spec hF hu
        exact (rootOf_eq hF hv h1 h2 (desc_trans h3 ⟨1, rfl⟩)).symm
      have hb := ih (F.up v) hu (by omega)
      rw [hRu] at hb
      obtain ⟨ht, htd, htc⟩ := child_down hF hv hroot rfl
      have hitem : F.item (pair (F.par v)) = .node v := by rw [item_down htd, htc]
      by_cases hz : F.IsRoot (F.up v) ∧ pair (F.par v) = F.zOf (F.up v)
      · -- the child reached by the distinguished dart of the root hangs below the top
        have hur : F.rootOf (F.up v) = F.up v := rootOf_root hF hu hz.1
        rw [← hRu, hur]
        refine Plan.Below.step Plan.Below.refl ?_
        show Item.node v ∈ F.parts (F.top (F.up v))
        rw [parts_top hu hz.1, ite_eq_left (by rw [← hz.2]; exact (mem_dartsAt.mp ht).1), ← hz.2, hitem]
        simp
      · refine Plan.Below.step hb ?_
        show Item.node v ∈ F.parts (F.up v)
        rw [parts_vertex hu, ← hitem]
        apply List.mem_map_of_mem
        apply ((dartsAt_nodup (F.up v)).mem_erase_iff).mpr
        refine ⟨?_, ht⟩
        by_cases hur : F.IsRoot (F.up v)
        · rw [ite_eq_left hur]; exact fun e => hz ⟨hur, e⟩
        · rw [ite_eq_right hur]
          intro e
          exact not_up_and_down hF (mem_dartsAt.mp ht).1 (e ▸ par_isUp hF hu hur) htd
  exact main _ v hv rfl

theorem fork_below {v : Nat} {p q : Item} (hf : (F.plan hF).IsFork pair F.key v p q) :
    ∃ r, F.IsVertex r ∧ F.IsRoot r ∧ (F.plan hF).Below (F.top r) v := by
  by_cases hv : F.IsVertex v
  · obtain ⟨h1, h2, _⟩ := rootOf_spec hF hv
    exact ⟨_, h1, h2, below_top hF hv⟩
  · by_cases ht : F.IsTop v
    · obtain ⟨h0, h1, h2⟩ := ht
      have : v = F.top (v - 2 * F.E) := by unfold top; omega
      exact ⟨_, h1, h2, this ▸ Plan.Below.refl⟩
    · have := hf.parts
      change F.parts v = _ at this
      unfold parts at this; rw [ite_eq_right hv, ite_eq_right ht] at this; simp at this

theorem top_closed (β : Nat → Bool) {r : Nat} (hr : F.IsVertex r) (hroot : F.IsRoot r) :
    openEnds pair ((F.plan hF).W β (F.top r)) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro e he
  obtain ⟨hb, hd⟩ := (mem_W_top hF β hr hroot e).mp he
  have : pair e ∈ (F.plan hF).W β (F.top r) := (mem_W_top hF β hr hroot _).mpr ⟨isBack_pair hb,
    desc_root_of_rel hF hr hroot (isVertex_rep hF hb.1) (isVertex_rep hF (pair_lt hb.1)) hd
      (hF.back e hb.1 hb.2).symm⟩
  simp [this]

/-- **The graph has a planar embedding iff some sides make every fork of its plan `ForkOK`.** -/
theorem exists_planar_iff :
    (∃ G : Hypermap (2 * F.E), IsGraphEdge G.edge ∧
      (∀ d d', Reaches G.node d d' ↔ F.rep d'.val = F.rep d.val) ∧ G.Planar) ↔
    ∃ s, ∀ v p q, (F.plan hF).IsFork pair F.key v p q → (F.plan hF).ForkOK pair F.key s p q := by
  have hk := kind hF
  constructor
  · rintro ⟨G, he, hn, hp⟩
    obtain ⟨β, rfl⟩ := exists_bits hF G he hn
    have hwn := (hyp_planar_iff hF β).mp hp
    refine ⟨(F.plan hF).sides0 pair β, fun v p q hf => ?_⟩
    obtain ⟨r, h1, h2, hb⟩ := fork_below hF hf
    exact (F.plan hF).nec_forkOK pair_pair hk (hwn r h1 h2) (top_closed hF β h1 h2) hb hf
  · rintro ⟨s, hs⟩
    obtain ⟨β, hβ⟩ := (F.plan hF).exists_placed hk hs
    have hwn := (F.plan hF).suff pair_pair hk hβ
    refine ⟨hyp hF β, (hyp_valid hF β).1, (hyp_valid hF β).2, ?_⟩
    exact (hyp_planar_iff hF β).mpr (fun r _ _ => (hwn _).1)

end ForestData

end STACS2027.Embed

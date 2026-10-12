module

public import Outerplanar.BlockTheory
import Mathlib.Tactic

/-!
# Blocks are 2-connected

The vertices of the block of a head `h` are `par h` and the vertices below `h` whose head
is `h` (`isVertex_block`). The tree path from such a vertex up to any block vertex above
it stays in the block (`reach_up`). Hence the block is connected through `par h`; deleting
`par h`, it is connected through `h`; deleting a vertex `z` below `h`, a vertex `v` below
`z` climbs to the child `x'` of `z` on its path, descends to the end `u` of an edge `uw`
leaving the subtree of `x'` for a proper ancestor `w` of `z` (it exists since `x'` is not a
head), and climbs from `w` to `par h` (`twoConnected_block`).
-/

@[expose] public section

namespace STACS2027

namespace Palm

variable {g : Graph} (P : Palm g)

/-- The vertices of the block of `h`. -/
def InBlock (h v : ℕ) : Prop :=
  v = P.par h ∨ (IsVertex g v ∧ P.Anc h v ∧ P.head v = h)

theorem head_self {h : ℕ} (hh : P.IsHead h) : P.head h = h := by
  have h1 := P.anc_head hh.1 hh (P.anc_refl h)
  have h2 := (P.head_spec hh.1 hh.2.1).2.1
  exact (P.anc_antisymm hh.1 h2 h1)

theorem par_not_below {h : ℕ} (hh : P.IsHead h) : ¬ P.Anc h (P.par h) := fun h' =>
  hh.2.1 (P.anc_antisymm hh.1 (P.anc_par h) h')

/-- The tree edge above a vertex of the block lies in the block. -/
theorem tree_edge_block {h v : ℕ} (hh : P.IsHead h) (hv : IsVertex g v) (hhv : P.Anc h v)
    (hd : P.head v = h) : Adj (P.block h) (P.par v) v := by
  have hr := P.par_ne_of_head_anc hh hhv
  rw [P.adj_block]
  refine ⟨P.par_adj v hv hr, ?_⟩
  have : P.lower (P.par v) v = v := by
    unfold lower; exact ite_eq_left (P.anc_par v)
  rw [this, hd]

theorem isVertex_block {h v : ℕ} (hh : P.IsHead h) : IsVertex (P.block h) v ↔ P.InBlock h v := by
  constructor
  · rintro ⟨u, huv⟩
    rw [P.adj_block] at huv
    obtain ⟨hadj, hd⟩ := huv
    rcases P.lower_cases hadj with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1] at hd
      have hv : IsVertex g v := ⟨u, hadj⟩
      have hr : P.par v ≠ v := P.par_ne_of_anc h2 hadj.1
      exact Or.inr ⟨hv, hd ▸ (P.head_spec hv hr).2.1, hd⟩
    · rw [h1] at hd
      have hu : IsVertex g u := ⟨v, hadj.symm⟩
      have hr : P.par u ≠ u := P.par_ne_of_anc h2 hadj.1.symm
      have hhu : P.Anc h u := hd ▸ (P.head_spec hu hr).2.1
      by_cases hhv : P.Anc h v
      · right
        refine ⟨⟨u, hadj⟩, hhv, ?_⟩
        rw [P.head_eq_of_between hu hr h2 (hd ▸ hhv), hd]
      · exact Or.inl (hh.2.2 u v hhu hadj hhv)
  · rintro (rfl | ⟨hv, hhv, hd⟩)
    · exact ⟨h, (P.tree_edge_block hh hh.1 (P.anc_refl h) (P.head_self hh)).symm⟩
    · exact ⟨P.par v, P.tree_edge_block hh hv hhv hd⟩

/-- Between a block vertex `a` and a block vertex `x ≠ par h` below it, every vertex is in
the block. -/
theorem inBlock_between {h x a y : ℕ} (hh : P.IsHead h) (hx : IsVertex g x) (hhx : P.Anc h x)
    (hdx : P.head x = h) (ha : P.InBlock h a) (hay : P.Anc a y) (hyx : P.Anc y x) :
    P.InBlock h y := by
  by_cases hyp : y = P.par h
  · exact Or.inl hyp
  · right
    have hy : IsVertex g y := P.isVertex_anc hx hyx
    have hhy : P.Anc h y := by
      rcases P.anc_chain hhx hyx with h1 | h1
      · exact h1
      · by_cases hyh : y = h
        · rw [hyh]; exact P.anc_refl h
        · exfalso
          have h2 : P.Anc y (P.par h) := P.anc_par_of_ne h1 hyh
          rcases ha with rfl | ⟨-, hha, -⟩
          · exact hyp (P.anc_antisymm hy hay h2).symm
          · exact hyh (P.anc_antisymm hy (P.anc_trans hha hay) h1).symm
    have hxr : P.par x ≠ x := P.par_ne_of_head_anc hh hhx
    refine ⟨hy, hhy, ?_⟩
    rw [P.head_eq_of_between hx hxr hyx (hdx ▸ hhy), hdx]

/-- The tree path from a block vertex up to a block vertex above it stays in the block. -/
theorem reach_up {h : ℕ} (hh : P.IsHead h) {T : ℕ → Prop} :
    ∀ (n x a : ℕ), P.pre x < n → IsVertex g x → P.Anc h x → P.head x = h → P.Anc a x →
      P.InBlock h a → (∀ y, P.Anc a y → P.Anc y x → T y) → Reach (P.block h) T x a
  | 0, _, _, hn, _, _, _, _, _, _ => absurd hn (Nat.not_lt_zero _)
  | n + 1, x, a, hn, hx, hhx, hdx, hax, ha, hT => by
    by_cases hxa : x = a
    · subst hxa; exact .refl (hT x (P.anc_refl x) (P.anc_refl x))
    · have hxr : P.par x ≠ x := P.par_ne_of_anc hax (Ne.symm hxa)
      have hap : P.Anc a (P.par x) := P.anc_par_of_ne hax (Ne.symm hxa)
      have hedge : Adj (P.block h) x (P.par x) := (P.tree_edge_block hh hx hhx hdx).symm
      have hTx := hT x hax (P.anc_refl x)
      have hTp := hT (P.par x) hap (P.anc_par x)
      by_cases hpa : P.par x = a
      · rw [← hpa]; exact .edge hTx hTp hedge
      · have hpb := P.inBlock_between hh hx hhx hdx ha hap (P.anc_par x)
        rcases hpb with hpb | ⟨hpv, hhp, hdp⟩
        · -- `par x = par h`, so `a = par h` as well
          exfalso
          rcases ha with ha | ⟨-, hha, -⟩
          · exact hpa (hpb.trans ha.symm)
          · exact P.par_not_below hh (hpb ▸ P.anc_trans hha hap)
        · have hpre := P.par_pre x hx hxr
          have ih := reach_up hh n (P.par x) a (by omega) hpv hhp hdp hap ha
            (fun y hy1 hy2 => hT y hy1 (P.anc_trans hy2 (P.anc_par x)))
          exact .step hTx hedge ih

/-- **Blocks are 2-connected**: the block of a head with a vertex besides `h` and `par h`
is 2-connected. -/
theorem twoConnected_block {h : ℕ} (hh : P.IsHead h)
    (h3 : ∃ v, P.InBlock h v ∧ v ≠ h ∧ v ≠ P.par h) : TwoConnected (P.block h) := by
  have hV : ∀ v, IsVertex (P.block h) v ↔ P.InBlock h v := fun v => P.isVertex_block hh
  have hhIn : P.InBlock h h := Or.inr ⟨hh.1, P.anc_refl h, P.head_self hh⟩
  have hpIn : P.InBlock h (P.par h) := Or.inl rfl
  have hn := Nat.lt_succ_self
  -- every block vertex below `h` reaches `par h` within any set containing its tree path
  have up : ∀ x (T : ℕ → Prop), IsVertex g x → P.Anc h x → P.head x = h →
      (∀ y, P.Anc (P.par h) y → P.Anc y x → T y) → Reach (P.block h) T x (P.par h) := by
    intro x T hx hhx hdx hT
    exact P.reach_up hh _ x (P.par h) (hn _) hx hhx hdx (P.anc_trans (P.anc_par h) hhx) hpIn hT
  obtain ⟨v3, hv3, hv3h, hv3p⟩ := h3
  refine ⟨⟨h, P.par h, v3, (hV h).mpr hhIn, (hV _).mpr hpIn, (hV v3).mpr hv3, Ne.symm hh.2.1,
    Ne.symm hv3h, Ne.symm hv3p⟩, ?_, ?_⟩
  · -- connected through `par h`
    apply connectedWithin_of_hub (c := P.par h)
    intro v hv
    rw [hV] at hv
    rcases hv with rfl | ⟨hv, hhv, hdv⟩
    · exact .refl ((hV _).mpr hpIn)
    · exact up v _ hv hhv hdv (fun y hy1 hy2 => (hV y).mpr
        (P.inBlock_between hh hv hhv hdv hpIn hy1 hy2))
  · intro z
    by_cases hz : z = P.par h
    · -- without `par h`: through `h`
      subst hz
      apply connectedWithin_of_hub (c := h)
      rintro v ⟨hv, hvz⟩
      rw [hV] at hv
      rcases hv with hv | ⟨hv, hhv, hdv⟩
      · exact absurd hv hvz
      · refine P.reach_up hh _ v h (hn _) hv hhv hdv hhv hhIn ?_
        intro y hy1 hy2
        refine ⟨(hV y).mpr (P.inBlock_between hh hv hhv hdv hhIn hy1 hy2), ?_⟩
        intro hyz
        exact P.par_not_below hh (hyz ▸ hy1)
    · -- without a vertex `z ≠ par h`: through `par h`
      apply connectedWithin_of_hub (c := P.par h)
      rintro v ⟨hv, hvz⟩
      rw [hV] at hv
      rcases hv with rfl | ⟨hv, hhv, hdv⟩
      · exact .refl ⟨(hV _).mpr hpIn, hvz⟩
      · by_cases hzv : P.Anc z v ∧ P.Anc h z
        · obtain ⟨hzv, hhz⟩ := hzv
          -- the child `x'` of `z` on the path to `v`
          obtain ⟨k, hk⟩ := hzv
          cases k with
          | zero => exact absurd hk hvz
          | succ k =>
            set x' := P.par^[k] v with hx'
            have hpx : P.par x' = z := by
              rw [hx', ← Function.iterate_succ_apply' P.par k v]; exact hk
            have hx'v : P.Anc x' v := ⟨k, rfl⟩
            have hx'V : IsVertex g x' := P.isVertex_anc hv hx'v
            have hzV : IsVertex g z := hpx ▸ P.isVertex_par hx'V
            have hx'z : x' ≠ z := by
              intro he
              have hr := P.par_ne_of_head_anc hh (P.anc_trans hhz (P.anc_refl z))
              rw [he] at hpx; exact hr hpx
            have hhx' : P.Anc h x' := by
              rcases P.anc_chain hhv hx'v with h1 | h1
              · exact h1
              · exfalso
                have : P.Anc x' z := P.anc_trans h1 hhz
                exact hx'z (P.anc_antisymm hzV this (hpx ▸ P.anc_par x'))
            have hx'h : x' ≠ h := by
              intro he
              rw [he] at hpx
              exact P.par_not_below hh (hpx ▸ hhz)
            have hdx' : P.head x' = h := by
              rw [P.head_eq_of_between hv (P.par_ne_of_head_anc hh hhv) hx'v (hdv ▸ hhx'), hdv]
            have hx'nh : ¬ P.IsHead x' := by
              have := (P.head_spec hv (P.par_ne_of_head_anc hh hhv)).2.2
              rw [hdv] at this
              exact this x' hx'v hhx' hx'h
            have hx'r : P.par x' ≠ x' := by rw [hpx]; exact Ne.symm hx'z
            -- an edge `uw` leaving the subtree of `x'` above `z`
            obtain ⟨u, w, hx'u, huw, hx'w, hwz⟩ : ∃ u w, P.Anc x' u ∧ Adj g u w ∧
                ¬ P.Anc x' w ∧ w ≠ P.par x' := by
              by_contra hc
              apply hx'nh
              refine ⟨hx'V, hx'r, fun u w h1 h2 h3 => ?_⟩
              by_contra hne
              exact hc ⟨u, w, h1, h2, h3, hne⟩
            rw [hpx] at hwz
            have hwu : P.Anc w u := by
              rcases P.palm u w huw with h1 | h1
              · exact absurd (P.anc_trans hx'u h1) hx'w
              · exact h1
            have hwz' : P.Anc w z := by
              rcases P.anc_chain hx'u hwu with h1 | h1
              · exact absurd h1 hx'w
              · have := P.anc_par_of_ne h1 (fun e => hx'w (e ▸ P.anc_refl _))
                rwa [hpx] at this
            have huV : IsVertex g u := ⟨w, huw.symm⟩
            have hhu : P.Anc h u := P.anc_trans hhx' hx'u
            have hur : P.par u ≠ u := P.par_ne_of_head_anc hh hhu
            have hdu : P.head u = h := by
              obtain ⟨k1, k2, k3⟩ := P.head_spec huV hur
              have hh'' := P.anc_head huV hh hhu
              by_contra hne
              rcases P.anc_chain k2 hx'u with h1 | h1
              · -- `head u` above `x'`, so between `h` and `v`
                have hb := (P.head_spec hv (P.par_ne_of_head_anc hh hhv)).2.2
                rw [hdv] at hb
                exact hb _ (P.anc_trans h1 hx'v) hh'' hne k1
              · -- `head u` below `x'`
                by_cases he : P.head u = x'
                · exact hx'nh (he ▸ k1)
                · have := k1.2.2 u w k2 huw (fun hc => hx'w (P.anc_trans h1 hc))
                  exact hx'w (this ▸ P.anc_par_of_ne h1 (Ne.symm he))
            have hwIn : P.InBlock h w := by
              by_cases hhw : P.Anc h w
              · exact P.inBlock_between hh huV hhu hdu (Or.inr ⟨P.isVertex_anc huV hwu, hhw,
                  by rw [P.head_eq_of_between huV hur hwu (hdu ▸ hhw), hdu]⟩) (P.anc_refl w) hwu
              · exact Or.inl (hh.2.2 u w hhu huw hhw)
            have hwz'' : w ≠ z := hwz
            -- the walk `v ↑ x' ↓ u → w ↑ par h`, avoiding `z`
            have below : ∀ y, P.Anc x' y → y ≠ z := by
              intro y hy hyz
              subst hyz
              exact hx'z (P.anc_antisymm hzV hy (hpx ▸ P.anc_par x'))
            have r1 : Reach (P.block h) (fun y => IsVertex (P.block h) y ∧ y ≠ z) v x' :=
              P.reach_up hh _ v x' (hn _) hv hhv hdv hx'v (Or.inr ⟨hx'V, hhx', hdx'⟩)
                (fun y hy1 hy2 => ⟨(hV y).mpr (P.inBlock_between hh hv hhv hdv
                  (Or.inr ⟨hx'V, hhx', hdx'⟩) hy1 hy2), below y hy1⟩)
            have r2 : Reach (P.block h) (fun y => IsVertex (P.block h) y ∧ y ≠ z) u x' :=
              P.reach_up hh _ u x' (hn _) huV hhu hdu hx'u (Or.inr ⟨hx'V, hhx', hdx'⟩)
                (fun y hy1 hy2 => ⟨(hV y).mpr (P.inBlock_between hh huV hhu hdu
                  (Or.inr ⟨hx'V, hhx', hdx'⟩) hy1 hy2), below y hy1⟩)
            have huz : u ≠ z := below u hx'u
            have r3 : Reach (P.block h) (fun y => IsVertex (P.block h) y ∧ y ≠ z) u w := by
              refine .edge ⟨(hV u).mpr (Or.inr ⟨huV, hhu, hdu⟩), huz⟩ ⟨(hV w).mpr hwIn, hwz''⟩ ?_
              rw [P.adj_block]
              refine ⟨huw, ?_⟩
              have : P.lower u w = u := by
                unfold lower
                exact ite_eq_right (fun hc => huw.1 (P.anc_antisymm huV hwu hc).symm)
              rw [this, hdu]
            have r4 : Reach (P.block h) (fun y => IsVertex (P.block h) y ∧ y ≠ z) w (P.par h) := by
              rcases hwIn with hw | ⟨hwV, hhw, hdw⟩
              · rw [hw]; exact .refl ⟨(hV _).mpr hpIn, fun e => hz e.symm⟩
              · refine up w _ hwV hhw hdw ?_
                intro y hy1 hy2
                refine ⟨(hV y).mpr (P.inBlock_between hh hwV hhw hdw hpIn hy1 hy2), ?_⟩
                intro hyz; subst hyz
                exact hwz'' (P.anc_antisymm hzV hwz' hy2)
            exact r1.trans (r2.symm.trans (r3.trans r4))
        · -- `z` is not on the path from `v` up to `par h`
          refine up v _ hv hhv hdv ?_
          intro y hy1 hy2
          refine ⟨(hV y).mpr (P.inBlock_between hh hv hhv hdv hpIn hy1 hy2), ?_⟩
          intro hyz
          subst hyz
          apply hzv
          refine ⟨hy2, ?_⟩
          rcases (P.inBlock_between hh hv hhv hdv hpIn hy1 hy2) with h1 | ⟨-, h1, -⟩
          · exact absurd h1 hz
          · exact h1

end Palm

end STACS2027

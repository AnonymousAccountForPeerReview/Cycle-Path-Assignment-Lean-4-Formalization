module

public import ApproximationHardness.Embed.Iteration
public import ApproximationHardness.Embed.Orient
public import Mathlib.Data.List.Basic
import Lean.Elab.Tactic.Omega

/-!
# The live post-order frontier

Only results whose parent has not yet been processed remain live. Results below
that frontier may share successor cells with a merged ancestor and are not used
again. Distinct live results own disjoint group and dart identifiers.
-/

@[expose] public section

namespace STACS2027.Embed

theorem before_take_mem {post : List Nat} {k a b : Nat}
    (hnd : post.Nodup) (hab : Before post a b) (hb : b ∈ post.take k) :
    a ∈ post.take k := by
  have ha := before_mem hab
  have hb' : b ∈ post := List.mem_of_mem_take hb
  have hk : post.idxOf b < k := (List.mem_take_iff_idxOf_lt hb').mp hb
  obtain ⟨i, j, hij, hj, hi, hj'⟩ := before_iff_idx.mp hab
  have hia : post.idxOf a = i := by rw [← hi]; exact hnd.idxOf_getElem _ _
  have hib : post.idxOf b = j := by rw [← hj']; exact hnd.idxOf_getElem _ _
  exact (List.mem_take_iff_idxOf_lt ha.1).mpr (by omega)

namespace Sol

variable (S : Sol)

/-- A node result remains live until its parent is processed. -/
def Live (done : List Nat) (v : Nat) : Prop :=
  v ∈ done ∧ ∀ p, Item.node v ∈ S.P.parts p → p ∉ done

/-- The order places every strict descendant before its ancestor. -/
structure PostOrder (post : List Nat) : Prop where
  nodup : post.Nodup
  below : ∀ v w, S.P.Below v w → w ≠ v → v ∈ post → w ∈ post ∧ Before post w v

variable {S}

theorem PostOrder.below_done {post : List Nat} (H : S.PostOrder post) {k v w : Nat}
    (hv : v ∈ post.take k) (hb : S.P.Below v w) : w ∈ post.take k := by
  by_cases he : w = v
  · simpa [he] using hv
  · exact before_take_mem H.nodup (H.below v w hb he (List.mem_of_mem_take hv)).2 hv

/-- Two distinct live nodes are incomparable in the plan forest. -/
theorem PostOrder.live_incomparable {post : List Nat} (H : S.PostOrder post)
    {k v w : Nat} (Hv : S.Live (post.take k) v) (Hw : S.Live (post.take k) w)
    (hne : v ≠ w) : ¬ S.P.Below v w ∧ ¬ S.P.Below w v := by
  have first : ∀ {v w : Nat}, S.Live (post.take k) v → S.Live (post.take k) w →
      v ≠ w → ¬ S.P.Below v w := by
    intro v w Hv Hw hne hb
    rcases Plan.below_cases hb with h | ⟨p, hp, hc⟩
    · exact hne h.symm
    · exact Hw.2 p hc (H.below_done Hv.1 hp)
  exact ⟨first Hv Hw hne, first Hw Hv hne.symm⟩

/-- Incomparable subtrees have disjoint ownership sets. -/
theorem Tree.own_disjoint (T : S.Tree) {v w : Nat}
    (hvw : ¬ S.P.Below v w) (hwv : ¬ S.P.Below w v) :
    ∀ g, S.Own v g → S.Own w g → False := by
  intro g hv hw
  exact (T.own_cmp hv hw).elim hvw hwv

/-- All live result groups are distinct from the groups of another live result. -/
theorem Tree.live_groups_disjoint (T : S.Tree) (G : S.Good)
    {post : List Nat} (H : S.PostOrder post) {k v w : Nat}
    (Hv : S.Live (post.take k) v) (Hw : S.Live (post.take k) w) (hne : v ≠ w) :
    ∀ g ∈ gids (S.solve v), ∀ h ∈ gids (S.solve w), g ≠ h := by
  obtain ⟨hvw, hwv⟩ := H.live_incomparable Hv Hw hne
  intro g hg h hh he
  subst h
  exact T.own_disjoint hvw hwv g ((T.gids_ok G v).1 g hg) ((T.gids_ok G w).1 g hh)

/-- All live open ends are distinct from the ends of another live result. -/
theorem Tree.live_ends_disjoint (T : S.Tree) (G : S.Good)
    {sides : Nat → Bool}
    (hfork : ∀ v p q, S.P.IsFork S.α S.key v p q → S.P.ForkOK S.α S.key sides p q)
    {post : List Nat} (H : S.PostOrder post) {k v w : Nat}
    (Hv : S.Live (post.take k) v) (Hw : S.Live (post.take k) w) (hne : v ≠ w) :
    ∀ e ∈ els (S.solve v).seg, ∀ d ∈ els (S.solve w).seg, e ≠ d := by
  obtain ⟨hvw, hwv⟩ := H.live_incomparable Hv Hw hne
  intro e he d hd hed
  subst d
  have hv : e ∈ S.P.D v := List.mem_of_mem_filter ((G.solve_inv hfork v).mem e |>.mp he)
  have hw : e ∈ S.P.D w := List.mem_of_mem_filter ((G.solve_inv hfork w).mem e |>.mp hd)
  exact T.own_disjoint hvw hwv e (Or.inr hv) (Or.inr hw)

/-- Adding a processed node removes its children from the frontier and adds its result. -/
theorem live_append (done : List Nat) (v : Nat)
    (hparents : ∀ p, Item.node v ∈ S.P.parts p → p ∉ done) :
    ∀ w, S.Live (done ++ [v]) w ↔ w = v ∨
      (S.Live done w ∧ Item.node w ∉ S.P.parts v) := by
  intro w
  constructor
  · rintro ⟨hw, hp⟩
    rcases List.mem_append.mp hw with hw | hw
    · exact Or.inr ⟨⟨hw, fun p hc hpd => hp p hc (List.mem_append_left _ hpd)⟩,
        fun hc => hp v hc (by simp)⟩
    · exact Or.inl (by simpa using hw)
  · intro H
    rcases H with he | ⟨⟨hw, hp⟩, hn⟩
    · subst w
      refine ⟨by simp, ?_⟩
      intro p hc hm
      rcases List.mem_append.mp hm with hm | hm
      · exact hparents p hc hm
      · have he : p = v := by simpa using hm
        subst p
        have := S.P.ht_lt v v hc
        omega
    · refine ⟨List.mem_append_left _ hw, ?_⟩
      intro p hc hm
      rcases List.mem_append.mp hm with hm | hm
      · exact hp p hc hm
      · have he : p = v := by simpa using hm
        subst p
        exact hn hc

/-- The next post-order node has live children and is disjoint from the surviving frontier. -/
structure Ready (done : List Nat) (v : Nat) : Prop where
  fresh : v ∉ done
  parents : ∀ p, Item.node v ∈ S.P.parts p → p ∉ done
  children : ∀ c, Item.node c ∈ S.P.parts v → S.Live done c
  survives : ∀ w, S.Live done w → Item.node w ∉ S.P.parts v →
    ¬ S.P.Below v w ∧ ¬ S.P.Below w v

theorem PostOrder.ready (T : S.Tree) {post : List Nat} (H : S.PostOrder post)
    {k v : Nat} (hn : post[k]? = some v) : S.Ready (post.take k) v := by
  obtain ⟨hk, hv⟩ := List.getElem?_eq_some_iff.mp hn
  have hm : v ∈ post := hv ▸ List.getElem_mem hk
  have hvk : post.idxOf v = k := by rw [← hv]; exact H.nodup.idxOf_getElem _ _
  have fresh : v ∉ post.take k := by
    intro hv
    have := (List.mem_take_iff_idxOf_lt hm).mp hv
    omega
  have strict : ∀ w, S.P.Below v w → w ≠ v → w ∈ post.take k := by
    intro w hw hne
    obtain ⟨hwm, hb⟩ := H.below v w hw hne hm
    obtain ⟨i, j, hij, hj, hi, hj'⟩ := before_iff_idx.mp hb
    have hiw : post.idxOf w = i := by rw [← hi]; exact H.nodup.idxOf_getElem _ _
    have hjv : post.idxOf v = j := by rw [← hj']; exact H.nodup.idxOf_getElem _ _
    exact (List.mem_take_iff_idxOf_lt hwm).mpr (by omega)
  refine ⟨fresh, ?_, ?_, ?_⟩
  · intro p hp hpd
    have hb : S.P.Below p v := S.P.below_child hp
    exact fresh (H.below_done hpd hb)
  · intro c hc
    have hne : c ≠ v := by
      intro he
      subst c
      have := S.P.ht_lt v v hc
      omega
    refine ⟨strict c (S.P.below_child hc) hne, ?_⟩
    intro p hp hpd
    have he := T.uniq_parent p v c hp hc
    exact fresh (he ▸ hpd)
  · intro w Hw hchild
    constructor
    · intro hb
      rcases Plan.below_cases hb with hw | ⟨p, hp, hc⟩
      · exact fresh (hw ▸ Hw.1)
      · by_cases he : p = v
        · subst p; exact hchild hc
        · exact Hw.2 p hc (strict p hp he)
    · intro hb
      exact fresh (H.below_done Hw.1 hb)

/-- Stored results of the current live frontier. -/
def Frontier (m : SMem) (done : List Nat) : Prop :=
  ∀ v, S.Live done v → StackRep m (m.rs v) (S.solve v).seg ∧ m.rl v = (S.solve v).low

theorem frontier_nil (m : SMem) : S.Frontier m [] := by
  intro v hv
  simp [Live] at hv

end Sol

namespace ForestData

theorem PostOrder.solver {F : ForestData} (hF : F.Valid) {post : List Nat}
    (H : F.PostOrder hF post) : (F.sol hF).PostOrder post :=
  ⟨H.nodup, H.below⟩

end ForestData

end STACS2027.Embed

module

public import ApproximationHardness.Embed.NodeComplete
public import ApproximationHardness.Embed.MergeFrame

/-! # Preservation of the other live nodes by a completed node -/

@[expose] public section

namespace STACS2027.Embed.Sol

variable (S : Sol)

theorem itRes_instruction_frame (m : SMem) (it : Item) :
    (S.itRes m it).1.inf = m.inf ∧ (S.itRes m it).1.ia = m.ia := by
  cases it <;> exact ⟨rfl, rfl⟩

theorem completeFork_foreign (T : S.Tree) (G : S.Good) {sides : Nat → Bool}
    (hfork : ∀ v p q, S.P.IsFork S.α S.key v p q → S.P.ForkOK S.α S.key sides p q)
    {s : SMS} {v w : Nat} {p q : Item} (hf : S.P.IsFork S.α S.key v p q)
    (Hchildren : ∀ c, Item.node c ∈ S.P.parts v → Stored s.m c (S.solve c))
    (HF : Stored s.m w (S.solve w))
    (hvw : ¬ S.P.Below v w) (hwv : ¬ S.P.Below w v) :
    Stored (S.completeFork s v p q).m w (S.solve w) ∧
      (∀ z, z ≠ v → (S.completeFork s v p q).m.inf z = s.m.inf z) ∧
      (S.completeFork s v p q).m.ia = s.m.ia := by
  have hw : w ≠ v := fun he => hvw (he ▸ Plan.Below.refl)
  have hp : p ∈ S.P.parts v := by rw [hf.parts]; simp
  have hq : q ∈ S.P.parts v := by rw [hf.parts]; simp
  have ownW : ∀ g ∈ (S.solve w).seg, S.Own w g.id := by
    intro g hg
    exact (T.gids_ok G w).1 _ (List.mem_map.mpr ⟨g, hg, rfl⟩)
  have hfr : ∀ it ∈ S.P.parts v, ∀ e, it = .dart e →
      ∀ g ∈ (S.solve w).seg, g.id ≠ e := by
    intro it hit e he g hg hge
    have ho : S.Own v e := ownIt_own hit (by simp [OwnIt, he])
    exact T.own_disjoint hvw hwv e ho (hge ▸ ownW g hg)
  have Hfp := S.itRes_stored_foreign HF (hfr p hp)
  have Hfq := S.itRes_stored_foreign Hfp (hfr q hq)
  obtain ⟨Hrp, Hlp, Hrq, Hlq⟩ := S.prepare_fork_parts T G hf Hchildren
  have ip := G.rpart_inv hp hf.dp (fun c _ => G.solve_inv hfork c)
  have iq := G.rpart_inv hq hf.dq (fun c _ => G.solve_inv hfork c)
  have hnd : (els (S.rpart p).seg ++ els (S.rpart q).seg).Nodup := by
    refine List.nodup_append.mpr ⟨ip.core.nodup, iq.core.nodup, ?_⟩
    intro a ha b hb he; subst b
    exact hf.disj a (List.mem_of_mem_filter ((ip.mem a).mp ha))
      (List.mem_of_mem_filter ((iq.mem a).mp hb))
  have ownP : ∀ a ∈ els (S.rpart p).seg, S.Own v a := by
    intro a ha
    exact ownIt_own hp (by
      cases p with
      | node c => exact Or.inr (List.mem_of_mem_filter ((ip.mem a).mp ha))
      | dart e => simpa [Plan.ID, Plan.partW, OwnIt] using
          List.mem_of_mem_filter ((ip.mem a).mp ha))
  have ownQ : ∀ a ∈ els (S.rpart q).seg, S.Own v a := by
    intro a ha
    exact ownIt_own hq (by
      cases q with
      | node c => exact Or.inr (List.mem_of_mem_filter ((iq.mem a).mp ha))
      | dart e => simpa [Plan.ID, Plan.partW, OwnIt] using
          List.mem_of_mem_filter ((iq.mem a).mp ha))
  have ownEndsW : ∀ e ∈ els (S.solve w).seg, S.Own w e := by
    intro e he
    exact Or.inr (List.mem_of_mem_filter (((G.solve_inv hfork w).mem e).mp he))
  have hd : ∀ a ∈ els (S.rpart p).seg ++ els (S.rpart q).seg,
      ∀ e ∈ els (S.solve w).seg, a ≠ e := by
    intro a ha e he hae; subst e
    exact T.own_disjoint hvw hwv a
      ((List.mem_append.mp ha).elim (ownP a) (ownQ a)) (ownEndsW a he)
  have fresh : ∀ g ∈ (S.solve w).seg, g.id ≠ S.gid v := by
    intro g hg he
    exact T.own_disjoint hvw hwv (S.gid v)
      (Or.inl ⟨v, Plan.Below.refl, rfl⟩) (he ▸ ownW g hg)
  have Hi := S.itRes_instruction_frame s.m p
  have Hj := S.itRes_instruction_frame (S.itRes s.m p).1 q
  by_cases hlow : (S.rpart p).low < (S.rpart q).low
  · obtain ⟨Hs, Hinf, Hia⟩ := S.forkFinish_foreign (s := s) Hrp Hrq hnd Hfq hw fresh hd
    refine ⟨by simpa [completeFork, hlow] using Hs, ?_, ?_⟩
    · intro z hz
      simpa [completeFork, hlow, Hj.1, Hi.1] using Hinf z hz
    · simpa [completeFork, hlow, Hj.2, Hi.2] using Hia
  · have hnd' := List.nodup_append.mpr ⟨iq.core.nodup, ip.core.nodup,
        fun a ha b hb => Ne.symm ((List.nodup_append.mp hnd).2.2 b hb a ha)⟩
    have hd' : ∀ a ∈ els (S.rpart q).seg ++ els (S.rpart p).seg,
        ∀ e ∈ els (S.solve w).seg, a ≠ e := by
      intro a ha e he
      exact hd a ((List.mem_append.mp ha).elim (List.mem_append_right _) (List.mem_append_left _)) e he
    obtain ⟨Hs, Hinf, Hia⟩ := S.forkFinish_foreign (s := s) Hrq Hrp hnd' Hfq hw fresh hd'
    refine ⟨by simpa [completeFork, hlow] using Hs, ?_, ?_⟩
    · intro z hz
      simpa [completeFork, hlow, Hj.1, Hi.1] using Hinf z hz
    · simpa [completeFork, hlow, Hj.2, Hi.2] using Hia

theorem closeM_protected (m : SMem) (e h l : Nat) :
    (S.closeM m e h l).1.rs = m.rs ∧ (S.closeM m e h l).1.rl = m.rl ∧
      (S.closeM m e h l).1.inf = m.inf ∧ (S.closeM m e h l).1.ia = m.ia := by
  simp only [closeM]
  split
  · exact ⟨rfl, rfl, rfl, rfl⟩
  · split <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem nodeStep_single_foreign {s : SMS} {v w : Nat} {it : Item} {r : Res}
    (hp : S.P.parts v = [it]) (HF : Stored s.m w r) (hw : w ≠ v)
    (fresh : ∀ e, it = .dart e → ∀ g ∈ r.seg, g.id ≠ e) :
    Stored (S.nodeStep s v).m w r := by
  have H := S.itRes_stored_foreign HF fresh
  have hh : (S.nodeStep s v).m.rs w = (S.itRes s.m it).1.rs w := by
    simp [nodeStep, hp, SMem.store, upd_ne _ _ hw]
  constructor
  · rw [hh]
    simpa [nodeStep, hp, SMem.store] using
      (H.stack.store_frame v (S.itRes s.m it).2.1 (S.itRes s.m it).2.2).inf_frame v 0
  · simpa [nodeStep, hp, SMem.store, upd_ne _ _ hw] using H.low

theorem completeNode_foreign (T : S.Tree) (G : S.Good) {sides : Nat → Bool}
    (hfork : ∀ v p q, S.P.IsFork S.α S.key v p q → S.P.ForkOK S.α S.key sides p q)
    {s : SMS} {v w : Nat}
    (Hchildren : ∀ c, Item.node c ∈ S.P.parts v → Stored s.m c (S.solve c))
    (HF : Stored s.m w (S.solve w))
    (hvw : ¬ S.P.Below v w) (hwv : ¬ S.P.Below w v) :
    Stored (S.completeNode s v).m w (S.solve w) := by
  have hw : w ≠ v := fun he => hvw (he ▸ Plan.Below.refl)
  have ownW : ∀ g ∈ (S.solve w).seg, S.Own w g.id := by
    intro g hg; exact (T.gids_ok G w).1 _ (List.mem_map.mpr ⟨g, hg, rfl⟩)
  cases G.kind v with
  | leaf hp =>
    constructor
    · have hh : (S.completeNode s v).m.rs w = s.m.rs w := by
        simp [completeNode, nodeStep, hp, SMem.store, upd_ne _ _ hw]
      rw [hh]
      simpa [completeNode, nodeStep, hp, SMem.store] using
        (HF.stack.store_frame v 0 S.INF).inf_frame v 0
    · simpa [completeNode, nodeStep, hp, SMem.store, upd_ne _ _ hw] using HF.low
  | out e hp he =>
    have Hfresh : ∀ e', Item.dart e = .dart e' → ∀ g ∈ (S.solve w).seg, g.id ≠ e' := by
      intro e' he' g hg hge
      cases he'
      have hit : Item.dart e ∈ S.P.parts v := by rw [hp]; simp
      exact T.own_disjoint hvw hwv e (ownIt_own hit rfl) (hge ▸ ownW g hg)
    simpa [completeNode, hp] using S.nodeStep_single_foreign hp HF hw Hfresh
  | single c hp =>
    simpa [completeNode, hp] using S.nodeStep_single_foreign hp HF hw
      (by intro e he; cases he)
  | target c d ht =>
    obtain ⟨p, q, hp, htarget⟩ := Good.target_tgtOf S G ht
    have hc : Item.node c ∈ S.P.parts v := by rcases ht.parts with h | h <;> rw [h] <;> simp
    have Hc := Hchildren c hc
    have Hclose := S.closeM_foreign (e := S.α d) Hc.stack HF.stack (by
      intro g hg q hq he
      have ho : S.Own v g.id := ownIt_own hc
        ((T.gids_ok G c).1 _ (List.mem_map.mpr ⟨g, hg, rfl⟩))
      exact T.own_disjoint hvw hwv g.id ho (he ▸ ownW q hq))
    rw [← Hc.low] at Hclose
    have Hprot := S.closeM_protected s.m (S.α d) (s.m.rs c) (s.m.rl c)
    have hh : (S.completeNode s v).m.rs w = s.m.rs w := by
      simp [completeNode, hp, htarget, twoStep, SMem.store, upd_ne _ _ hw, Hprot.1]
    constructor
    · rw [hh]
      apply Hclose.array_frame
      all_goals intro _ _; simp [completeNode, hp, htarget, twoStep, SMem.store]
    · simpa [completeNode, hp, htarget, twoStep, SMem.store,
        upd_ne _ _ hw, Hprot.2.1] using HF.low
  | fork p q hf =>
    have ht := Good.tgtOf_fork S G hf
    simpa [completeNode, hf.parts, ht] using
      (S.completeFork_foreign T G hfork hf Hchildren HF hvw hwv).1

end STACS2027.Embed.Sol

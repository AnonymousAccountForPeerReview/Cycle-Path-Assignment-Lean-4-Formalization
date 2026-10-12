module

public import ApproximationHardness.Embed.ForkFinish
import Lean.Elab.Tactic.Omega

/-! # Represented completion of a fork node -/

@[expose] public section

namespace STACS2027.Embed.Sol

variable (S : Sol)

def completeFork (s : SMS) (v : Nat) (p q : Item) : SMS :=
  let rp := S.itRes s.m p
  let rq := S.itRes rp.1 q
  if (S.rpart p).low < (S.rpart q).low then
    S.forkFinish s rq.1 v rp.2.1 rq.2.1 3 (S.rpart p) (S.rpart q)
  else S.forkFinish s rq.1 v rq.2.1 rp.2.1 4 (S.rpart q) (S.rpart p)

def forkNodeTicks (p q : Item) : Nat :=
  if (S.rpart p).low < (S.rpart q).low then S.forkTicks (S.rpart p) (S.rpart q)
  else S.forkTicks (S.rpart q) (S.rpart p)

theorem completeFork_refines (T : S.Tree) (G : S.Good) {sides : Nat → Bool}
    (hfork : ∀ v p q, S.P.IsFork S.α S.key v p q → S.P.ForkOK S.α S.key sides p q)
    {s : SMS} {v : Nat} {p q : Item} (hf : S.P.IsFork S.α S.key v p q)
    (Hmode : s.mode = 0)
    (Hchildren : ∀ c, Item.node c ∈ S.P.parts v → Stored s.m c (S.solve c)) :
    Stored (S.completeFork s v p q).m v (S.solve v) ∧
      (S.completeFork s v p q).mode = 0 ∧
      (S.completeFork s v p q).k = s.k + 1 ∧
      ∀ post, S.completeFork s v p q =
        (S.mstep post)^[S.forkNodeTicks p q] (S.twoStep s v p q) := by
  let rp := S.itRes s.m p
  let rq := S.itRes rp.1 q
  obtain ⟨Hrp, Hlp, Hrq, Hlq⟩ := S.prepare_fork_parts T G hf Hchildren
  have hp : p ∈ S.P.parts v := by rw [hf.parts]; simp
  have hq : q ∈ S.P.parts v := by rw [hf.parts]; simp
  have ip := G.rpart_inv hp hf.dp (fun c _ => G.solve_inv hfork c)
  have iq := G.rpart_inv hq hf.dq (fun c _ => G.solve_inv hfork c)
  have hpq : ∀ a ∈ els (S.rpart p).seg, ∀ b ∈ els (S.rpart q).seg, a ≠ b := by
    intro a ha b hb he
    subst b
    exact hf.disj a (List.mem_of_mem_filter ((ip.mem a).mp ha))
      (List.mem_of_mem_filter ((iq.mem a).mp hb))
  have Hnd := List.nodup_append.mpr ⟨ip.core.nodup, iq.core.nodup, hpq⟩
  have HpFresh : ∀ g ∈ (S.rpart p).seg, g.id ≠ S.gid v := by
    intro g hg he
    apply T.gid_not_ownIt hp
    rw [← he]
    exact (T.rpart_ok G hp).1 _ (List.mem_map.mpr ⟨g, hg, rfl⟩)
  have HqFresh : ∀ g ∈ (S.rpart q).seg, g.id ≠ S.gid v := by
    intro g hg he
    apply T.gid_not_ownIt hq
    rw [← he]
    exact (T.rpart_ok G hq).1 _ (List.mem_map.mpr ⟨g, hg, rfl⟩)
  have htgt := Good.tgtOf_fork S G hf
  have Hsolve : S.solve v = S.forkRes v (S.rpart p) (S.rpart q) := by
    rw [S.solve_two hf.parts, G.twoRes_fork hf]
  by_cases hlow : (S.rpart p).low < (S.rpart q).low
  · obtain ⟨Hs, Hm, Hk, Hi⟩ := S.forkFinish_refines Hmode Hrp Hrq Hnd HpFresh
      (fun g hg => gtop_le_of_rest ip.core hg)
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [completeFork, hlow, Hsolve, forkRes] using Hs
    · simpa [completeFork, hlow] using Hm
    · simpa [completeFork, hlow] using Hk
    · intro post
      simpa [completeFork, forkNodeTicks, hlow, twoStep, htgt, Hlp, Hlq] using Hi post
  · have Hnd' := List.nodup_append.mpr ⟨iq.core.nodup, ip.core.nodup,
        fun a ha b hb => Ne.symm (hpq b hb a ha)⟩
    obtain ⟨Hs, Hm, Hk, Hi⟩ := S.forkFinish_refines Hmode Hrq Hrp Hnd' HqFresh
      (fun g hg => gtop_le_of_rest iq.core hg)
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [completeFork, hlow, Hsolve, forkRes] using Hs
    · simpa [completeFork, hlow] using Hm
    · simpa [completeFork, hlow] using Hk
    · intro post
      simpa [completeFork, forkNodeTicks, hlow, twoStep, htgt, Hlp, Hlq] using Hi post

theorem forkNodeTicks_le (G : S.Good) {v : Nat} {p q : Item}
    (hf : S.P.IsFork S.α S.key v p q) :
    S.forkNodeTicks p q ≤ (S.consAt v).length + 2 := by
  have hc : S.consAt v = S.forkCons (S.rpart p) (S.rpart q) := by
    simp only [consAt, hf.parts]
    exact G.twoCons_fork hf _ _
  rw [hc]
  unfold forkNodeTicks forkCons
  split <;> exact S.forkTicks_le _ _

end STACS2027.Embed.Sol

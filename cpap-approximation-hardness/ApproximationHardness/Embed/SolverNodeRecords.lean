module

public import ApproximationHardness.Embed.SolverMergeRecords

/-! # Exact records written by each completed node -/

@[expose] public section

namespace STACS2027.Embed.Sol

variable (S : Sol)

def forkRows (p q : Item) : List (Nat × Bool) :=
  if (S.rpart p).low < (S.rpart q).low then S.finishRows (S.rpart p) (S.rpart q)
  else S.finishRows (S.rpart q) (S.rpart p)

def nodeRows (v : Nat) : List (Nat × Bool) :=
  match S.P.parts v with
  | [p, q] => if S.tgtOf p q = none then S.forkRows p q else []
  | _ => []

theorem itRes_records_frame (m : SMem) (it : Item) :
    (S.itRes m it).1.gp = m.gp ∧ (S.itRes m it).1.gf = m.gf := by
  cases it <;> exact ⟨rfl, rfl⟩

theorem completeFork_records (T : S.Tree) (G : S.Good) {sides : Nat → Bool}
    (hfork : ∀ v p q, S.P.IsFork S.α S.key v p q → S.P.ForkOK S.α S.key sides p q)
    {s : SMS} {v : Nat} {p q : Item} (hf : S.P.IsFork S.α S.key v p q)
    (Hchildren : ∀ c, Item.node c ∈ S.P.parts v → Stored s.m c (S.solve c)) :
    (S.completeFork s v p q).m.gp = writeParents (S.gid v) (S.forkRows p q) s.m.gp ∧
      (S.completeFork s v p q).m.gf = writeFlips (S.forkRows p q) s.m.gf := by
  obtain ⟨Hrp, Hlp, Hrq, Hlq⟩ := S.prepare_fork_parts T G hf Hchildren
  have hp : p ∈ S.P.parts v := by rw [hf.parts]; simp
  have hq : q ∈ S.P.parts v := by rw [hf.parts]; simp
  have ip := G.rpart_inv hp hf.dp (fun c _ => G.solve_inv hfork c)
  have iq := G.rpart_inv hq hf.dq (fun c _ => G.solve_inv hfork c)
  have hnd : (els (S.rpart p).seg ++ els (S.rpart q).seg).Nodup := by
    refine List.nodup_append.mpr ⟨ip.core.nodup, iq.core.nodup, ?_⟩
    intro a ha b hb he; subst b
    exact hf.disj a (List.mem_of_mem_filter ((ip.mem a).mp ha))
      (List.mem_of_mem_filter ((iq.mem a).mp hb))
  have Hi := S.itRes_records_frame s.m p
  have Hj := S.itRes_records_frame (S.itRes s.m p).1 q
  by_cases hlow : (S.rpart p).low < (S.rpart q).low
  · have H := S.forkFinish_records (s := s) (v := v) (code := 3) Hrp Hrq hnd
    simpa [completeFork, forkRows, hlow, Hi.1, Hj.1, Hi.2, Hj.2] using H
  · have hnd' := List.nodup_append.mpr ⟨iq.core.nodup, ip.core.nodup,
        fun a ha b hb => Ne.symm ((List.nodup_append.mp hnd).2.2 b hb a ha)⟩
    have H := S.forkFinish_records (s := s) (v := v) (code := 4) Hrq Hrp hnd'
    simpa [completeFork, forkRows, hlow, Hi.1, Hj.1, Hi.2, Hj.2] using H

theorem closeM_records_frame (m : SMem) (e h l : Nat) :
    (S.closeM m e h l).1.gp = m.gp ∧ (S.closeM m e h l).1.gf = m.gf := by
  simp only [closeM]
  split
  · exact ⟨rfl, rfl⟩
  · split <;> exact ⟨rfl, rfl⟩

theorem nodeRows_perm (G : S.Good) (v : Nat) : (S.nodeRows v).Perm (S.consAt v) := by
  cases G.kind v with
  | leaf hp => simp [nodeRows, consAt, hp]
  | out e hp he => simp [nodeRows, consAt, hp]
  | single c hp => simp [nodeRows, consAt, hp]
  | target c d ht =>
    obtain ⟨p, q, hp, htarget⟩ := Good.target_tgtOf S G ht
    simp [nodeRows, hp, htarget, G.consAt_target ht]
  | fork p q hf =>
    have ht := Good.tgtOf_fork S G hf
    simp only [nodeRows, hf.parts, ht, ↓reduceIte, consAt]
    rw [G.twoCons_fork hf]
    unfold forkRows forkCons
    split <;> exact S.finishRows_perm _ _

theorem completeNode_recordArrays (T : S.Tree) (G : S.Good) {sides : Nat → Bool}
    (hfork : ∀ v p q, S.P.IsFork S.α S.key v p q → S.P.ForkOK S.α S.key sides p q)
    {s : SMS} {v : Nat}
    (Hchildren : ∀ c, Item.node c ∈ S.P.parts v → Stored s.m c (S.solve c)) :
    (S.completeNode s v).m.gp = writeParents (S.gid v) (S.nodeRows v) s.m.gp ∧
      (S.completeNode s v).m.gf = writeFlips (S.nodeRows v) s.m.gf := by
  cases G.kind v with
  | leaf hp => simp [completeNode, nodeStep, nodeRows, hp, SMem.store, writeParents, writeFlips]
  | out e hp he => simp [completeNode, nodeStep, nodeRows, hp, itRes, SMem.store, writeParents, writeFlips]
  | single c hp => simp [completeNode, nodeStep, nodeRows, hp, itRes, SMem.store, writeParents, writeFlips]
  | target c d ht =>
    obtain ⟨p, q, hp, htarget⟩ := Good.target_tgtOf S G ht
    have H := S.closeM_records_frame s.m (S.α d) (s.m.rs c) (s.m.rl c)
    simp [completeNode, nodeRows, hp, htarget, twoStep, SMem.store, writeParents, writeFlips, H.1, H.2]
  | fork p q hf =>
    have ht := Good.tgtOf_fork S G hf
    simpa [completeNode, nodeRows, hf.parts, ht] using
      S.completeFork_records T G hfork hf Hchildren

theorem Tree.consAt_ids_nodup (T : S.Tree) (G : S.Good) (v : Nat) :
    ((S.consAt v).map Prod.fst).Nodup := by
  by_cases hn : S.consAt v = []
  · simp [hn]
  · obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil (S.consAt v) hn
    obtain ⟨p, q, hf⟩ := Sol.Good.fork_of_cons G hx
    exact (T.cons_ok G hf).2.1

theorem completeNode_records (T : S.Tree) (G : S.Good) {sides : Nat → Bool}
    (hfork : ∀ v p q, S.P.IsFork S.α S.key v p q → S.P.ForkOK S.α S.key sides p q)
    {s : SMS} {v : Nat}
    (Hchildren : ∀ c, Item.node c ∈ S.P.parts v → Stored s.m c (S.solve c)) :
    (∀ x ∈ S.consAt v, (S.completeNode s v).m.gp x.1 = S.gid v + 1 ∧
      (S.completeNode s v).m.gf x.1 = if x.2 then 1 else 0) ∧
      (∀ g, g ∉ (S.consAt v).map Prod.fst →
        (S.completeNode s v).m.gp g = s.m.gp g ∧ (S.completeNode s v).m.gf g = s.m.gf g) := by
  obtain ⟨Hp, Hf⟩ := S.completeNode_recordArrays T G hfork Hchildren
  have Hperm := S.nodeRows_perm G v
  have Hkeys := Hperm.map Prod.fst
  have Hnd := Hkeys.nodup_iff.mpr (Tree.consAt_ids_nodup S T G v)
  constructor
  · intro x hx
    have hx' := Hperm.mem_iff.mpr hx
    rw [Hp, Hf]
    exact ⟨writeParents_mem _ _ _ Hnd x hx', writeFlips_mem _ _ Hnd x hx'⟩
  · intro g hg
    have hg' : g ∉ (S.nodeRows v).map Prod.fst := fun h => hg (Hkeys.mem_iff.mp h)
    rw [Hp, Hf]
    exact ⟨writeParents_other _ _ _ _ hg', writeFlips_other _ _ _ hg'⟩

end STACS2027.Embed.Sol

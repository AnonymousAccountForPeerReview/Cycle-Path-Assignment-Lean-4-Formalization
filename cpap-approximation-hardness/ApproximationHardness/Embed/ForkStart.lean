module

public import ApproximationHardness.Embed.Merge
import Lean.Elab.Tactic.Omega

/-!
# Preparing the two live parts of a fork

Initializing either dart part preserves the disjoint stack of the other part.
Thus both operands of the linked merge have the exact abstract solver results.
-/

@[expose] public section

namespace STACS2027.Embed.Sol

variable (S : Sol)

theorem prepare_fork_parts (T : S.Tree) (G : S.Good)
    {m : SMem} {v : Nat} {p q : Item} (hf : S.P.IsFork S.α S.key v p q)
    (Hchildren : ∀ c, Item.node c ∈ S.P.parts v → Stored m c (S.solve c)) :
    let rp := S.itRes m p
    let rq := S.itRes rp.1 q
    StackRep rq.1 rp.2.1 (S.rpart p).seg ∧ rp.2.2 = (S.rpart p).low ∧
      StackRep rq.1 rq.2.1 (S.rpart q).seg ∧ rq.2.2 = (S.rpart q).low := by
  have hp : p ∈ S.P.parts v := by rw [hf.parts]; simp
  have hq : q ∈ S.P.parts v := by rw [hf.parts]; simp
  have Hop := (T.rpart_ok G hp).1
  have Hoq := (T.rpart_ok G hq).1
  obtain ⟨Hrp, Hlp⟩ := S.itRes_rep (fun c hc => Hchildren c (hc ▸ hp))
  have Hrp' := S.itRes_foreign Hrp (it := q) (by
    intro e hqe g hg he
    have hg' : g.id ∈ gids (S.rpart p) := List.mem_map.mpr ⟨g, hg, rfl⟩
    have hgOwn := Hop g.id hg'
    have hqeOwn : S.OwnIt q e := by simp [OwnIt, hqe]
    exact T.fork_disj hf (he ▸ hgOwn) hqeOwn)
  have Hqchildren : ∀ c, q = .node c → Stored (S.itRes m p).1 c (S.solve c) := by
    intro c hqc
    have Hc := Hchildren c (hqc ▸ hq)
    apply S.itRes_stored_foreign Hc
    intro e hpe g hg he
    have hg' : g.id ∈ gids (S.rpart q) := by
      simpa only [hqc, rpart, gids] using
        (List.mem_map.mpr ⟨g, hg, rfl⟩ : g.id ∈ (S.solve c).seg.map Grp.id)
    have hgOwn := Hoq g.id hg'
    have hpeOwn : S.OwnIt p e := by simp [OwnIt, hpe]
    exact T.fork_disj hf hpeOwn (he ▸ hgOwn)
  obtain ⟨Hrq, Hlq⟩ := S.itRes_rep Hqchildren
  exact ⟨Hrp', Hlp, Hrq, Hlq⟩

theorem Good.tgtOf_fork (G : S.Good) {v : Nat} {p q : Item}
    (hf : S.P.IsFork S.α S.key v p q) : S.tgtOf p q = none := by
  cases p with
  | node c =>
    cases q with
    | node w => rfl
    | dart d => simp [tgtOf, G.isIn_fork v c d (Or.inl hf)]
  | dart d =>
    cases q with
    | node c => simp [tgtOf, G.isIn_fork v c d (Or.inr hf)]
    | dart e => rfl

end STACS2027.Embed.Sol

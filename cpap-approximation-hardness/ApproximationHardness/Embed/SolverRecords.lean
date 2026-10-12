module

public import ApproximationHardness.Embed.SolverNodeRecords

/-! # The actual solver arrays satisfy the orientation pass's complete record contract -/

@[expose] public section

namespace STACS2027.Embed.Sol

variable (S : Sol)

structure RecordPrefix (m : SMem) (done : List Nat) : Prop where
  par : ∀ v ∈ done, ∀ x ∈ S.consAt v, m.gp x.1 = S.gid v + 1
  flip : ∀ v ∈ done, ∀ x ∈ S.consAt v, m.gf x.1 = if x.2 then 1 else 0
  zero : ∀ g, m.gp g ≠ 0 → ∃ v ∈ done, ∃ x ∈ S.consAt v, x.1 = g

theorem recordPrefix_empty (m : SMem) (H : ∀ g, m.gp g = 0) : S.RecordPrefix m [] := by
  refine ⟨by intros; contradiction, by intros; contradiction, ?_⟩
  intro g hg; exact False.elim (hg (H g))

theorem recordPrefix_append (T : S.Tree) (G : S.Good) {sides : Nat → Bool}
    (hfork : ∀ v p q, S.P.IsFork S.α S.key v p q → S.P.ForkOK S.α S.key sides p q)
    {s : SMS} {done : List Nat} {v : Nat} (Hrecord : S.RecordPrefix s.m done)
    (Hfresh : v ∉ done)
    (Hchildren : ∀ c, Item.node c ∈ S.P.parts v → Stored s.m c (S.solve c)) :
    S.RecordPrefix (S.completeNode s v).m (done ++ [v]) := by
  obtain ⟨Hnew, Hother⟩ := S.completeNode_records T G hfork Hchildren
  have hforeign : ∀ w ∈ done, ∀ x ∈ S.consAt w, x.1 ∉ (S.consAt v).map Prod.fst := by
    intro w hw x hx hm
    obtain ⟨y, hy, he⟩ := List.mem_map.mp hm
    have hsame := (T.consumed_unique G hx hy he.symm).1
    exact Hfresh (hsame ▸ hw)
  refine ⟨?_, ?_, ?_⟩
  · intro w hw x hx
    rcases List.mem_append.mp hw with hw | hw
    · exact (Hother x.1 (hforeign w hw x hx)).1.trans (Hrecord.par w hw x hx)
    · have he : w = v := by simpa using hw
      subst w; exact (Hnew x hx).1
  · intro w hw x hx
    rcases List.mem_append.mp hw with hw | hw
    · exact (Hother x.1 (hforeign w hw x hx)).2.trans (Hrecord.flip w hw x hx)
    · have he : w = v := by simpa using hw
      subst w; exact (Hnew x hx).2
  · intro g hg
    by_cases hn : g ∈ (S.consAt v).map Prod.fst
    · obtain ⟨x, hx, he⟩ := List.mem_map.mp hn
      exact ⟨v, by simp, x, hx, he⟩
    · have hgold : s.m.gp g ≠ 0 := by rw [← (Hother g hn).1]; exact hg
      obtain ⟨w, hw, x, hx, he⟩ := Hrecord.zero g hgold
      exact ⟨w, List.mem_append_left _ hw, x, hx, he⟩

theorem runPrefix_records (T : S.Tree) (G : S.Good) {sides : Nat → Bool}
    (hfork : ∀ v p q, S.P.IsFork S.α S.key v p q → S.P.ForkOK S.α S.key sides p q)
    {post : List Nat} (Hpost : S.PostOrder post) (init : SMS)
    (Hmode : init.mode = 0) (Hindex : init.k = 0) (Hzero : ∀ g, init.m.gp g = 0) :
    ∀ k, k ≤ post.length → S.RecordPrefix (S.runPrefix post init k).m (post.take k) := by
  intro k
  induction k with
  | zero => intro hk; simpa [runPrefix] using S.recordPrefix_empty init.m Hzero
  | succ k ih =>
    intro hk
    have hkl : k < post.length := by omega
    let v := post[k]
    have hv : post[k]? = some v := List.getElem?_eq_getElem hkl
    have Htake : post.take (k + 1) = post.take k ++ [v] := by
      rw [List.take_add_one]; simp [hv]
    let s := S.runPrefix post init k
    have Hprefix := S.runPrefix_spec T G hfork Hpost init Hmode Hindex k (by omega)
    have Hready := Hpost.ready T hv
    have Hchildren : ∀ c, Item.node c ∈ S.P.parts v → Stored s.m c (S.solve c) := by
      intro c hc
      have H := Hprefix.1 c (Hready.children c hc)
      exact ⟨H.1, H.2⟩
    have H := S.recordPrefix_append T G hfork (ih (by omega)) Hready.fresh Hchildren
    simpa [runPrefix, hv, Htake, s] using H

end STACS2027.Embed.Sol

namespace STACS2027.Embed.ForestData

theorem solver_records {F : ForestData} (hF : F.Valid) {post : List Nat}
    {sides : Nat → Bool}
    (hfork : ∀ v p q, (F.sol hF).P.IsFork (F.sol hF).α (F.sol hF).key v p q →
      (F.sol hF).P.ForkOK (F.sol hF).α (F.sol hF).key sides p q)
    (Hpost : F.PostOrder hF post) (init : SMS) (Hmode : init.mode = 0) (Hindex : init.k = 0)
    (Hzero : ∀ g, init.m.gp g = 0) :
    let final := (F.sol hF).runPrefix post init post.length
    Records F hF final.m.gp final.m.gf := by
  have H := (F.sol hF).runPrefix_records (tree hF) (good hF) hfork Hpost.solver
    init Hmode Hindex Hzero post.length (Nat.le_refl _)
  simp only [List.take_length] at H
  refine ⟨?_, ?_, ?_⟩
  · intro v x hx; exact H.par v (Hpost.mem v x hx) x hx
  · intro v x hx; exact H.flip v (Hpost.mem v x hx) x hx
  · intro g hg
    obtain ⟨v, hv, x, hx, he⟩ := H.zero g hg
    exact ⟨v, x, hx, he⟩

end STACS2027.Embed.ForestData

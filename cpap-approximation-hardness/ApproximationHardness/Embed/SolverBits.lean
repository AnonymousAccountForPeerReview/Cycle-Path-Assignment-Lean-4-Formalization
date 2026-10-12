module

public import ApproximationHardness.Embed.NodeBits

/-! # All visited Boolean instructions agree with the abstract solver -/

@[expose] public section

namespace STACS2027.Embed.Sol

variable (S : Sol)

theorem runPrefix_bits (T : S.Tree) (G : S.Good) {sides : Nat → Bool}
    (hfork : ∀ v p q, S.P.IsFork S.α S.key v p q → S.P.ForkOK S.α S.key sides p q)
    {post : List Nat} (Hpost : S.PostOrder post) (init : SMS)
    (Hmode : init.mode = 0) (Hindex : init.k = 0) :
    ∀ k, k ≤ post.length → ∀ v ∈ post.take k, ∀ o : Nat → Bool,
      (S.runPrefix post init k).m.evalBit S.gid o v = S.bit o v := by
  intro k
  induction k with
  | zero => intro hk v hv; simp at hv
  | succ k ih =>
    intro hk v hv o
    have hkl : k < post.length := by omega
    let w := post[k]
    have hw : post[k]? = some w := List.getElem?_eq_getElem hkl
    have Htake : post.take (k + 1) = post.take k ++ [w] := by
      rw [List.take_add_one]; simp [hw]
    let s := S.runPrefix post init k
    have Hprefix := S.runPrefix_spec T G hfork Hpost init Hmode Hindex k (by omega)
    have Hready := Hpost.ready T hw
    have Hchildren : ∀ c, Item.node c ∈ S.P.parts w → Stored s.m c (S.solve c) := by
      intro c hc
      have H := Hprefix.1 c (Hready.children c hc)
      exact ⟨H.1, H.2⟩
    have Hnext : S.runPrefix post init (k + 1) = S.completeNode s w := by simp [runPrefix, hw, s]
    rw [Hnext]
    rw [Htake] at hv
    rcases List.mem_append.mp hv with hv | hv
    · have hvw : v ≠ w := by intro he; exact Hready.fresh (he ▸ hv)
      obtain ⟨Hinf, Hia⟩ := S.completeNode_instruction_other T G Hchildren v hvw
      simp only [SMem.evalBit, Hinf, Hia]
      exact ih (by omega) v hv o
    · have he : v = w := by simpa using hv
      subst v
      exact S.completeNode_bit T G Hchildren o

end STACS2027.Embed.Sol

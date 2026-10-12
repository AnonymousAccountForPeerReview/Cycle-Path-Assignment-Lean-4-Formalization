module

public import ApproximationHardness.Embed.ForkNode
public import ApproximationHardness.Embed.EncodedBits
import Lean.Elab.Tactic.Omega

/-! # Completing each post-order node with a consumption bound -/

@[expose] public section

namespace STACS2027.Embed.Sol

variable (S : Sol)

def completeNode (s : SMS) (v : Nat) : SMS :=
  match S.P.parts v with
  | [p, q] => if S.tgtOf p q = none then S.completeFork s v p q else S.twoStep s v p q
  | _ => S.nodeStep s v

def nodeTicks (v : Nat) : Nat :=
  match S.P.parts v with
  | [p, q] => if S.tgtOf p q = none then S.forkNodeTicks p q + 1 else 1
  | _ => 1

theorem Good.target_tgtOf (G : S.Good) {v c d : Nat}
    (ht : S.P.IsTarget S.α S.key v c d) :
    ∃ p q, S.P.parts v = [p, q] ∧ S.tgtOf p q = some (c, d) := by
  rcases ht.parts with h | h
  · exact ⟨.node c, .dart d, h, by simp [tgtOf, G.isIn_target v c d ht]⟩
  · exact ⟨.dart d, .node c, h, by simp [tgtOf, G.isIn_target v c d ht]⟩

theorem completeNode_refines (T : S.Tree) (G : S.Good) {sides : Nat → Bool}
    (hfork : ∀ v p q, S.P.IsFork S.α S.key v p q → S.P.ForkOK S.α S.key sides p q)
    {s : SMS} {v : Nat} (Hmode : s.mode = 0)
    (Hchildren : ∀ c, Item.node c ∈ S.P.parts v → Stored s.m c (S.solve c)) :
    Stored (S.completeNode s v).m v (S.solve v) ∧
      (S.completeNode s v).mode = 0 ∧ (S.completeNode s v).k = s.k + 1 ∧
      S.nodeTicks v ≤ (S.consAt v).length + 3 ∧
      ∀ post, post[s.k]? = some v → S.completeNode s v =
        (S.mstep post)^[S.nodeTicks v] s := by
  have Hfirst : ∀ post, post[s.k]? = some v → S.mstep post s = S.nodeStep s v := by
    intro post hp; simp [mstep, Hmode, hp]
  cases G.kind v with
  | leaf h =>
    obtain ⟨Hr, Hk⟩ := S.nodeStep_leaf h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [completeNode, h] using Hr
    · simp [completeNode, nodeStep, h, Hmode]
    · simpa [completeNode, h] using Hk
    · simp [nodeTicks, h]
    · intro post hp; simpa [completeNode, nodeTicks, h] using (Hfirst post hp).symm
  | out e h he =>
    obtain ⟨Hr, Hk⟩ := S.nodeStep_single h (by intro c hc; cases hc)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [completeNode, h] using Hr
    · simp [completeNode, nodeStep, h, Hmode]
    · simpa [completeNode, h] using Hk
    · simp [nodeTicks, h]
    · intro post hp; simpa [completeNode, nodeTicks, h] using (Hfirst post hp).symm
  | single c h =>
    obtain ⟨Hr, Hk⟩ := S.nodeStep_single h (by
      intro c' hc; cases hc; exact Hchildren c (by rw [h]; simp))
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [completeNode, h] using Hr
    · simp [completeNode, nodeStep, h, Hmode]
    · simpa [completeNode, h] using Hk
    · simp [nodeTicks, h]
    · intro post hp; simpa [completeNode, nodeTicks, h] using (Hfirst post hp).symm
  | target c d ht =>
    obtain ⟨p, q, hp, htarget⟩ := Good.target_tgtOf S G ht
    have Hc := Hchildren c (by rcases ht.parts with h | h <;> rw [h] <;> simp)
    obtain ⟨Hr, Hk⟩ := S.twoStep_target htarget Hc (Good.target_head S G hfork ht)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [completeNode, hp, htarget, G.solve_target ht] using Hr
    · simp [completeNode, hp, htarget, twoStep, Hmode]
    · simpa [completeNode, hp, htarget] using Hk
    · simp [nodeTicks, hp, htarget]
    · intro post hn
      simpa [completeNode, nodeTicks, hp, htarget, nodeStep] using (Hfirst post hn).symm
  | fork p q hf =>
    have ht := Good.tgtOf_fork S G hf
    obtain ⟨Hr, Hm, Hk, Hi⟩ := S.completeFork_refines T G hfork hf Hmode Hchildren
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [completeNode, hf.parts, ht] using Hr
    · simpa [completeNode, hf.parts, ht] using Hm
    · simpa [completeNode, hf.parts, ht] using Hk
    · have Hbound := S.forkNodeTicks_le G hf
      simp [nodeTicks, hf.parts, ht]; omega
    · intro post hp
      simpa [completeNode, nodeTicks, hf.parts, ht,
        Function.iterate_succ_apply, Hfirst post hp, nodeStep] using Hi post

end STACS2027.Embed.Sol

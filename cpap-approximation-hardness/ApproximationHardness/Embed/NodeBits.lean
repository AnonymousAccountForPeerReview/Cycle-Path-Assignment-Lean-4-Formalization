module

public import ApproximationHardness.Embed.SolverRun

/-! # Correctness of the Boolean instruction stored for every processed node -/

@[expose] public section

namespace STACS2027.Embed.Sol

variable (S : Sol)

theorem completeFork_instruction (T : S.Tree) (G : S.Good) {s : SMS} {v : Nat} {p q : Item}
    (hf : S.P.IsFork S.α S.key v p q)
    (Hchildren : ∀ c, Item.node c ∈ S.P.parts v → Stored s.m c (S.solve c)) :
    (S.completeFork s v p q).m.inf v =
      (if (S.rpart p).low < (S.rpart q).low then
        (if (S.rpart q).seg = [] then 0 else 3)
      else (if (S.rpart p).seg = [] then 0 else 4)) ∧
      (∀ z, z ≠ v → (S.completeFork s v p q).m.inf z = s.m.inf z) ∧
      (S.completeFork s v p q).m.ia = s.m.ia := by
  obtain ⟨Hrp, Hlp, Hrq, Hlq⟩ := S.prepare_fork_parts T G hf Hchildren
  have Hi := S.itRes_instruction_frame s.m p
  have Hj := S.itRes_instruction_frame (S.itRes s.m p).1 q
  by_cases hlow : (S.rpart p).low < (S.rpart q).low
  · obtain ⟨Hv, Hother, Hia⟩ := S.forkFinish_instruction (s := s) (code := 3) (hx := (S.itRes s.m p).2.1)
      (rx := S.rpart p) Hrq
    refine ⟨by simpa [completeFork, hlow] using Hv, ?_, ?_⟩
    · intro z hz; simpa [completeFork, hlow, Hi.1, Hj.1] using Hother z hz
    · simpa [completeFork, hlow, Hi.2, Hj.2] using Hia
  · obtain ⟨Hv, Hother, Hia⟩ := S.forkFinish_instruction (s := s) (code := 4)
      (hx := (S.itRes (S.itRes s.m p).1 q).2.1) (rx := S.rpart q) Hrp
    refine ⟨by simpa [completeFork, hlow] using Hv, ?_, ?_⟩
    · intro z hz; simpa [completeFork, hlow, Hi.1, Hj.1] using Hother z hz
    · simpa [completeFork, hlow, Hi.2, Hj.2] using Hia

theorem completeNode_instruction_other (T : S.Tree) (G : S.Good) {s : SMS} {v : Nat}
    (Hchildren : ∀ c, Item.node c ∈ S.P.parts v → Stored s.m c (S.solve c)) :
    ∀ z, z ≠ v → (S.completeNode s v).m.inf z = s.m.inf z ∧
      (S.completeNode s v).m.ia z = s.m.ia z := by
  intro z hz
  cases G.kind v with
  | leaf hp => simp [completeNode, nodeStep, hp, SMem.store, upd_ne _ _ hz]
  | out e hp he => simp [completeNode, nodeStep, hp, itRes, SMem.store, upd_ne _ _ hz]
  | single c hp => simp [completeNode, nodeStep, hp, itRes, SMem.store, upd_ne _ _ hz]
  | target c d ht =>
    obtain ⟨p, q, hp, htarget⟩ := Good.target_tgtOf S G ht
    have Hprot := S.closeM_protected s.m (S.α d) (s.m.rs c) (s.m.rl c)
    simp [completeNode, hp, htarget, twoStep, SMem.store, upd_ne _ _ hz,
      Hprot.2.2.1, Hprot.2.2.2]
  | fork p q hf =>
    have ht := Good.tgtOf_fork S G hf
    obtain ⟨_, Hinf, Hia⟩ := S.completeFork_instruction T G hf Hchildren
    exact ⟨by simpa [completeNode, hf.parts, ht] using Hinf z hz,
      by simpa [completeNode, hf.parts, ht] using congrFun Hia z⟩

theorem completeNode_bit (T : S.Tree) (G : S.Good) {s : SMS} {v : Nat}
    (Hchildren : ∀ c, Item.node c ∈ S.P.parts v → Stored s.m c (S.solve c)) (o : Nat → Bool) :
    (S.completeNode s v).m.evalBit S.gid o v = S.bit o v := by
  cases G.kind v with
  | leaf hp => simp [completeNode, nodeStep, hp, SMem.evalBit, bit]
  | out e hp he => simp [completeNode, nodeStep, hp, SMem.evalBit, bit]
  | single c hp => simp [completeNode, nodeStep, hp, SMem.evalBit, bit]
  | target c d ht =>
    have hin := G.isIn_target v c d ht
    rcases ht.parts with hp | hp
    · simp [completeNode, hp, tgtOf, hin, twoStep, SMem.evalBit, bit, twoBit, tcode]
    · simp [completeNode, hp, tgtOf, hin, twoStep, SMem.evalBit, bit, twoBit, tcode]
  | fork p q hf =>
    have ht := Good.tgtOf_fork S G hf
    have Hi := (S.completeFork_instruction T G hf Hchildren).1
    simp only [completeNode, hf.parts, ht, ↓reduceIte, bit]
    rw [G.twoBit_fork hf, SMem.evalBit, Hi]
    by_cases hlow : (S.rpart p).low < (S.rpart q).low
    · by_cases hnil : (S.rpart q).seg = [] <;> simp [forkBit, hlow, hnil]
    · by_cases hnil : (S.rpart p).seg = [] <;> simp [forkBit, hlow, hnil]

end STACS2027.Embed.Sol

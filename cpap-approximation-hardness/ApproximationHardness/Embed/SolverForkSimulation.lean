module

public import ApproximationHardness.Embed.SolverForkOrder

/-! # Constant-time RAM refinement of the fork branch -/

@[expose] public section

namespace STACS2027.Embed.RAMSolver

open RAM

set_option maxHeartbeats 1500000

theorem forkNodeProgram_rep {L : Layout} {c : Config} {s : SMS} {S : Sol} {post : List Nat}
    {vertices darts v : Nat} (hr : Rep L c s) (ht : Tables L c S post vertices darts)
    (p q : Item) (hp : match p with | .node w => w < vertices | .dart e => e < darts)
    (hq : match q with | .node w => w < vertices | .dart e => e < darts)
    (hv : v < vertices) (hnode : c.reg 20 = v)
    (hpType : c.reg 22 = itemType p) (hpValue : c.reg 23 = itemValue p)
    (hqType : c.reg 26 = itemType q) (hqValue : c.reg 27 = itemValue q)
    (hnt : S.tgtOf p q = none) :
    Rep L (run forkNodeProgram c) (S.twoStep s v p q) ∧
      Tables L (run forkNodeProgram c) S post vertices darts := by
  let c₁ := run (itemResultInto 22 23 24 25) c
  let s₁ := {s with m := (S.itRes s.m p).1}
  obtain ⟨Hph, Hpl, Hr₁, Ht₁⟩ := itemResultInto_rep (typ := 22) (value := 23) (head := 24) (low := 25)
    hr ht p hp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hpType hpValue
  have hqType₁ : c₁.reg 26 = itemType q := by
    rw [show c₁.reg 26 = c.reg 26 from itemResultInto_reg_frame c 22 23 24 25 26 (by decide) (by decide) (by decide)]
    exact hqType
  have hqValue₁ : c₁.reg 27 = itemValue q := by
    rw [show c₁.reg 27 = c.reg 27 from itemResultInto_reg_frame c 22 23 24 25 27 (by decide) (by decide) (by decide)]
    exact hqValue
  let c₂ := run (itemResultInto 26 27 28 29) c₁
  let s₂ := {s₁ with m := (S.itRes s₁.m q).1}
  obtain ⟨Hqh, Hql, Hr₂, Ht₂⟩ := itemResultInto_rep (typ := 26) (value := 27) (head := 28) (low := 29)
    Hr₁ Ht₁ q hq (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hqType₁ hqValue₁
  have Hph₂ : c₂.reg 24 = (S.itRes s.m p).2.1 := by
    exact (itemResultInto_reg_frame c₁ 26 27 28 29 24 (by decide) (by decide) (by decide)).trans Hph
  have Hpl₂ : c₂.reg 25 = (S.itRes s.m p).2.2 := by
    exact (itemResultInto_reg_frame c₁ 26 27 28 29 25 (by decide) (by decide) (by decide)).trans Hpl
  have Hnode₂ : c₂.reg 20 = v := by
    rw [show c₂.reg 20 = c₁.reg 20 from itemResultInto_reg_frame c₁ 26 27 28 29 20 (by decide) (by decide) (by decide)]
    rw [show c₁.reg 20 = c.reg 20 from itemResultInto_reg_frame c 22 23 24 25 20 (by decide) (by decide) (by decide)]
    exact hnode
  let c₃ := run orderForkProgram c₂
  obtain ⟨Hr₃, Ht₃⟩ := orderForkProgram_rep Hr₂ Ht₂
  obtain ⟨H24, H25, H28, H29, H31, Hframe, _, _⟩ := orderForkProgram_raw c₂ Hr₂.bases.1
  have Hnode₃ : c₃.reg 20 = v := (Hframe 20 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)).trans Hnode₂
  obtain ⟨Hr₄, Ht₄⟩ := forkResultProgram_rep (v := v) (code := c₃.reg 31) Hr₃ Ht₃ hv Hnode₃ rfl
  have Hstate : S.forkStart s₂ s₂.m v (c₃.reg 24) (c₃.reg 25) (c₃.reg 28) (c₃.reg 29) (c₃.reg 31) =
      S.twoStep s v p q := by
    rw [H24, H25, H28, H29, H31, Hph₂, Hpl₂, Hqh, Hql]
    simp only [Sol.twoStep, hnt]
    dsimp only [s₂, s₁]
    by_cases hlow : (S.itRes s.m p).2.2 < (S.itRes (S.itRes s.m p).1 q).2.2 <;>
      simp only [hlow, decide_true, decide_false, Bool.false_eq_true, ↓reduceIte]
    all_goals unfold Sol.forkStart; split <;> rfl
  rw [← Hstate]
  exact ⟨by simpa only [run_forkNodeProgram, c₃, c₂, c₁] using Hr₄,
    by simpa only [run_forkNodeProgram, c₃, c₂, c₁] using Ht₄⟩

theorem forkNodeProgram_addrOK {L : Layout} {c : Config} {s : SMS} {S : Sol} {post : List Nat}
    {vertices darts v : Nat} (hr : Rep L c s) (ht : Tables L c S post vertices darts)
    (p q : Item) (hp : match p with | .node w => w < vertices | .dart e => e < darts)
    (hq : match q with | .node w => w < vertices | .dart e => e < darts)
    (hv : v < vertices) (hnode : c.reg 20 = v)
    (hpType : c.reg 22 = itemType p) (hpValue : c.reg 23 = itemValue p)
    (hqType : c.reg 26 = itemType q) (hqValue : c.reg 27 = itemValue q) :
    AddrOK L.limit forkNodeProgram c := by
  let c₁ := run (itemResultInto 22 23 24 25) c
  obtain ⟨_, _, Hr₁, Ht₁⟩ := itemResultInto_rep (typ := 22) (value := 23) (head := 24) (low := 25)
    hr ht p hp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hpType hpValue
  have hqType₁ : c₁.reg 26 = itemType q :=
    (itemResultInto_reg_frame c 22 23 24 25 26 (by decide) (by decide) (by decide)).trans hqType
  have hqValue₁ : c₁.reg 27 = itemValue q :=
    (itemResultInto_reg_frame c 22 23 24 25 27 (by decide) (by decide) (by decide)).trans hqValue
  let c₂ := run (itemResultInto 26 27 28 29) c₁
  obtain ⟨_, _, Hr₂, Ht₂⟩ := itemResultInto_rep (typ := 26) (value := 27) (head := 28) (low := 29)
    Hr₁ Ht₁ q hq (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hqType₁ hqValue₁
  have Hnode₂ : c₂.reg 20 = v :=
    (itemResultInto_reg_frame c₁ 26 27 28 29 20 (by decide) (by decide) (by decide)).trans
      ((itemResultInto_reg_frame c 22 23 24 25 20 (by decide) (by decide) (by decide)).trans hnode)
  let c₃ := run orderForkProgram c₂
  obtain ⟨Hr₃, _⟩ := orderForkProgram_rep Hr₂ Ht₂
  have Hframe := (orderForkProgram_raw c₂ Hr₂.bases.1).2.2.2.2.2.1
  have Hnode₃ : c₃.reg 20 = v := (Hframe 20 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)).trans Hnode₂
  have Ha₁ := itemResultInto_addrOK (typ := 22) (value := 23) (head := 24) (low := 25)
    (by decide) (by decide) (by decide) (by decide) (by decide) hr.bases.1 hr.bases.2.1
    (ItemAddressOK.ofRep hr ht p hp hpType hpValue)
  have Ha₂ := itemResultInto_addrOK (typ := 26) (value := 27) (head := 28) (low := 29)
    (by decide) (by decide) (by decide) (by decide) (by decide) Hr₁.bases.1 Hr₁.bases.2.1
    (ItemAddressOK.ofRep Hr₁ Ht₁ q hq hqType₁ hqValue₁)
  have Ha₃ : AddrOK L.limit orderForkProgram c₂ := by simp [orderForkProgram, AddrOK, seqs]
  have Ha₄ := forkResultProgram_addrOK Hr₃ (hv.trans_le ht.vertices) Hnode₃
  change AddrOK L.limit (seqs ([itemResultInto 22 23 24 25, itemResultInto 26 27 28 29] ++
    ([.sub 30 29 25, .ifz 30 (seqs [.add 21 24 0, .add 24 28 0, .add 28 21 0,
      .add 21 25 0, .add 25 29 0, .add 29 21 0, .const 31 4]) (.const 31 3)] ++
      [forkResultProgram]))) c
  rw [addrOK_seqs_append]
  constructor
  · simpa only [addrOK_seqs_cons, addrOK_seqs_nil, run_seqs_cons, run_seqs_nil] using
      And.intro Ha₁ (And.intro Ha₂ trivial)
  · rw [addrOK_seqs_append]
    exact ⟨Ha₃, by simpa only [addrOK_seqs_cons, addrOK_seqs_nil,
      orderForkProgram, run_seqs_cons, run_seqs_nil] using And.intro Ha₄ trivial⟩

theorem forkNodeProgram_exec {L : Layout} {c : Config} {s : SMS} {S : Sol} {post : List Nat}
    {vertices darts v : Nat} (hr : Rep L c s) (ht : Tables L c S post vertices darts)
    (p q : Item) (hp : match p with | .node w => w < vertices | .dart e => e < darts)
    (hq : match q with | .node w => w < vertices | .dart e => e < darts)
    (hv : v < vertices) (hnode : c.reg 20 = v)
    (hpType : c.reg 22 = itemType p) (hpValue : c.reg 23 = itemValue p)
    (hqType : c.reg 26 = itemType q) (hqValue : c.reg 27 = itemValue q) :
    ∃ t, ExecB L.limit forkNodeProgram c t (run forkNodeProgram c) ∧ t ≤ 1000 := by
  have Ha := forkNodeProgram_addrOK hr ht p q hp hq hv hnode hpType hpValue hqType hqValue
  have Hl : LoopFree forkNodeProgram := by
    simp [forkNodeProgram, itemResultInto, forkResultProgram, beginForkProgram,
      storeNodeResult, loadCell, storeCell, LoopFree, seqs]
  have Hsize : size forkNodeProgram ≤ 1000 := by decide
  exact ⟨_, execB_run _ Hl c Ha, (cost_le_size _ _).trans Hsize⟩

end STACS2027.Embed.RAMSolver

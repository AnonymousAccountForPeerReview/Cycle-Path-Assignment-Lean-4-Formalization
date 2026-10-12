module

public import ApproximationHardness.Embed.NodeFrame
public import ApproximationHardness.Embed.Accounting
import Lean.Elab.Tactic.Omega

/-!
# Running the complete live-frontier solver

Only the disjoint live frontier is retained as a representation invariant.
The exact machine transition bound charges the groups consumed at each node.
-/

@[expose] public section

namespace STACS2027.Embed.Sol

variable (S : Sol)

def runPrefix (S : Sol) (post : List Nat) (init : SMS) : Nat → SMS
  | 0 => init
  | k + 1 =>
    let s := runPrefix S post init k
    match post[k]? with
    | some v => S.completeNode s v
    | none => s

def prefixCharge (S : Sol) (post : List Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => prefixCharge S post k +
      (match post[k]? with | some v => (S.consAt v).length + 3 | none => 0)

theorem completeNode_frontier (T : S.Tree) (G : S.Good) {sides : Nat → Bool}
    (hfork : ∀ v p q, S.P.IsFork S.α S.key v p q → S.P.ForkOK S.α S.key sides p q)
    {s : SMS} {done : List Nat} {v : Nat} (Hmode : s.mode = 0)
    (Hfront : S.Frontier s.m done) (Hready : S.Ready done v) :
    S.Frontier (S.completeNode s v).m (done ++ [v]) := by
  have Hchildren : ∀ c, Item.node c ∈ S.P.parts v → Stored s.m c (S.solve c) := by
    intro c hc; exact ⟨(Hfront c (Hready.children c hc)).1, (Hfront c (Hready.children c hc)).2⟩
  have Hnode := (S.completeNode_refines T G hfork Hmode Hchildren).1
  intro w Hw
  rcases (S.live_append done v Hready.parents w).mp Hw with rfl | ⟨Hw, Hnc⟩
  · exact ⟨Hnode.stack, Hnode.low⟩
  · obtain ⟨hvw, hwv⟩ := Hready.survives w Hw Hnc
    have Hold : Stored s.m w (S.solve w) := ⟨(Hfront w Hw).1, (Hfront w Hw).2⟩
    have H := S.completeNode_foreign T G hfork Hchildren Hold hvw hwv
    exact ⟨H.stack, H.low⟩

theorem runPrefix_spec (T : S.Tree) (G : S.Good) {sides : Nat → Bool}
    (hfork : ∀ v p q, S.P.IsFork S.α S.key v p q → S.P.ForkOK S.α S.key sides p q)
    {post : List Nat} (Hpost : S.PostOrder post) (init : SMS)
    (Hmode : init.mode = 0) (Hindex : init.k = 0) :
    ∀ k, k ≤ post.length →
      S.Frontier (S.runPrefix post init k).m (post.take k) ∧
      (S.runPrefix post init k).mode = 0 ∧ (S.runPrefix post init k).k = k ∧
      ∃ t, t ≤ S.prefixCharge post k ∧ S.runPrefix post init k = (S.mstep post)^[t] init := by
  intro k
  induction k with
  | zero =>
    intro hk
    exact ⟨by simpa [runPrefix] using S.frontier_nil init.m, Hmode, Hindex,
      ⟨0, by simp [prefixCharge], rfl⟩⟩
  | succ k ih =>
    intro hk
    have hkl : k < post.length := by omega
    let v := post[k]
    have hv : post[k]? = some v := List.getElem?_eq_getElem hkl
    obtain ⟨Hfront, HmodeK, HindexK, t, Ht, Hiter⟩ := ih (by omega)
    let s := S.runPrefix post init k
    have Hready := Hpost.ready T hv
    have Hchildren : ∀ c, Item.node c ∈ S.P.parts v → Stored s.m c (S.solve c) := by
      intro c hc; exact ⟨(Hfront c (Hready.children c hc)).1, (Hfront c (Hready.children c hc)).2⟩
    obtain ⟨Hnode, HmodeN, HindexN, Hticks, HiterN⟩ :=
      S.completeNode_refines T G hfork HmodeK Hchildren
    have HfrontN := S.completeNode_frontier T G hfork HmodeK Hfront Hready
    have Htake : post.take (k + 1) = post.take k ++ [v] := by
      rw [List.take_add_one]
      simp [hv]
    have Hnext : S.runPrefix post init (k + 1) = S.completeNode s v := by simp [runPrefix, hv, s]
    refine ⟨?_, ?_, ?_, ⟨S.nodeTicks v + t, ?_, ?_⟩⟩
    · rw [Hnext, Htake]; exact HfrontN
    · rw [Hnext]; exact HmodeN
    · rw [Hnext, HindexN, HindexK]
    · have Hcharge : S.prefixCharge post (k + 1) =
          S.prefixCharge post k + (S.consAt v).length + 3 := by
        simp [prefixCharge, hv, Nat.add_assoc]
      rw [Hcharge]
      omega
    · rw [Hnext, HiterN post (by simpa [HindexK] using hv)]
      change (S.mstep post)^[S.nodeTicks v] s = _
      rw [show s = (S.mstep post)^[t] init from Hiter]
      exact (Function.iterate_add_apply (S.mstep post) _ _ _).symm

theorem prefixCharge_eq {post : List Nat} : ∀ k, k ≤ post.length →
    S.prefixCharge post k = ((post.take k).flatMap S.consAt).length + 3 * k := by
  intro k
  induction k with
  | zero => intro hk; simp [prefixCharge]
  | succ k ih =>
    intro hk
    have hkl : k < post.length := by omega
    let v := post[k]
    have hv : post[k]? = some v := List.getElem?_eq_getElem hkl
    have Htake : post.take (k + 1) = post.take k ++ [v] := by
      rw [List.take_add_one]; simp [hv]
    rw [Htake]
    simp only [List.flatMap_append, List.flatMap_singleton, List.length_append]
    have Hcharge : S.prefixCharge post (k + 1) =
        S.prefixCharge post k + (S.consAt v).length + 3 := by
      simp [prefixCharge, hv, Nat.add_assoc]
    rw [Hcharge, ih (by omega)]
    omega

end STACS2027.Embed.Sol

namespace STACS2027.Embed.ForestData

theorem iterate_fixed {α : Type} (step : α → α) {x : α} (h : step x = x) :
    ∀ n, step^[n] x = x := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, h]

theorem solver_linear {F : ForestData} (hF : F.Valid) {post : List Nat}
    {sides : Nat → Bool}
    (hfork : ∀ v p q, (F.sol hF).P.IsFork (F.sol hF).α (F.sol hF).key v p q →
      (F.sol hF).P.ForkOK (F.sol hF).α (F.sol hF).key sides p q)
    (Hpost : F.PostOrder hF post) (init : SMS) (Hmode : init.mode = 0) (Hindex : init.k = 0) :
    let final := (F.sol hF).runPrefix post init post.length
    final.mode = 0 ∧ final.k = post.length ∧
      (F.sol hF).mstep post final = final ∧
      ∃ t, t ≤ 20 * F.E ∧ final = ((F.sol hF).mstep post)^[t] init := by
  have H := (F.sol hF).runPrefix_spec (tree hF) (good hF) hfork
    Hpost.solver init Hmode Hindex post.length (Nat.le_refl _)
  obtain ⟨_, HmodeF, HindexF, t, Ht, Hiter⟩ := H
  refine ⟨HmodeF, HindexF, ?_, ⟨t, ?_, Hiter⟩⟩
  · simp [Sol.mstep, HmodeF, HindexF]
  · have Hcharge := (F.sol hF).prefixCharge_eq post.length (Nat.le_refl _)
    have Hlen : (post.flatMap (F.sol hF).consAt).length = (consumptionIds hF post).length := by
      simp [consumptionIds, List.length_flatMap]
    have Hcons := consumptionIds_length_le hF Hpost
    have Hnodes := length_le_of_nodup_lt (4 * F.E) post Hpost.nodup Hpost.lt
    simp only [List.take_length] at Hcharge
    rw [Hlen] at Hcharge
    omega

theorem solver_fixedBudget {F : ForestData} (hF : F.Valid) {post : List Nat}
    {sides : Nat → Bool}
    (hfork : ∀ v p q, (F.sol hF).P.IsFork (F.sol hF).α (F.sol hF).key v p q →
      (F.sol hF).P.ForkOK (F.sol hF).α (F.sol hF).key sides p q)
    (Hpost : F.PostOrder hF post) (init : SMS) (Hmode : init.mode = 0) (Hindex : init.k = 0) :
    ((F.sol hF).mstep post)^[20 * F.E] init = (F.sol hF).runPrefix post init post.length := by
  obtain ⟨_, _, Hfixed, t, Ht, Hiter⟩ := solver_linear hF hfork Hpost init Hmode Hindex
  have Hsplit : 20 * F.E = (20 * F.E - t) + t := by omega
  rw [Hsplit, Function.iterate_add_apply, ← Hiter]
  exact iterate_fixed _ Hfixed _

end STACS2027.Embed.ForestData

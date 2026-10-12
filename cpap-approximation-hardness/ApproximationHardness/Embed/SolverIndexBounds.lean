module

public import ApproximationHardness.Embed.SolverExecution
public import ApproximationHardness.Embed.SolverInit
import Lean.Elab.Tactic.Omega

/-! # Bounds on the recorded target indices throughout the actual solver -/

@[expose] public section

namespace STACS2027.Embed.RAMSolver

open RAM

theorem itRes_ia (S : Sol) (m : SMem) (it : Item) : (S.itRes m it).1.ia=m.ia := by
  cases it <;> rfl

theorem closeM_ia (S : Sol) (m : SMem) (e h l : Nat) :
    (S.closeM m e h l).1.ia=m.ia := by
  simp only [Sol.closeM]
  split
  · rfl
  · split <;> rfl

theorem forkStart_ia (S : Sol) (s : SMS) (m : SMem) (v hx lx hy ly code : Nat) :
    (S.forkStart s m v hx lx hy ly code).m.ia=m.ia := by
  simp only [Sol.forkStart]
  split <;> rfl

theorem tgtOf_dart_mem (S : Sol) {p q : Item} {c d : Nat}
    (h : S.tgtOf p q=some (c,d)) : Item.dart d∈[p,q] := by
  cases p <;> cases q <;> simp only [Sol.tgtOf] at h
  all_goals first
    | contradiction
    | (split at h <;> simp_all)

theorem twoStep_ia_bound {S : Sol} {s : SMS} {v width : Nat} {p q : Item}
    (hs : ∀ i,s.m.ia i<width)
    (hd : ∀ d,Item.dart d∈[p,q] → S.α d<width) :
    ∀ i,(S.twoStep s v p q).m.ia i<width := by
  intro i
  unfold Sol.twoStep
  split
  · rename_i c d he
    dsimp only
    rw [closeM_ia]
    by_cases hi : i=v
    · simp [upd,hi]
      exact hd d (tgtOf_dart_mem S he)
    · simp [upd,hi]
      exact hs i
  · rw [forkStart_ia,itRes_ia,itRes_ia]
    exact hs i

theorem nodeStep_ia_bound {L : Layout} {S : Sol} {post : List Nat}
    {vertices darts : Nat} {c : Config} {s : SMS} {v : Nat}
    (ht : Tables L c S post vertices darts) (hv : v<vertices)
    (hs : ∀ i,s.m.ia i<L.width) :
    ∀ i,(S.nodeStep s v).m.ia i<L.width := by
  unfold Sol.nodeStep
  split
  · exact hs
  · simpa only [SMem.store,itRes_ia] using hs
  · rename_i p q he
    apply twoStep_ia_bound hs
    intro d hd
    have hm : Item.dart d∈S.P.parts v := by simpa only [he] using hd
    have hb : d<darts := ht.children v hv (.dart d) hm
    exact (ht.partnersBound d hb).trans_le ht.darts
  · exact hs

theorem mstep_ia_bound {L : Layout} {S : Sol} {post : List Nat}
    {vertices darts : Nat} {c : Config} {s : SMS}
    (ht : Tables L c S post vertices darts)
    (hs : ∀ i,s.m.ia i<L.width) :
    ∀ i,(S.mstep post s).m.ia i<L.width := by
  unfold Sol.mstep
  split
  · split
    · rename_i v hv
      exact nodeStep_ia_bound ht (ht.nodeBound v (List.mem_of_getElem? hv)) hs
    · exact hs
  · split
    · unfold Sol.popStep
      split <;> exact hs
    · unfold Sol.consStep
      split <;> exact hs

theorem iterate_ia_bound {L : Layout} {S : Sol} {post : List Nat}
    {vertices darts : Nat} {c : Config} {s : SMS}
    (ht : Tables L c S post vertices darts)
    (hs : ∀ i,s.m.ia i<L.width) :
    ∀ n i,((S.mstep post)^[n] s).m.ia i<L.width := by
  intro n
  induction n with
  | zero => exact hs
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact mstep_ia_bound ht ih

/-- Every recorded target index is in the allocated solver width at the end of
its fixed linear execution, including indices outside the processed postorder. -/
theorem solver_final_ia_bound {F : ForestData} (hF : F.Valid) {L : Layout}
    {post : List Nat} {vertices darts : Nat} {c : Config} {sides : Nat→Bool}
    (ht : Tables L c (F.sol hF) post vertices darts) (hw : 0<L.width)
    (hfork : ∀ v p q,(F.sol hF).P.IsFork (F.sol hF).α (F.sol hF).key v p q →
      (F.sol hF).P.ForkOK (F.sol hF).α (F.sol hF).key sides p q)
    (hpost : F.PostOrder hF post) :
    ∀ v,((F.sol hF).runPrefix post initialState post.length).m.ia v<L.width := by
  rw [← ForestData.solver_fixedBudget hF hfork hpost initialState rfl rfl]
  exact iterate_ia_bound ht (by intro i;exact hw) _

end STACS2027.Embed.RAMSolver

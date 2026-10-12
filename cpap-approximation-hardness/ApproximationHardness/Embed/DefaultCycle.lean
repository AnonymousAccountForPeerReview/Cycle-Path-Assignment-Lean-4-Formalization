module

public import ApproximationHardness.Embed.RotationChoice
public import ApproximationHardness.Embed.SolverRAM
import Lean.Elab.Tactic.Omega

/-! # Reconstruct the default local rotation from two plan parts -/

@[expose] public section

namespace STACS2027.Embed

/-- The first dart not listed among the plan parts. -/
def missingDart (ds ps : List Nat) : Nat :=
  (ds.filter (fun d=> !(ps.contains d))).headD 0

theorem filter_missing_erase (ds : List Nat) (z : Nat) (hnd : ds.Nodup) (hz : z∈ds) :
    ds.filter (fun d=> !((ds.erase z).contains d))=[z] := by
  let result := ds.filter (fun d=> !((ds.erase z).contains d))
  have hm : ∀ x,x∈result ↔ x=z := by
    intro x
    have hnot : (!(ds.erase z).contains x)=true ↔ x∉ds.erase z := by
      by_cases hmem : x∈ds.erase z <;> simp [hmem]
    simp only [result,List.mem_filter,hnot,hnd.mem_erase_iff]
    constructor
    · intro ⟨hx,hnot⟩
      by_contra he
      exact hnot ⟨he,hx⟩
    · intro he;subst x;exact ⟨hz,by simp⟩
  have hn : result.Nodup := hnd.filter _
  have hz' : z∈result := (hm z).mpr rfl
  cases he : result with
  | nil => simp [he] at hz'
  | cons x xs =>
    have hx : x=z := (hm x).mp (by simp [he])
    subst x
    have htail : xs=[] := by
      cases hxs : xs with
      | nil => rfl
      | cons y ys =>
        have hy : y=z := (hm y).mp (by simp [he,hxs])
        have := hn
        simp [he,hxs,hy] at this
    change result=[z]
    rw [he,htail]

namespace ForestData

/-- Plan parts decoded to incident darts, with the missing root dart recovered. -/
def defaultCycle (F : ForestData) (v : Nat) : List Nat :=
  let ps := (F.parts v).map F.itemDart
  if F.IsRoot v then
    ps++(if (F.dartsAt v).length=3 then [missingDart (F.dartsAt v) ps] else [])
  else F.par v::ps

theorem defaultCycle_eq {F : ForestData} (hF : F.Valid) {v : Nat} (hv : F.IsVertex v) :
    F.defaultCycle v=cycOf hF (fun _=>false) v := by
  unfold defaultCycle cycOf
  have hp : (F.parts v).map F.itemDart =
      (F.dartsAt v).erase (if F.IsRoot v then F.zOf v else F.par v) := by
    have he := ord_map_itemDart hF (β:=fun _=>false) hv
    simpa [Plan.ord,ForestData.plan] using he
  rw [ord_map_itemDart hF hv]
  simp only [Bool.false_eq_true,ite_false]
  by_cases hr : F.IsRoot v
  · simp only [hr,ite_true,hp]
    have hiff : (F.dartsAt v).length=3 ↔ F.zOf v<2*F.E := by
      constructor
      · intro hlen
        unfold zOf
        rw [ite_eq_left hlen]
        split
        · rename_i d he
          have hd : d∈(F.dartsAt v).filter (fun d=>!decide (F.IsTree d)) :=
            List.mem_of_getLast? he
          exact (mem_dartsAt.mp (List.mem_of_mem_filter hd)).1
        · have hmem : (F.dartsAt v).getLastD 0∈F.dartsAt v := by
            cases hd : F.dartsAt v with
            | nil => simp [hd] at hlen
            | cons a ds =>
              simp [List.getLastD_eq_getLast?,List.getLast?_eq_some_getLast]
          exact (mem_dartsAt.mp hmem).1
      · intro hz;exact (zOf_mem hz).2
    by_cases hlen : (F.dartsAt v).length=3
    · have hz := hiff.mp hlen
      have hm := (zOf_mem hz).1
      rw [ite_eq_left hlen,ite_eq_left hz]
      congr 2
      unfold missingDart
      rw [filter_missing_erase _ _ (dartsAt_nodup _) hm]
      rfl
    · simp only [hlen,ite_false,hiff.not.mp hlen ]
  · simp only [hr,ite_false,hp ]

end ForestData

end STACS2027.Embed

module

public import NPHardness.PlanarSourceRotationTableCoverage

/-! The actual finite candidate syntax projects to precisely the certified
geometric neighborhoods, with invalid boundary blocks removed. -/

@[expose] public section
namespace STACS2027.PlanarSource.RotationTable
open Complexity Complexity.SAT Complexity.Planar Grid
open Complexity.StackTableauEmitter STACS2027.PlanarSource.Packed

theorem start_projection {n : Nat} (d : Layout n) (k : NumExpr n)
    (odd : Bool) (w : SAT.Word) (env : Env n) :
    liveProjection (d.startOccurrences k odd) w env =
      blockTags (d.W.eval env) (d.M.eval env) (d.Q.eval env) (layoutBits d w env) (.start (k.eval env) odd) := by
  rw [start_liveProjection,Layout.columnBase_eval]
  rfl

theorem end_projection {n : Nat} (d : Layout n) (k : NumExpr n)
    (odd : Bool) (w : SAT.Word) (env : Env n) :
    liveProjection (d.endOccurrences k odd) w env =
      blockTags (d.W.eval env) (d.M.eval env) (d.Q.eval env) (layoutBits d w env) (.finish (k.eval env) odd) := by
  rw [end_liveProjection,Layout.endBase_eval]
  rfl

theorem cell_projection {n : Nat} (d : Layout n) (k idx : NumExpr n)
    (odd : Bool) (w : SAT.Word) (env : Env n) :
    liveProjection (d.cellOccurrences k idx odd) w env =
      blockTags (d.W.eval env) (d.M.eval env) (d.Q.eval env) (layoutBits d w env)
        (.cell (k.eval env) (idx.eval env) odd) := by
  rw [cell_liveProjection,Layout.cellBase_eval]
  rfl

theorem rainbow_projection {n : Nat} (d : Layout n) (k v : NumExpr n)
    (odd : Bool) (w : SAT.Word) (env : Env n) :
    liveProjection (d.rainbowOccurrences k v odd) w env =
      blockTags (d.W.eval env) (d.M.eval env) (d.Q.eval env) (layoutBits d w env)
        (.rainbow (k.eval env) (v.eval env) odd) := by
  rw [rainbow_liveProjection,Layout.rainbowBase_eval]
  rfl

theorem chain_projection {n : Nat} (d : Layout n) (k idx : NumExpr n)
    (odd : Bool) (w : SAT.Word) (env : Env n) :
    liveProjection (d.chainCandidates k idx odd) w env =
      neighborhoodTags (d.W.eval env) (d.M.eval env) (d.Q.eval env) (layoutBits d w env)
        (chainNeighborhood (d.W.eval env) (k.eval env) (idx.eval env) odd) := by
  simp only [Layout.chainCandidates,liveProjection_append,liveProjection_gate,
    cell_projection,start_projection,end_projection,Test.eval_eq]
  by_cases hi : 0<idx.eval env <;> by_cases hz : idx.eval env=0 <;> by_cases hw : idx.eval env=d.W.eval env <;>
    simp_all [chainNeighborhood,Test.eval,NumExpr.eval,subN,
      neighborhoodTags, show (1≤idx.eval env) ↔ (0<idx.eval env) by omega]

theorem cellCandidates_projection {n : Nat} (d : Layout n) (k idx : NumExpr n)
    (odd : Bool) (p : Nat) (w : SAT.Word) (env : Env n) :
    liveProjection (d.cellCandidates k idx odd p) w env =
      neighborhoodTags (d.W.eval env) (d.M.eval env) (d.Q.eval env) (layoutBits d w env)
        (cellNeighborhood (d.W.eval env) (k.eval env) (idx.eval env) odd p) := by
  by_cases hp0 : p=0
  · subst p
    simp only [Layout.cellCandidates,cellNeighborhood,ite_true]
    exact chain_projection d k idx odd w env
  · by_cases hp9 : p=9
    · subst p
      simp only [Layout.cellCandidates,cellNeighborhood,show (9:Nat)≠0 by decide,ite_false,ite_true]
      exact chain_projection d k (addN idx 1) odd w env
    · by_cases hp1 : p=1 <;> by_cases hp8 : p=8 <;> cases odd <;>
        by_cases hk : 0<k.eval env <;>
        simp [Layout.cellCandidates,cellNeighborhood,interiorNeighborhood,hp0,hp9,hp1,hp8,
          liveProjection_append,liveProjection_gate,cell_projection,rainbow_projection,
          Test.eval,NumExpr.eval,subN,Complexity.Planar.Emit.revE,neighborhoodTags,hk,
          show (1≤k.eval env) ↔ (0<k.eval env) by omega]

theorem startCandidates_projection {n : Nat} (d : Layout n) (k : NumExpr n)
    (odd : Bool) (p : Nat) (w : SAT.Word) (env : Env n) :
    liveProjection (d.startCandidates k odd p) w env =
      neighborhoodTags (d.W.eval env) (d.M.eval env) (d.Q.eval env) (layoutBits d w env)
        (startNeighborhood (d.W.eval env) (k.eval env) odd p) := by
  by_cases hp : p=0
  · simp [Layout.startCandidates,startNeighborhood,hp,start_projection,neighborhoodTags]
  · simp only [Layout.startCandidates,startNeighborhood,hp,ite_false]
    exact chain_projection d k (.const 0) odd w env

theorem endCandidates_projection {n : Nat} (d : Layout n) (k : NumExpr n)
    (odd : Bool) (p : Nat) (w : SAT.Word) (env : Env n) :
    liveProjection (d.endCandidates k odd p) w env =
      neighborhoodTags (d.W.eval env) (d.M.eval env) (d.Q.eval env) (layoutBits d w env)
        (endNeighborhood (d.W.eval env) (k.eval env) odd p) := by
  by_cases hp : p=0
  · simp only [Layout.endCandidates,endNeighborhood,hp,ite_true]
    exact chain_projection d k d.W odd w env
  · simp [Layout.endCandidates,endNeighborhood,hp,end_projection,neighborhoodTags]

theorem rainbowCandidates_projection {n : Nat} (d : Layout n) (k v : NumExpr n)
    (odd : Bool) (p : Nat) (w : SAT.Word) (env : Env n) :
    liveProjection (d.rainbowCandidates k v odd p) w env =
      neighborhoodTags (d.W.eval env) (d.M.eval env) (d.Q.eval env) (layoutBits d w env)
        (rainbowNeighborhood (d.W.eval env) (k.eval env) (v.eval env) odd p) := by
  cases odd <;> by_cases hp : p=0 <;>
    simp only [Layout.rainbowCandidates,rainbowNeighborhood,Bool.false_eq_true,ite_false,ite_true,hp,
      cellCandidates_projection,addN,NumExpr.eval,Complexity.Planar.Emit.revE]

end STACS2027.PlanarSource.RotationTable

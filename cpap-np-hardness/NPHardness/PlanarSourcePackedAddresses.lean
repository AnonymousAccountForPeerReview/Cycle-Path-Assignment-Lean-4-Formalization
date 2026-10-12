module

public import NPHardness.PlanarSourcePackedPrefix

/-! The emitted arithmetic addresses are the actual clause and occurrence
prefixes of the registered grid formula. -/

@[expose] public section
namespace STACS2027.PlanarSource.Packed
open Complexity Complexity.SAT Complexity.StackTableauEmitter Complexity.Planar.Grid
open Complexity.Planar.Emit

theorem Layout.columnSize_eval {n : Nat} (d : Layout n) (b : Bool) (env : Env n) :
    (d.columnSize b).eval env = Index.columnSize b (d.W.eval env) := by
  cases b <;> rfl

theorem Layout.columnBase_eval {n : Nat} (d : Layout n) (k : NumExpr n)
    (odd b : Bool) (env : Env n) :
    (d.columnBase k odd b).eval env =
      Index.columnBase (d.W.eval env) (d.M.eval env) (d.Q.eval env) (k.eval env) odd b := by
  cases odd <;> simp only [Layout.columnBase,Index.columnBase,↓reduceIte,
    Bool.false_eq_true,NumExpr.eval,revE,Layout.columnSize_eval]

theorem Layout.cellBase_eval {n : Nat} (d : Layout n) (k idx : NumExpr n)
    (odd b : Bool) (env : Env n) :
    (d.cellBase k idx odd b).eval env =
      Index.columnBase (d.W.eval env) (d.M.eval env) (d.Q.eval env) (k.eval env) odd b+
        (if b then 4 else 2)+(d.W.eval env-1-idx.eval env)*(if b then 48 else 20) := by
  simp only [Layout.cellBase,NumExpr.eval,addN,mulN,revE,Layout.columnBase_eval,Nat.mul_comm]

theorem Layout.endBase_eval {n : Nat} (d : Layout n) (k : NumExpr n)
    (odd b : Bool) (env : Env n) :
    (d.endBase k odd b).eval env =
      Index.columnBase (d.W.eval env) (d.M.eval env) (d.Q.eval env) (k.eval env) odd b+
        (if b then 4 else 2)+d.W.eval env*(if b then 48 else 20) := by
  simp only [Layout.endBase,NumExpr.eval,addN,mulN,Layout.columnBase_eval,Nat.mul_comm]

theorem Layout.rainbowBase_eval {n : Nat} (d : Layout n) (k v : NumExpr n)
    (odd b : Bool) (env : Env n) :
    (d.rainbowBase k v odd b).eval env =
      Index.rainbowBase (d.W.eval env) (d.M.eval env) (d.Q.eval env) (k.eval env) (v.eval env) odd b := by
  cases odd <;> simp only [Layout.rainbowBase,Index.rainbowBase,↓reduceIte,
    Bool.false_eq_true,NumExpr.eval,mulN,revE,subN,Layout.columnSize_eval,Nat.mul_comm]

theorem Layout.formulaLength_eval {n : Nat} (d : Layout n) (env : Env n)
    (bits : Nat → Nat → Bool×Bool)
    (hq : 2*(d.Q.eval env)=d.M.eval env ∨ 2*(d.Q.eval env)=d.M.eval env+1) :
    d.formulaLength.eval env=(gridCNF (d.W.eval env) (d.M.eval env) bits).length := by
  have h := Index.grid_size false (d.W.eval env) (d.M.eval env) (d.Q.eval env) bits hq
  simp only [Index.size,Bool.false_eq_true,↓reduceIte] at h
  rw [h]
  simp only [Layout.formulaLength,NumExpr.eval,mulN,subN,Layout.columnSize_eval,
    Nat.mul_comm,Nat.mul_left_comm]

theorem Layout.columnLive_eval {n : Nat} (d : Layout n) (k : NumExpr n)
    (odd : Bool) (w : SAT.Word) (env : Env n) :
    (d.columnLive k odd).eval w env = true ↔ 2*k.eval env+(if odd then 2 else 1)≤d.M.eval env := by
  change decide _ = true ↔ _
  exact ⟨of_decide_eq_true,fun h => decide_eq_true h⟩

theorem Layout.cellLive_eval {n : Nat} (d : Layout n) (k idx : NumExpr n)
    (odd : Bool) (w : SAT.Word) (env : Env n) :
    (d.cellLive k idx odd).eval w env = true ↔
      2*k.eval env+(if odd then 2 else 1)≤d.M.eval env ∧ idx.eval env<d.W.eval env := by
  simp only [Layout.cellLive,Test.eval,Bool.and_eq_true,Layout.columnLive_eval,addN,
    NumExpr.eval,decide_eq_true_eq,Nat.add_one_le_iff]

theorem Layout.rainbowLive_eval {n : Nat} (d : Layout n) (k v : NumExpr n)
    (odd : Bool) (w : SAT.Word) (env : Env n) :
    (d.rainbowLive k v odd).eval w env = true ↔
      2*k.eval env+(if odd then 3 else 2)≤d.M.eval env ∧ v.eval env<d.W.eval env := by
  cases odd <;> simp [Layout.rainbowLive,Test.eval,twoE,addN,
    NumExpr.eval,Nat.add_one_le_iff]

theorem Layout.cell_block {n : Nat} (d : Layout n) (k idx : NumExpr n)
    (odd : Bool) (w : SAT.Word) (env : Env n) (bits : Nat → Nat → Bool×Bool)
    (hq : 2*(d.Q.eval env)=d.M.eval env ∨ 2*(d.Q.eval env)=d.M.eval env+1)
    (hlive : (d.cellLive k idx odd).eval w env = true) :
    Index.BlockAt (gridCNF (d.W.eval env) (d.M.eval env) bits)
      (cellCNF (d.W.eval env) (2*k.eval env+(if odd then 1 else 0)) (idx.eval env) odd
        (bits (2*k.eval env+(if odd then 1 else 0)) (row (d.W.eval env) odd (idx.eval env))))
      (fun b => (d.cellBase k idx odd b).eval env) := by
  obtain ⟨hc,hi⟩ := (d.cellLive_eval k idx odd w env).mp hlive
  simpa only [Layout.cellBase_eval] using
    Index.grid_cell_block _ _ _ _ _ odd bits hq hc hi

theorem Layout.start_block {n : Nat} (d : Layout n) (k : NumExpr n)
    (odd : Bool) (w : SAT.Word) (env : Env n) (bits : Nat → Nat → Bool×Bool)
    (hq : 2*(d.Q.eval env)=d.M.eval env ∨ 2*(d.Q.eval env)=d.M.eval env+1)
    (hlive : (d.columnLive k odd).eval w env = true) :
    Index.BlockAt (gridCNF (d.W.eval env) (d.M.eval env) bits)
      (startG (d.W.eval env) (2*k.eval env+(if odd then 1 else 0)))
      (fun b => (d.columnBase k odd b).eval env) := by
  simpa only [Layout.columnBase_eval] using
    Index.grid_start_block _ _ _ _ odd bits hq ((d.columnLive_eval k odd w env).mp hlive)

theorem Layout.end_block {n : Nat} (d : Layout n) (k : NumExpr n)
    (odd : Bool) (w : SAT.Word) (env : Env n) (bits : Nat → Nat → Bool×Bool)
    (hq : 2*(d.Q.eval env)=d.M.eval env ∨ 2*(d.Q.eval env)=d.M.eval env+1)
    (hlive : (d.columnLive k odd).eval w env = true) :
    Index.BlockAt (gridCNF (d.W.eval env) (d.M.eval env) bits)
      (endG (d.W.eval env) (2*k.eval env+(if odd then 1 else 0)))
      (fun b => (d.endBase k odd b).eval env) := by
  simpa only [Layout.endBase_eval] using
    Index.grid_end_block _ _ _ _ odd bits hq ((d.columnLive_eval k odd w env).mp hlive)

theorem Layout.rainbow_block {n : Nat} (d : Layout n) (k v : NumExpr n)
    (odd : Bool) (w : SAT.Word) (env : Env n) (bits : Nat → Nat → Bool×Bool)
    (hq : 2*(d.Q.eval env)=d.M.eval env ∨ 2*(d.Q.eval env)=d.M.eval env+1)
    (hlive : (d.rainbowLive k v odd).eval w env = true) :
    Index.BlockAt (gridCNF (d.W.eval env) (d.M.eval env) bits)
      ((if odd then rbOdd else rbEven) (d.W.eval env)
        (2*k.eval env+(if odd then 1 else 0)) (v.eval env))
      (fun b => (d.rainbowBase k v odd b).eval env) := by
  obtain ⟨hc,hv⟩ := (d.rainbowLive_eval k v odd w env).mp hlive
  simpa only [Layout.rainbowBase_eval] using
    Index.grid_rainbow_block _ _ _ _ _ odd bits hq hc hv

end STACS2027.PlanarSource.Packed

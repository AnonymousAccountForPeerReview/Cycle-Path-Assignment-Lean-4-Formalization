module

public import NPHardness.SourceGrid

/-! Explicit bounded-loop implementation of every implication wheel. -/

@[expose] public section
namespace STACS2027
open Complexity.SAT Complexity.ThreeSAT Complexity.StackTableauEmitter

def gridPair (next base : Nat) : CNF :=
  [[pos base,pos (base+1)],[neg (base+1),neg next]]

def gridSegment (first base : Nat) : Nat → CNF
  | 0 => []
  | n+1 => gridPair (if n = 0 then first else base+2) base ++ gridSegment first (base+2) n

theorem sourceGrid_chain (v first base n : Nat) :
    sourceChain (⟨v,true⟩,base)
      ((⟨v,false⟩,base+1) :: (sourceGridFrom v (base+2) n ++ [(⟨v,true⟩,first)])) =
      gridSegment first base (n+1) := by
  induction n generalizing base with
  | zero => rfl
  | succ n ih =>
    simp only [sourceGridFrom,List.cons_append,sourceChain,sourceImplication,
      Bool.not_true,Bool.not_false]
    change _ = gridPair (if n+1 = 0 then first else base+2) base ++ gridSegment first (base+2) (n+1)
    rw [ite_eq_right (by omega),← ih]
    rfl

theorem sourceWheel_gridFrom (v base n : Nat) :
    sourceWheel (sourceGridFrom v base n) = gridSegment base base n := by
  cases n with
  | zero => rfl
  | succ n => exact sourceGrid_chain v base base n

def gridAt (first base n j : Nat) : CNF :=
  gridPair (if j+1 < n then base+2*j+2 else first) (base+2*j)

theorem gridSegment_range (first base n : Nat) :
    gridSegment first base n = (List.range n).flatMap (gridAt first base n) := by
  induction n generalizing base with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ_eq_map,List.flatMap_cons,List.flatMap_map]
    have hh : gridAt first base (n+1) 0 = gridPair (if n = 0 then first else base+2) base := by
      unfold gridAt
      by_cases hn : n = 0
      · simp [hn]
      · have hn' : 0 < n := by omega
        simp [hn,hn']
    rw [hh,gridSegment,ih]
    apply congrArg (gridPair (if n = 0 then first else base+2) base ++ ·)
    apply congrArg (List.flatMap · (List.range n))
    funext j
    unfold gridAt
    have he : (j+1)+1 < n+1 ↔ j+1 < n := by omega
    by_cases hj : j+1 < n
    · have hj' := he.mpr hj
      simp only [hj,hj',↓reduceIte]
      congr 1 <;> omega
    · have hj' : ¬ (j+1)+1 < n+1 := fun h => hj (he.mp h)
      simp only [hj,hj',↓reduceIte]
      congr 1 <;> omega

def gridWheelRows (slots v : Nat) : CNF :=
  (List.range slots).reverse.flatMap (gridAt (v*(2*slots)) (v*(2*slots)) slots)

theorem gridWheelRows_perm (slots v : Nat) :
    (gridWheelRows slots v).Perm (sourceWheel (sourceGrid slots v)) := by
  rw [sourceGrid,sourceWheel_gridFrom,gridSegment_range]
  exact List.Perm.flatMap_right _ (List.reverse_perm _)

def gridWheelFamily (V slots : Nat) : CNF :=
  (List.range V).reverse.flatMap (gridWheelRows slots)

theorem gridWheelFamily_perm (V slots : Nat) :
    (gridWheelFamily V slots).Perm (taggedWheels V (sourceGrid slots)) := by
  apply List.Perm.trans (List.Perm.flatMap_right (gridWheelRows slots) (List.reverse_perm (List.range V)))
  have h : ∀ vs : List Nat, (vs.flatMap (gridWheelRows slots)).Perm
      (vs.flatMap (fun v => sourceWheel (sourceGrid slots v))) := by
    intro vs
    induction vs with
    | nil => exact List.Perm.refl _
    | cons v vs ih => exact (gridWheelRows_perm slots v).append ih
  exact h (List.range V)

def gridPairExpr {n : Nat} (next base : NumExpr n) : ClauseProgram n :=
  .seq (.clause [⟨base,true⟩,⟨.add base (.const 1),true⟩])
    (.clause [⟨.add base (.const 1),false⟩,⟨next,false⟩])

theorem gridPairExpr_emit {n : Nat} (next base : NumExpr n) (input : Complexity.SAT.Word) (env : Env n) :
    (gridPairExpr next base).emit input env = gridPair (next.eval env) (base.eval env) := rfl

def gridWheelProgram {n : Nat} (V slots : NumExpr n) : ClauseProgram n :=
  .forDown V (.forDown slots.lift
    (let first : NumExpr (n+2) := .mul (.var 1) (.mul (.const 2) slots.lift.lift)
     let base : NumExpr (n+2) := .add first (.mul (.const 2) (.var 0))
     .ifLe (.add (.var 0) (.const 2)) slots.lift.lift
       (gridPairExpr (.add base (.const 2)) base) (gridPairExpr first base)))

theorem gridWheelProgram_emit {n : Nat} (V slots : NumExpr n) (input : Complexity.SAT.Word) (env : Env n) :
    (gridWheelProgram V slots).emit input env = gridWheelFamily (V.eval env) (slots.eval env) := by
  simp only [gridWheelProgram,ClauseProgram.emit,NumExpr.eval_lift]
  apply congrArg (List.flatMap · (List.range (V.eval env)).reverse)
  funext v
  simp only [gridWheelRows]
  apply congrArg (List.flatMap · (List.range (slots.eval env)).reverse)
  funext j
  simp only [NumExpr.eval,NumExpr.eval_lift,extend_zero,gridPairExpr_emit,gridAt]
  have hev : extend j (extend v env) (1 : Fin (n+2)) = v := rfl
  rw [hev]
  by_cases h : j+1 < slots.eval env
  · have hh : j+2 ≤ slots.eval env := by omega
    simp [h,hh]
  · have hh : ¬ j+2 ≤ slots.eval env := by omega
    simp [h,hh]

end STACS2027

module

public import NPHardness.PlanarSourcePackedSemantics
public import NPHardness.PlanarSourceRotationTableGeometry
public import NPHardness.PlanarSourcePackedIndex

/-! Exact copied-source semantics for the packed block and counted column
emitters.  All offsets are justified from source literal counts. -/

@[expose] public section
namespace STACS2027.PlanarSource.Packed
open Complexity Complexity.SAT Complexity.StackTableauEmitter Complexity.Planar.Grid
open Complexity.Planar.Emit

theorem cell_literals (W j idx : Nat) (odd : Bool) (b : Bool × Bool) :
    (cellCNF W j idx odd b).flatten.length = 48 := by
  have h := congrArg List.length (RotationTable.cell_variables W j idx odd b.1 b.2)
  simpa only [List.length_map, RotationTable.cellPositions_length] using h

theorem reverse_blocks_literals {α : Type} (F : α → CNF) (xs : List α) (size : Nat)
    (hs : ∀ x ∈ xs, (F x).flatten.length = size) :
    (xs.flatMap F).flatten.length = xs.length*size := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.flatMap_cons, List.flatten_append, List.length_append,
        hs x (by simp), ih (fun y hy => hs y (by simp [hy])), List.length_cons,
        Nat.add_mul, Nat.one_mul]
      omega

theorem column_literals (W j : Nat) (odd : Bool) (bits : Nat → Nat → Bool × Bool) :
    (column W j odd bits).flatten.length = 48*W+8 := by
  have h := reverse_blocks_literals
    (fun idx => cellCNF W j idx odd (bits j (row W odd idx)))
    (List.range W).reverse 48 (by intro idx hi; exact cell_literals _ _ _ _ _)
  simp only [List.length_reverse, List.length_range] at h
  simp only [column, List.flatten_append, List.length_append, h]
  have hs : (startG W j).flatten.length = 4 := rfl
  have he : (endG W j).flatten.length = 4 := rfl
  rw [hs,he]
  omega

theorem startProgram_copies {n : Nat} (d : Layout n) (k : NumExpr n) (odd : Bool)
    (w : SAT.Word) (env : Env n) :
    (d.startProgram k odd false).emit w env = copiesAt ((d.columnBase k odd true).eval env)
      (startG (d.W.eval env) (2*k.eval env+(if odd then 1 else 0))) := by
  simp only [Layout.startProgram, Bool.false_eq_true, ite_false, copyBlock_emit,
    startTemplates_eval, twoE, NumExpr.eval]

theorem endProgram_copies {n : Nat} (d : Layout n) (k : NumExpr n) (odd : Bool)
    (w : SAT.Word) (env : Env n) :
    (d.endProgram k odd false).emit w env = copiesAt ((d.endBase k odd true).eval env)
      (endG (d.W.eval env) (2*k.eval env+(if odd then 1 else 0))) := by
  simp only [Layout.endProgram, Bool.false_eq_true, ite_false, copyBlock_emit,
    endTemplates_eval, twoE, NumExpr.eval]

theorem rainbowProgram_copies {n : Nat} (d : Layout n) (k v : NumExpr n) (odd : Bool)
    (w : SAT.Word) (env : Env n) :
    (d.rainbowProgram k v odd false).emit w env = copiesAt ((d.rainbowBase k v odd true).eval env)
      (if odd then rbOdd (d.W.eval env) (2*k.eval env+1) (v.eval env)
       else rbEven (d.W.eval env) (2*k.eval env) (v.eval env)) := by
  cases odd <;>
    simp [Layout.rainbowProgram, copyBlock_emit, rainbowTemplates_eval, twoE, NumExpr.eval]

theorem columnProgram_copies {n : Nat} (d : Layout n) (k : NumExpr n) (odd : Bool)
    (w : SAT.Word) (env : Env n) :
    (d.columnProgram k odd false).emit w env = copiesAt ((d.columnBase k odd true).eval env)
      (column (d.W.eval env) (2*k.eval env+(if odd then 1 else 0)) odd
        (bitsW w (d.A.eval env) (d.M.eval env) (d.R.eval env) (d.W.eval env))) := by
  let W := d.W.eval env
  let j := 2*k.eval env+(if odd then 1 else 0)
  let bits := bitsW w (d.A.eval env) (d.M.eval env) (d.R.eval env) W
  let B := (d.columnBase k odd true).eval env
  let F := fun idx => cellCNF W j idx odd (bits j (row W odd idx))
  have hf (i : Nat) : (F i).flatten.length = 48 := cell_literals _ _ _ _ _
  have hmid : ((List.range W).reverse.flatMap F).flatten.length = W*48 := by
    simpa only [List.length_reverse, List.length_range] using
      reverse_blocks_literals F (List.range W).reverse 48 (by intro i hi; exact hf i)
  have he : (d.endBase k odd true).eval env = B+4+W*48 := by
    simp [Layout.endBase, addN, mulN, NumExpr.eval, B, W, Nat.mul_comm]
  have hc (idx : Nat) :
      (d.lift.cellProgram k.lift (.var 0) odd false).emit w (extend idx env) =
        copiesAt (B+4+(W-1-idx)*48) (F idx) := by
    rw [cellProgram_copies]
    cases odd <;> simp [Layout.lift, Layout.cellBase, Layout.columnBase, Layout.columnSize,
      addN, mulN, revE, NumExpr.eval, B, W, F, j, bits, Nat.mul_comm]
  simp only [Layout.columnProgram, ClauseProgram.emit_seq, ClauseProgram.emit_forDown,
    startProgram_copies, endProgram_copies, he]
  change copiesAt B (startG W j) ++
      ((List.range W).reverse.flatMap fun idx =>
        (d.lift.cellProgram k.lift (.var 0) odd false).emit w (extend idx env)) ++
      copiesAt (B+4+W*48) (endG W j) = _
  simp only [hc]
  rw [← copiesAt_reverse_blocks (B+4) 48 W F (fun i hi => hf i)]
  change _ = copiesAt B (startG W j ++ (List.range W).reverse.flatMap F ++ endG W j)
  rw [copiesAt_append, copiesAt_append]
  have hs : (startG W j).flatten.length = 4 := rfl
  rw [hs]
  simp only [List.flatten_append, List.length_append, hs, hmid, Nat.add_assoc]

def rowBaseValue (W m q k : Nat) (odd : Bool) : Nat :=
  m*(48*W+8) + if odd then (m-q)*(4*W)+(q-2-k)*(4*W) else (m-q-1-k)*(4*W)

theorem forDown_guard_emit {n : Nat} (bound : NumExpr n) (a b : NumExpr (n+1))
    (body : ClauseProgram (n+1)) (w : SAT.Word) (env : Env n) :
    (ClauseProgram.forDown bound (.ifLe a b body .skip)).emit w env =
      (List.range (bound.eval env)).reverse.flatMap fun i =>
        if a.eval (extend i env) ≤ b.eval (extend i env) then body.emit w (extend i env) else [] := rfl

theorem rainbowRowProgram_copies {n : Nat} (d : Layout n) (k : Nat) (odd : Bool)
    (w : SAT.Word) (env : Env n) :
    (ClauseProgram.forDown d.W.lift
      (d.lift.lift.rainbowProgram (.var 1) (.var 0) odd false)).emit w (extend k env) =
      copiesAt (rowBaseValue (d.W.eval env) (d.M.eval env) (d.Q.eval env) k odd)
        ((List.range (d.W.eval env)).reverse.flatMap
          (if odd then rbOdd (d.W.eval env) (2*k+1) else rbEven (d.W.eval env) (2*k))) := by
  let W := d.W.eval env
  let B := rowBaseValue W (d.M.eval env) (d.Q.eval env) k odd
  let F := if odd then rbOdd W (2*k+1) else rbEven W (2*k)
  have hf (i : Nat) : (F i).flatten.length = 4 := by cases odd <;> rfl
  have hc (idx : Nat) :
      (d.lift.lift.rainbowProgram (.var 1) (.var 0) odd false).emit w
        (extend idx (extend k env)) = copiesAt (B+(W-1-idx)*4) (F idx) := by
    rw [rainbowProgram_copies]
    cases odd <;> simp [Layout.lift, Layout.rainbowBase, Layout.columnSize,
      addN, mulN, subN, revE, NumExpr.eval, B, W, F, rowBaseValue, Nat.mul_comm]
  simp only [ClauseProgram.emit_forDown, NumExpr.eval_lift, hc]
  exact (copiesAt_reverse_blocks B 4 W F (fun i hi => hf i)).symm

theorem gridPhase_copies {n : Nat} (d : Layout n) (w : SAT.Word) (env : Env n)
    (hq : 2*(d.Q.eval env)=d.M.eval env ∨ 2*(d.Q.eval env)=d.M.eval env+1) :
    (d.gridPhase false).emit w env = copiesAt 0
      (gridCNF (d.W.eval env) (d.M.eval env)
        (bitsW w (d.A.eval env) (d.M.eval env) (d.R.eval env) (d.W.eval env))) := by
  let W := d.W.eval env
  let m := d.M.eval env
  let q := d.Q.eval env
  let C := 48*W+8
  let R := 4*W
  let bits := bitsW w (d.A.eval env) m (d.R.eval env) W
  let E := fun k => column W (2*k) false bits
  let O := fun k => column W (2*k+1) true bits
  let RE := fun k => (List.range W).reverse.flatMap (rbEven W (2*k))
  let RO := fun k => (List.range W).reverse.flatMap (rbOdd W (2*k+1))
  have hq' : 2*q=m ∨ 2*q=m+1 := hq
  have hc (k : Nat) (odd : Bool) :
      (d.lift.columnProgram (.var 0) odd false).emit w (extend k env) =
        copiesAt (if odd then q*C+(m-q-1-k)*C else (q-1-k)*C)
          (if odd then O k else E k) := by
    rw [columnProgram_copies]
    cases odd <;> simp [Layout.lift, Layout.columnBase, Layout.columnSize,
      revE, addN, mulN, NumExpr.eval, q, m, C, W, E, O, bits]
  have he : ∀ k, (2*k+1≤m) = (k<q) := fun k => propext (by omega)
  have ho : ∀ k, (2*k+2≤m) = (k<m-q) := fun k => propext (by omega)
  have hr : ∀ k, (2*k+3≤m) = (k<q-1) := fun k => propext (by omega)
  simp only [Layout.gridPhase, ClauseProgram.emit_seq, forDown_guard_emit,
    twoE, NumExpr.eval, NumExpr.eval_lift, extend_zero]
  change
    ((List.range m).reverse.flatMap fun k => if 2*k+1≤m then
      (d.lift.columnProgram (.var 0) false false).emit w (extend k env) else []) ++
    ((List.range m).reverse.flatMap fun k => if 2*k+2≤m then
      (d.lift.columnProgram (.var 0) true false).emit w (extend k env) else []) ++
    ((List.range m).reverse.flatMap fun k => if 2*k+2≤m then
      (ClauseProgram.forDown d.W.lift
        (d.lift.lift.rainbowProgram (.var 1) (.var 0) false false)).emit w (extend k env) else []) ++
    ((List.range m).reverse.flatMap fun k => if 2*k+3≤m then
      (ClauseProgram.forDown d.W.lift
        (d.lift.lift.rainbowProgram (.var 1) (.var 0) true false)).emit w (extend k env) else []) = _
  simp only [hc, rainbowRowProgram_copies, rowBaseValue, Bool.false_eq_true, ↓reduceIte]
  change
    ((List.range m).reverse.flatMap fun k => if 2*k+1≤m then copiesAt ((q-1-k)*C) (E k) else []) ++
    ((List.range m).reverse.flatMap fun k => if 2*k+2≤m then copiesAt (q*C+(m-q-1-k)*C) (O k) else []) ++
    ((List.range m).reverse.flatMap fun k => if 2*k+2≤m then copiesAt (m*C+(m-q-1-k)*R) (RE k) else []) ++
    ((List.range m).reverse.flatMap fun k => if 2*k+3≤m then copiesAt (m*C+((m-q)*R+(q-2-k)*R)) (RO k) else []) = _
  simp only [he,ho,hr]
  rw [Index.truncate_reverse_flatMap m q (by omega),
    Index.truncate_reverse_flatMap m (m-q) (by omega),
    Index.truncate_reverse_flatMap m (m-q) (by omega),
    Index.truncate_reverse_flatMap m (q-1) (by omega)]
  have hE (k : Nat) : (E k).flatten.length = C := column_literals _ _ _ _
  have hO (k : Nat) : (O k).flatten.length = C := column_literals _ _ _ _
  have hRE (k : Nat) : (RE k).flatten.length = R := by
    have h := Index.rainbow_row_size true W (2*k) false
    simpa [Index.size, RE, R, Nat.mul_comm] using h
  have hRO (k : Nat) : (RO k).flatten.length = R := by
    have h := Index.rainbow_row_size true W (2*k+1) true
    simpa [Index.size, RO, R, Nat.mul_comm] using h
  have hfirst := copiesAt_reverse_blocks 0 C q E (fun k hk => hE k)
  simp only [Nat.zero_add] at hfirst
  rw [← hfirst,
    ← copiesAt_reverse_blocks (q*C) C (m-q) O (fun k hk => hO k),
    ← copiesAt_reverse_blocks (m*C) R (m-q) RE (fun k hk => hRE k)]
  have hlast (k : Nat) : m*C+((m-q)*R+(q-2-k)*R) =
      (m*C+(m-q)*R)+((q-1)-1-k)*R := by
    rw [show q-1-1=q-2 by omega]
    omega
  simp only [hlast]
  rw [← copiesAt_reverse_blocks (m*C+(m-q)*R) R (q-1) RO (fun k hk => hRO k)]
  have hlenE : ((List.range q).reverse.flatMap E).flatten.length = q*C := by
    simpa using reverse_blocks_literals E (List.range q).reverse C (fun k hk => hE k)
  have hlenO : ((List.range (m-q)).reverse.flatMap O).flatten.length = (m-q)*C := by
    simpa using reverse_blocks_literals O (List.range (m-q)).reverse C (fun k hk => hO k)
  have hlenRE : ((List.range (m-q)).reverse.flatMap RE).flatten.length = (m-q)*R := by
    simpa using reverse_blocks_literals RE (List.range (m-q)).reverse R (fun k hk => hRE k)
  rw [Index.grid_blocks W m q bits hq']
  change _ = copiesAt 0 (((List.range q).reverse.flatMap E) ++
    ((List.range (m-q)).reverse.flatMap O) ++
    ((List.range (m-q)).reverse.flatMap RE) ++ ((List.range (q-1)).reverse.flatMap RO))
  simp only [copiesAt_append, List.flatten_append, List.length_append,
    hlenE,hlenO,hlenRE,Nat.zero_add]
  have hm : q*C+(m-q)*C=m*C := by rw [← Nat.add_mul]; congr 1; omega
  rw [hm]

end STACS2027.PlanarSource.Packed

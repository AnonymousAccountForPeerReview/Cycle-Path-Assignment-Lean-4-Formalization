module

public import NPHardness.PlanarSourceGraphCopyLocal

/-! Exact graph records for the complete counted copied-source phase. -/

@[expose] public section
namespace STACS2027.PlanarSource.Packed
open Complexity Complexity.SAT Complexity.StackTableauEmitter Complexity.Planar Grid
open Complexity.Planar.Emit

theorem Layout.columnGraphProgram_copies {n : Nat} (d : Layout n) (length : Nat)
    (k : NumExpr n) (odd : Bool) (w : SAT.Word) (env : Env n)
    (hq : 2*d.Q.eval env=d.M.eval env ∨ 2*d.Q.eval env=d.M.eval env+1)
    (hk : 2*k.eval env+(if odd then 2 else 1)≤d.M.eval env) :
    (d.columnGraphProgram length k odd false).emit w env =
      copyGraphAt (sourceEndpointChoices (Formula.sourceSigns (d.source w env))) length
        (d.occurrenceCount.eval env) ((d.columnBase k odd false).eval env)
        ((d.columnBase k odd true).eval env)
        (column (d.W.eval env) (2*k.eval env+(if odd then 1 else 0)) odd (d.bits w env)) := by
  rw [copyGraphAt_column]
  simp only [Layout.columnGraphProgram,ClauseProgram.emit_seq,ClauseProgram.emit_forDown,
    d.startGraphProgram_copies length k odd w env hq hk,
    d.endGraphProgram_copies length k odd w env hq hk]
  have he (b : Bool) : (d.endBase k odd b).eval env =
      (d.columnBase k odd b).eval env+(if b then 4 else 2)+d.W.eval env*(if b then 48 else 20) := by
    cases b <;> simp [Layout.endBase,addN,mulN,NumExpr.eval,Nat.mul_comm]
  rw [he false,he true]
  congr 2
  apply flatMap_congr_range
  intro idx hi
  have hq' : 2*d.lift.Q.eval (extend idx env)=d.lift.M.eval (extend idx env) ∨
      2*d.lift.Q.eval (extend idx env)=d.lift.M.eval (extend idx env)+1 := by
    simpa only [Layout.lift,NumExpr.eval_lift] using hq
  have hk' : 2*k.lift.eval (extend idx env)+(if odd then 2 else 1)≤d.lift.M.eval (extend idx env) := by
    simpa only [Layout.lift,NumExpr.eval_lift] using hk
  rw [d.lift.cellGraphProgram_copies length k.lift (.var 0) odd w (extend idx env) hq' hk'
    (by simpa only [NumExpr.eval,extend_zero,Layout.lift,NumExpr.eval_lift] using hi)]
  simp only [Layout.source_lift,Layout.occurrenceCount_lift_eval]
  cases odd <;> simp [Layout.lift,Layout.cellBase,Layout.columnBase,Layout.columnSize,
    Layout.bits,addN,mulN,revE,NumExpr.eval,Nat.mul_comm]

def clauseRowBaseValue (W m q k : Nat) (odd : Bool) : Nat :=
  m*(20*W+4) + if odd then (m-q)*(2*W)+(q-2-k)*(2*W) else (m-q-1-k)*(2*W)

theorem Layout.rainbowRowGraphProgram_copies {n : Nat} (d : Layout n) (length k : Nat)
    (odd : Bool) (w : SAT.Word) (env : Env n)
    (hq : 2*d.Q.eval env=d.M.eval env ∨ 2*d.Q.eval env=d.M.eval env+1)
    (hk : 2*k+(if odd then 3 else 2)≤d.M.eval env) :
    (ClauseProgram.forDown d.W.lift
      (d.lift.lift.rainbowGraphProgram length (.var 1) (.var 0) odd false)).emit w (extend k env) =
      copyGraphAt (sourceEndpointChoices (Formula.sourceSigns (d.source w env))) length
        (d.occurrenceCount.eval env)
        (clauseRowBaseValue (d.W.eval env) (d.M.eval env) (d.Q.eval env) k odd)
        (rowBaseValue (d.W.eval env) (d.M.eval env) (d.Q.eval env) k odd)
        ((List.range (d.W.eval env)).reverse.flatMap
          (if odd then rbOdd (d.W.eval env) (2*k+1) else rbEven (d.W.eval env) (2*k))) := by
  have ht : (if odd then rbOdd (d.W.eval env) (2*k+1) else rbEven (d.W.eval env) (2*k)) =
      (if odd then rbOdd (d.W.eval env) (2*k+(if odd then 1 else 0))
       else rbEven (d.W.eval env) (2*k+(if odd then 1 else 0))) := by cases odd <;> rfl
  rw [ht,copyGraphAt_rainbowRow]
  simp only [ClauseProgram.emit_forDown,NumExpr.eval_lift]
  apply flatMap_congr_range
  intro idx hi
  rw [d.lift.lift.rainbowGraphProgram_copies length (.var 1) (.var 0) odd w
    (extend idx (extend k env))
    (by simpa only [Layout.lift,NumExpr.eval_lift] using hq)
    (by simpa [Layout.lift,NumExpr.eval_lift,NumExpr.eval] using hk)
    (by simpa only [Layout.lift,NumExpr.eval_lift,NumExpr.eval,extend_zero] using hi)]
  simp only [Layout.source_lift,Layout.occurrenceCount_lift_eval]
  cases odd <;> simp [Layout.lift,Layout.rainbowBase,Layout.columnSize,clauseRowBaseValue,rowBaseValue,
    addN,mulN,subN,revE,NumExpr.eval,Nat.mul_comm]

set_option maxHeartbeats 400000 in
theorem Layout.graphPhase_copies {n : Nat} (d : Layout n) (length : Nat)
    (w : SAT.Word) (env : Env n)
    (hq : 2*d.Q.eval env=d.M.eval env ∨ 2*d.Q.eval env=d.M.eval env+1) :
    (d.graphPhase length false).emit w env =
      copyGraphAt (sourceEndpointChoices (Formula.sourceSigns (d.source w env))) length
        (d.occurrenceCount.eval env) 0 0 (d.source w env) := by
  let W := d.W.eval env
  let m := d.M.eval env
  let q := d.Q.eval env
  let C := 20*W+4
  let L := 48*W+8
  let R := 2*W
  let S := 4*W
  let bits := d.bits w env
  let E := fun k => column W (2*k) false bits
  let O := fun k => column W (2*k+1) true bits
  let RE := fun k => (List.range W).reverse.flatMap (rbEven W (2*k))
  let RO := fun k => (List.range W).reverse.flatMap (rbOdd W (2*k+1))
  let G := copyGraphAt (sourceEndpointChoices (Formula.sourceSigns (d.source w env))) length
    (d.occurrenceCount.eval env)
  have hq' : 2*q=m ∨ 2*q=m+1 := hq
  have hc (k : Nat) (odd : Bool) (hk : 2*k+(if odd then 2 else 1)≤m) :
      (d.lift.columnGraphProgram length (.var 0) odd false).emit w (extend k env) =
        G (if odd then q*C+(m-q-1-k)*C else (q-1-k)*C)
          (if odd then q*L+(m-q-1-k)*L else (q-1-k)*L)
          (if odd then O k else E k) := by
    rw [d.lift.columnGraphProgram_copies length (.var 0) odd w (extend k env)
      (by simpa only [Layout.lift,NumExpr.eval_lift] using hq)
      (by simpa only [Layout.lift,NumExpr.eval_lift,NumExpr.eval,extend_zero] using hk)]
    simp only [Layout.source_lift,Layout.occurrenceCount_lift_eval]
    cases odd <;> simp [G,Layout.lift,Layout.columnBase,Layout.columnSize,
      Layout.bits,revE,addN,mulN,NumExpr.eval,q,m,C,L,W,E,O,bits]
  have hr (k : Nat) (odd : Bool) (hk : 2*k+(if odd then 3 else 2)≤m) :
      (ClauseProgram.forDown d.W.lift
        (d.lift.lift.rainbowGraphProgram length (.var 1) (.var 0) odd false)).emit w (extend k env) =
        G (m*C+(if odd then (m-q)*R+(q-2-k)*R else (m-q-1-k)*R))
          (m*L+(if odd then (m-q)*S+(q-2-k)*S else (m-q-1-k)*S))
          (if odd then RO k else RE k) := by
    rw [d.rainbowRowGraphProgram_copies length k odd w env hq hk]
    cases odd <;> rfl
  have hphase : (d.graphPhase length false).emit w env =
      ((List.range m).reverse.flatMap fun k => if 2*k+1≤m then G ((q-1-k)*C) ((q-1-k)*L) (E k) else []) ++
      ((List.range m).reverse.flatMap fun k => if 2*k+2≤m then G (q*C+(m-q-1-k)*C) (q*L+(m-q-1-k)*L) (O k) else []) ++
      ((List.range m).reverse.flatMap fun k => if 2*k+2≤m then G (m*C+(m-q-1-k)*R) (m*L+(m-q-1-k)*S) (RE k) else []) ++
      ((List.range m).reverse.flatMap fun k => if 2*k+3≤m then G (m*C+((m-q)*R+(q-2-k)*R)) (m*L+((m-q)*S+(q-2-k)*S)) (RO k) else []) := by
    simp only [Layout.graphPhase,ClauseProgram.emit_seq,forDown_guard_emit,
      twoE,NumExpr.eval,NumExpr.eval_lift,extend_zero]
    have happend {a b c d : CNF} (ha : a=c) (hb : b=d) : a++b=c++d := by rw [ha,hb]
    refine happend (happend (happend ?_ ?_) ?_) ?_
    · apply flatMap_congr_range
      intro k hk
      by_cases hl : 2*k+1≤d.M.eval env
      · simp only [m,ite_eq_left hl]
        exact hc k false hl
      · simp only [m,ite_eq_right hl]
    · apply flatMap_congr_range
      intro k hk
      by_cases hl : 2*k+2≤d.M.eval env
      · simp only [m,ite_eq_left hl]
        exact hc k true hl
      · simp only [m,ite_eq_right hl]
    · apply flatMap_congr_range
      intro k hk
      by_cases hl : 2*k+2≤d.M.eval env
      · simp only [m,ite_eq_left hl]
        exact hr k false hl
      · simp only [m,ite_eq_right hl]
    · apply flatMap_congr_range
      intro k hk
      by_cases hl : 2*k+3≤d.M.eval env
      · simp only [m,ite_eq_left hl]
        exact hr k true hl
      · simp only [m,ite_eq_right hl]
  rw [hphase]
  have he : ∀ k, (2*k+1≤m) = (k<q) := fun k => propext (by omega)
  have ho : ∀ k, (2*k+2≤m) = (k<m-q) := fun k => propext (by omega)
  have hrr : ∀ k, (2*k+3≤m) = (k<q-1) := fun k => propext (by omega)
  simp only [he,ho,hrr]
  rw [Index.truncate_reverse_flatMap m q (by omega),
    Index.truncate_reverse_flatMap m (m-q) (by omega),
    Index.truncate_reverse_flatMap m (m-q) (by omega),
    Index.truncate_reverse_flatMap m (q-1) (by omega)]
  have hE (k : Nat) : (E k).length=C := Index.column_size false W (2*k) false bits
  have hO (k : Nat) : (O k).length=C := Index.column_size false W (2*k+1) true bits
  have hEL (k : Nat) : (E k).flatten.length=L := column_literals _ _ _ _
  have hOL (k : Nat) : (O k).flatten.length=L := column_literals _ _ _ _
  have hRE (k : Nat) : (RE k).length=R := by
    have h := Index.rainbow_row_size false W (2*k) false
    simpa [Index.size,RE,R,Nat.mul_comm] using h
  have hRO (k : Nat) : (RO k).length=R := by
    have h := Index.rainbow_row_size false W (2*k+1) true
    simpa [Index.size,RO,R,Nat.mul_comm] using h
  have hREL (k : Nat) : (RE k).flatten.length=S := by
    have h := Index.rainbow_row_size true W (2*k) false
    simpa [Index.size,RE,S,Nat.mul_comm] using h
  have hROL (k : Nat) : (RO k).flatten.length=S := by
    have h := Index.rainbow_row_size true W (2*k+1) true
    simpa [Index.size,RO,S,Nat.mul_comm] using h
  have hblocks (cb lb clauses literals count : Nat) (F : Nat→CNF)
      (hcs : ∀i,i<count→(F i).length=clauses) (hls : ∀i,i<count→(F i).flatten.length=literals) :
      G cb lb ((List.range count).reverse.flatMap F)=
        (List.range count).reverse.flatMap (fun i => G (cb+(count-1-i)*clauses) (lb+(count-1-i)*literals) (F i)) :=
    copyGraphAt_reverse_blocks _ _ _ cb lb clauses literals count F hcs hls
  have hfirst := hblocks 0 0 C L q E (fun i _ => hE i) (fun i _ => hEL i)
  simp only [Nat.zero_add] at hfirst
  rw [←hfirst,←hblocks (q*C) (q*L) C L (m-q) O (fun i _ => hO i) (fun i _ => hOL i),
    ←hblocks (m*C) (m*L) R S (m-q) RE (fun i _ => hRE i) (fun i _ => hREL i)]
  have hlast (k a b : Nat) : a+((m-q)*b+(q-2-k)*b)=(a+(m-q)*b)+((q-1)-1-k)*b := by
    rw [show q-1-1=q-2 by omega]
    omega
  simp only [hlast]
  rw [←hblocks (m*C+(m-q)*R) (m*L+(m-q)*S) R S (q-1) RO (fun i _ => hRO i) (fun i _ => hROL i)]
  have hlenE : ((List.range q).reverse.flatMap E).length=q*C := by
    simpa [Index.size] using Index.size_flatMap_const false (List.range q).reverse E C (fun i _ => hE i)
  have hlenEL : ((List.range q).reverse.flatMap E).flatten.length=q*L := by
    simpa using reverse_blocks_literals E (List.range q).reverse L (fun i _ => hEL i)
  have hlenO : ((List.range (m-q)).reverse.flatMap O).length=(m-q)*C := by
    simpa [Index.size] using Index.size_flatMap_const false (List.range (m-q)).reverse O C (fun i _ => hO i)
  have hlenOL : ((List.range (m-q)).reverse.flatMap O).flatten.length=(m-q)*L := by
    simpa using reverse_blocks_literals O (List.range (m-q)).reverse L (fun i _ => hOL i)
  have hlenRE : ((List.range (m-q)).reverse.flatMap RE).length=(m-q)*R := by
    simpa [Index.size] using Index.size_flatMap_const false (List.range (m-q)).reverse RE R (fun i _ => hRE i)
  have hlenREL : ((List.range (m-q)).reverse.flatMap RE).flatten.length=(m-q)*S := by
    simpa using reverse_blocks_literals RE (List.range (m-q)).reverse S (fun i _ => hREL i)
  change _ = G 0 0 (gridCNF W m bits)
  rw [Index.grid_blocks W m q bits hq']
  change _ = G 0 0 (((List.range q).reverse.flatMap E) ++
    ((List.range (m-q)).reverse.flatMap O) ++
    ((List.range (m-q)).reverse.flatMap RE) ++ ((List.range (q-1)).reverse.flatMap RO))
  dsimp only [G]
  simp only [copyGraphAt_append,List.flatten_append,List.length_append,
    hlenE,hlenEL,hlenO,hlenOL,hlenRE,hlenREL,Nat.zero_add]
  have hm (a : Nat) : q*a+(m-q)*a=m*a := by rw [←Nat.add_mul]; congr 1; omega
  rw [hm C,hm L]

end STACS2027.PlanarSource.Packed

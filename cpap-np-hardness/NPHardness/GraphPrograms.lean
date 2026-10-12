module

public import NPHardness.GraphEncoding
public import NPHardness.GridProperties

/-! Graph serialization programs in the existing, machine-compiled emitter
language. The edge list of each fixed-k gadget is static program data. -/

@[expose] public section
namespace STACS2027
open Complexity.SAT Complexity.StackTableauEmitter

def edgeProgram {n : Nat} (u v : NumExpr n) : ClauseProgram n :=
  .ifLe u v (.clause [⟨u,true⟩,⟨v,true⟩]) (.clause [⟨v,true⟩,⟨u,true⟩])

theorem edgeProgram_emit {n : Nat} (u v : NumExpr n) (input : Complexity.SAT.Word) (env : Env n) :
    (edgeProgram u v).emit input env = [graphRecord (edge (u.eval env) (v.eval env))] := by
  unfold edgeProgram ClauseProgram.emit
  by_cases h : u.eval env ≤ v.eval env
  · simp [h,graphRecord,edge,Nat.min_eq_left h,Nat.max_eq_right h,LiteralExpr.eval]
  · have h' : v.eval env ≤ u.eval env := by omega
    simp [h,graphRecord,edge,Nat.min_eq_right h',Nat.max_eq_left h',LiteralExpr.eval]

def graphProgram {n : Nat} (t : Nat → NumExpr n) : Graph → ClauseProgram n
  | [] => .skip
  | e :: g => .seq (edgeProgram (t e.1) (t e.2)) (graphProgram t g)

theorem graphProgram_emit {n : Nat} (t : Nat → NumExpr n) (g : Graph)
    (input : Complexity.SAT.Word) (env : Env n) :
    (graphProgram t g).emit input env = graphRecords (mapGraph (fun x => (t x).eval env) g) := by
  induction g with
  | nil => rfl
  | cons e g ih => simp only [graphProgram,ClauseProgram.emit,edgeProgram_emit,ih]; rfl

def variableGraphProgram {n : Nat} (k : Nat) (V : NumExpr n) : ClauseProgram n :=
  .forDown V (graphProgram (fun v => .add (.mul (.var 0) (.const (gadgetWidth k))) (.const v)) (variableGraph k))

theorem variableGraphProgram_emit {n : Nat} (k : Nat) (V : NumExpr n)
    (input : Complexity.SAT.Word) (env : Env n) :
    (variableGraphProgram k V).emit input env =
      graphRecords ((List.range (V.eval env)).reverse.flatMap (placedVariableGraph k)) := by
  simp only [variableGraphProgram,ClauseProgram.emit,graphProgram_emit,graphRecords,List.map_flatMap]
  apply congrArg (List.flatMap · (List.range (V.eval env)).reverse)
  funext v
  rfl

def clauseVertexExpr {n : Nat} (k : Nat) (V slot : NumExpr n)
    (r : Nat) (ls : List (LiteralExpr n)) (v : Nat) : NumExpr n :=
  match (clausePortAt v).bind (fun ib => (ls[ib.1]?).map (fun l => (l,ib.2))) with
  | some (l,side) => .add (.mul l.index (.const (gadgetWidth k)))
      (.const (variableEndpoint (if l.positive then 0 else r+1) side))
  | none => .add (.mul (.add V slot) (.const (gadgetWidth k))) (.const v)

theorem clauseVertexExpr_eval {n : Nat} (k : Nat) (V slot : NumExpr n)
    (r : Nat) (ls : List (LiteralExpr n)) (v : Nat) (env : Env n) :
    (clauseVertexExpr k V slot r ls v).eval env =
      clauseVertex (gadgetWidth k) (V.eval env) (slot.eval env)
        (ls.map (fun l => PlacedLiteral.mk (l.eval env) r)) v := by
  unfold clauseVertexExpr clauseVertex attachmentAt
  cases h : clausePortAt v with
  | none => simp [NumExpr.eval,blockVertex]
  | some ib =>
    cases hl : ls[ib.1]? with
    | none => simp [hl,List.getElem?_map,NumExpr.eval,blockVertex]
    | some l => simp [hl,List.getElem?_map,NumExpr.eval,blockVertex,PlacedLiteral.port,LiteralExpr.eval]

def clauseGraphProgram {n : Nat} (k : Nat) (V slot : NumExpr n)
    (r : Nat) (ls : List (LiteralExpr n)) : ClauseProgram n :=
  .seq (.clause []) (graphProgram (clauseVertexExpr k V slot r ls)
    (if ls.length = 2 then clauseTwoGraph k else clauseThreeGraph k))

theorem clauseGraphProgram_emit {n : Nat} (k : Nat) (V slot : NumExpr n)
    (r : Nat) (ls : List (LiteralExpr n)) (input : Complexity.SAT.Word) (env : Env n) :
    (clauseGraphProgram k V slot r ls).emit input env =
      clauseGraphRecords k (V.eval env) (slot.eval env) r (ls.map (fun l => l.eval env)) := by
  simp only [clauseGraphProgram,ClauseProgram.emit,graphProgram_emit,clauseVertexExpr_eval,
    clauseGraphRecords,placedClauseGraph,clauseGraph,List.map_map,List.length_map,Function.comp_def]
  rfl

def transformParameterized
    (replace : {n : Nat} → List (LiteralExpr n) → NumExpr n → NumExpr n → ClauseProgram n) :
    {n : Nat} → ClauseProgram n → NumExpr n → NumExpr n → NumExpr n → ClauseProgram n
  | _, .clause ls, _, base, R => replace ls R base
  | _, .seq p q, C, base, R => .seq
      (transformParameterized replace p C (.add base (emitterSlotsExpr q C)) R)
      (transformParameterized replace q C base R)
  | _, .forDown bound p, C, base, R => .forDown bound
      (transformParameterized replace p C.lift
        (.add base.lift (.mul (.var 0) (emitterSlotsExpr p C.lift))) R.lift)
  | _, .ifLe l r p q, C, base, R => .ifLe l r
      (transformParameterized replace p C base R) (transformParameterized replace q C base R)
  | _, .ifInput i p q r, C, base, R => .ifInput i
      (transformParameterized replace p C base R) (transformParameterized replace q C base R)
      (transformParameterized replace r C base R)

theorem transformParameterized_emit
    (replace : {n : Nat} → List (LiteralExpr n) → NumExpr n → NumExpr n → ClauseProgram n)
    (sem : Nat → Nat → Clause → CNF)
    (hreplace : ∀ {n} (ls : List (LiteralExpr n)) (R base : NumExpr n) (input : Complexity.SAT.Word) (env : Env n),
      (replace ls R base).emit input env = sem (R.eval env) (base.eval env) (ls.map (fun l => l.eval env)))
    {n : Nat} (p : ClauseProgram n) (C base R : NumExpr n) (input : Complexity.SAT.Word) (env : Env n) :
    (transformParameterized replace p C base R).emit input env =
      (allocatedEmit p input env (C.eval env) (base.eval env)).flatMap
        (fun x => sem (R.eval env) x.1 x.2) := by
  induction p with
  | clause ls => simp [transformParameterized,allocatedEmit,hreplace]
  | seq p q ihp ihq =>
    simp only [transformParameterized,ClauseProgram.emit,ihp,ihq,allocatedEmit,List.flatMap_append,
      NumExpr.eval,emitterSlotsExpr_eval]
  | forDown bound p ih =>
    simp only [transformParameterized,ClauseProgram.emit,allocatedEmit,List.flatMap_assoc]
    apply congrArg (List.flatMap · (List.range (bound.eval env)).reverse)
    funext i
    simpa only [NumExpr.eval,NumExpr.eval_lift,extend_zero,emitterSlotsExpr_eval] using
      ih C.lift (.add base.lift (.mul (.var 0) (emitterSlotsExpr p C.lift))) R.lift (extend i env)
  | ifLe l r p q ihp ihq =>
    simp only [transformParameterized,ClauseProgram.emit,allocatedEmit]
    split <;> simp [ihp,ihq]
  | ifInput i p q r ihp ihq ihr =>
    simp only [transformParameterized,ClauseProgram.emit,allocatedEmit]
    split
    · next h => simp only [h,ihp]
    · next h => simp only [h,ihq]
    · next h => simp only [h,ihr]

end STACS2027

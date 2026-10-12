module

public import NPHardness.GraphPrograms
public import NPHardness.OrientedGluing
public import NPHardness.PlanarSourcePackedTest

/-! Finite single-tape-compiled graph templates with input-dependent endpoint
choices. Every choice is an explicit guard in the registered emitter syntax. -/

@[expose] public section
namespace STACS2027
open Complexity.SAT Complexity.StackTableauEmitter
open PlanarSource.Packed

structure ChoiceNum (n : Nat) where
  test : Test n
  yes : NumExpr n
  no : NumExpr n

def ChoiceNum.eval {n : Nat} (e : ChoiceNum n) (w : Complexity.SAT.Word) (env : Env n) : Nat :=
  if e.test.eval w env then e.yes.eval env else e.no.eval env

def ChoiceNum.plain {n : Nat} (e : NumExpr n) : ChoiceNum n := ⟨.const true,e,e⟩

def edgeChoiceProgram {n : Nat} (u v : ChoiceNum n) : ClauseProgram n :=
  u.test.select (v.test.select (edgeProgram u.yes v.yes) (edgeProgram u.yes v.no))
    (v.test.select (edgeProgram u.no v.yes) (edgeProgram u.no v.no))

theorem edgeChoiceProgram_emit {n : Nat} (u v : ChoiceNum n) (w : Complexity.SAT.Word) (env : Env n) :
    (edgeChoiceProgram u v).emit w env=[graphRecord (edge (u.eval w env) (v.eval w env))] := by
  simp only [edgeChoiceProgram,Test.select_emit,edgeProgram_emit,ChoiceNum.eval]
  split <;> split <;> rfl

def graphChoiceProgram {n : Nat} (t : Nat → ChoiceNum n) : Graph → ClauseProgram n
  | [] => .skip
  | e::g => .seq (edgeChoiceProgram (t e.1) (t e.2)) (graphChoiceProgram t g)

theorem graphChoiceProgram_emit {n : Nat} (t : Nat → ChoiceNum n) (g : Graph)
    (w : Complexity.SAT.Word) (env : Env n) :
    (graphChoiceProgram t g).emit w env=graphRecords (mapGraph (fun v => (t v).eval w env) g) := by
  induction g with
  | nil => rfl
  | cons e g ih => simp only [graphChoiceProgram,ClauseProgram.emit_seq,edgeChoiceProgram_emit,ih]; rfl

structure GraphLiteralExpr (n : Nat) where
  literal : LiteralExpr n
  earlier : Nat
  flip : Test n

def GraphLiteralExpr.eval {n : Nat} (l : GraphLiteralExpr n) (env : Env n) : PlacedLiteral :=
  ⟨l.literal.eval env,l.earlier⟩

def clauseVertexChoice {n : Nat} (k : Nat) (V slot : NumExpr n)
    (ls : List (GraphLiteralExpr n)) (v : Nat) : ChoiceNum n :=
  match (clausePortAt v).bind (fun ib => (ls[ib.1]?).map (fun l => (l,ib.2))) with
  | some (l,side) =>
      let port := if l.literal.positive then 0 else l.earlier+1
      ⟨l.flip,
        .add (.mul l.literal.index (.const (gadgetWidth k))) (.const (variableEndpoint port (!side))),
        .add (.mul l.literal.index (.const (gadgetWidth k))) (.const (variableEndpoint port side))⟩
  | none => ChoiceNum.plain (.add (.mul (.add V slot) (.const (gadgetWidth k))) (.const v))

theorem clauseVertexChoice_eval {n : Nat} (flips : EndpointChoices) (k : Nat) (V slot : NumExpr n)
    (ls : List (GraphLiteralExpr n)) (v : Nat) (w : Complexity.SAT.Word) (env : Env n)
    (hf : ∀ l∈ls, l.flip.eval w env=flips (l.eval env)) :
    (clauseVertexChoice k V slot ls v).eval w env=
      @Oriented.clauseVertex ⟨flips⟩ (gadgetWidth k) (V.eval env) (slot.eval env)
        (ls.map (fun l => l.eval env)) v := by
  unfold clauseVertexChoice Oriented.clauseVertex attachmentAt
  cases h : clausePortAt v with
  | none => simp [ChoiceNum.plain,ChoiceNum.eval,Test.eval,NumExpr.eval,blockVertex]
  | some ib =>
    cases hl : ls[ib.1]? with
    | none => simp [hl,List.getElem?_map,ChoiceNum.plain,ChoiceNum.eval,Test.eval,NumExpr.eval,blockVertex]
    | some l =>
      have hh := hf l (List.mem_of_getElem? hl)
      simp only [hl,Option.map_some,Option.bind_some,List.getElem?_map,ChoiceNum.eval,hh,
        Oriented.orientSide,GraphLiteralExpr.eval,PlacedLiteral.port,LiteralExpr.eval,NumExpr.eval,blockVertex]
      split <;> rfl

def orientedClauseGraphProgram {n : Nat} (k : Nat) (V slot : NumExpr n)
    (ls : List (GraphLiteralExpr n)) : ClauseProgram n :=
  .seq (.clause []) (graphChoiceProgram (clauseVertexChoice k V slot ls)
    (if ls.length=2 then clauseTwoGraph k else clauseThreeGraph k))

theorem orientedClauseGraphProgram_emit {n : Nat} (flips : EndpointChoices) (k : Nat) (V slot : NumExpr n)
    (ls : List (GraphLiteralExpr n)) (w : Complexity.SAT.Word) (env : Env n)
    (hf : ∀ l∈ls, l.flip.eval w env=flips (l.eval env)) :
    (orientedClauseGraphProgram k V slot ls).emit w env =
      [] :: graphRecords (orientedPlacedClauseGraph flips k (V.eval env) (slot.eval env)
        (ls.map (fun l => l.eval env))) := by
  simp only [orientedClauseGraphProgram,ClauseProgram.emit_seq,ClauseProgram.emit_clause,
    graphChoiceProgram_emit,clauseVertexChoice_eval flips k V slot ls _ w env hf,
    orientedPlacedClauseGraph,Oriented.placedClauseGraph,clauseGraph,List.length_map]
  rfl

end STACS2027

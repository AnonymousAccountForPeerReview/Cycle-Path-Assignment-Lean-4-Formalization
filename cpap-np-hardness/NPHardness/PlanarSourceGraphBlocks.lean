module

public import NPHardness.OrientedGraphPrograms
public import NPHardness.PlanarSourceEndpointChoices
public import NPHardness.PlanarSourceGraphSerialization
public import NPHardness.PlanarSourcePackedRingCorrect

/-! Concrete graph-emitting source blocks. Endpoint choices are computed from
original literal sign tests, and implication clauses use fixed bits false/true. -/

@[expose] public section
namespace STACS2027.PlanarSource.Packed
open Complexity Complexity.SAT Complexity.StackTableauEmitter

/-- The copied clause is all-negative and uses each variable's first negative
port. Its endpoint bit is its original source sign. -/
def copyGraphLiterals {n : Nat} (lb : NumExpr n) (t : Template n) : List (GraphLiteralExpr n) :=
  t.literals.zipIdx.map fun p => ⟨⟨addN lb p.2,false⟩,0,p.1.2⟩

theorem copyGraphLiterals_eval {n : Nat} (lb : NumExpr n) (t : Template n)
    (w : SAT.Word) (env : Env n) :
    (copyGraphLiterals lb t).map (fun p => p.eval env)=
      ((copiesAt (lb.eval env) [t.eval w env]).headD []).map (fun l => PlacedLiteral.mk l 0) := by
  simp only [copyGraphLiterals,List.map_map,copiesAt,Template.eval,List.append_nil,
    List.zipIdx_map,Function.comp_def,List.headD_cons,GraphLiteralExpr.eval,
    LiteralExpr.eval,addN,NumExpr.eval,Prod.map,id_eq]

def copyGraphBlock {n : Nat} (k : Nat) (V : NumExpr n) :
    NumExpr n → NumExpr n → List (Template n) → ClauseProgram n
  | _,_,[] => .skip
  | cb,lb,t::ts => .seq (orientedClauseGraphProgram k V cb (copyGraphLiterals lb t))
      (copyGraphBlock k V (addN cb 1) (addN lb t.literals.length) ts)

def copiedAt (base : Nat) (f : CNF) : List (List PlacedLiteral) :=
  (copiesAt base f).map (List.map (fun l => PlacedLiteral.mk l 0))

theorem copyGraphBlock_emit {n : Nat} (signs : Nat → Bool) (live : Test n)
    (N K : NumExpr n) (k : Nat) (V cb lb : NumExpr n) (ts : List (Template n))
    (w : SAT.Word) (env : Env n)
    (hs : ∀ p∈blockOccurrences live N K cb lb ts, p.sign.eval w env=signs (p.index.eval env)) :
    (copyGraphBlock k V cb lb ts).emit w env=
      orientedClauseRecordsAt (sourceEndpointChoices signs) k (V.eval env) (cb.eval env)
        (copiedAt (lb.eval env) (ts.map (fun t => t.eval w env))) := by
  induction ts generalizing cb lb with
  | nil => rfl
  | cons t ts ih =>
    have hflip : ∀ p∈copyGraphLiterals lb t,
        p.flip.eval w env=sourceEndpointChoices signs (p.eval env) := by
      intro p hp
      obtain ⟨⟨l,i⟩,hli,rfl⟩ := List.mem_map.mp hp
      have hh := hs ⟨live,addN lb i,l.1,t.top,keyExpr N K cb t i,l.2⟩
        (List.mem_append_left _ (List.mem_map.mpr ⟨(l,i),hli,rfl⟩))
      change l.2.eval w env=signs (lb.eval env+i) at hh
      change l.2.eval w env=sourceEndpointChoices signs ⟨⟨lb.eval env+i,false⟩,0⟩
      rw [sourceEndpointChoices_negative,hh]
    have htail := ih (addN cb 1) (addN lb t.literals.length)
      (fun p hp => hs p (List.mem_append_right _ hp))
    rw [copyGraphBlock,ClauseProgram.emit_seq,
      orientedClauseGraphProgram_emit (sourceEndpointChoices signs) k V cb _ w env hflip,htail]
    simp only [orientedClauseRecordsAt,copiedAt,List.map_cons,copiesAt,Template.eval,
      List.length_map,List.singleton_append,List.map_cons,List.zipIdx_cons,List.flatMap_cons,
      orientedClauseGraphRecords,addN,NumExpr.eval]
    congr 2
    rw [copyGraphLiterals_eval]
    rfl

/-- One implication edge, translated into a graph gadget. Sign branches are
ordinary finite tests; its first endpoint is direct and its second is reversed. -/
def pairGraphProgram {n : Nat} (k : Nat) (V slot i j : NumExpr n) (si sj : Test n) : ClauseProgram n :=
  si.select
    (sj.select
      (orientedClauseGraphProgram k V slot [⟨⟨i,true⟩,0,.const false⟩,⟨⟨j,false⟩,1,.const true⟩])
      (orientedClauseGraphProgram k V slot [⟨⟨i,true⟩,0,.const false⟩,⟨⟨j,true⟩,0,.const true⟩]))
    (sj.select
      (orientedClauseGraphProgram k V slot [⟨⟨i,false⟩,1,.const false⟩,⟨⟨j,false⟩,1,.const true⟩])
      (orientedClauseGraphProgram k V slot [⟨⟨i,false⟩,1,.const false⟩,⟨⟨j,true⟩,0,.const true⟩]))

theorem pairGraphProgram_emit {n : Nat} (signs : Nat → Bool) (k : Nat)
    (V slot i j : NumExpr n) (si sj : Test n) (w : SAT.Word) (env : Env n)
    (hi : si.eval w env=signs (i.eval env)) (hj : sj.eval w env=signs (j.eval env)) :
    (pairGraphProgram k V slot i j si sj).emit w env=
      orientedClauseGraphRecords (sourceEndpointChoices signs) k (V.eval env) (slot.eval env)
        ([⟨i.eval env,si.eval w env⟩,⟨j.eval env,!(sj.eval w env)⟩].map
          (fun l : Literal => PlacedLiteral.mk l (if l.positive then 0 else 1))) := by
  have hfirst (r : Nat) : sourceEndpointChoices signs ⟨⟨i.eval env,si.eval w env⟩,r⟩=false := by
    rw [hi,sourceEndpointChoices_first]
  have hsecond (r : Nat) : sourceEndpointChoices signs ⟨⟨j.eval env,!(sj.eval w env)⟩,r⟩=true := by
    rw [hj,sourceEndpointChoices_second]
  rw [pairGraphProgram,Test.select_emit]
  cases hsi : si.eval w env <;> cases hsj : sj.eval w env <;>
    simp only [hsj,Bool.false_eq_true,↓reduceIte,Test.select_emit] <;>
    rw [orientedClauseGraphProgram_emit (sourceEndpointChoices signs) k V slot _ w env] <;>
    try rfl
  all_goals
    intro p hp
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl <;>
      simp only [GraphLiteralExpr.eval,LiteralExpr.eval,Test.eval] <;>
      first
      | simpa only [hsi,hsj,Bool.not_true,Bool.not_false] using (hfirst _).symm
      | simpa only [hsi,hsj,Bool.not_true,Bool.not_false] using (hsecond _).symm

def successorGraphProgram {n : Nat} (k : Nat) (V slot : NumExpr n)
    (p : Occurrence n) (xs : List (Occurrence n)) : ClauseProgram n :=
  sequence (xs.map fun q => (successorTest p q xs).select
    (pairGraphProgram k V slot p.index q.index p.sign q.sign) .skip)

def ringGraphBlock {n : Nat} (k : Nat) (V N : NumExpr n)
    (ps : List (Occurrence n)) (positions : List Nat)
    (candidates : Nat → List (Occurrence n)) : ClauseProgram n :=
  sequence ((ps.zip positions).map fun p =>
    successorGraphProgram k V (.add N p.1.index) p.1 (candidates p.2))

end STACS2027.PlanarSource.Packed

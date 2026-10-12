module

public import NPHardness.PlanarSourceGraphBlocks
public import NPHardness.PlanarSourcePackedGraphLists

/-! The graph blocks refine the already checked source emitter. The same
finite successor guard emits the corresponding graph records, with no new
choice or search hidden in the semantic bridge. -/

@[expose] public section
namespace STACS2027.PlanarSource.Packed
open Complexity Complexity.SAT Complexity.StackTableauEmitter Complexity.Planar Comb Grid
open RotationTable

def ringRecords (signs : Nat → Bool) (k V slot : Nat) (c : Clause) : CNF :=
  orientedClauseGraphRecords (sourceEndpointChoices signs) k V slot
    (c.map (fun l => PlacedLiteral.mk l (if l.positive then 0 else 1)))

theorem successorGraphProgram_refines {n : Nat} (signs : Nat → Bool) (k : Nat)
    (V slot : NumExpr n) (p : Occurrence n) (xs : List (Occurrence n))
    (w : SAT.Word) (env : Env n)
    (hp : p.sign.eval w env=signs (p.index.eval env))
    (hs : ∀ q∈xs, (successorTest p q xs).eval w env=true → q.sign.eval w env=signs (q.index.eval env)) :
    (successorGraphProgram k V slot p xs).emit w env =
      ((successorProgram p xs).emit w env).flatMap (ringRecords signs k (V.eval env) (slot.eval env)) := by
  rw [successorGraphProgram,sequence_emit,List.flatMap_map,successorProgram_emit,List.flatMap_assoc]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro q hq
  rw [Test.select_emit]
  by_cases h : (successorTest p q xs).eval w env=true
  · rw [ite_eq_left h,ite_eq_left h,pairGraphProgram_emit signs k V slot p.index q.index p.sign q.sign w env hp (hs q hq h)]
    simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,ringRecords]
  · rw [ite_eq_right h,ite_eq_right h]
    rfl

theorem successorGraphProgram_source {n : Nat} {f : CNF} (hf : CombOK f) (k : Nat)
    (V N : NumExpr n) (p : Occurrence n) (xs : List (Occurrence n))
    (w : SAT.Word) (env : Env n) (hp : DescriptorSound f (p.eval w env))
    (hx : SoundList f w env xs) (hl : (p.eval w env).live=true)
    (hc : CompleteCandidates f p xs w env) :
    (successorGraphProgram k V (.add N p.index) p xs).emit w env=
      ringRecords (Formula.sourceSigns f) k (V.eval env) (N.eval env+p.index.eval env)
        (ringEdge f (p.index.eval env)) := by
  rw [successorGraphProgram_refines (Formula.sourceSigns f) k V _ p xs w env (hp.sign hl)]
  · rw [successorProgram_source hf p xs w env hp hx hl hc]
    simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,NumExpr.eval]
  · intro q hq hsel
    have hn := (successorTest_eval p q xs w env).mp hsel
    exact (hx q hq).sign hn.2.1.1

theorem ringGraphBlock_exact {n : Nat} (k : Nat) (V N : NumExpr n)
    (ps : List (Occurrence n)) (positions : List Nat) (candidates : Nat → List (Occurrence n))
    (records : Nat → CNF) (w : SAT.Word) (env : Env n)
    (hlen : positions.length=ps.length)
    (hlocal : ∀ p s, (p,s)∈ps.zip positions →
      (successorGraphProgram k V (.add N p.index) p (candidates s)).emit w env=records (p.index.eval env)) :
    (ringGraphBlock k V N ps positions candidates).emit w env=
      ps.flatMap (fun p => records (p.index.eval env)) := by
  simp only [ringGraphBlock,sequence_emit,List.flatMap_map]
  have he : (ps.zip positions).flatMap (fun p =>
      (successorGraphProgram k V (.add N p.1.index) p.1 (candidates p.2)).emit w env)=
      (ps.zip positions).flatMap (fun p => records (p.1.index.eval env)) := by
    apply congrArg List.flatten
    apply List.map_congr_left
    intro p hp
    exact hlocal p.1 p.2 hp
  rw [he]
  have hf : (ps.zip positions).map Prod.fst=ps := List.map_fst_zip (by omega)
  have h := congrArg (List.flatMap (fun p : Occurrence n => records (p.index.eval env))) hf
  simpa only [List.flatMap_map] using h

theorem ringGraphBlock_copies {n : Nat} (k : Nat) (V N : NumExpr n)
    (live : Test n) (K cb lb : NumExpr n) (ts : List (Template n))
    (positions : List Nat) (candidates : Nat → List (Occurrence n))
    (records : Nat → CNF) (w : SAT.Word) (env : Env n)
    (hlen : positions.length=(blockOccurrences live N K cb lb ts).length)
    (hlocal : ∀ p s, (p,s)∈(blockOccurrences live N K cb lb ts).zip positions →
      (successorGraphProgram k V (.add N p.index) p (candidates s)).emit w env=records (p.index.eval env)) :
    (ringGraphBlock k V N (blockOccurrences live N K cb lb ts) positions candidates).emit w env=
      expandCopyRecords records ((copyBlock lb ts).emit w env) := by
  rw [ringGraphBlock_exact k V N _ _ _ records w env hlen hlocal,copyBlock_emit,expandCopyRecords_copiesAt]
  have h := congrArg (List.flatMap records)
    (RotationTable.blockOccurrences_indices live N K cb lb ts w env)
  simpa only [List.flatMap_map] using h

end STACS2027.PlanarSource.Packed

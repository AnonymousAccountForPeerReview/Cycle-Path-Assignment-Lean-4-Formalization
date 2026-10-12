module

public import NPHardness.PlanarSourceRotationTableActive
public import NPHardness.PlanarSourcePackedSound

/-! Complete, duplicate-free incidence candidates for every concrete block
family of the polynomial source program. The only hypotheses describe the
current source literal's geometric position and the actual loop bounds. -/

@[expose] public section
namespace STACS2027.PlanarSource.RotationTable
open Complexity Complexity.SAT Complexity.Planar Grid Comb
open Complexity.StackTableauEmitter STACS2027.PlanarSource.Packed

structure CompleteCandidates {n : Nat} (f : CNF) (p : Occurrence n)
    (xs : List (Occurrence n)) (w : SAT.Word) (env : Env n) : Prop where
  coverage : ∀ e, e ∈ activeIndices (p.eval w env) (xs.map (fun q => q.eval w env)) ↔
    e<nM f ∧ vr f (oj f e) (ot f e)=(p.eval w env).variable
  distinct : (activeIndices (p.eval w env) (xs.map (fun q => q.eval w env))).Nodup

theorem complete_of_projection {n : Nat} (d : Layout n) (p : Occurrence n)
    (xs : List (Occurrence n)) (bs : List GridBlock) (w : SAT.Word) (env : Env n)
    (hq : 2*d.Q.eval env=d.M.eval env ∨ 2*d.Q.eval env=d.M.eval env+1)
    (hproj : liveProjection xs w env =
      neighborhoodTags (d.W.eval env) (d.M.eval env) (d.Q.eval env) (layoutBits d w env) bs)
    (hbs : bs.Nodup)
    (hcover : ∀ b, b.Valid (d.W.eval env) (d.M.eval env) →
      ∀ l ∈ (b.formula (d.W.eval env) (layoutBits d w env)).flatten,
        p.variable.eval env=l.var → b∈bs) :
    CompleteCandidates (d.source w env) p xs w env :=
  ⟨activeIndices_complete d p xs bs w env hq hproj hcover,
    activeIndices_nodup_of_projection d p xs bs w env hq hproj hbs⟩

theorem cellCandidates_complete {n : Nat} (d : Layout n) (k idx : NumExpr n)
    (odd : Bool) (s : Nat) (p : Occurrence n) (w : SAT.Word) (env : Env n)
    (hq : 2*d.Q.eval env=d.M.eval env ∨ 2*d.Q.eval env=d.M.eval env+1)
    (hi : idx.eval env<d.W.eval env) (hs : s<10)
    (hv : p.variable.eval env=cellOff (d.W.eval env) (columnIndex (k.eval env) odd) (idx.eval env)+s) :
    CompleteCandidates (d.source w env) p (d.cellCandidates k idx odd s) w env := by
  apply complete_of_projection d p _ _ w env hq (cellCandidates_projection d k idx odd s w env)
    (cellNeighborhood_nodup _ _ _ _ _)
  intro b hb l hl he
  exact cellNeighborhood_complete (layoutBits d w env) hi hs b hb l hl (hv.symm.trans he)

theorem startCandidates_complete {n : Nat} (d : Layout n) (k : NumExpr n)
    (odd : Bool) (s : Nat) (p : Occurrence n) (w : SAT.Word) (env : Env n)
    (hq : 2*d.Q.eval env=d.M.eval env ∨ 2*d.Q.eval env=d.M.eval env+1)
    (hs : s<2)
    (hv : p.variable.eval env=colBase (d.W.eval env) (columnIndex (k.eval env) odd)+s) :
    CompleteCandidates (d.source w env) p (d.startCandidates k odd s) w env := by
  apply complete_of_projection d p _ _ w env hq (startCandidates_projection d k odd s w env)
    (startNeighborhood_nodup _ _ _ _)
  intro b hb l hl he
  exact startNeighborhood_cover (layoutBits d w env) hs b hb l hl (hv.symm.trans he)

theorem endCandidates_complete {n : Nat} (d : Layout n) (k : NumExpr n)
    (odd : Bool) (s : Nat) (p : Occurrence n) (w : SAT.Word) (env : Env n)
    (hq : 2*d.Q.eval env=d.M.eval env ∨ 2*d.Q.eval env=d.M.eval env+1)
    (hs : s<2)
    (hv : p.variable.eval env=cellOff (d.W.eval env) (columnIndex (k.eval env) odd) (d.W.eval env)+s) :
    CompleteCandidates (d.source w env) p (d.endCandidates k odd s) w env := by
  apply complete_of_projection d p _ _ w env hq (endCandidates_projection d k odd s w env)
    (endNeighborhood_nodup _ _ _ _)
  intro b hb l hl he
  exact endNeighborhood_cover (layoutBits d w env) hs b hb l hl (hv.symm.trans he)

theorem rainbowCandidates_complete {n : Nat} (d : Layout n) (k v : NumExpr n)
    (odd : Bool) (s : Nat) (p : Occurrence n) (w : SAT.Word) (env : Env n)
    (hq : 2*d.Q.eval env=d.M.eval env ∨ 2*d.Q.eval env=d.M.eval env+1)
    (hi : v.eval env<d.W.eval env) (hs : s<2)
    (hv : p.variable.eval env=rainbowVariable (d.W.eval env) (k.eval env) (v.eval env) odd s) :
    CompleteCandidates (d.source w env) p (d.rainbowCandidates k v odd s) w env := by
  apply complete_of_projection d p _ _ w env hq (rainbowCandidates_projection d k v odd s w env)
    (rainbowNeighborhood_nodup _ _ _ _ _)
  intro b hb l hl he
  exact rainbowNeighborhood_cover (layoutBits d w env) hi hs b hb l hl (hv.symm.trans he)

end STACS2027.PlanarSource.RotationTable

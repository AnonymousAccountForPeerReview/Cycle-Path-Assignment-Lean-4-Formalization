module

public import NPHardness.PlanarSourceRotationTableProjection
public import NPHardness.PlanarSourceCombRotation

/-! Complete, duplicate-free active occurrence indices for actual candidate
syntax whose geometric neighborhood contains all source incidences. -/

@[expose] public section
namespace STACS2027.PlanarSource.RotationTable
open Complexity Complexity.SAT Complexity.Planar Grid Comb
open Complexity.StackTableauEmitter STACS2027.PlanarSource.Packed

theorem nM_eq_flatten (f : CNF) : nM f = f.flatten.length := by
  rw [length_flatten']
  rfl

theorem indexed_literal_variable {f : CNF} {l : Literal} {e : Nat}
    (hp : (l,e) ∈ f.flatten.zipIdx) : e < nM f ∧ vr f (oj f e) (ot f e) = l.var := by
  obtain ⟨hi,he⟩ := List.mem_zipIdx' hp
  have hib : e<nM f := by rw [nM_eq_flatten]; exact hi
  refine ⟨hib,?_⟩
  rw [← ComputableComb.variableAt_eq_vr hib,
    FromFormula.variableAt_get f ⟨e,hi⟩,←he]

theorem occurrence_at {f : CNF} {e : Nat} (hi : e<f.flatten.length) :
    (f.flatten[e],e) ∈ f.flatten.zipIdx := by
  have hp := List.getElem_mem (l := f.flatten.zipIdx) (n := e) (by simpa using hi)
  simpa only [List.getElem_zipIdx,Nat.zero_add] using hp

/-- Geometric neighborhood completeness plus exact projection gives exactly
the occurrences required by the compiled cyclic successor guard. -/
theorem activeIndices_complete {n : Nat} (d : Layout n) (p : Occurrence n)
    (xs : List (Occurrence n)) (bs : List GridBlock) (w : SAT.Word) (env : Env n)
    (hq : 2*d.Q.eval env=d.M.eval env ∨ 2*d.Q.eval env=d.M.eval env+1)
    (hproj : liveProjection xs w env =
      neighborhoodTags (d.W.eval env) (d.M.eval env) (d.Q.eval env) (layoutBits d w env) bs)
    (hcover : ∀ b, b.Valid (d.W.eval env) (d.M.eval env) →
      ∀ l ∈ (b.formula (d.W.eval env) (layoutBits d w env)).flatten,
        p.variable.eval env=l.var → b∈bs) :
    ∀ e, e ∈ activeIndices (p.eval w env) (xs.map (fun q => q.eval w env)) ↔
      e < nM (gridCNF (d.W.eval env) (d.M.eval env) (layoutBits d w env)) ∧
        vr (gridCNF (d.W.eval env) (d.M.eval env) (layoutBits d w env))
          (oj (gridCNF (d.W.eval env) (d.M.eval env) (layoutBits d w env)) e)
          (ot (gridCNF (d.W.eval env) (d.M.eval env) (layoutBits d w env)) e) =
          (p.eval w env).variable := by
  intro e
  rw [activeIndices_projection,hproj,List.mem_map]
  constructor
  · rintro ⟨⟨l,i⟩,hi,hei⟩
    obtain ⟨hi,hv⟩ := List.mem_filter.mp hi
    have hh := indexed_literal_variable (neighborhoodTags_source (layoutBits d w env) hq bs hi)
    have he : i=e := hei
    subst i
    exact ⟨hh.1,hh.2.trans (beq_iff_eq.mp hv)⟩
  · rintro ⟨hi,hv⟩
    let f := gridCNF (d.W.eval env) (d.M.eval env) (layoutBits d w env)
    have hi' : e<f.flatten.length := by rw [← nM_eq_flatten]; exact hi
    have hs := occurrence_at hi'
    have hvar := (indexed_literal_variable hs).2
    have htarget : p.variable.eval env=(f.flatten[e]).var := hv.symm.trans hvar
    have hc := neighborhoodTags_complete (layoutBits d w env) hq bs hcover hs htarget
    refine ⟨(f.flatten[e],e),List.mem_filter.mpr ⟨hc,?_⟩,rfl⟩
    exact beq_iff_eq.mpr htarget.symm

theorem activeIndices_nodup_of_projection {n : Nat} (d : Layout n) (p : Occurrence n)
    (xs : List (Occurrence n)) (bs : List GridBlock) (w : SAT.Word) (env : Env n)
    (hq : 2*d.Q.eval env=d.M.eval env ∨ 2*d.Q.eval env=d.M.eval env+1)
    (hproj : liveProjection xs w env =
      neighborhoodTags (d.W.eval env) (d.M.eval env) (d.Q.eval env) (layoutBits d w env) bs)
    (hbs : bs.Nodup) :
    (activeIndices (p.eval w env) (xs.map (fun q => q.eval w env))).Nodup := by
  rw [activeIndices_projection,hproj]
  exact List.Nodup.sublist (List.Sublist.map Prod.snd List.filter_sublist)
    (neighborhoodTags_indices_nodup (layoutBits d w env) hq bs hbs)

end STACS2027.PlanarSource.RotationTable

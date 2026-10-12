module

public import NPHardness.PlanarSourceRotationTableEnumeration
public import NPHardness.PlanarSourceRotationTablePages
public import NPHardness.PlanarSourcePackedPrefix
public import NPHardness.PlanarSourceFormulaSemantics

/-! The exact packed prefix certificates connect descriptor blocks to actual
source occurrences, including signs. -/

@[expose] public section
namespace STACS2027.PlanarSource.RotationTable
open Complexity Complexity.SAT Complexity.Planar Comb
open Complexity.StackTableauEmitter
open STACS2027.PlanarSource.Packed

/-- The registered source's block-prefix certificate discharges all geometric
metadata fields of the corresponding arithmetic descriptor block. -/
theorem blockOccurrences_correct_of_blockAt {n : Nat} {f : CNF}
    (live : Test n) (N K cb lb : NumExpr n) (ts : List (Template n))
    (w : SAT.Word) (env : Env n)
    (hN : N.eval env = f.length) (hK : K.eval env = nK f)
    (hb : Index.BlockAt f (ts.map (fun t => t.eval w env))
      (fun b => if b then lb.eval env else cb.eval env))
    (htop : ∀ t ∈ ts, t.top = sideOf (t.eval w env)) :
    ∀ p ∈ blockOccurrences live N K cb lb ts, EntryCorrect f (p.eval w env) := by
  apply blockOccurrences_correct live N K cb lb ts w env hN hK
  · exact hb.off.symm
  · intro i hi
    have hi' : i < (ts.map (fun t => t.eval w env)).length := by simpa using hi
    have hj := hb.index_lt i hi'
    have he := hb.getElem? i hi'
    simp only [Bool.false_eq_true,ite_false] at hj he
    rw [List.getElem?_eq_getElem hj,List.getElem?_map,List.getElem?_eq_getElem hi] at he
    have hc : f[cb.eval env+i] = ts[i].eval w env := Option.some.inj he
    exact ⟨hj,hc,template_source_page ts[i] w env hj hc (htop _ (List.getElem_mem hi))⟩

theorem blockAt_occurrence_mem {f g : CNF} {start : Bool → Nat}
    (h : Index.BlockAt f g start) {p : SourceOccurrence}
    (hp : p ∈ g.flatten.zipIdx (start true)) : p ∈ f.flatten.zipIdx := by
  obtain ⟨pre,post,he,hs⟩ := h
  have hl : pre.flatten.length = start true := hs true
  rw [he,List.flatten_append,List.flatten_append,List.zipIdx_append,List.zipIdx_append]
  simp only [Nat.zero_add,List.length_append,hl]
  exact List.mem_append_left _ (List.mem_append_right _ hp)

theorem blockOccurrences_source {n : Nat} {f : CNF}
    (live : Test n) (N K cb lb : NumExpr n) (ts : List (Template n))
    (w : SAT.Word) (env : Env n)
    (hb : Index.BlockAt f (ts.map (fun t => t.eval w env))
      (fun b => if b then lb.eval env else cb.eval env))
    {p : Occurrence n} (hp : p ∈ blockOccurrences live N K cb lb ts) :
    entryOccurrence (p.eval w env) ∈ f.flatten.zipIdx := by
  apply blockAt_occurrence_mem hb
  simp only [ite_true]
  rw [← blockOccurrences_enumerate live N K cb lb ts w env]
  exact List.mem_map.mpr ⟨p,hp,rfl⟩

theorem sourceOccurrence_sign {f : CNF} {p : Packed.Entry}
    (hp : entryOccurrence p ∈ f.flatten.zipIdx) :
    p.sign = Formula.sourceSigns f p.index := by
  obtain ⟨hi,he⟩ := List.mem_zipIdx' hp
  have hlit : f.flatten[p.index] = (⟨p.variable,p.sign⟩ : Literal) := he.symm
  simp only [Formula.sourceSigns,List.getElem?_eq_getElem hi,Option.getD_some,hlit]

end STACS2027.PlanarSource.RotationTable

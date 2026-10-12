module

public import NPHardness.PlanarSourceRotationTableDescriptors

/-! Exact occurrence enumeration by the arithmetic block descriptors. This
also proves uniqueness of their indices and preserves the source signs. -/

@[expose] public section
namespace STACS2027.PlanarSource.RotationTable
open Complexity Complexity.SAT Complexity.Planar
open Complexity.StackTableauEmitter
open STACS2027.PlanarSource.Packed

def entryOccurrence (p : Packed.Entry) : SourceOccurrence := (⟨p.variable,p.sign⟩,p.index)

theorem templateOccurrences_enumerate {n : Nat}
    (live : Test n) (N K cb lb : NumExpr n) (t : Template n)
    (w : SAT.Word) (env : Env n) :
    (templateOccurrences live N K cb lb t).map (fun p => entryOccurrence (p.eval w env)) =
      (t.eval w env).zipIdx (lb.eval env) := by
  apply List.ext_getElem
  · simp [templateOccurrences,Template.eval]
  · intro i hi hj
    simp [templateOccurrences,Template.eval,entryOccurrence,Occurrence.eval,
      addN,NumExpr.eval,List.getElem_zipIdx]

theorem blockOccurrences_enumerate {n : Nat}
    (live : Test n) (N K cb lb : NumExpr n) (ts : List (Template n))
    (w : SAT.Word) (env : Env n) :
    (blockOccurrences live N K cb lb ts).map (fun p => entryOccurrence (p.eval w env)) =
      (ts.map (fun t => t.eval w env)).flatten.zipIdx (lb.eval env) := by
  induction ts generalizing cb lb with
  | nil => rfl
  | cons t ts ih =>
    simp only [blockOccurrences,List.map_append,templateOccurrences_enumerate,ih,
      List.map_cons,List.flatten_cons,List.zipIdx_append,Template.eval,List.length_map,
      addN,NumExpr.eval]

/-- Every block's arithmetic indices are a contiguous interval, without repeats. -/
theorem blockOccurrences_indices {n : Nat}
    (live : Test n) (N K cb lb : NumExpr n) (ts : List (Template n))
    (w : SAT.Word) (env : Env n) :
    (blockOccurrences live N K cb lb ts).map (fun p => p.index.eval env) =
      List.range' (lb.eval env) (ts.map (fun t => t.eval w env)).flatten.length := by
  have he := congrArg (List.map Prod.snd) (blockOccurrences_enumerate live N K cb lb ts w env)
  simpa [List.map_map,Function.comp_def,entryOccurrence,Occurrence.eval] using he

end STACS2027.PlanarSource.RotationTable

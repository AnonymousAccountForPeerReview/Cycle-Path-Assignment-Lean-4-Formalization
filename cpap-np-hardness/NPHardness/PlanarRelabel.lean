module

public import NPHardness.PlanarFoundation
public import NPHardness.PlanarGluingOrientation

/-! Injective vertex renaming preserves the registered planarity predicate. -/

@[expose] public section
namespace STACS2027
open Complexity

theorem halfEdgeEnd_relabel {V W : Type} (f : V → W) (es : List (V × V)) (d : Nat) :
    halfEdgeEnd (es.map fun e => (f e.1, f e.2)) d = (halfEdgeEnd es d).map f := by
  simp only [halfEdgeEnd, List.getElem?_map, Option.map_map]
  cases es[d / 2]? with
  | none => rfl
  | some e =>
    cases h : Nat.beq (d % 2) 0 <;> rfl

theorem planarGraph_relabel_iff {V W : Type} (f : V → W)
    (hf : ∀ a b, f a = f b → a = b) (es : List (V × V)) :
    PlanarGraph (es.map fun e => (f e.1, f e.2)) ↔ PlanarGraph es := by
  have hi (a b : Option V) : a.map f = b.map f ↔ a = b := by
    cases a with
    | none => cases b <;> simp
    | some a =>
      cases b with
      | none => simp
      | some b => simp only [Option.map_some, Option.some.injEq]; exact ⟨hf a b, congrArg f⟩
  unfold PlanarGraph
  simp only [halfEdgeEnd_relabel, hi]
  rw [List.length_map]

theorem planarGraph_relabel {V W : Type} (f : V → W)
    (hf : ∀ a b, f a = f b → a = b) {es : List (V × V)} (hp : PlanarGraph es) :
    PlanarGraph (es.map fun e => (f e.1, f e.2)) :=
  (planarGraph_relabel_iff f hf es).mpr hp

theorem halfEdgeEnd_bound {g : Graph} {n d : Nat} (hb : VerticesBelow g n)
    (hd : d < 2 * g.length) : ∃ v, v < n ∧ halfEdgeEnd g d = some v := by
  have hi : d / 2 < g.length := by omega
  have he := hb g[d / 2] (List.getElem_mem hi)
  simp only [halfEdgeEnd, List.getElem?_eq_getElem hi, Option.map_some]
  cases h : Nat.beq (d % 2) 0 with
  | false => exact ⟨g[d / 2].2, he.2, rfl⟩
  | true => exact ⟨g[d / 2].1, he.1, rfl⟩

end STACS2027

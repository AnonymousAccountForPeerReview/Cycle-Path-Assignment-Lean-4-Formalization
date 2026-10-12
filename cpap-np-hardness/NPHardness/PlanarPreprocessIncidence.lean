module

public import NPHardness.PlanarPreprocessPruning
public import NPHardness.PlanarRelabel

/-! A concrete renamed-subgraph witness for incidence pruning.  This reduces
the still-needed planarity bridge to genuine edge deletion; it does not assert
that closure property without a proof. -/

@[expose] public section
namespace STACS2027.PlanarPreprocess
open Complexity Complexity.SAT

abbrev IncidenceVertex := Sum Nat Nat
abbrev IncidenceEdge := IncidenceVertex × IncidenceVertex

def renameClause (ρ : Nat → Nat) : IncidenceVertex → IncidenceVertex
  | .inl v => .inl v
  | .inr j => .inr (ρ j)

def mapEdge {V W : Type} (r : V → W) (e : V × V) : W × W := (r e.1,r e.2)

def labelledIncidence : CNF → (Nat → Nat) → List IncidenceEdge
  | [], _ => []
  | c::f, label => c.map (fun l => (.inl l.var,.inr (label 0))) ++
      labelledIncidence f (fun j => label (j+1))

theorem labelledIncidence_offset (f : CNF) (start : Nat) :
    labelledIncidence f (fun j => start+j) =
      (f.zipIdx start).flatMap (fun p => p.1.map fun l => (.inl l.var,.inr p.2)) := by
  induction f generalizing start with
  | nil => rfl
  | cons c f ih =>
    simp only [labelledIncidence,Nat.add_zero,List.zipIdx_cons,List.flatMap_cons]
    have he : (fun j => start+(j+1)) = (fun j => start+1+j) := by funext j; omega
    rw [he,ih]

theorem incidenceGraph_labelled (f : CNF) : incidenceGraph f = labelledIncidence f (fun j => j) := by
  simpa [incidenceGraph] using (labelledIncidence_offset f 0).symm

theorem labelledIncidence_map (f : CNF) (label ρ : Nat → Nat) :
    (labelledIncidence f label).map (mapEdge (renameClause ρ)) =
      labelledIncidence f (fun j => ρ (label j)) := by
  induction f generalizing label with
  | nil => rfl
  | cons c f ih =>
    simp only [labelledIncidence,List.map_append,List.map_map,ih,Function.comp_def,mapEdge,renameClause]

def keepLabel (ρ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | j+1 => ρ j+1

theorem keepLabel_injective {ρ : Nat → Nat} (h : ∀ {i j}, ρ i = ρ j → i = j) :
    ∀ {i j}, keepLabel ρ i = keepLabel ρ j → i = j := by
  intro i j he
  cases i with
  | zero => cases j with
    | zero => rfl
    | succ j => simp [keepLabel] at he
  | succ i => cases j with
    | zero => simp [keepLabel] at he
    | succ j =>
      have hij : ρ i = ρ j := by simpa [keepLabel] using he
      exact congrArg Nat.succ (h hij)

/-- Clause vertices embed injectively into the original clause vertices;
after this relabeling the entire edge list is a sublist, preserving repeated
incidence edges as well. -/
theorem Prunes.incidence_sublist {g f : CNF} (h : Prunes g f) :
    ∃ ρ : Nat → Nat, (∀ {i j}, ρ i = ρ j → i = j) ∧
      ((incidenceGraph g).map (mapEdge (renameClause ρ))).Sublist (incidenceGraph f) := by
  have hmain : ∃ ρ : Nat → Nat, (∀ {i j}, ρ i = ρ j → i = j) ∧
      (labelledIncidence g ρ).Sublist (labelledIncidence f (fun j => j)) := by
    induction h with
    | nil => exact ⟨(fun j => j),fun h => h,List.Sublist.refl _⟩
    | drop c h ih =>
      obtain ⟨ρ,hρ,hs⟩ := ih
      refine ⟨fun j => ρ j+1,?_,?_⟩
      · intro i j he
        change ρ i+1 = ρ j+1 at he
        exact hρ (Nat.add_right_cancel he)
      · have hmap := hs.map (mapEdge (renameClause (fun j => j+1)))
        rw [labelledIncidence_map,labelledIncidence_map] at hmap
        exact hmap.trans (List.sublist_append_right _ _)
    | keep hcd h ih =>
      obtain ⟨ρ,hρ,hs⟩ := ih
      refine ⟨keepLabel ρ,keepLabel_injective hρ,?_⟩
      have hmap := hs.map (mapEdge (renameClause (fun j => j+1)))
      rw [labelledIncidence_map,labelledIncidence_map] at hmap
      exact (hcd.map (fun l => (Sum.inl l.var,Sum.inr 0))).append hmap
  obtain ⟨ρ,hρ,hs⟩ := hmain
  refine ⟨ρ,hρ,?_⟩
  rw [incidenceGraph_labelled,incidenceGraph_labelled,labelledIncidence_map]
  exact hs

theorem renameClause_injective {ρ : Nat → Nat} (h : ∀ {i j}, ρ i = ρ j → i = j) :
    ∀ {v w}, renameClause ρ v = renameClause ρ w → v = w := by
  intro v w he
  cases v with
  | inl v => cases w with
    | inl w => exact congrArg Sum.inl (Sum.inl.inj he)
    | inr w => cases he
  | inr v => cases w with
    | inl w => cases he
    | inr w => exact congrArg Sum.inr (h (Sum.inr.inj he))

/-- Injective relabeling changes no dart or rotation and preserves the exact
registered `PlanarGraph` predicate in both directions. -/
theorem planarGraph_map_injective {V W : Type} (es : List (V×V)) (r : V → W)
    (hr : ∀ {v w}, r v = r w → v = w) :
    PlanarGraph (es.map (mapEdge r)) ↔ PlanarGraph es :=
  STACS2027.planarGraph_relabel_iff r (fun _ _ h => hr h) es

end STACS2027.PlanarPreprocess

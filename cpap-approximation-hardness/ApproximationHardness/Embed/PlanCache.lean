module

public import ApproximationHardness.Embed.ForestSolver
public import ApproximationHardness.Embed.SolverRAM
import Mathlib.Tactic.SplitIfs
import Lean.Elab.Tactic.Omega

/-! # Constant-size forest-plan views from three adjacency slots -/

@[expose] public section

namespace STACS2027.Embed.PlanCache

open Complexity Complexity.Planar

def threeDarts (n a b c : Nat) : List Nat := [a,b,c].take n

theorem threeDarts_eq (ds : List Nat) (hn : ds.length ≤ 3) :
    threeDarts ds.length (ds.getD 0 0) (ds.getD 1 0) (ds.getD 2 0) = ds := by
  cases ds with
  | nil => rfl
  | cons a ds =>
    cases ds with
    | nil => rfl
    | cons b ds =>
      cases ds with
      | nil => rfl
      | cons c ds =>
        cases ds with
        | nil => rfl
        | cons d ds => simp only [List.length_cons] at hn; omega

def distinguished (F : ForestData) (a b c : Nat) : Nat :=
  if ¬ F.IsTree c then c else if ¬ F.IsTree b then b else if ¬ F.IsTree a then a else c

theorem zOf_three {F : ForestData} {r a b c : Nat} (hd : F.dartsAt r = [a,b,c]) :
    F.zOf r = distinguished F a b c := by
  by_cases ha : F.IsTree a <;> by_cases hb : F.IsTree b <;> by_cases hc : F.IsTree c
  all_goals simp [ForestData.zOf, distinguished, hd, ha, hb, hc]

theorem zOf_from_slots {F : ForestData} (hF : F.Valid) (r : Nat) :
    F.zOf r = if (F.dartsAt r).length = 3 then
      distinguished F ((F.dartsAt r).getD 0 0) ((F.dartsAt r).getD 1 0)
        ((F.dartsAt r).getD 2 0) else 2 * F.E := by
  by_cases h3 : (F.dartsAt r).length = 3
  · have he := threeDarts_eq (F.dartsAt r) (hF.deg r)
    rw [h3] at he
    have hd : F.dartsAt r = [(F.dartsAt r).getD 0 0,
        (F.dartsAt r).getD 1 0, (F.dartsAt r).getD 2 0] := by simpa [threeDarts] using he.symm
    simp only [h3, ↓reduceIte]
    exact zOf_three hd
  · simp [ForestData.zOf, h3]

theorem parts_vertex_slots {F : ForestData} (hF : F.Valid) {v : Nat} (hv : F.IsVertex v) :
    F.parts v = ((threeDarts (F.dartsAt v).length ((F.dartsAt v).getD 0 0)
      ((F.dartsAt v).getD 1 0) ((F.dartsAt v).getD 2 0)).erase
        (if F.IsRoot v then F.zOf v else F.par v)).map F.item := by
  rw [threeDarts_eq _ (hF.deg v)]
  exact ForestData.parts_vertex hv

theorem item_cached (F : ForestData) (d : Nat) :
    F.item d = if F.par (F.rep (pair d)) < 2 * F.E ∧
        F.par (F.rep (pair d)) = pair d then .node (F.rep (pair d)) else .dart d := by
  have he : F.IsDown d ↔ F.par (F.rep (pair d)) < 2 * F.E ∧
      F.par (F.rep (pair d)) = pair d := by
    simp [ForestData.IsDown, ForestData.IsUp, ForestData.IsRoot]
  simp only [ForestData.item, he]

end STACS2027.Embed.PlanCache

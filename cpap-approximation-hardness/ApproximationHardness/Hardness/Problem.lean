module

public import ApproximationHardness.Sim.ParsePaths
public import ApproximationHardness.Optimization
public import ComplexityExt.Approx.Defs

/-!
# `CPAP(·, k)` as an optimization problem

The optimization problems of the MaxSNP-completeness formalization (`Complexity.OptProblem`)
live on binary words. `cpapProblem k` is `CPAP(·, k)` in this form (Definition 1, a
minimization problem):

* the instances are the codes `encode f` of record lists `f` in the instance format of the
  Section 5 language `CPAP k` — every record is an edge record (two positive literals) and there
  is no budget record — which write the graph `G = instructionGraph f`;
* the solutions of an instance are the codes `Sim.encodePaths ps` (`ps` written as a list of
  paths, each a list of edges, numbers in unary) of the cycle-path assignments `ps` of `G`: one
  path of `k - 2` edges in each simple `k`-cycle of `G`, each cycle counted once
  (`ValidChoices`, as in `HasAssignment`);
* the value of a solution is its cost `c(ps)` (`cost`, the number of pairs of chosen paths
  sharing an edge, counted per edge).

On an instance writing the graph `G`, the optimum of `cpapProblem k` is exactly `C*`
(`cpapProblem_isOpt_iff`).
-/

@[expose] public section

namespace STACS2027

open Complexity Complexity.SAT

/-- **`CPAP(·, k)`** (Definition 1, minimization): instances `encode f`, `f` Section 5 CPAP records without
budget (the graph `G = instructionGraph f`); solutions `Sim.encodePaths ps` for assignments `ps` of `G`; value: cost. -/
def cpapProblem (k : Nat) : OptProblem where
  maximize := false
  Sol x y v := ∃ (recs : CNF) (ps : List (List Edge)), encode recs = x ∧
    ValidGraphInstructions recs ∧ instructionBudget recs = 0 ∧ Sim.encodePaths ps = y ∧
    ValidChoices ((cycles (instructionGraph recs) k).map selectedOptions) ps ∧ v = cost ps

/-- The solutions of `cpapProblem k` on the code of records writing the graph `g`. -/
theorem cpapProblem_sol_encode {k : Nat} {recs : CNF} {g : Graph} (hG : GraphOutput recs g 0)
    {y : Complexity.Word} {v : Nat} :
    (cpapProblem k).Sol (encode recs) y v ↔
      ∃ ps, Sim.encodePaths ps = y ∧ ValidChoices ((cycles g k).map selectedOptions) ps ∧
        v = cost ps := by
  constructor
  · rintro ⟨recs', ps, he, -, -, hy, hps, hv⟩
    obtain rfl := encode_injective _ _ he
    rw [hG.2.1] at hps
    exact ⟨ps, hy, hps, hv⟩
  · rintro ⟨ps, hy, hps, hv⟩
    exact ⟨recs, ps, rfl, hG.1, hG.2.2, hy, by rwa [hG.2.1], hv⟩

/-- On the code of records writing the graph `g`, the optimum of `cpapProblem k` is `C*`. -/
theorem cpapProblem_isOpt_iff {k : Nat} {recs : CNF} {g : Graph} (hG : GraphOutput recs g 0)
    {C : Nat} : (cpapProblem k).IsOpt (encode recs) C ↔ IsMinCost g k C := by
  constructor
  · rintro ⟨⟨y, hy⟩, hmin⟩
    obtain ⟨ps, -, hps, rfl⟩ := (cpapProblem_sol_encode hG).mp hy
    refine ⟨⟨ps, hps, Nat.le_refl _⟩, fun B ⟨ps', hps', hB⟩ => ?_⟩
    have := (hmin _ _ ((cpapProblem_sol_encode hG).mpr ⟨ps', rfl, hps', rfl⟩)).2 rfl
    omega
  · rintro ⟨⟨ps, hps, hle⟩, hmin⟩
    have hge := hmin _ ⟨ps, hps, Nat.le_refl _⟩
    refine ⟨⟨Sim.encodePaths ps, (cpapProblem_sol_encode (v := C) hG).mpr ⟨ps, rfl, hps, by omega⟩⟩, ?_⟩
    intro y v' hy
    obtain ⟨ps', -, hps', rfl⟩ := (cpapProblem_sol_encode hG).mp hy
    exact ⟨fun h => (nomatch h), fun _ => hmin _ ⟨ps', hps', Nat.le_refl _⟩⟩

theorem cpapProblem_isOpt {k : Nat} {recs : CNF} {g : Graph} (hG : GraphOutput recs g 0)
    {C : Nat} (hC : IsMinCost g k C) : (cpapProblem k).IsOpt (encode recs) C :=
  (cpapProblem_isOpt_iff hG).mpr hC

end STACS2027

module

public import ApproximationHardness.Sim.OrientRegistered
public import ApproximationHardness.PolarizeLReduction
public import NPHardness.OrientedGluing
import Lean.Elab.Tactic.Omega

/-!
# The running times of Lemma 10's transformation, of the decoding map, and of the planar
# orientation

Paper-facing statements, in both machine models:

* the unit-cost RAM of `ApproximationHardness/RAM/Model.lean`: linear time and space (`polarize_linear_ram`,
  `decoder_linear_ram`: `C · (n + 1)`; `orientation_linear_ram`: time `C · (N + 1)` and space
  `C · (N + n + 1)`, `N` the input length), as bounded computations (`RAM.ComputesIn`);
* the single-tape machines of the registered foundation: polynomial time
  (`polarize_polyTime_machine`, `decoder_polyTime`, `orientation_polyTime`).

The decoded assignment is read from the output: variable `v` is true when the `v`-th output
number is `1` (RAM), or the `v`-th output bit is `true` (registered model). The orientation is
read from the output as one bit per literal occurrence, in the order of `(placeFormula [] f).flatten`
(`choicesOfBits`); its input is a planar rotation list of the incidence graph
(`IsPlanarRotation`: the node permutation of a planar embedding, listed dart by dart).
-/

@[expose] public section

namespace STACS2027

open Complexity Complexity.SAT PlanarAssembly

theorem satisfiedCount_congr {a b : Assignment} {f : CNF} (h : ∀ v, v < variableBound f → a v = b v) :
    satisfiedCount a f = satisfiedCount b f := by
  unfold satisfiedCount
  apply List.countP_congr
  intro c hc
  rw [evalClause_congr (fun l hl => h l.var (literal_lt_variableBound hc hl))]

/-! ### Lemma 10 -/

/-- **Lemma 10's transformation in `O(n)` time and space on a unit-cost RAM**: some RAM program and
constant `C` satisfy, for every 3-OCCURRENCE MAX-3-SAT formula `f` with `n = variableBound f`: on the
input `ramInput f` the program halts within `C · (n + 1)` steps with output `ramInput (polarize f)`,
accessing only the memory addresses below `C · (n + 1)`. -/
theorem polarize_linear_ram :
    ∃ (prog : RAM.Stmt) (C : Nat), ∀ f, ThreeOccurrence f →
      ∃ t, RAM.ComputesIn prog (RAM.ramInput f) (RAM.ramInput (polarize f)) t (C * (variableBound f + 1)) ∧
        t ≤ C * (variableBound f + 1) :=
  ⟨RAM.polProgram, RAM.polLinConst, fun f hf => RAM.polarize_linear_time f hf⟩

/-- **Lemma 10's transformation in polynomial time in the registered model**: some word function
computed by a polynomial-time single-tape machine maps `encode f` to `encode (polarize f)` for every
3-OCCURRENCE MAX-3-SAT formula `f`. -/
theorem polarize_polyTime_machine :
    ∃ g : Complexity.Word → Complexity.Word, Complexity.PolyTime g ∧
      ∀ f, ThreeOccurrence f → g (encode f) = encode (polarize f) :=
  Sim.polarize_polyTime

/-! ### The decoding map of Theorem 11 -/

/-- **The decoding map of Theorem 11 in `O(n)` time and space on a unit-cost RAM**: for every `k ≥ 5`
some RAM program and constant `C` satisfy, for every Definition 7 formula `f` with
`n = variableBound f` and every valid choice `ps` of paths for the `k`-cycles of the Theorem 8 graph:
on the input `ramInput f ++ pathsCode ps` the program halts within `C · (n + 1)` steps, accessing
only the memory addresses below `C · (n + 1)`, and the assignment `A` read from its output (`A v` iff
the `v`-th number is `1`) satisfies `S* + C* ≤ s(A) + c(ps)`, the inequality `S* − s(A) ≤ c(ps) − C*`
of Theorem 11. -/
theorem decoder_linear_ram {k : Nat} (hk : 5 ≤ k) :
    ∃ (prog : RAM.Stmt) (C : Nat), ∀ f ps, LeOneLeTwoCNF f →
      ValidChoices ((cycles (formulaGraph k f) k).map selectedOptions) ps →
      ∃ out t, RAM.ComputesIn prog (RAM.ramInput f ++ RAM.pathsCode ps) out t (C * (variableBound f + 1)) ∧
        t ≤ C * (variableBound f + 1) ∧
        ∀ S C', IsMaxSat f S → IsMinCost (formulaGraph k f) k C' →
          S + C' ≤ satisfiedCount (fun v => out.getD v 0 == 1) f + cost ps := by
  refine ⟨RAM.decProgram k, RAM.decLinConst k + RAM.decSpaceConst k, fun f ps hf hv => ?_⟩
  obtain ⟨⟨t, hc, ht⟩, hβ⟩ := RAM.decoder_ram hk hf hv
  refine ⟨_, t, hc.mono (Nat.mul_le_mul_right _ (Nat.le_add_left _ _)),
    Nat.le_trans ht (Nat.mul_le_mul_right _ (Nat.le_add_right _ _)), fun S C' hS hC => ?_⟩
  rw [satisfiedCount_congr (b := decodeAssign k ps) (fun v hv => ?_)]
  · exact hβ S C' hS hC
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hv, Option.map_some,
      Option.getD_some]
    cases decodeAssign k ps v <;> rfl

/-- **The decoding map of Theorem 11 in polynomial time in the registered model**: for every `k ≥ 5`
some word function `g` computed by a polynomial-time single-tape machine satisfies, for every
Definition 7 formula `f` and every valid choice `ps` of paths for the `k`-cycles of the Theorem 8
graph: the assignment `A` read from `g (encode f ++ encodePaths ps)` (`A v` iff its `v`-th bit is
`true`) satisfies `S* + C* ≤ s(A) + c(ps)`. -/
theorem decoder_polyTime {k : Nat} (hk : 5 ≤ k) :
    ∃ g : Complexity.Word → Complexity.Word, Complexity.PolyTime g ∧
      ∀ f ps, LeOneLeTwoCNF f → ValidChoices ((cycles (formulaGraph k f) k).map selectedOptions) ps →
        ∀ S C, IsMaxSat f S → IsMinCost (formulaGraph k f) k C →
          S + C ≤ satisfiedCount (fun v => (g (encode f ++ Sim.encodePaths ps)).getD v false) f + cost ps := by
  obtain ⟨g, hg, hc⟩ := Sim.decoder_polyTime hk
  refine ⟨g, hg, fun f ps hf hv S C hS hC => ?_⟩
  obtain ⟨ho, hβ⟩ := hc f ps hf hv
  rw [satisfiedCount_congr (b := decodeAssign k ps) (fun v hv => ?_)]
  · exact hβ S C hS hC
  · rw [ho]
    simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hv]

/-! ### The planar orientation -/

/-- **The planar gadget orientation in `O(N)` time and `O(N + n)` space on a unit-cost RAM**: some
RAM program and constant `C` satisfy, for every formula `f` of bounded occurrence (clauses of two or
three literals, at most one positive and two negative occurrences of each variable) and every planar
rotation list `rot` of its incidence graph: on the input `ramInput f ++ rot` (of length `N`) the
program halts within `C · (N + 1)` steps, accessing only the memory addresses below
`C · (N + n + 1)`, `n = variableBound f` (the program keeps two cells per variable number), and the
bits read from its output (`1` for true, one per literal occurrence) are endpoint choices for which
the oriented Theorem 8 graph is planar, for every `k`. -/
theorem orientation_linear_ram :
    ∃ (prog : RAM.Stmt) (C : Nat), ∀ f rot, BoundedOccurrence f → IsPlanarRotation f rot →
      ∃ out t, RAM.ComputesIn prog (RAM.ramInput f ++ rot) out t
          (C * ((RAM.ramInput f ++ rot).length + variableBound f + 1)) ∧
        t ≤ C * ((RAM.ramInput f ++ rot).length + 1) ∧
        ∀ k, PlanarGraph (orientedFormulaGraph (choicesOfBits f (out.map fun x => x == 1)) k f) := by
  refine ⟨RAM.orProgram, RAM.orConst + 4, fun f rot hf h => ?_⟩
  refine ⟨RAM.orOutput f rot, ?_⟩
  obtain ⟨t, hc, ht, -⟩ := RAM.orientation_linear_time 0 hf h
  exact ⟨t, hc.mono (Nat.mul_le_mul_right _ (Nat.le_add_left _ _)),
    Nat.le_trans ht (Nat.mul_le_mul_right _ (Nat.le_add_right _ _)),
    fun k => (RAM.orientation_linear_time k hf h).choose_spec.2.2⟩

/-- **Theorem 8 for planar formulas, with the orientation computed in `O(N)` time and `O(N + n)`
space on a unit-cost RAM**: for every `k ≥ 5` some RAM program and constant `C` satisfy, for every
Definition 7 formula `f` and every planar rotation list `rot` of its incidence graph: on
`ramInput f ++ rot` the program halts within `C · (N + 1)` steps, accessing only the addresses below
`C · (N + n + 1)`, and with the endpoint choices read from its output the oriented Theorem 8 graph is
planar, and `f` is satisfiable iff that graph has an assignment of cost at most `|f|`. -/
theorem gadget_reduction_planar_orientation_ram {k : Nat} (hk : 5 ≤ k) :
    ∃ (prog : RAM.Stmt) (C : Nat), ∀ f rot, LeOneLeTwoCNF f → IsPlanarRotation f rot →
      ∃ out t, RAM.ComputesIn prog (RAM.ramInput f ++ rot) out t
          (C * ((RAM.ramInput f ++ rot).length + variableBound f + 1)) ∧
        t ≤ C * ((RAM.ramInput f ++ rot).length + 1) ∧
        PlanarGraph (orientedFormulaGraph (choicesOfBits f (out.map fun x => x == 1)) k f) ∧
        (Satisfiable f ↔
          HasAssignment (orientedFormulaGraph (choicesOfBits f (out.map fun x => x == 1)) k f) k f.length) := by
  obtain ⟨prog, C, h⟩ := orientation_linear_ram
  refine ⟨prog, C, fun f rot hf hr => ?_⟩
  obtain ⟨out, t, hc, ht, hp⟩ := h f rot hf.1 hr
  exact ⟨out, t, hc, ht, hp k, orientedFormulaGraph_sat_iff_assignment _ hk hf.1 hf.2⟩

/-- **The planar gadget orientation in polynomial time in the registered model**: some word
function `g` computed by a polynomial-time single-tape machine satisfies, for every formula `f` of
bounded occurrence and every planar rotation list `rot` of its incidence graph: with the endpoint
choices read from the bits of `g (encode f ++ encodeRot rot)` the oriented Theorem 8 graph is
planar, for every `k`. -/
theorem orientation_polyTime :
    ∃ g : Complexity.Word → Complexity.Word, Complexity.PolyTime g ∧
      ∀ f rot, BoundedOccurrence f → IsPlanarRotation f rot →
        ∀ k, PlanarGraph (orientedFormulaGraph (choicesOfBits f (g (encode f ++ Sim.encodeRot rot))) k f) := by
  obtain ⟨g, hg, hc⟩ := Sim.orientation_polyTime
  exact ⟨g, hg, fun f rot hf h => (hc f rot hf h).2⟩

end STACS2027

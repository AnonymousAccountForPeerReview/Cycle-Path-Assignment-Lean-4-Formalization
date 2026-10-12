module

public import ApproximationHardness.Hardness.Problem
public import ApproximationHardness.Hardness.NormalizePT
public import ApproximationHardness.Hardness.RecoverPT
public import ApproximationHardness.RunningTimes
public import ApproximationHardness.RegisteredInstance
public import Hardness.MaxSNP.Max3SAT
import Lean.Elab.Tactic.Omega

/-!
# Theorem 11: 3-OCCURRENCE MAX-3-SAT L-reduces to `CPAP(·, k)`

For every `k ≥ 5`, `lReducible_max3SAT3_cpap` is an L-reduction, in the sense of
`Complexity.LReducible`, from the problem `max3SAT3` of the MaxSNP-completeness formalization
to `cpapProblem k`, with `α = 9` and `β = 1`. Its instance map is the composition of four
polynomial-time maps of the registered machine model:

1. `normalize` (`Hardness.Normalize`), from `max3SAT3` instances to the instances of Lemma 10,
   with `OPT(normalize f) = OPT(f) + 2u ≤ 5 OPT(f)`;
2. Lemma 10's `polarize` (`polarize_polyTime_machine`), which preserves the optimum;
3. the Theorem 8 construction (`cpap_lreduction_polyTime`), which writes the records of
   `(formulaGraph k ψ).reverse`, with `3 C* ≤ 5 S*` (Theorem 11);
4. the reversal of the record list, so that the instance writes `formulaGraph k ψ`.

Hence `C* ≤ (5/3) · 5 · OPT(f) ≤ 9 OPT(f)`. The solution map decodes a cycle-path assignment
with the decoding map of Theorem 11 (`decoder_polyTime`), undoes Lemma 10 (`recover`), and
writes the values of the variables below the length of the instance; the three inequalities
`S*(ψ) − s(A) ≤ c(τ) − C*`, `s_ψ(A) ≤ s_{normalize f}(recover A)` and
`s_{normalize f}(B) ≤ s_f(B) + 2u` give `OPT(f) − s_f ≤ c(τ) − C*`, i.e. `β = 1`.
-/

@[expose] public section

namespace STACS2027.Hardness

open Complexity Complexity.PT

theorem satisfiedCount_eq_satCount (a : SAT.Assignment) (f : SAT.CNF) :
    satisfiedCount a f = SAT.satCount a f := rfl

/-- The solutions of `max3SAT3` on the code of a formula. -/
theorem max3SAT3_sol_encode {f : SAT.CNF} {y : Complexity.Word} {v : Nat} :
    max3SAT3.Sol (SAT.encode f) y v ↔
      SAT.IsThreeCNF f ∧ SAT.IsThreeOcc f ∧ y.length ≤ (SAT.encode f).length ∧
        v = SAT.satCount (SAT.assignmentOf y) f := by
  constructor
  · rintro ⟨f', hf, h3, ho, hl, hv⟩
    obtain rfl := SAT.encode_injective _ _ hf
    exact ⟨h3, ho, hl, hv⟩
  · rintro ⟨h3, ho, hl, hv⟩
    exact ⟨f, rfl, h3, ho, hl, hv⟩

/-- The optimum of `max3SAT3` on the code of a formula is `S*`, the optimum of MAX-SAT over all
truth assignments (every variable of `f` is below the length of its code). -/
theorem isMaxSat_of_isOpt {f : SAT.CNF} {opt : Nat} (h : max3SAT3.IsOpt (SAT.encode f) opt) :
    IsMaxSat f opt := by
  obtain ⟨⟨y, hy⟩, hmax⟩ := h
  obtain ⟨h3, ho, -, hv⟩ := max3SAT3_sol_encode.mp hy
  refine ⟨⟨SAT.assignmentOf y, hv.symm⟩, fun a => ?_⟩
  let y' : Complexity.Word := (List.range (SAT.encode f).length).map a
  have hcongr : SAT.satCount (SAT.assignmentOf y') f = SAT.satCount a f :=
    SAT.satCount_congr fun _ hc _ hl =>
      SAT.assignmentOf_map_range _ a (SAT.var_lt_encode_length hc hl)
  have hsol : max3SAT3.Sol (SAT.encode f) y' (SAT.satCount a f) :=
    max3SAT3_sol_encode.mpr ⟨h3, ho, by simp [y'], hcongr.symm⟩
  exact (hmax _ _ hsol).1 rfl

/-- The solution map of the L-reduction, on a formula `φ` and a word `y`: the decoding map `Dec`
of Theorem 11 on the code of `ψ = polarize (normalize φ)` (computed by `G23` from the code of
`normalize φ`) followed by `y`, then Lemma 10's `recover`, written on the variables below the
length of the code of `φ`. -/
def solMap (Dec G23 : Complexity.Word → Complexity.Word) (φ : SAT.CNF) (y : Complexity.Word) :
    Complexity.Word :=
  (List.range (SAT.encode φ).length).map (recover (normalize φ)
    (fun v => (Dec (G23 (SAT.encode (normalize φ)) ++ y)).getD v false))

theorem pt_solMap {Dec G23 : Complexity.Word → Complexity.Word} (hDec : PolyTime Dec)
    (hG23 : PolyTime G23) :
    PT (fun p : SAT.CNF × Complexity.Word => solMap Dec G23 p.1 p.2) := by
  have hD := PT.of_polyTime hDec
  have hG := PT.of_polyTime hG23
  have hN := pt_normalize
  unfold solMap
  fun_prop

/-- **Theorem 11, the L-reduction**: for every `k ≥ 5`, 3-OCCURRENCE MAX-3-SAT L-reduces to
`CPAP(·, k)` (with `α = 9`, `β = 1`), by maps computed in polynomial time by single-tape
machines of the registered model. -/
theorem lReducible_max3SAT3_cpap {k : Nat} (hk : 5 ≤ k) : LReducible max3SAT3 (cpapProblem k) := by
  obtain ⟨FN, hFN, hFN'⟩ := pt_normalize
  obtain ⟨G23, hG23, hG23'⟩ := polarize_polyTime_machine
  obtain ⟨Inst, hInst, hInst', -⟩ := cpap_lreduction_polyTime hk
  obtain ⟨Rev, hRev, hRev'⟩ := (PT.reverse PT.id : PT (fun f : SAT.CNF => f.reverse))
  obtain ⟨Dec, hDec, hDec'⟩ := decoder_polyTime hk
  obtain ⟨G, hG, hG'⟩ := PT.exists_polyTime_pairWords_raw_word (pt_solMap hDec hG23)
  refine ⟨fun x => Rev (Inst (G23 (FN x))), G, 9, 1,
    polyTime_comp hRev (polyTime_comp hInst (polyTime_comp hG23 hFN)), hG, ?_⟩
  intro x opt hopt
  obtain ⟨⟨y₀, hy₀⟩, -⟩ := id hopt
  obtain ⟨f, rfl, h3, ho, -, -⟩ := hy₀
  have hS : IsMaxSat f opt := isMaxSat_of_isOpt hopt
  -- The intermediate formulas: `normalize f`, then `ψ = polarize (normalize f)`.
  have hN : ThreeOccurrence (normalize f) := normalize_threeOccurrence h3 ho
  have hψ : LeOneLeTwoCNF (polarize (normalize f)) := polarize_leOneLeTwo hN
  have hFNf : FN (SAT.encode f) = SAT.encode (normalize f) := hFN' f
  have hG23N := hG23' _ hN
  obtain ⟨Sψ, hSψ⟩ := maxSat_exists (polarize (normalize f))
  have heq := polarize_maxSat_eq (isMaxSat_normalize hS) hSψ
  have hrec := satisfiedCount_recover (normalize f)
  -- From here on `ψ` is opaque (this keeps the elaborator from unfolding the construction).
  generalize polarize (normalize f) = ψ at hψ hG23N hSψ hrec
  obtain ⟨recs, hrecs, hout⟩ := hInst' _ hψ
  have hout' : GraphOutput recs.reverse (formulaGraph k ψ) 0 := by
    have := Registered.GraphOutput.reverse hout
    rwa [List.reverse_reverse] at this
  have hfx : Rev (Inst (G23 (FN (SAT.encode f)))) = SAT.encode recs.reverse := by
    rw [hFNf, hG23N, hrecs]
    exact hRev' recs
  -- The optima: `3 C* ≤ 5 S*(ψ)`, `S*(ψ) = OPT(f) + 2u` and `2u ≤ 4 OPT(f)`.
  obtain ⟨C, hC⟩ := minCost_exists (formulaGraph_hasAssignment_exists hk hψ.1 hψ.2)
  have hα := (cpap_lreduction hk _ hψ Sψ C hSψ hC).1
  have hu := two_mul_unitCount_le hS
  refine ⟨C, ?_, by omega, ?_⟩
  · show (cpapProblem k).IsOpt (Rev (Inst (G23 (FN (SAT.encode f))))) C
    rw [hfx]
    exact cpapProblem_isOpt hout' hC
  · intro y v' hy
    change (cpapProblem k).Sol (Rev (Inst (G23 (FN (SAT.encode f))))) y v' at hy
    rw [hfx] at hy
    obtain ⟨ps, rfl, hps, rfl⟩ := (cpapProblem_sol_encode hout').mp hy
    -- The decoded assignment `A` of `ψ`, and `B = recover (normalize f) A`.
    have hdec := hDec' ψ ps hψ hps Sψ C hSψ hC
    generalize hA : (fun v => (Dec (SAT.encode ψ ++ Sim.encodePaths ps)).getD v false) = A at hdec
    have h1 := hrec A
    have h2 := satisfiedCount_normalize_le (recover (normalize f) A) f
    have hle := hS.2 (recover (normalize f) A)
    have hCle : C ≤ cost ps := hC.2 _ ⟨ps, hps, Nat.le_refl _⟩
    refine ⟨SAT.satCount (recover (normalize f) A) f, ?_, ?_⟩
    · rw [show G (pairWords (SAT.encode f) (Sim.encodePaths ps)) =
          solMap Dec G23 f (Sim.encodePaths ps) from hG' f _]
      refine max3SAT3_sol_encode.mpr ⟨h3, ho, by simp [solMap], ?_⟩
      apply SAT.satCount_congr
      intro _ hc l hl
      simp only [solMap]
      rw [SAT.assignmentOf_map_range _ _ (SAT.var_lt_encode_length hc hl), hG23N, hA]
    · simp only [satisfiedCount_eq_satCount] at hle h1 h2 hdec
      simp only [absDiff]
      omega

end STACS2027.Hardness

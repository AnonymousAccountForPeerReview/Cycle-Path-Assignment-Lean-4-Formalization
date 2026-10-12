module

public import Runtimes.ConvexQP.RAM.QPIface
import Mathlib.Tactic

/-!
# Lemma 16 on the RAM: the assembly

The machine of Lemma 16 is `relaxSolverProg p₁ p₂ p₃ = seq p₁ (ifz qT skip (seq p₂ p₃))`: the
parser `p₁` (with the constants), then, if there is a cycle, Phase E `p₂` and Phases K, M, O
`p₃`. This file depends only on the specifications of `QPIface.lean`:

* `relaxSolver_ram_of` (from the bounded specifications `ParseSpecRamB`, `PhaseERamB`,
  `PhaseKMORamB`): on `zeroCostInput g k` (`g` duplicate-free) the machine halts with output
  `D :: W₀ ++ ⋯ ++ W_{t−1}` for `(D, [W₀, …]) = solveExact g k opts`, within
  `C · (|input| + 2)^10` steps **and** accessing only the addresses below
  `C · (|input| + 2)^10` (`ComputesIn`);
* `relaxSolver_ram_optimal_of`: that output is an optimal fractional solution of the relaxation of
  Section 7.2 (`relaxation_exact_optimal`), with `t` weight lists of length `k`.

Ingredients: B10 (`ellRun_success`) gives the output `Xs` of Phase E and its properties, which
are the hypotheses of `PhaseKMORamB`; `solveExact = solveExactWith phaseE` is then
`exactFrom Xs 2^p` (or `(1, [])` when `t = 0`); and `t k ≤ |input|`.
-/

@[expose] public section

namespace STACS2027.Runtimes.QPRam

open STACS2027 STACS2027.RAM STACS2027.Runtimes.ConvexQP

/-- **The machine of Lemma 16**: parse (and compute the constants), then,
if there is a cycle, Phase E and Phases K, M, O. -/
def relaxSolverProg (p₁ p₂ p₃ : Stmt) : Stmt := .seq p₁ (.ifz qT .skip (.seq p₂ p₃))

end STACS2027.Runtimes.QPRam

namespace STACS2027.Runtimes.QPRam.Top

open STACS2027 STACS2027.RAM STACS2027.Runtimes.ConvexQP

/-- `t k ≤ |input|`. -/
theorem tk_le_input (g : Graph) (k : ℕ) :
    (instOf g k).t * (instOf g k).k ≤ (ZeroCost.zeroCostInput g k).length := by
  have h : (instOf g k).t * (instOf g k).k = (cycles g k).length * k := by simp
  rw [h, ZeroCost.length_zeroCostInput, ZeroCost.bD]
  rw [Nat.mul_comm]
  omega

/-- The result of `solveExact` with no cycle. -/
theorem solveExact_nil {g : Graph} {k : ℕ} (ht : (cycles g k).length = 0) :
    solveExact g k ((cycles g k).map selectedOptions) = (1, []) := by
  simp [solveExact, solveExactWith, ht]

/-- The result of `solveExact` with a cycle: the exact rounding of Phase E's output. -/
theorem solveExact_cons {g : Graph} {k : ℕ} {Xs : Fin (instOf g k).t → Fin (instOf g k).k → ℤ}
    (ht : 0 < (cycles g k).length)
    (hrun : ellRun (instOf g k) (consts (instOf g k).t (instOf g k).k) = some Xs) :
    solveExact g k ((cycles g k).map selectedOptions) =
      (((instOf g k).exactFrom Xs (2 ^ prec (instOf g k).t (instOf g k).k)).1,
        wlists ((instOf g k).exactFrom Xs (2 ^ prec (instOf g k).t (instOf g k).k)).2) := by
  have hl : ((cycles g k).map selectedOptions).length ≠ 0 := by rw [List.length_map]; omega
  have hE : phaseE (instOf g k) =
      some (Xs, 2 ^ prec (instOf g k).t (instOf g k).k) := by
    simp only [phaseE, hrun, Option.map_some]
    rfl
  unfold solveExact solveExactWith
  simp only [hl, ↓reduceIte]
  rw [show phaseE (ofOpts g k ((cycles g k).map selectedOptions)) = phaseE (instOf g k) from rfl,
    hE]

/-- **The execution** of `relaxSolverProg` within polynomial space: from the bounded
specifications, the output and the step bound, by a run accessing only the addresses below
`C · (|input| + 2)^10`. -/
theorem relaxSolver_exec {p₁ p₂ p₃ : Stmt} (h₁ : ParseSpecRamB p₁) (h₂ : PhaseERamB p₂)
    (h₃ : PhaseKMORamB p₃) :
    ∃ C : ℕ, ∀ (g : Graph) (k : ℕ), g.Nodup →
      HTB (C * ((ZeroCost.zeroCostInput g k).length + 2) ^ 10) (relaxSolverProg p₁ p₂ p₃)
        (fun c => c = initial (ZeroCost.zeroCostInput g k))
        (fun c => c.out = (solveExact g k ((cycles g k).map selectedOptions)).1 ::
          (solveExact g k ((cycles g k).map selectedOptions)).2.flatten)
        (C * ((ZeroCost.zeroCostInput g k).length + 2) ^ 10) := by
  obtain ⟨C₁, hP⟩ := h₁
  obtain ⟨C₂, hE⟩ := h₂
  obtain ⟨C₃, hK⟩ := h₃
  refine ⟨C₁ + C₂ + C₃ + 1, fun g k hg => ?_⟩
  have htk0 := tk_le_input g k
  set L := (ZeroCost.zeroCostInput g k).length
  set I := instOf g k
  have h310 : (L + 2) ^ 3 ≤ (L + 2) ^ 10 := Nat.pow_le_pow_right (by omega) (by omega)
  have htk : (I.t * I.k + 2) ^ 10 ≤ (L + 2) ^ 10 := Nat.pow_le_pow_left (by omega) 10
  have hX : 2 ≤ (L + 2) ^ 10 :=
    le_trans (by omega) (Nat.le_self_pow (by norm_num : (10 : ℕ) ≠ 0) (L + 2))
  have hsum : (C₁ + C₂ + C₃ + 1) * (L + 2) ^ 10 =
      C₁ * (L + 2) ^ 10 + C₂ * (L + 2) ^ 10 + C₃ * (L + 2) ^ 10 + (L + 2) ^ 10 := by ring
  have e1 : C₁ * (L + 2) ^ 3 ≤ C₁ * (L + 2) ^ 10 := Nat.mul_le_mul_left _ h310
  have e2 : C₂ * (I.t * I.k + 2) ^ 10 ≤ C₂ * (L + 2) ^ 10 := Nat.mul_le_mul_left _ htk
  have e3 : C₃ * (I.t * I.k + 2) ^ 10 ≤ C₃ * (L + 2) ^ 10 := Nat.mul_le_mul_left _ htk
  set S := (C₁ + C₂ + C₃ + 1) * (L + 2) ^ 10 with hS
  have hS1 : C₁ * (L + 2) ^ 3 ≤ S := by omega
  intro c hc
  obtain ⟨c₁, t₁, he₁, ⟨hq₁, hF₁⟩, ht₁⟩ := hP g k hg S hS1 c hc
  change t₁ ≤ C₁ * (L + 2) ^ 3 at ht₁
  change c₁.reg rFREE ≤ C₁ * (L + 2) ^ 3 at hF₁
  rcases hq₁ with ⟨ht0, hqT, hout⟩ | ⟨htpos, hIn⟩
  · -- no cycle: the output `[1]` is already written
    refine ⟨c₁, t₁ + (1 + 1), ExecB.seq he₁ (ExecB.ifzTrue hqT (ExecB.skip c₁)), ?_, ?_⟩
    · show c₁.out = _
      rw [hout, solveExact_nil ht0]; rfl
    · omega
  · have hI : I.Valid := ofOpts_valid_cycles hg (by intro h; simp [h] at htpos)
    have hIt : I.t = (cycles g k).length := by simp [I]
    have htI : 0 < I.t := by rw [hIt]; exact htpos
    obtain ⟨Xs, hrun, hX, hgap⟩ := ellRun_success hI htI
    have hqT : c₁.reg qT ≠ 0 := by
      have h := hIn.1.1; change c₁.reg qT = I.t at h; omega
    obtain ⟨c₂, t₂, he₂, ⟨hq₂, hF₂⟩, ht₂⟩ := hE I hI htI Xs hrun S c₁ hIn (by omega) c₁ rfl
    obtain ⟨c₃, t₃, he₃, ⟨hq₃, -⟩, ht₃⟩ := hK I hI htI Xs hX hgap S c₂ hq₂ (by omega) c₂ rfl
    refine ⟨c₃, t₁ + ((t₂ + t₃) + 1),
      ExecB.seq he₁ (ExecB.ifzFalse hqT (ExecB.seq he₂ he₃)), ?_, ?_⟩
    · show c₃.out = _
      rw [hq₃, solveExact_cons htpos hrun]
      rfl
    · omega

/-- The shape of `solveExact`'s weights: one list of length `k` per cycle. -/
theorem solveExact_shape {g : Graph} (hg : g.Nodup) (k : ℕ) :
    (solveExact g k ((cycles g k).map selectedOptions)).2.length = (cycles g k).length ∧
      ∀ w ∈ (solveExact g k ((cycles g k).map selectedOptions)).2, w.length = k := by
  rcases Nat.eq_zero_or_pos (cycles g k).length with ht | ht
  · rw [solveExact_nil ht]; simp [ht]
  · have hI : (instOf g k).Valid := ofOpts_valid_cycles hg (by intro h; simp [h] at ht)
    have hIt : (instOf g k).t = (cycles g k).length := by simp
    obtain ⟨Xs, hrun, -, -⟩ := ellRun_success hI (by rw [hIt]; exact ht)
    rw [solveExact_cons ht hrun]
    refine ⟨by simp [wlists], fun w hw => ?_⟩
    simp only [wlists, List.mem_ofFn] at hw
    obtain ⟨c, rfl⟩ := hw
    simp

end STACS2027.Runtimes.QPRam.Top

namespace STACS2027.Runtimes.QPRam

open STACS2027 STACS2027.RAM STACS2027.Runtimes.ConvexQP STACS2027.Runtimes.QPRam.Top

/-- **Lemma 16 on the RAM** within polynomial time **and space**, from the
bounded specifications of the three parts: on `zeroCostInput g k` the machine outputs
`solveExact`'s `D` followed by the weights, cycle by cycle, within `C · (|input| + 2)^10` steps,
accessing only the addresses below `C · (|input| + 2)^10` (no memory indexed by a label). -/
theorem relaxSolver_ram_of {p₁ p₂ p₃ : Stmt} (h₁ : ParseSpecRamB p₁) (h₂ : PhaseERamB p₂)
    (h₃ : PhaseKMORamB p₃) :
    ∃ C : ℕ, ∀ (g : Graph) (k : ℕ), g.Nodup →
      ∃ T, ComputesIn (relaxSolverProg p₁ p₂ p₃) (ZeroCost.zeroCostInput g k)
          ((solveExact g k ((cycles g k).map selectedOptions)).1 ::
            (solveExact g k ((cycles g k).map selectedOptions)).2.flatten) T
          (C * ((ZeroCost.zeroCostInput g k).length + 2) ^ 10) ∧
        T ≤ C * ((ZeroCost.zeroCostInput g k).length + 2) ^ 10 := by
  obtain ⟨C, h⟩ := relaxSolver_exec h₁ h₂ h₃
  refine ⟨C, fun g k hg => ?_⟩
  obtain ⟨T, hT, hc⟩ := HTB.computesIn (h g k hg)
  exact ⟨T, hc, hT⟩

/-- **Lemma 16 on the RAM** (optimality, polynomial time and space): the output
`D :: W₀ ++ ⋯ ++ W_{t−1}` of the machine, computed within `C · (|input| + 2)^10` steps and the
addresses below `C · (|input| + 2)^10`, is an optimal fractional solution of the relaxation of
Section 7.2 on the `k`-cycles of `g` (`t` weight lists of length `k`). -/
theorem relaxSolver_ram_optimal_of {p₁ p₂ p₃ : Stmt} (h₁ : ParseSpecRamB p₁) (h₂ : PhaseERamB p₂)
    (h₃ : PhaseKMORamB p₃) :
    ∃ C : ℕ, ∀ (g : Graph) (k : ℕ), g.Nodup →
      ∃ (D : ℕ) (W : List (List ℕ)) (T : ℕ),
        ComputesIn (relaxSolverProg p₁ p₂ p₃) (ZeroCost.zeroCostInput g k) (D :: W.flatten) T
          (C * ((ZeroCost.zeroCostInput g k).length + 2) ^ 10) ∧
        T ≤ C * ((ZeroCost.zeroCostInput g k).length + 2) ^ 10 ∧
        W.length = (cycles g k).length ∧ (∀ w ∈ W, w.length = k) ∧
        OptimalFractional g D (((cycles g k).map selectedOptions).zip W) := by
  obtain ⟨C, h⟩ := relaxSolver_ram_of h₁ h₂ h₃
  refine ⟨C, fun g k hg => ?_⟩
  obtain ⟨T, hc, hT⟩ := h g k hg
  obtain ⟨hlen, hw⟩ := solveExact_shape hg k
  exact ⟨_, _, T, hc, hT, hlen, hw, relaxation_exact_optimal hg k⟩

end STACS2027.Runtimes.QPRam

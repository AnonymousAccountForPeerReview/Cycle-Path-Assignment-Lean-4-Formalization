module

public import Runtimes.BoundedCost.Extract
public import Runtimes.BoundedCost.Zero
import Mathlib.Tactic

/-!
# Theorem 4 on the RAM, with the Almost 2-SAT algorithm as a hypothesis (`k ≥ 4`)

The manuscript's Theorem 4 (`thm:CostFPT`): *for `k ≥ 3`, given the enumerated simple
`k`-cycles of `G` (`t` of them, enumerated in time `Υ_k`) and `Ψ ∈ ℕ₀`, an assignment for
`CPAP(G, k)` of cost at most `Ψ` can be found, or its nonexistence certified, in time
`O(15^Ψ Ψ ((Ψ+1)k²t + kt²)³ + k²t + kt² + Υ_k)`*; the proof applies, for `Ψ ≥ 1`, the
`O(15^Ψ Ψ m³)`-time Almost 2-SAT algorithm of ANONYMIZED and ANONYMIZED to `Γ'`, and ordinary 2-SAT
for `Ψ = 0`. The Almost 2-SAT algorithm is **cited, not formalized**: it is the hypothesis
`Almost2SatSolver F T` (`Runtimes/BoundedCost/Solver.lean`), a RAM program `F` within `T Ψ N` steps
and addresses on inputs of length `N`. Everything else is a RAM program proved here, with its
time and its space (`RAM.ComputesIn`), and **no program indexes memory by a vertex label** (the
cycle vertices are relabelled by the sorting front end `Sort.front`).

**`boundedCost_ram`** (`k ≥ 4`; `t` the number of cycles, `m = |g|`,
`B = (Ψ+1)k²t + kt² + m + 1`): three programs and a constant `C`:
* `Ψ = 0`: `zero` (`zero5`: the formula `Γ' = Γ_∅`, the formalized linear 2-SAT, the
  recovery) answers within `C B` steps and addresses;
* `Ψ ≥ 1`: `build` (`build5`) writes the solver's input `a2In (shiftF Γ') Ψ` (`Γ'` with its
  variables renamed `v ↦ v + 1`, `2 |Γ'| + 2 ≤ 2 ((Ψ+1)k²t + kt² + 1)` numbers) within `C B`
  steps and addresses; `F` answers within `T Ψ N'` steps and addresses, `N'` that length; and
  `extract` (`extract5`), on the input followed by that answer, writes the answer within `C B`
  steps and addresses.

The answer (`BoundedCostAnswer`): `[0]` iff there is no assignment of cost at most `Ψ`, and otherwise
`1` followed by one position `pos_i < k` per cycle whose paths `selected C_i pos_i` form a
cycle-path assignment of cost at most `Ψ`. The single-program forms (the solver as a relocated
subroutine) and the manuscript's bound under `FPTBound T` are in `Runtimes/BoundedCost/Top.lean`.

As in Corollary 5, the cycles are part of the input, so their enumeration (`Υ_k ≥ m`) is
charged separately; `m + 1` is the reading of the input. Algorithm 3's restriction to the
`k`-cycle core is skipped: Section 4 proves it changes neither the cycles nor the answer
(`cycles_kCycleCore`, `hasAssignment_kCycleCore_iff`).
-/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 STACS2027.RAM STACS2027.Runtimes.ZeroCost Complexity.SAT

/-! ### Arithmetic -/

/-- `⌈log₂ (kt)⌉ ≤ k + t`, so the sorting front end costs `O(kt (k + t)) = O(k²t + kt²)`. -/
theorem clog_le_add (k t : ℕ) : Nat.clog 2 (k * t) ≤ k + t := by
  apply Nat.clog_le_of_le_pow
  rw [pow_add]
  exact Nat.mul_le_mul (Nat.lt_two_pow_self).le (Nat.lt_two_pow_self).le

/-- The size of `Γ'`: `|Γ'| ≤ (Ψ+1)k²t + kt²`. -/
theorem almost_len_le (g : Graph) (k Ψ : ℕ) :
    (almostFormula g k Ψ).length ≤ (Ψ + 1) * k * k * (cycles g k).length +
      k * (cycles g k).length * (cycles g k).length := by
  obtain ⟨-, h2, h3, h4⟩ := almostFormula_size g k Ψ
  set t := (cycles g k).length
  have e1 : k * (k - 3) * t ≤ k * k * t :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
  have e2 : k * t * (t - 1) ≤ k * t * t := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  have e3 : (Ψ + 1) * (pathConstraints g k).length ≤ (Ψ + 1) * (k * k * t) :=
    Nat.mul_le_mul_left _ (by omega)
  have e4 : (Ψ + 1) * (k * k * t) = (Ψ + 1) * k * k * t := by ring
  omega

/-- The front end: `CF (kt (⌈log₂ kt⌉ + 1) + 1) ≤ CF (2 (k²t + kt²) + 1)`. -/
theorem frontCost_le (g : Graph) (k : ℕ) (hk : 1 ≤ k) :
    frontCost g k ≤ Sort.CF * (2 * (k * k * (cycles g k).length +
      k * (cycles g k).length * (cycles g k).length) + 1) := by
  unfold frontCost
  apply Nat.mul_le_mul_left
  simp only [Sort.fL]
  set t := (cycles g k).length
  have hkt : k * t ≤ k * k * t := by
    rw [Nat.mul_assoc]; exact Nat.le_mul_of_pos_left _ (by omega)
  have h : k * t * (Nat.clog 2 (k * t) + 1) ≤ k * k * t + k * t * t + k * t :=
    calc k * t * (Nat.clog 2 (k * t) + 1) ≤ k * t * (k + t + 1) :=
          Nat.mul_le_mul_left _ (Nat.add_le_add_right (clog_le_add k t) 1)
      _ = k * k * t + k * t * t + k * t := by ring
  omega

/-- The copies of the path constraints: `nCopies (t (k (65k + 7) + 8) + 8) ≤ 88 (Ψ+1) k²t`. -/
theorem nCopies_le (g : Graph) (k Ψ : ℕ) (hk : 1 ≤ k) :
    nCopies g k Ψ * ((cycles g k).length * (k * (k * 65 + 7) + 8) + 8) ≤
      88 * ((Ψ + 1) * k * k * (cycles g k).length) := by
  unfold nCopies
  split_ifs with h
  · simp
  · set t := (cycles g k).length
    have h1 : t * (k * (k * 65 + 7) + 8) + 8 ≤ 88 * (k * k * t) := by
      have e : t * (k * (k * 65 + 7) + 8) = 65 * (k * k * t) + 7 * (k * t) + 8 * t := by ring
      have hkt : k * t ≤ k * k * t := by
        rw [Nat.mul_assoc]; exact Nat.le_mul_of_pos_left _ (by omega)
      have ht : t ≤ k * t := Nat.le_mul_of_pos_left _ (by omega)
      omega
    calc (Ψ + 1) * (t * (k * (k * 65 + 7) + 8) + 8) ≤ (Ψ + 1) * (88 * (k * k * t)) :=
          Nat.mul_le_mul_left _ h1
      _ = 88 * ((Ψ + 1) * k * k * t) := by ring

/-- The bound `B = (Ψ+1)k²t + kt² + m + 1`. -/
def bnd5 (g : Graph) (k Ψ : ℕ) : ℕ :=
  (Ψ + 1) * k * k * (cycles g k).length + k * (cycles g k).length * (cycles g k).length +
    g.length + 1

/-- The constant of the polynomial parts. -/
def C5 : ℕ := 20000

/-- The parts of `bnd5`. -/
theorem bnd5_facts (g : Graph) (k Ψ : ℕ) (hk : 1 ≤ k) :
    (cycles g k).length ≤ k * (cycles g k).length ∧
      k * (cycles g k).length ≤ k * k * (cycles g k).length ∧
      k * k * (cycles g k).length ≤ (Ψ + 1) * k * k * (cycles g k).length ∧
      (Ψ + 1) * k * k * (cycles g k).length + k * (cycles g k).length * (cycles g k).length +
        g.length + 1 = bnd5 g k Ψ := by
  set t := (cycles g k).length
  refine ⟨Nat.le_mul_of_pos_left _ (by omega), ?_, ?_, rfl⟩
  · rw [Nat.mul_assoc]; exact Nat.le_mul_of_pos_left _ (by omega)
  · have : (Ψ + 1) * k * k * t = (Ψ + 1) * (k * k * t) := by ring
    rw [this]; exact Nat.le_mul_of_pos_left _ (by omega)

theorem formCost_le (g : Graph) (k Ψ : ℕ) (hk : 1 ≤ k) : formCost g k Ψ ≤ 2000 * bnd5 g k Ψ := by
  have hf := frontCost_le g k hk
  have hn := nCopies_le g k Ψ hk
  obtain ⟨h1, h2, h3, h4⟩ := bnd5_facts g k Ψ hk
  unfold formCost
  set t := (cycles g k).length
  have e : t * (t * (k * 44 + 16) + 9) = 44 * (k * t * t) + 16 * (t * t) + 9 * t := by ring
  have htt : t * t ≤ k * t * t := by
    rw [Nat.mul_assoc]; exact Nat.le_mul_of_pos_left _ (by omega)
  have eCF : Sort.CF = 500 := rfl
  rw [eCF] at hf
  omega

theorem buildCost_le (g : Graph) (k Ψ : ℕ) (hk : 1 ≤ k) : buildCost g k Ψ ≤ C5 * bnd5 g k Ψ := by
  have h := formCost_le g k Ψ hk
  have hl := almost_len_le g k Ψ
  obtain ⟨-, -, -, h4⟩ := bnd5_facts g k Ψ hk
  unfold buildCost C5
  omega

theorem formSpace_le (g : Graph) (k Ψ : ℕ) (hk : 1 ≤ k) : formSpace g k Ψ ≤ C5 * bnd5 g k Ψ := by
  have hl := almost_len_le g k Ψ
  have hL := lay5 g k
  obtain ⟨h1, h2, h3, h4⟩ := bnd5_facts g k Ψ hk
  unfold formSpace C5
  omega

theorem extractCost_le (g : Graph) (k Ψ : ℕ) (hk : 1 ≤ k) : extractCost g k ≤ C5 * bnd5 g k Ψ := by
  obtain ⟨h1, h2, h3, h4⟩ := bnd5_facts g k Ψ hk
  unfold extractCost readCost C5
  set t := (cycles g k).length
  have e : t * (k * (k * 40 + 18) + 11) = 40 * (k * k * t) + 18 * (k * t) + 11 * t := by ring
  omega

theorem extractSpace_le (g : Graph) (k Ψ : ℕ) (hk : 1 ≤ k) :
    extractSpace g k Ψ ≤ C5 * bnd5 g k Ψ := by
  have hl := almost_len_le g k Ψ
  have hL := lay5 g k
  obtain ⟨h1, h2, h3, h4⟩ := bnd5_facts g k Ψ hk
  unfold extractSpace C5
  omega

theorem zeroCost_le (g : Graph) (k : ℕ) (hk : 1 ≤ k) : zeroCost g k ≤ C5 * bnd5 g k 0 := by
  have h := formCost_le g k 0 hk
  have hl := almost_len_le g k 0
  obtain ⟨h1, h2, h3, h4⟩ := bnd5_facts g k 0 hk
  unfold zeroCost C5
  set t := (cycles g k).length
  have e : t * (k * (k * 40 + 18) + 11) = 40 * (k * k * t) + 18 * (k * t) + 11 * t := by ring
  have eCT : TwoSat.CT = 700 := rfl
  rw [eCT]
  omega

theorem zeroSpace_le (g : Graph) (k : ℕ) (hk : 1 ≤ k) : zeroSpace g k ≤ C5 * bnd5 g k 0 := by
  have h := formSpace_le g k 0 hk
  have hE := TwoSat.endL_le (k * (cycles g k).length) (almostFormula g k 0).length (formSpace g k 0)
  have hl := almost_len_le g k 0
  have hL := lay5 g k
  obtain ⟨h1, h2, h3, h4⟩ := bnd5_facts g k 0 hk
  unfold zeroSpace
  unfold formSpace C5 at *
  omega

/-! ### The parts as computations -/

/-- **`Ψ = 0`**: the machine `zero5`. -/
theorem zero5_ram (g : Graph) (k : ℕ) (hk : 4 ≤ k) :
    ∃ (out : List ℕ) (steps : ℕ),
      RAM.ComputesIn zero5 (boundedCostInput g k 0) out steps (C5 * bnd5 g k 0) ∧
        steps ≤ C5 * bnd5 g k 0 ∧ BoundedCostAnswer g k 0 out := by
  obtain ⟨out, t, ht, ho, hc⟩ := HTB.computesIn_post (zero5_spec g k hk)
  exact ⟨out, t, hc.mono (zeroSpace_le g k (by omega)), ht.trans (zeroCost_le g k (by omega)), ho⟩

/-- The one-based shifted formula lies in the word-bounded solver domain. -/
theorem almostFormula_shift_solverDomain (g : Graph) (k Ψ : ℕ) (hk : 4 ≤ k) :
    SolverDomain (shiftF (almostFormula g k Ψ)) := by
  have hpc := (almostFormula_size g k Ψ).2.1
  have hlen := (almostFormula_size g k Ψ).2.2.2
  have hk1 : 1 ≤ k - 3 := by omega
  have hkt : k * (cycles g k).length ≤ 2 * (pathConstraints g k).length := by
    rw [hpc]
    have := Nat.mul_le_mul_right (cycles g k).length (Nat.mul_le_mul_left k hk1)
    simpa using this
  have hpcf : (pathConstraints g k).length ≤ (almostFormula g k Ψ).length := by
    have := Nat.mul_le_mul_right (pathConstraints g k).length (show 1 ≤ Ψ + 1 by omega)
    omega
  intro c hc
  obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hc
  refine ⟨by simpa using (almost_two g k Ψ c' hc').1, ?_⟩
  intro l hl
  obtain ⟨l', hl', rfl⟩ := List.mem_map.mp hl
  have hv := (almost_two g k Ψ c' hc').2 l' hl'
  simp only [shiftL, length_shiftF]
  omega

/-- **`Ψ ≥ 1`**: the construction, the cited solver, the extraction. -/
theorem pipeline5 {F : RAM.Stmt} {T : ℕ → ℕ → ℕ} (hA : Almost2SatSolver F T) (g : Graph)
    (k Ψ : ℕ) (hk : 4 ≤ k) :
    ∃ (ans out : List ℕ) (t₁ t₂ t₃ : ℕ),
      RAM.ComputesIn build5 (boundedCostInput g k Ψ) (a2In (shiftF (almostFormula g k Ψ)) Ψ) t₁
          (formSpace g k Ψ) ∧ t₁ ≤ buildCost g k Ψ ∧
      RAM.ComputesIn F (a2In (shiftF (almostFormula g k Ψ)) Ψ) ans t₂
          (T Ψ (2 * (almostFormula g k Ψ).length + 2)) ∧
        t₂ ≤ T Ψ (2 * (almostFormula g k Ψ).length + 2) ∧
      ans.length ≤ (almostFormula g k Ψ).length + k * (cycles g k).length + 2 ∧
      RAM.ComputesIn extract5 (boundedCostInput g k Ψ ++ ans) out t₃ (extractSpace g k Ψ) ∧
        t₃ ≤ extractCost g k ∧
      BoundedCostAnswer g k Ψ out := by
  obtain ⟨t₁, ht₁, h₁⟩ := HTB.computesIn (build5_spec g k Ψ)
  obtain ⟨ans, t₂, h₂, ht₂, hans⟩ := hA _ Ψ (almostFormula_shift_solverDomain g k Ψ hk)
  have hN : (a2In (shiftF (almostFormula g k Ψ)) Ψ).length = 2 * (almostFormula g k Ψ).length + 2 := by
    rw [a2In, List.length_cons, List.length_cons, codes_shiftF, List.length_map,
      length_codes_almost]
  rw [hN] at h₂ ht₂
  have hlen : ans.length ≤ (almostFormula g k Ψ).length + k * (cycles g k).length + 2 := by
    rcases hans with ⟨_, rfl⟩ | ⟨D, T, rfl, hD, hDm, -, hT, hTo, -⟩
    · simp
    · have hDf := keptOf_length hD (fun i hi => by simpa using hDm i hi)
      have hTl := length_le_of_pairwise hT fun y hy => occursIn_shiftF (almost_two g k Ψ) (hTo y hy)
      simp only [List.length_cons, List.length_append]
      omega
  obtain ⟨out, t₃, ht₃, ho, h₃⟩ := HTB.computesIn_post (extract5_spec g k Ψ hk hans)
  exact ⟨ans, out, t₁, t₂, t₃, h₁, ht₁, h₂, ht₂, hlen, h₃, ht₃, ho⟩

/-! ### The statement -/

/-- **Theorem 4 on the RAM** (`k ≥ 4`, the Almost 2-SAT hypothesis), `B = (Ψ+1)k²t + kt² + m + 1`:
for `Ψ = 0`, `zero` answers (`BoundedCostAnswer`) within `C B` steps and addresses; for `Ψ ≥ 1`, `build`
writes the solver's input for `Γ'` (variables shifted by one), `F` answers within `T Ψ N'`, and
`extract`, on the input followed by that answer, writes the answer, each within `C B`. -/
theorem boundedCost_ram {F : RAM.Stmt} {T : ℕ → ℕ → ℕ} (hA : Almost2SatSolver F T) :
    ∃ (zero build extract : RAM.Stmt) (C : ℕ), ∀ (g : Graph) (k Ψ : ℕ), 4 ≤ k →
      (Ψ = 0 → ∃ (out : List ℕ) (steps : ℕ),
        RAM.ComputesIn zero (boundedCostInput g k Ψ) out steps
          (C * ((Ψ + 1) * k * k * (cycles g k).length +
            k * (cycles g k).length * (cycles g k).length + g.length + 1)) ∧
        steps ≤ C * ((Ψ + 1) * k * k * (cycles g k).length +
          k * (cycles g k).length * (cycles g k).length + g.length + 1) ∧
        BoundedCostAnswer g k Ψ out) ∧
      (1 ≤ Ψ → ∃ (fin ans out : List ℕ) (t₁ t₂ t₃ : ℕ),
        RAM.ComputesIn build (boundedCostInput g k Ψ) fin t₁
          (C * ((Ψ + 1) * k * k * (cycles g k).length +
            k * (cycles g k).length * (cycles g k).length + g.length + 1)) ∧
        t₁ ≤ C * ((Ψ + 1) * k * k * (cycles g k).length +
          k * (cycles g k).length * (cycles g k).length + g.length + 1) ∧
        fin = a2In (shiftF (almostFormula g k Ψ)) Ψ ∧
        fin.length ≤ 2 * ((Ψ + 1) * k * k * (cycles g k).length +
          k * (cycles g k).length * (cycles g k).length + 1) ∧
        RAM.ComputesIn F fin ans t₂ (T Ψ fin.length) ∧ t₂ ≤ T Ψ fin.length ∧
        RAM.ComputesIn extract (boundedCostInput g k Ψ ++ ans) out t₃
          (C * ((Ψ + 1) * k * k * (cycles g k).length +
            k * (cycles g k).length * (cycles g k).length + g.length + 1)) ∧
        t₃ ≤ C * ((Ψ + 1) * k * k * (cycles g k).length +
          k * (cycles g k).length * (cycles g k).length + g.length + 1) ∧
        BoundedCostAnswer g k Ψ out) := by
  refine ⟨zero5, build5, extract5, C5, fun g k Ψ hk => ⟨fun hΨ => ?_, fun _ => ?_⟩⟩
  · subst hΨ; exact zero5_ram g k hk
  · obtain ⟨ans, out, t₁, t₂, t₃, h₁, ht₁, h₂, ht₂, -, h₃, ht₃, ho⟩ := pipeline5 hA g k Ψ hk
    have hN : (a2In (shiftF (almostFormula g k Ψ)) Ψ).length =
        2 * (almostFormula g k Ψ).length + 2 := by
      rw [a2In, List.length_cons, List.length_cons, codes_shiftF, List.length_map,
        length_codes_almost]
    have hl := almost_len_le g k Ψ
    refine ⟨_, ans, out, t₁, t₂, t₃, h₁.mono (formSpace_le g k Ψ (by omega)),
      ht₁.trans (buildCost_le g k Ψ (by omega)), rfl, by rw [hN]; omega, by rw [hN]; exact h₂,
      by rw [hN]; exact ht₂, h₃.mono (extractSpace_le g k Ψ (by omega)),
      ht₃.trans (extractCost_le g k Ψ (by omega)), ho⟩

end STACS2027.Runtimes.BoundedCost

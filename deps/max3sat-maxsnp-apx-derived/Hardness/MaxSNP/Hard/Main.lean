module

public import Hardness.MaxSNP.Hard.Count
public import Hardness.MaxSNP.Hard.Fit
public import Hardness.MaxSNP.Hard.Poly
public import Hardness.MaxSNP.Final

/-!
# MAX-3-SAT is MaxSNP-hard

Every problem of the syntactic class MaxSNP₀ given by a well-formed formula is L-reducible to
MAX-3-SAT (`lReducible_maxSNP0_max3SATu`, ANONYMIZED–ANONYMIZED 1991, Theorem 2), hence
MAX-3-SAT is MaxSNP-hard (`max3SATu_maxSNPHard`). The solution map writes relations from an
assignment and then cuts out a structure of the solution signature (`fitRel`), which for a
well-formed formula does not change the value.

For a formula `φ` with `a` occurrences of solution atoms, the constants of the L-reduction
are `α = 2 ^ a * 2 ^ a * (a + 1)` and `β = 1`: with `I` the number of clauses of the formula
`snpToSat k φ (n, G)` and `N'` the number of kept tuples, the optima are related by
`opt' + N' = I + opt`, every assignment of value `v'` gives solution relations of value `v`
with `v' + N' ≤ I + v`, and `I ≤ N' * 2 ^ a * (a + 1)`, `N' ≤ 2 ^ a * opt`.

Throughout this file MAX-3-SAT is the auxiliary problem `max3SATu` of `Hardness.Unbounded`, in
which every word is an assignment; the results are transferred to `max3SAT` (assignments no
longer than the instance) in `Hardness.Final.Max3SAT`.
-/

@[expose] public section

namespace Complexity

open Complexity.PT Complexity.Reg

/-- **Every MaxSNP₀ problem L-reduces to MAX-3-SAT.** -/
theorem lReducible_maxSNP0_max3SATu (ga sa : List Nat) (k : Nat) (φ : QF)
    (hφ : φ.WellFormed ga sa k) : LReducible (maxSNP0 ga sa k φ) max3SATu := by
  obtain ⟨F, hF, hF'⟩ := pt_snpToSat k φ
  obtain ⟨H, hH, hH'⟩ := PT.exists_polyTime_pairWords_raw
    (h := fun (p : Nat × Relations) (y : Word) => fitRel sa p.1 (satToSnp k φ p y))
    (pt_fitRel_satToSnp sa k φ)
  refine ⟨F, H, 2 ^ φ.atoms.length * 2 ^ φ.atoms.length * (φ.atoms.length + 1), 1, hF, hH, ?_⟩
  intro x opt hopt
  obtain ⟨⟨y₀, n, G, S₀, hG, -, rfl, -, hv₀⟩, hmax⟩ := hopt
  have hFx : F (SAT.writeNat n ++ encodeRelations G) = SAT.encode (snpToSat k φ (n, G)) :=
    hF' (n, G)
  have h3 := isThreeCNF_snpToSat k φ (n, G)
  obtain ⟨opt', ⟨w₀, hw₀⟩, hmax'⟩ := max3SATu_exists_opt h3
  -- no relations are better than the optimum (cut out a structure of the signature)
  have hle : ∀ S : Relations, (tuples n k).countP (fun t => φ.eval G S t) ≤ opt := fun S => by
    rw [← countP_fitRel hφ G S]
    exact (hmax (encodeRelations (fitRel sa n S)) _
      (maxSNP0_sol_iff.mpr ⟨hG, _, fits_fitRel sa n S, rfl, rfl⟩)).1 rfl
  -- no assignment is better than the optimum of the formula
  have hle' : ∀ w : Word,
      SAT.satCount (SAT.assignmentOf w) (snpToSat k φ (n, G)) ≤ opt' := fun w =>
    (hmax' w _ (max3SATu_sol_encode.mpr ⟨h3, rfl⟩)).1 rfl
  obtain ⟨-, hw₀v⟩ := max3SATu_sol_encode.mp hw₀
  have hup := satCount_snpToSat_le k φ n G w₀
  have hup' := hle (satToSnp k φ (n, G) w₀)
  obtain ⟨w₁, hw₁⟩ := exists_satCount_snpToSat k φ n G S₀
  have hw₁' := hle' w₁
  obtain ⟨S₁, hS₁⟩ := exists_large_solution k φ n G
  have hI := length_snpToSat_le k φ n G
  have hoptI : opt' ≤ (snpToSat k φ (n, G)).length := by
    rw [hw₀v]
    exact SAT.satCount_le_length _ _
  rw [hFx]
  refine ⟨opt', ⟨⟨w₀, hw₀⟩, hmax'⟩, ?_, ?_⟩
  · calc opt' ≤ (snpToSat k φ (n, G)).length := hoptI
      _ ≤ (keptTuples k φ n G).length * 2 ^ φ.atoms.length * (φ.atoms.length + 1) := hI
      _ ≤ (2 ^ φ.atoms.length * opt) * 2 ^ φ.atoms.length * (φ.atoms.length + 1) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
          (Nat.le_trans hS₁ (Nat.mul_le_mul_left _ (hle S₁))))
      _ = 2 ^ φ.atoms.length * 2 ^ φ.atoms.length * (φ.atoms.length + 1) * opt := by
        ac_rfl
  · intro y v' hy
    obtain ⟨-, rfl⟩ := max3SATu_sol_encode.mp hy
    have hH2 : H (pairWords (SAT.writeNat n ++ encodeRelations G) y) =
        encodeRelations (fitRel sa n (satToSnp k φ (n, G) y)) := hH' (n, G) y
    refine ⟨(tuples n k).countP (fun t => φ.eval G (satToSnp k φ (n, G) y) t), ?_, ?_⟩
    · rw [hH2]
      exact maxSNP0_sol_iff.mpr ⟨hG, _, fits_fitRel sa n _, rfl, (countP_fitRel hφ G _).symm⟩
    · have h₁ := satCount_snpToSat_le k φ n G y
      have h₂ := hle (satToSnp k φ (n, G) y)
      have h₃ := hle' y
      rw [← hv₀] at hw₁
      unfold absDiff
      omega

/-- **MAX-3-SAT (with unbounded assignments) is MaxSNP-hard.** (It is not in MaxSNP, which
consists of NPO problems; `max3SAT` is, and is MaxSNP-complete: `Hardness.Final.Max3SAT`.) -/
theorem max3SATu_maxSNPHard : MaxSNPHard max3SATu :=
  fun _ ⟨_, ga, sa, k, φ, hφ, h⟩ => h.trans (lReducible_maxSNP0_max3SATu ga sa k φ hφ)

end Complexity

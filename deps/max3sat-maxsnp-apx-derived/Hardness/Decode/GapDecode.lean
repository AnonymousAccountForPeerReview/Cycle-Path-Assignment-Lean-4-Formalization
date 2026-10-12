module

public import Hardness.Decode.Round
public import Hardness.Decode.Endpoints
public import OAI.Computability.UniqueGames.PCP.TableIteration

/-!
# The decoder of the gap-amplification map

`gapDecode H F τ` turns an assignment `τ` of `gapMap H F` into an assignment of `F`:

1. `finalDecode` reads a labeling of the last table `outputTable H F` off `τ`;
2. `runDecode` applies the round decoder `roundDecode` for the rounds
   `i = iterationCount F, …, 1`, the `i`-th one going from labelings of
   `runTables H i (table F)` to labelings of `runTables H (i - 1) (table F)`;
3. `initialDecode` reads the assignment off the labeling of the initial table `table F`.

`gapDecode_satisfies`: if `τ` fails fewer than one clause in `walkLength * 40960`, then
`gapDecode H F τ` satisfies `F`.  `GapTheorem.exists_gapMap_decoder` (in
`Hardness.Decode.Main`) packages this together with the polynomial-time machine and
completeness of `GapTheorem.exists_gapMap`.

All selectors used by the stage decoders are deterministic (least maximiser / least minimiser
in the numeric order, see `Hardness.Decode.Selectors`); see `Hardness/Decode/NOTES.md` for an
index-level description.
-/

@[expose] public section

namespace OAI.UniqueGamesTheorem.Foundations.PCP.Decode

noncomputable section

open RoundTables TableIteration SpectralReturn Target

/-- One step of the backward recursion: decode the last round, then continue with `rest`. -/
def runDecodeStep (H : BaseTable) (t : GraphTables.Table) (n : Nat)
    (rest : (Fin (runTables H n t).vertices → GraphTables.Label) →
      Fin t.vertices → GraphTables.Label) :
    (Fin (runTables H (n + 1) t).vertices → GraphTables.Label) →
      Fin t.vertices → GraphTables.Label :=
  fun L => rest (roundDecode H (runTables H n t) L)

/-- Decode `n` rounds: from labelings of `runTables H n t` to labelings of `t`.
`runDecode H t 0 L = L` and
`runDecode H t (n + 1) L = runDecode H t n (roundDecode H (runTables H n t) L)`. -/
def runDecode (H : BaseTable) (t : GraphTables.Table) :
    (n : Nat) → (Fin (runTables H n t).vertices → GraphTables.Label) →
      Fin t.vertices → GraphTables.Label
  | 0 => fun L => L
  | n + 1 => runDecodeStep H t n (runDecode H t n)

theorem runTables_darts_positive (H : BaseTable) (t : GraphTables.Table) (ht : 0 < t.darts)
    (n : Nat) : 0 < (runTables H n t).darts := by
  cases n with
  | zero => exact ht
  | succ n => exact build_darts_positive H (runTables H n t)

/-- Real arithmetic of one halving step, kept free of the concrete tables. -/
theorem halving_step (r m D R c cap : ℝ) (hm : 0 < m) (hD : 0 < D) (hc : c ≤ cap)
    (hround : min (2 * (r / m)) cap * D ≤ R) (h : R < c * D) : r < c / 2 * m := by
  have hlt : min (2 * (r / m)) cap < c := lt_of_mul_lt_mul_right (lt_of_le_of_lt hround h) hD.le
  have hlt2 : 2 * (r / m) < c := by
    rcases min_lt_iff.mp hlt with h1 | h2
    · exact h1
    · exact absurd h2 (not_lt.mpr hc)
  have h3 : r / m < c / 2 := by linarith
  exact (div_lt_iff₀ hm).mp h3

theorem runDecode_zero (H : BaseTable) (t : GraphTables.Table)
    (L : Fin (runTables H 0 t).vertices → GraphTables.Label) : runDecode H t 0 L = L := rfl

theorem runDecode_succ_eq (H : BaseTable) (t : GraphTables.Table) (n : Nat) :
    runDecode H t (n + 1) = runDecodeStep H t n (runDecode H t n) := rfl

theorem runDecodeStep_apply (H : BaseTable) (t : GraphTables.Table) (n : Nat)
    (rest : (Fin (runTables H n t).vertices → GraphTables.Label) →
      Fin t.vertices → GraphTables.Label)
    (L : Fin (runTables H (n + 1) t).vertices → GraphTables.Label) :
    runDecodeStep H t n rest L = rest (roundDecode H (runTables H n t) L) := rfl

/-- The recursion equation of `runDecode`.  (It is proved through `runDecodeStep` because a
direct `rfl` makes the kernel compare `L` with `roundDecode … L` by unfolding the decoders.) -/
theorem runDecode_succ (H : BaseTable) (t : GraphTables.Table) (n : Nat)
    (L : Fin (runTables H (n + 1) t).vertices → GraphTables.Label) :
    runDecode H t (n + 1) L = runDecode H t n (roundDecode H (runTables H n t) L) := by
  rw [runDecode_succ_eq, runDecodeStep_apply]

/-- Halving: a labeling of the `n`-th table violating less than a fraction `c ≤ cap` of the
darts decodes to a labeling of `t` violating less than a fraction `c / 2 ^ n`. -/
theorem runDecode_bound (H : BaseTable)
    (certificate : SpectralCertificate (ExpanderTables.graph H) (1 / 100 : ℝ))
    (t : GraphTables.Table) (ht : 0 < t.darts) (n : Nat) :
    ∀ (L : Fin (runTables H n t).vertices → GraphTables.Label) (c : ℝ),
      c ≤ FinalConstants.cap →
      ((GraphTables.semantics (runTables H n t)).rejectionCount L : ℝ) <
        c * ((runTables H n t).darts : ℝ) →
      ((GraphTables.semantics t).rejectionCount (runDecode H t n L) : ℝ) <
        c / 2 ^ n * (t.darts : ℝ) := by
  induction n with
  | zero =>
    intro L c _ h
    rw [pow_zero, div_one, runDecode_zero]
    exact h
  | succ n ih =>
    intro L c hc h
    have hm := runTables_darts_positive H t ht n
    have hprev : ((GraphTables.semantics (runTables H n t)).rejectionCount
        (roundDecode H (runTables H n t) L) : ℝ) < c / 2 * ((runTables H n t).darts : ℝ) :=
      halving_step _ _ _ _ c FinalConstants.cap (Nat.cast_pos.mpr hm)
        (Nat.cast_pos.mpr (build_darts_positive H (runTables H n t))) hc
        (roundDecode_bound H certificate (runTables H n t) hm L) h
    have hc2 : c / 2 ≤ FinalConstants.cap := by
      have := FinalConstants.cap_positive
      rcases le_or_gt c 0 with h0 | h0
      · linarith
      · linarith
    have key := ih (roundDecode H (runTables H n t) L) (c / 2) hc2 hprev
    have e : c / 2 / 2 ^ n = c / 2 ^ (n + 1) := by rw [pow_succ]; ring
    rw [e] at key
    rw [runDecode_succ]
    exact key

/-- Arithmetic at the final stage, kept free of the concrete tables: failing fewer than one
clause in `W * 40960` gives a violated fraction below `1 / W` in the last table. -/
theorem final_start (W failed clauses darts rej : Nat) (hW : 0 < W)
    (hclauses : clauses = darts * 40960) (hτ : (W * 40960) * failed < clauses)
    (hfinal : rej ≤ failed) : (rej : ℝ) < 1 / (W : ℝ) * (darts : ℝ) := by
  subst hclauses
  have h1 : W * failed < darts := by
    have : (W * failed) * 40960 < darts * 40960 := by
      calc _ = (W * 40960) * failed := by ring
        _ < _ := hτ
    exact Nat.lt_of_mul_lt_mul_right this
  have h2 : W * rej < darts := lt_of_le_of_lt (Nat.mul_le_mul_left _ hfinal) h1
  have hWr : (0 : ℝ) < (W : ℝ) := Nat.cast_pos.mpr hW
  have h2r : (W : ℝ) * (rej : ℝ) < (darts : ℝ) := by exact_mod_cast h2
  rw [one_div_mul_eq_div, lt_div_iff₀ hWr, mul_comm]
  exact h2r

/-- Arithmetic at the initial stage, kept free of the concrete tables: a violated fraction
below `cap / 2 ^ k` with `darts < 2 ^ k` and `cap ≤ 1` means no violated dart. -/
theorem initial_end (rej darts k : Nat) (cap : ℝ) (hcap : cap ≤ 1) (hsize : darts < 2 ^ k)
    (hend : (rej : ℝ) < cap / 2 ^ k * (darts : ℝ)) : rej = 0 := by
  have hpow : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have hsizer : (darts : ℝ) < (2 : ℝ) ^ k := by exact_mod_cast hsize
  have hd0 : (0 : ℝ) ≤ (darts : ℝ) := Nat.cast_nonneg _
  have hlt1 : (rej : ℝ) < 1 := by
    refine lt_of_lt_of_le hend ?_
    calc cap / 2 ^ k * (darts : ℝ) ≤ 1 / 2 ^ k * (darts : ℝ) :=
          mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hcap hpow.le) hd0
      _ ≤ 1 := by
          rw [one_div_mul_eq_div, div_le_one hpow]
          exact hsizer.le
  have : rej < 1 := by exact_mod_cast hlt1
  omega

/-- The decoder of the gap map: from assignments of `gapMap H F` to assignments of `F`. -/
def gapDecode (H : BaseTable) (F : Formula) (τ : Fin (gapMap H F).variables → Bool) :
    Fin F.variables → Bool :=
  initialDecode F
    (runDecode H (RawInitialTables.table F) (iterationCount F)
      (finalDecode (outputTable H F) τ))

/-- Constructive, pointwise soundness of the gap map: an assignment of `gapMap H F` failing
fewer than one clause in `walkLength * 40960` decodes to a satisfying assignment of `F`. -/
theorem gapDecode_satisfies (H : BaseTable)
    (certificate : SpectralCertificate (ExpanderTables.graph H) (1 / 100 : ℝ))
    (F : Formula) (τ : Fin (gapMap H F).variables → Bool)
    (hτ : (FinalConstants.walkLength * 40960) * NameCompaction.failedCount (gapMap H F) τ
            < (gapMap H F).clauses.length) :
    ∀ cl ∈ F.clauses, cl.eval (gapDecode H F τ) = true := by
  apply initialDecode_satisfies
  have ht : 0 < (RawInitialTables.table F).darts := RawInitialTables.table_darts_positive F
  have hfinal := finalDecode_bound (outputTable H F) τ
  have hclauses : (gapMap H F).clauses.length = (outputTable H F).darts * 40960 :=
    FinalTableFormula.clause_count (outputTable H F)
  have hstart : ((GraphTables.semantics (runTables H (iterationCount F)
      (RawInitialTables.table F))).rejectionCount (finalDecode (outputTable H F) τ) : ℝ) <
      FinalConstants.cap *
        ((runTables H (iterationCount F) (RawInitialTables.table F)).darts : ℝ) :=
    final_start _ _ _ _ _ FinalConstants.walkLength_positive hclauses hτ hfinal
  have hend := runDecode_bound H certificate (RawInitialTables.table F) ht (iterationCount F)
    (finalDecode (outputTable H F) τ) FinalConstants.cap le_rfl hstart
  have hsize : (RawInitialTables.table F).darts < 2 ^ iterationCount F :=
    lt_of_le_of_lt (Nat.le_add_left _ _)
      (AmplificationIteration.rounds_large (size (initial F)))
  exact initial_end _ _ _ _ FinalConstants.cap_le_one hsize hend

end

end OAI.UniqueGamesTheorem.Foundations.PCP.Decode

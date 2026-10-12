module

public import Runtimes.BoundedCost.PathRestore
public import Runtimes.BoundedCost.OccurrenceTables
import Mathlib.Tactic

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 STACS2027.RAM Complexity.SAT

def maskWords (rows : List (Bool × Clause)) : List ℕ :=
  rows.map fun row => if row.1 then 1 else 0

def forcedWords (n : ℕ) (forced : ℕ → Bool) : List ℕ :=
  List.ofFn fun u : Fin (2 * n) => if forced u.val then 1 else 0

@[simp] theorem maskWords_length (rows : List (Bool × Clause)) :
    (maskWords rows).length = rows.length := by simp [maskWords]

@[simp] theorem forcedWords_length (n : ℕ) (forced : ℕ → Bool) :
    (forcedWords n forced).length = 2 * n := by simp [forcedWords]

theorem MaskTable.array {memory : ℕ → ℕ} {base : ℕ} {rows : List (Bool × Clause)}
    (h : MaskTable memory base rows) : Arr memory base (maskWords rows) := by
  intro i hi
  have hi' : i < rows.length := by simpa using hi
  simpa [maskWords] using h i hi'

theorem ForcedTable.array {memory : ℕ → ℕ} {base n : ℕ} {forced : ℕ → Bool}
    (h : ForcedTable memory base n forced) : Arr memory base (forcedWords n forced) := by
  intro i hi
  have hi' : i < 2 * n := by simpa using hi
  simpa [forcedWords] using h i hi'

def PathRestoreMemoryFrame (active forced count n a : ℕ) : Prop :=
  OutsideCells active count a ∧ OutsideCells forced (2 * n) a

/-- The copied occurrence and requirement snapshots give their exact dense
tables; all other memory cells retain their former values. -/
theorem pathRestore_tables (memory : ℕ → ℕ) (active forced n : ℕ)
    (rows : List (Bool × Clause)) (bits : ℕ → Bool)
    (hsep : active + rows.length ≤ forced ∨ forced + 2 * n ≤ active) :
    let next := PathRestore.restoredMemory memory active forced (maskWords rows) (forcedWords n bits)
    MaskTable next active rows ∧ ForcedTable next forced n bits ∧
      SameOn (PathRestoreMemoryFrame active forced rows.length n) memory next := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    dsimp only [PathRestore.restoredMemory]
    rw [ArrayBlocks.prefixMemory_outside (by simpa using
      (show active + i < forced ∨ forced + 2 * n ≤ active + i by rcases hsep with h | h <;> omega))]
    have hget := (ArrayBlocks.prefixMemory_array memory active (maskWords rows)).getD
      (i := i) (by simpa using hi)
    simpa [maskWords, List.getD_eq_getElem?_getD, hi] using hget
  · intro u hu
    have hget := (ArrayBlocks.prefixMemory_array
      (ArrayBlocks.prefixMemory memory active (maskWords rows) (maskWords rows).length)
      forced (forcedWords n bits)).getD (i := u) (by simpa using hu)
    simpa [PathRestore.restoredMemory, forcedWords, List.getD_eq_getElem?_getD, hu] using hget
  · intro a ha
    dsimp only [PathRestore.restoredMemory]
    rw [ArrayBlocks.prefixMemory_outside (by simpa [OutsideCells] using ha.2),
      ArrayBlocks.prefixMemory_outside (by simpa [OutsideCells] using ha.1)]

theorem pathRestore_array {memory : ℕ → ℕ} {active forced n base : ℕ}
    {rows : List (Bool × Clause)} {bits : ℕ → Bool} {values : List ℕ}
    (h : Arr memory base values)
    (hframe : ∀ i < values.length,
      PathRestoreMemoryFrame active forced rows.length n (base + i)) :
    Arr (PathRestore.restoredMemory memory active forced (maskWords rows) (forcedWords n bits))
      base values := by
  intro i hi
  have ha := hframe i hi
  dsimp only [PathRestore.restoredMemory]
  rw [ArrayBlocks.prefixMemory_outside (by simpa [OutsideCells] using ha.2),
    ArrayBlocks.prefixMemory_outside (by simpa [OutsideCells] using ha.1)]
  exact h i hi

theorem pathRestore_truth {memory : ℕ → ℕ} {active forced n base : ℕ}
    {rows : List (Bool × Clause)} {bits : ℕ → Bool} {τ : Assignment}
    (h : TruthTable memory base n τ)
    (hframe : ∀ u < 2 * n,
      PathRestoreMemoryFrame active forced rows.length n (base + u)) :
    TruthTable (PathRestore.restoredMemory memory active forced (maskWords rows) (forcedWords n bits))
      base n τ := by
  intro u hu
  have ha := hframe u hu
  dsimp only [PathRestore.restoredMemory]
  rw [ArrayBlocks.prefixMemory_outside (by simpa [OutsideCells] using ha.2),
    ArrayBlocks.prefixMemory_outside (by simpa [OutsideCells] using ha.1)]
  exact h u hu

end STACS2027.Runtimes.BoundedCost

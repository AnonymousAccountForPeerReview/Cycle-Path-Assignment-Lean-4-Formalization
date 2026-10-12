module

public import Hardness.DecodeList.AlphabetDef
public import Hardness.Decode.Alphabet

/-!
# List form of the alphabet-reduction decoder: correctness

`alphaList_spec`: on the list of a labeling of `AlphabetTable.Table.build input`, the list
program `alphaList` of `Hardness/DecodeList/AlphabetDef.lean` returns the list of
`Decode.alphabetDecode hq input labeling`.

The proof translates the `Finset.card` of `codeDistance` into the `List.countP` of `alphaCount`:
the tapes `Cube (Fin q)` are transported to their ranks `r < 2 ^ q` by `Enumeration.cubeEquiv`,
the address vertex `(v, tape)` has the number `eventCount + (v * 2 ^ q + r)`
(`Enumeration.vertexEquiv_vertexAddress_val`), `blockBit` is bit `0` of its label
(`blockBit_bitValue`) and the tape of rank `r` has the bits `r / 2 ^ a % 2`
(`Enumeration.cubeUnrank_digit`).
-/

@[expose] public section

set_option linter.dupNamespace false

namespace Complexity.DecodeList

open OAI.UniqueGamesTheorem.Foundations.PCP.Decode
open OAI.UniqueGamesTheorem.Foundations.PCP
open OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable
open OAI.UniqueGamesTheorem.Foundations.Hastad

/-- The arg-min scan up to `k` only reads the counts at the indices `≤ k`. -/
theorem argMinUpTo_congr {c c' : Nat → Nat} {k : Nat} (h : ∀ i, i ≤ k → c i = c' i) :
    argMinUpTo c k = argMinUpTo c' k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have ih' := ih fun i hi => h i (Nat.le_succ_of_le hi)
    have hle := argMinUpTo_le c' k
    simp only [argMinUpTo]
    rw [ih', h (k + 1) (Nat.le_refl _), h (argMinUpTo c' k) (Nat.le_succ_of_le hle)]

private theorem if_pos' {α : Sort _} {c : Prop} [Decidable c] (hc : c) {t e : α} :
    (if c then t else e) = t := by
  simp only [hc, ↓reduceIte]

private theorem if_neg' {α : Sort _} {c : Prop} [Decidable c] (hc : ¬c) {t e : α} :
    (if c then t else e) = e := by
  simp only [hc, ↓reduceIte]

/-- Counting over `Fin n` is counting over `List.range n`. -/
theorem card_filter_fin_eq_countP (n : Nat) (p : Nat → Bool) :
    (Finset.univ.filter fun r : Fin n => p r.val = true).card = (List.range n).countP p := by
  have hrange : ∀ m : Nat,
      ((Finset.range m).filter fun r => p r = true).card = (List.range m).countP p := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [Finset.range_add_one, Finset.filter_insert, List.range_succ, List.countP_append,
        List.countP_singleton, ← ih]
      by_cases hp : p m = true
      · rw [if_pos' hp, if_pos' hp, Finset.card_insert_of_notMem]
        intro hmem
        exact absurd (Finset.mem_range.mp (Finset.mem_filter.mp hmem).1) (Nat.lt_irrefl m)
      · rw [if_neg' hp, if_neg' hp, Nat.add_zero]
  rw [← hrange, Finset.card_filter, Finset.card_filter]
  exact Fin.sum_univ_eq_sum_range (fun r => if p r = true then 1 else 0) n

/-- The count against the dictator table, at a letter `a < q`: the number of ranks `r < 2 ^ q`
at which bit `0` of `L[base + r]` differs from bit `a` of `r`. -/
theorem alphaCount_tapeTable {q : Nat} (L : List Nat) (base : Nat) {a : Nat} (ha : a < q) :
    alphaCount (tapeTable q) L base a =
      (List.range (2 ^ q)).countP fun r => decide (L.getD (base + r) 0 % 2 ≠ r / 2 ^ a % 2) := by
  unfold alphaCount tapeTable
  rw [List.countP_map]
  apply List.countP_congr
  intro r _
  have hget : ((List.range q).map fun a => r / 2 ^ a % 2).getD a 0 = r / 2 ^ a % 2 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ha]
    rfl
  simp only [Function.comp_apply, hget]

theorem alphaLocalCount_eq (q : Nat) : alphaLocalCount q = Enumeration.localCount q := by
  simp only [alphaLocalCount, Enumeration.localCount, Enumeration.tapeCount,
    Enumeration.fiveTapeCount, Enumeration.pairTapeCount]

theorem bitValue_eq_iff (b b' : Bool) :
    Enumeration.bitValue b = Enumeration.bitValue b' ↔ b = b' := by
  cases b <;> cases b' <;> simp [Enumeration.bitValue]

/-- `codeDistance` as the list count of `alphaList`. -/
theorem codeDistance_eq_alphaCount {q : Nat} (input : GenericGraphTables.Table q)
    (labeling : Fin (AlphabetTable.Table.build input).vertices → GraphTables.Label)
    (v : Fin input.vertices) (a : Fin q) :
    codeDistance input labeling v a =
      alphaCount (tapeTable q) (labelList labeling)
        (input.darts * alphaLocalCount q + v.val * 2 ^ q) a.val := by
  rw [alphaCount_tapeTable _ _ a.isLt]
  have hcount := card_filter_fin_eq_countP (Enumeration.tapeCount q) fun r =>
    decide ((labelList labeling).getD
      (input.darts * alphaLocalCount q + v.val * 2 ^ q + r) 0 % 2 ≠ r / 2 ^ a.val % 2)
  refine Eq.trans ?_ hcount
  unfold codeDistance
  refine Finset.card_equiv (Enumeration.cubeEquiv q) fun tape => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]
  have hbit := blockBit_bitValue input labeling v tape
  have hdigit := Enumeration.cubeUnrank_digit (Enumeration.cubeRank tape) a
  rw [Enumeration.cubeUnrank_cubeRank] at hdigit
  have hget := labelList_getD labeling
    (Enumeration.vertexEquiv input.vertices input.darts q (.inr (.inl (v, tape)))) 0
  rw [Enumeration.vertexEquiv_vertexAddress_val] at hget
  have hindex : input.darts * alphaLocalCount q + v.val * 2 ^ q +
      (Enumeration.cubeEquiv q tape).val =
      Enumeration.eventCount input.darts q +
        (v.val * Enumeration.tapeCount q + (Enumeration.cubeEquiv q tape).val) := by
    rw [alphaLocalCount_eq, Nat.add_assoc]
    rfl
  rw [hindex, hget, ← hbit]
  have hdigit' : (Enumeration.cubeEquiv q tape).val / 2 ^ a.val % 2 =
      Enumeration.bitValue (tape a) := hdigit.symm
  rw [hdigit', Ne, Ne, bitValue_eq_iff]

/-- **Correctness of the list form of the alphabet-reduction decoder.** -/
theorem alphaList_spec {q : Nat} (hq : 0 < q) (input : GenericGraphTables.Table q)
    (labeling : Fin (AlphabetTable.Table.build input).vertices → GraphTables.Label) :
    alphaList q input.vertices input.darts (labelList labeling) =
      labelList (alphabetDecode hq input labeling) := by
  apply List.ext_getElem
  · rw [alphaList_length, labelList_length]
  · intro i h₁ h₂
    have hi : i < input.vertices := by
      rw [labelList_length] at h₂
      exact h₂
    rw [alphaList_getElem]
    have hright : (labelList (alphabetDecode hq input labeling))[i] =
        argMinUpTo (extendCount (codeDistance input labeling ⟨i, hi⟩)) (q - 1) := by
      simp only [labelList, List.getElem_ofFn]
      rfl
    rw [hright]
    apply argMinUpTo_congr
    intro a ha
    have haq : a < q := Nat.lt_of_le_of_lt ha (Nat.sub_lt hq Nat.one_pos)
    rw [show extendCount (codeDistance input labeling ⟨i, hi⟩) a =
      codeDistance input labeling ⟨i, hi⟩ ⟨a, haq⟩ from extendCount_val _ ⟨a, haq⟩]
    exact (codeDistance_eq_alphaCount input labeling ⟨i, hi⟩ ⟨a, haq⟩).symm

end Complexity.DecodeList

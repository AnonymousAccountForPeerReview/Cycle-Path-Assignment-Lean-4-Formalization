module

public import Runtimes.BoundedCost.Iterative
public import Runtimes.BoundedCost.Contraction
import Mathlib.Tactic

/-!
# Operational call counts for the Almost 2-SAT search

The counters follow the executable search's short-circuit choices.  They
count least-cut calls and compression-branch visits, separately from the
RAM cost of each call and the formula scans.
-/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 Complexity.SAT

/-- The maximum number of nodes in a ternary tree of the given depth. -/
def searchNodeBound : ℕ → ℕ
  | 0 => 0
  | n + 1 => 1 + 3 * searchNodeBound n

theorem searchNodeBound_identity (n : ℕ) : 2 * searchNodeBound n + 1 = 3 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [searchNodeBound, pow_succ]
    omega

theorem searchNodeBound_le (n : ℕ) : searchNodeBound n ≤ 3 ^ n := by
  have := searchNodeBound_identity n
  omega

/-- Number of least-cut calls made by the short-circuit search. -/
def annotatedSearchCalls (cut : LeastCutOperation) (τ : Assignment) :
    ℕ → CNF → List Literal → ℕ → ℕ
  | 0, _, _, _ => 0
  | fuel + 1, f, L, k =>
      match cut f L with
      | none => 1
      | some δ =>
          if unsatisfiedCount δ f ≤ k then 1
          else if k < cutCost τ δ f then 1
          else match findCutConflict τ δ f with
            | some [a, b] =>
                let deleted := if k = 0 then none else annotatedSearch cut τ fuel (f.erase [a, b]) L (k - 1)
                let deleteCalls := if k = 0 then 0 else annotatedSearchCalls cut τ fuel (f.erase [a, b]) L (k - 1)
                1 + deleteCalls + if deleted.isSome then 0 else
                  annotatedSearchCalls cut τ fuel f (a :: L) k +
                    if (annotatedSearch cut τ fuel f (a :: L) k).isSome then 0 else
                      annotatedSearchCalls cut τ fuel f (b :: L) k
            | _ => 1

theorem annotatedSearchCalls_le (cut : LeastCutOperation) (τ : Assignment) :
    ∀ fuel f L k, annotatedSearchCalls cut τ fuel f L k ≤ searchNodeBound fuel := by
  intro fuel
  induction fuel with
  | zero => intro f L k; rfl
  | succ fuel ih =>
    intro f L k
    have hnonneg : 1 ≤ searchNodeBound (fuel + 1) := by simp [searchNodeBound]
    cases hd : cut f L with
    | none => simpa [annotatedSearchCalls, hd] using hnonneg
    | some δ =>
      by_cases hs : unsatisfiedCount δ f ≤ k
      · simpa [annotatedSearchCalls, hd, hs] using hnonneg
      · by_cases hb : k < cutCost τ δ f
        · simpa [annotatedSearchCalls, hd, hs, hb] using hnonneg
        · cases hc : findCutConflict τ δ f with
          | none => simpa [annotatedSearchCalls, hd, hs, hb, hc] using hnonneg
          | some c =>
            cases c with
            | nil => simpa [annotatedSearchCalls, hd, hs, hb, hc] using hnonneg
            | cons a c =>
              cases c with
              | nil => simpa [annotatedSearchCalls, hd, hs, hb, hc] using hnonneg
              | cons b c =>
                cases c with
                | cons x c => simpa [annotatedSearchCalls, hd, hs, hb, hc] using hnonneg
                | nil =>
                  by_cases hk : k = 0
                  · subst k
                    have ha := ih f (a :: L) 0
                    have hb' := ih f (b :: L) 0
                    simp only [annotatedSearchCalls, hd, hs, hb, hc, ↓reduceIte,
                      Option.isSome_none, Bool.false_eq_true, searchNodeBound, Nat.add_zero]
                    split <;> omega
                  · have hdel := ih (f.erase [a, b]) L (k - 1)
                    have ha := ih f (a :: L) k
                    have hb' := ih f (b :: L) k
                    simp only [annotatedSearchCalls, hd, hs, hb, hc, hk, ↓reduceIte, searchNodeBound]
                    split <;> (try split) <;> omega

/-- Number of compression-branch visits plus their least-cut calls. -/
def tryCompressionCalls (cut : LeastCutOperation) (τ : Assignment) (base : CNF) (k : ℕ) :
    List CompressionBranch → ℕ
  | [] => 0
  | r :: rs =>
      if r.1 ≤ k then
        1 + annotatedSearchCalls cut τ (k - r.1 + 1) base r.2 (k - r.1) +
          if (annotatedSearch cut τ (k - r.1 + 1) base r.2 (k - r.1)).isSome then 0
          else tryCompressionCalls cut τ base k rs
      else 1 + tryCompressionCalls cut τ base k rs

theorem tryCompressionCalls_le (cut : LeastCutOperation) (τ : Assignment) (base : CNF) (k : ℕ) :
    ∀ rs, tryCompressionCalls cut τ base k rs ≤ rs.length * (1 + 3 ^ (k + 1)) := by
  intro rs
  induction rs with
  | nil => simp [tryCompressionCalls]
  | cons r rs ih =>
    have hs := (annotatedSearchCalls_le cut τ (k - r.1 + 1) base r.2 (k - r.1)).trans
      (searchNodeBound_le _)
    have hp : 3 ^ (k - r.1 + 1) ≤ 3 ^ (k + 1) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have hsp := hs.trans hp
    simp only [tryCompressionCalls, List.length_cons]
    split
    · split <;> nlinarith
    · nlinarith

def compressionSearchCalls (cut : LeastCutOperation) (τ : Assignment)
    (base special : CNF) (k : ℕ) : ℕ :=
  tryCompressionCalls cut τ base k (compressionBranches special)

theorem compressionSearchCalls_le (cut : LeastCutOperation) (τ : Assignment)
    (base : CNF) {special : CNF} (hs : Clauses2 special) {k : ℕ}
    (hlen : special.length ≤ k + 1) :
    compressionSearchCalls cut τ base special k ≤ 18 * 15 ^ k := by
  have hw := tryCompressionCalls_le cut τ base k (compressionBranches special)
  rw [compressionBranches_length hs] at hw
  have hp : 3 ^ special.length ≤ 3 ^ (k + 1) := Nat.pow_le_pow_right (by decide) hlen
  have hone : 1 ≤ 3 ^ (k + 1) := Nat.one_le_pow _ _ (by decide)
  have hmul : 3 ^ k * 3 ^ k = 9 ^ k := by rw [← mul_pow]; norm_num
  have hpow : 9 ^ k ≤ 15 ^ k := Nat.pow_le_pow_left (by decide : 9 ≤ 15) k
  change tryCompressionCalls cut τ base k (compressionBranches special) ≤ _
  have hquad : 3 ^ (k + 1) * (1 + 3 ^ (k + 1)) ≤ 18 * 9 ^ k := by
    rw [pow_succ]
    nlinarith
  exact hw.trans ((Nat.mul_le_mul_right _ hp).trans (hquad.trans (Nat.mul_le_mul_left _ hpow)))

/-- Number of prefix visits and compression calls in the executable search. -/
def iterativeSearchCalls (factory : LeastCutFactory) (k : ℕ) :
    CNF → Assignment → CNF → ℕ
  | _, _, [] => 0
  | processed, σ, c :: rest =>
      if unsatisfiedCount σ (processed ++ [c]) ≤ k then
        1 + iterativeSearchCalls factory k (processed ++ [c]) σ rest
      else
        compressionSearchCalls (factory σ) σ (compressionBase σ processed)
            (compressionSpecial σ processed c) k + 1 +
          match compressionSearch (factory σ) σ (compressionBase σ processed)
              (compressionSpecial σ processed c) k with
          | none => 0
          | some δ => iterativeSearchCalls factory k (processed ++ [c]) δ rest

theorem iterativeSearchCalls_le (factory : LeastCutFactory)
    (hfactory : LeastCutFactoryCorrect factory) (k : ℕ) :
    ∀ rest processed σ, Clauses2 (processed ++ rest) → unsatisfiedCount σ processed ≤ k →
      iterativeSearchCalls factory k processed σ rest ≤ rest.length * (1 + 18 * 15 ^ k) := by
  intro rest
  induction rest with
  | nil => intro processed σ _ _; simp [iterativeSearchCalls]
  | cons c rest ih =>
    intro processed σ hf hσ
    have hpre : Clauses2 processed := fun d hd => hf d (by simp [hd])
    have hc : c.length = 2 := hf c (by simp)
    have hnext : Clauses2 ((processed ++ [c]) ++ rest) := by
      simpa [List.append_assoc] using hf
    have hspecial := compressionSpecial_clauses2 hpre hc σ
    have hlen : (compressionSpecial σ processed c).length ≤ k + 1 := by
      rw [compressionSpecial_length]
      omega
    have hw := compressionSearchCalls_le (factory σ) σ (compressionBase σ processed) hspecial hlen
    by_cases hs : unsatisfiedCount σ (processed ++ [c]) ≤ k
    · have hi := ih (processed ++ [c]) σ hnext hs
      simp only [iterativeSearchCalls, hs, ↓reduceIte, List.length_cons]
      nlinarith
    · cases hd : compressionSearch (factory σ) σ (compressionBase σ processed)
          (compressionSpecial σ processed c) k with
      | none =>
        simp only [iterativeSearchCalls, hs, ↓reduceIte, hd, List.length_cons]
        nlinarith
      | some δ =>
        have hδ := compressionSearch_sound (factory σ) σ (hfactory σ)
          (compressionBase_clauses2 hpre σ) hspecial (compressionBase_satisfied σ processed) hd
        rw [unsatisfiedCount_perm (compression_partition_perm σ processed c) δ] at hδ
        have hi := ih (processed ++ [c]) δ hnext hδ
        simp only [iterativeSearchCalls, hs, ↓reduceIte, hd, List.length_cons]
        nlinarith

def almostTwoSatSearchCalls (factory : LeastCutFactory) (f : CNF) (k : ℕ) : ℕ :=
  iterativeSearchCalls factory k [] (fun _ => false) f

theorem almostTwoSatSearchCalls_le (factory : LeastCutFactory)
    (hfactory : LeastCutFactoryCorrect factory) {f : CNF} (hf : Clauses2 f) (k : ℕ) :
    almostTwoSatSearchCalls factory f k ≤ 19 * 15 ^ k * f.length := by
  have hw := iterativeSearchCalls_le factory hfactory k f [] (fun _ => false)
    (by simpa using hf) (by simp)
  have hp : 1 ≤ 15 ^ k := Nat.one_le_pow _ _ (by decide)
  change iterativeSearchCalls factory k [] (fun _ => false) f ≤ _
  nlinarith

/-- The compiler may traverse every ternary word instead of maintaining a DFS
stack.  The additional path-length factor is the budget factor in `FPTBound`. -/
theorem compressionPathWork_le (k : ℕ) :
    3 ^ (k + 1) * 3 ^ (k + 1) * (k + 1) ≤ 9 * 15 ^ k * (k + 1) := by
  have hm : 3 ^ k * 3 ^ k = 9 ^ k := by rw [← mul_pow]; norm_num
  have hp : 9 ^ k ≤ 15 ^ k := Nat.pow_le_pow_left (by decide : 9 ≤ 15) k
  rw [pow_succ]
  nlinarith

end STACS2027.Runtimes.BoundedCost

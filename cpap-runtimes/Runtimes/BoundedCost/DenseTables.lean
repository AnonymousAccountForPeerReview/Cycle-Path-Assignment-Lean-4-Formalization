module

public import Runtimes.BoundedCost.CertificateRAM
public import Runtimes.BoundedCost.SearchScan
import Mathlib.Tactic

/-! Original formula codes and dense dual truth tables reconstruct the precise
clause-occurrence semantics used by the search and certificate programs. -/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 STACS2027.RAM Complexity.SAT

def TruthTable (memory : ℕ → ℕ) (base n : ℕ) (σ : Assignment) : Prop :=
  ∀ u, u < 2 * n → memory (base + u) = (if TwoSat.nodeVal σ u then 1 else 0)

theorem codes_clause_pair {n : ℕ} {f : CNF} (hf : TwoSat.IsTwoCNF n f)
    (i : ℕ) (hi : i < f.length) :
    ∃ a b : Literal, f[i] = [a, b] ∧ a.var < n ∧ b.var < n ∧
      (TwoSat.codes f).getD (2 * i) 0 = TwoSat.code a ∧
      (TwoSat.codes f).getD (2 * i + 1) 0 = TwoSat.code b := by
  induction f generalizing i with
  | nil => simp at hi
  | cons c f ih =>
    obtain ⟨a, b, rfl⟩ := TwoSat.clause_eq (c := c) hf (by simp)
    have ha := (hf [a, b] (by simp)).2 a (by simp)
    have hb := (hf [a, b] (by simp)).2 b (by simp)
    have ht : TwoSat.IsTwoCNF n f := fun d hd => hf d (by simp [hd])
    cases i with
    | zero => exact ⟨a, b, rfl, ha, hb, by simp [TwoSat.codes], by simp [TwoSat.codes]⟩
    | succ i =>
      obtain ⟨a', b', he, ha', hb', hx, hy⟩ := ih ht i (by simpa using hi)
      refine ⟨a', b', by simpa using he, ha', hb', ?_, ?_⟩
      · simpa [TwoSat.codes, show 2 * (i + 1) = (2 * i + 1) + 1 by omega] using hx
      · simpa [TwoSat.codes, show 2 * (i + 1) + 1 = (2 * i + 1 + 1) + 1 by omega] using hy

theorem clauseMemory_of_tables {n formula candidate : ℕ} {f : CNF} {σ : Assignment}
    {memory : ℕ → ℕ} (hf : TwoSat.IsTwoCNF n f)
    (hcodes : Arr memory formula (TwoSat.codes f)) (htruth : TruthTable memory candidate n σ) :
    Certificate.ClauseMemory f σ formula candidate (2 * n) memory := by
  intro i hi
  obtain ⟨a, b, he, ha, hb, hx, hy⟩ := codes_clause_pair hf i hi
  have hlen := TwoSat.length_codes hf
  have hx' := hcodes.getD (i := 2 * i) (by rw [hlen]; omega)
  have hy' := hcodes.getD (i := 2 * i + 1) (by rw [hlen]; omega)
  have hta := htruth (TwoSat.code a) (TwoSat.code_lt ha)
  have htb := htruth (TwoSat.code b) (TwoSat.code_lt hb)
  refine ⟨a, b, he, TwoSat.code_lt ha, TwoSat.code_lt hb, hx'.trans hx, ?_, ?_, ?_⟩
  · simpa only [Nat.add_assoc] using hy'.trans hy
  · simpa only [TwoSat.nodeVal_code] using hta
  · simpa only [TwoSat.nodeVal_code] using htb

theorem truthTable_positive {n base : ℕ} {memory : ℕ → ℕ} {σ : Assignment}
    (h : TruthTable memory base n σ) (x : ℕ) (hx : x < n) :
    memory (base + 2 * x) = (if σ x then 1 else 0) := by
  simpa only [TwoSat.nodeVal_even] using h (2 * x) (by omega)

theorem truthTable_negative {n base : ℕ} {memory : ℕ → ℕ} {σ : Assignment}
    (h : TruthTable memory base n σ) (x : ℕ) (hx : x < n) :
    memory (base + 2 * x + 1) = (if !(σ x) then 1 else 0) := by
  simpa only [TwoSat.nodeVal_odd, Nat.add_assoc] using h (2 * x + 1) (by omega)

end STACS2027.Runtimes.BoundedCost

module

public import Runtimes.BoundedCost.Contraction
public import Outerplanar.RAM.BoundedLib
public import Outerplanar.RAM.Layout
import Mathlib.Tactic

/-! # Linear RAM decoding of a contracted cut into a dual truth table

The region bits are stored at stride four, as produced by a reusable separator
call. All input regions are preserved. Artifact date: 2026-10-12.
-/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost.CandidateDecode

open STACS2027 STACS2027.RAM Complexity.SAT

abbrev candidateBase : ℕ := 203
abbrev referenceBase : ℕ := 204
abbrev variableCount : ℕ := 220
abbrev labelBase : ℕ := 223
abbrev regionBase : ℕ := 350
abbrev index : ℕ := 360
abbrev codeIndex : ℕ := 361
abbrev node : ℕ := 362
abbrev regionOffset : ℕ := 363
abbrev regionValue : ℕ := 364
abbrev referenceValue : ℕ := 365
abbrev positiveValue : ℕ := 366
abbrev negativeValue : ℕ := 367
abbrev oddIndex : ℕ := 368
abbrev one : ℕ := 369

def body : Stmt :=
  .seq (.add codeIndex index index)
  (.seq (ld node labelBase codeIndex)
  (.seq (.add regionOffset node node)
  (.seq (.add regionOffset regionOffset regionOffset)
  (.seq (ld regionValue regionBase regionOffset)
  (.seq (ld referenceValue referenceBase codeIndex)
  (.seq (.ifz regionValue
    (.seq (.const one 1) (.sub positiveValue one referenceValue))
    (mov positiveValue referenceValue))
  (.seq (st candidateBase codeIndex positiveValue)
  (.seq (addc oddIndex codeIndex 1)
  (.seq (.const one 1)
  (.seq (.sub negativeValue one positiveValue)
    (st candidateBase oddIndex negativeValue)))))))))))

def program : Stmt := forUp index variableCount body

def decoded (τ : Assignment) (label : ℕ → ℕ) (region : ℕ → Bool) : Assignment :=
  assignmentOfRegion τ (fun x => region (label x))

theorem decoded_contracted (τ : Assignment) (L : List Literal) (region : ℕ → Bool) :
    decoded τ (contractVariable τ L) region =
      assignmentOfRegion τ (liftContractRegion τ L region) := rfl

def bit (b : Bool) : ℕ := if b then 1 else 0

def prefixMemory (memory : ℕ → ℕ) (base : ℕ) (σ : Assignment) (j : ℕ) : ℕ → ℕ :=
  fun a => if base ≤ a ∧ a < base + 2 * j
    then bit (TwoSat.nodeVal σ (a - base)) else memory a

@[simp] theorem prefixMemory_zero (memory : ℕ → ℕ) (base : ℕ) (σ : Assignment) :
    prefixMemory memory base σ 0 = memory := by
  funext a
  simp [prefixMemory]

theorem prefixMemory_outside {memory : ℕ → ℕ} {base j a : ℕ} {σ : Assignment}
    (h : a < base ∨ base + 2 * j ≤ a) : prefixMemory memory base σ j a = memory a := by
  simp [prefixMemory]
  omega

theorem prefixMemory_succ (memory : ℕ → ℕ) (base : ℕ) (σ : Assignment) (j : ℕ) :
    upd (upd (prefixMemory memory base σ j) (base + 2 * j) (bit (σ j)))
      (base + 2 * j + 1) (bit (!(σ j))) = prefixMemory memory base σ (j + 1) := by
  funext a
  by_cases hp : a = base + 2 * j
  · subst a
    simp [prefixMemory, bit, TwoSat.nodeVal_even]
  by_cases hn : a = base + 2 * j + 1
  · subst a
    have hsub : base + 2 * j + 1 - base = 2 * j + 1 := by omega
    simp [prefixMemory, bit, hsub, TwoSat.nodeVal_odd,
      show base ≤ base + 2 * j + 1 by omega,
      show base + 2 * j + 1 < base + 2 * (j + 1) by omega]
  simp only [upd_apply, hp, hn, ↓reduceIte]
  have hiff : (base ≤ a ∧ a < base + 2 * (j + 1)) ↔
      (base ≤ a ∧ a < base + 2 * j) := by omega
  simp only [prefixMemory, hiff]

def Globals (candidate reference labels region n : ℕ) (c : Config) : Prop :=
  c.reg candidateBase = candidate ∧ c.reg referenceBase = reference ∧
    c.reg labelBase = labels ∧ c.reg regionBase = region ∧ c.reg variableCount = n

def Inv (candidate reference labels region n : ℕ) (memory : ℕ → ℕ)
    (τ : Assignment) (label : ℕ → ℕ) (bits : ℕ → Bool) (O : List ℕ)
    (j : ℕ) (c : Config) : Prop :=
  Globals candidate reference labels region n c ∧
    c.mem = prefixMemory memory candidate (decoded τ label bits) j ∧ c.out = O

/-- Three disjoint input regions: dual labels, reference truth values and strided
cut bits. The output table is the only memory region changed. -/
def Separated (candidate reference labels region n nodes : ℕ) : Prop :=
  (candidate + 2 * n ≤ reference ∨ reference + 2 * n ≤ candidate) ∧
    (candidate + 2 * n ≤ labels ∨ labels + 2 * n ≤ candidate) ∧
    (candidate + 2 * n ≤ region ∨ region + 4 * nodes ≤ candidate)

theorem body_spec {S candidate reference labels region n nodes j : ℕ}
    {memory : ℕ → ℕ} {τ : Assignment} {label : ℕ → ℕ} {bits : ℕ → Bool}
    {O : List ℕ}
    (hlabel : ∀ x, x < n → label x < nodes ∧ memory (labels + 2 * x) = label x)
    (href : ∀ x, x < n → memory (reference + 2 * x) = bit (τ x))
    (hbits : ∀ x, x < nodes → memory (region + 4 * x) = bit (bits x))
    (hsep : Separated candidate reference labels region n nodes)
    (hS : candidate + 2 * n ≤ S ∧ reference + 2 * n ≤ S ∧
      labels + 2 * n ≤ S ∧ region + 4 * nodes ≤ S) (hj : j < n) :
    HTB S body
      (fun c => Inv candidate reference labels region n memory τ label bits O j c ∧
        c.reg index = j ∧ c.reg variableCount = n)
      (fun c => Inv candidate reference labels region n memory τ label bits O (j + 1) c ∧
        c.reg index = j ∧ c.reg variableCount = n) 40 := by
  refine HTB.run_le (by decide) (by decide) ?_
  rintro c ⟨⟨hg, hm, ho⟩, hi, _⟩
  obtain ⟨hcan, hreference, hlabels, hregion, hn⟩ := hg
  obtain ⟨hlabBound, hlab⟩ := hlabel j hj
  have hreadLabels : c.mem (labels + (j + j)) = label j := by
    rw [hm, prefixMemory_outside (by rcases hsep.2.1 with h | h <;> omega)]
    simpa [Nat.two_mul] using hlab
  have hreadReference : c.mem (reference + (j + j)) = bit (τ j) := by
    rw [hm, prefixMemory_outside (by rcases hsep.1 with h | h <;> omega)]
    simpa [Nat.two_mul] using href j hj
  have hreadBits : c.mem (region + (label j + label j + (label j + label j))) =
      bit (bits (label j)) := by
    rw [hm, prefixMemory_outside (by rcases hsep.2.2 with h | h <;> omega)]
    rw [show label j + label j + (label j + label j) = 4 * label j by omega]
    exact hbits (label j) hlabBound
  have hreadBits' : c.mem (region + (label j + (label j + (label j + label j)))) =
      bit (bits (label j)) := by
    simpa only [Nat.add_assoc] using hreadBits
  have hg' : Globals candidate reference labels region n (run body c) := by
    have hgi : RegIndep (wregs body) (Globals candidate reference labels region n) := by
      indep [Globals, body, wregs, st, ld, mov, addc]
    exact hgi.run (by decide) ⟨hcan, hreference, hlabels, hregion, hn⟩
  have hi' : (run body c).reg index = j :=
    (run_reg_of_not_mem (by decide) (by decide) c).trans hi
  have ho' : (run body c).out = O := (run_out_of_writes (by decide) (by decide) c).trans ho
  refine ⟨?_, ⟨hg', ?_, ho'⟩, hi', hg'.2.2.2.2⟩
  · addr_ok [body, hcan, hreference, hlabels, hregion, hi, hreadLabels,
      hreadReference, hreadBits]
  · rw [← prefixMemory_succ]
    cases hr : bits (label j) <;> cases ht : τ j <;>
      simp +decide [body, mov, addc, st, bit, hi, hcan, hreference, hlabels, hregion,
        hreadLabels, hreadReference, hreadBits', hr, ht, decoded, assignmentOfRegion, hm,
        Nat.two_mul, Nat.add_assoc]

/-- A single fixed program decodes all variables in linear time and changes only
its dense output table. -/
theorem program_spec {S candidate reference labels region n nodes : ℕ}
    {memory : ℕ → ℕ} {τ : Assignment} {label : ℕ → ℕ} {bits : ℕ → Bool} {O : List ℕ}
    (hlabel : ∀ x, x < n → label x < nodes ∧ memory (labels + 2 * x) = label x)
    (href : ∀ x, x < n → memory (reference + 2 * x) = bit (τ x))
    (hbits : ∀ x, x < nodes → memory (region + 4 * x) = bit (bits x))
    (hsep : Separated candidate reference labels region n nodes)
    (hS : candidate + 2 * n ≤ S ∧ reference + 2 * n ≤ S ∧
      labels + 2 * n ≤ S ∧ region + 4 * nodes ≤ S) :
    HTB S program
      (fun c => Globals candidate reference labels region n c ∧ c.mem = memory ∧ c.out = O)
      (fun c => Globals candidate reference labels region n c ∧
        c.mem = prefixMemory memory candidate (decoded τ label bits) n ∧ c.out = O)
      (44 * n + 3) := by
  have h := HTB.forUpC (S := S) (i := index) (n := variableCount)
    (Inv candidate reference labels region n memory τ label bits O) 40
    (by decide) (by decide) (by decide)
    (fun _ => by indep [Inv, Globals])
    (fun _ hj => body_spec hlabel href hbits hsep hS hj)
  refine h.mono ?_ (fun _ h => h.1) (by omega)
  rintro c ⟨hg, hm, ho⟩
  exact ⟨⟨hg, by simpa using hm, ho⟩, hg.2.2.2.2⟩

theorem prefixMemory_truth {memory : ℕ → ℕ} {base n : ℕ} {σ : Assignment}
    {x : ℕ} (hx : x < n) :
    prefixMemory memory base σ n (base + 2 * x) = bit (σ x) ∧
      prefixMemory memory base σ n (base + 2 * x + 1) = bit (!(σ x)) := by
  constructor
  · simp [prefixMemory, TwoSat.nodeVal_even, show base ≤ base + 2 * x by omega,
      show base + 2 * x < base + 2 * n by omega]
  · simp [prefixMemory, show base + 2 * x + 1 - base = 2 * x + 1 by omega,
      TwoSat.nodeVal_odd, show base ≤ base + 2 * x + 1 by omega,
      show base + 2 * x + 1 < base + 2 * n by omega]

end STACS2027.Runtimes.BoundedCost.CandidateDecode

module

public import Runtimes.Flow.ReusableCall
public import Runtimes.BoundedCost.ArrayBlocks
import Mathlib.Tactic

@[expose] public section

namespace STACS2027.Runtimes.Flow

open STACS2027 STACS2027.RAM

abbrev strideIndex : ℕ := 155
abbrev strideAddress : ℕ := 159
abbrev strideValue : ℕ := 163
abbrev strideTwo : ℕ := 167
abbrev strideFour : ℕ := 171
abbrev strideZero : ℕ := 175

def StridedInput (memory : ℕ → ℕ) (input : List ℕ) : Prop :=
  ∀ i, i < input.length → memory (4 * i + 2) = input.getD i 0

def strideReady : Stmt := .seq (.const strideTwo 2)
  (.seq (.const strideFour 4) (.seq (.const strideZero 0)
  (.seq (.add callInput callSpan callSpan)
  (.seq (.add callInput callInput callInput)
  (.seq (.add callInput callInput strideFour) (.add callOutput callSpan strideZero))))))

def strideCopyBody : Stmt := .seq (.add strideAddress strideIndex strideIndex)
  (.seq (.add strideAddress strideAddress strideAddress)
  (.seq (.add strideAddress strideAddress strideTwo)
  (.seq (.load strideValue strideAddress)
  (.seq (.add strideAddress callInput strideIndex) (.store strideAddress strideValue)))))

def strideCopy : Stmt := forUp strideIndex callLength strideCopyBody
def stridedCall (program : Stmt) : Stmt := .seq strideReady (.seq strideCopy (reusableCall program))

def StrideGlobals (span length : ℕ) (c : Config) : Prop :=
  c.reg callSpan = span ∧ c.reg callLength = length ∧ c.reg callInput = 4 * span + 4 ∧
    c.reg callOutput = span ∧ c.reg strideTwo = 2

def StrideCopyInv (span : ℕ) (input : List ℕ) (memory : ℕ → ℕ) (out : List ℕ)
    (j : ℕ) (c : Config) : Prop :=
  StrideGlobals span input.length c ∧
    c.mem = BoundedCost.ArrayBlocks.prefixMemory memory (4 * span + 4) input j ∧ c.out = out

theorem strideReady_spec {S span length : ℕ} (c₀ : Config)
    (hspan : c₀.reg callSpan = span) (hlen : c₀.reg callLength = length) :
    HTB S strideReady (· = c₀)
      (fun c => StrideGlobals span length c ∧ c.mem = c₀.mem ∧ c.out = c₀.out) 7 := by
  refine HTB.run_le (by decide) (by decide) ?_
  intro c hc
  subst c
  refine ⟨AddrOK.of_memFree rfl, ?_⟩
  simp +decide [strideReady, StrideGlobals, hspan, hlen]
  omega

theorem strideCopyBody_spec {S span : ℕ} {input : List ℕ} {memory : ℕ → ℕ} {out : List ℕ}
    (hinput : StridedInput memory input) (hlen : input.length + 1 ≤ span)
    (hS : 8 * span + 8 ≤ S) (j : ℕ) (hj : j < input.length) :
    HTB S strideCopyBody
      (fun c => StrideCopyInv span input memory out j c ∧ c.reg strideIndex = j ∧ c.reg callLength = input.length)
      (fun c => StrideCopyInv span input memory out (j + 1) c ∧ c.reg strideIndex = j ∧ c.reg callLength = input.length) 6 := by
  refine HTB.run_le (by decide) (by decide) ?_
  rintro c ⟨⟨⟨hs, hl, hb, ho, htwo⟩, hm, hout⟩, hi, _⟩
  have hread : c.mem (4 * j + 2) = input.getD j 0 := by
    rw [hm, BoundedCost.ArrayBlocks.prefixMemory_outside (Or.inl (by omega))]
    exact hinput j hj
  have haddress : j + j + (j + j) + 2 = 4 * j + 2 := by omega
  refine ⟨?_, ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩
  · addr_ok [strideCopyBody, hs, hl, hb, ho, htwo, hi]
  all_goals simp +decide only [strideCopyBody, run_seq', run_add, run_load, run_store,
    setReg_reg, setReg_mem, setMem_reg, setMem_mem_upd, setReg_out, setMem_out,
    hs, hl, hb, ho, htwo, hi, haddress, hread, hm, hout, ↓reduceIte]
  · exact BoundedCost.ArrayBlocks.prefixMemory_succ memory (4 * span + 4) input j

theorem strideCopy_spec {S span : ℕ} {input : List ℕ} {memory : ℕ → ℕ} {out : List ℕ}
    (hinput : StridedInput memory input) (hlen : input.length + 1 ≤ span) (hS : 8 * span + 8 ≤ S) :
    HTB S strideCopy
      (fun c => StrideGlobals span input.length c ∧ c.mem = memory ∧ c.out = out)
      (fun c => StrideGlobals span input.length c ∧
        c.mem = BoundedCost.ArrayBlocks.prefixMemory memory (4 * span + 4) input input.length ∧ c.out = out)
      (10 * input.length + 3) := by
  have h := HTB.forUpC (S := S) (i := strideIndex) (n := callLength)
    (N := input.length) (body := strideCopyBody) (StrideCopyInv span input memory out) 6
    (by decide) (by decide) (by decide) (fun _ => by indep [StrideCopyInv, StrideGlobals])
    (fun j hj => strideCopyBody_spec hinput hlen hS j hj)
  refine h.mono ?_ (fun c hc => hc.1) (by omega)
  rintro c ⟨hg, hm, ho⟩
  exact ⟨⟨hg, by simpa [BoundedCost.ArrayBlocks.prefixMemory_zero] using hm, ho⟩, hg.2.1⟩

def StridedCallResult (program : Stmt) (span : ℕ) (c₀ : Config) (output : List ℕ) (c : Config) : Prop :=
  c.reg callCount = output.length ∧
  (∀ i, i < output.length → c.mem (4 * (span + i) + 1) = output.getD i 0) ∧
  c.out = c₀.out ∧
  (∀ r, r ∉ wregs program → c.reg (rl 0 r) = 0) ∧
  (∀ r, 180 ≤ r → r % 4 ≠ 0 → c.reg r = c₀.reg r) ∧
  (∀ a, a % 4 = 2 → a < 4 * span + 4 → c.mem a = c₀.mem a) ∧
  (∀ a, 8 * span + 8 ≤ a → c.mem a = c₀.mem a)

/-- A dynamically sized reusable call preserves its compact class-two input.
Only the current call's bound determines its workspace and running time. -/
theorem stridedCall_spec {S span steps : ℕ} (program : Stmt) (input output : List ℕ)
    (hcompute : ComputesIn program input output steps span) (htime : steps ≤ span)
    (hlen : input.length + 1 ≤ span) (hS : 8 * span + 8 ≤ S)
    (c₀ : Config) (hinput : StridedInput c₀.mem input)
    (hspan : c₀.reg callSpan = span) (hlength : c₀.reg callLength = input.length)
    (hzero : ∀ r, r ∉ wregs program → c₀.reg (rl 0 r) = 0) :
    HTB S (stridedCall program) (· = c₀) (StridedCallResult program span c₀ output)
      ((60 + (wregs program).length) * (span + 1)) := by
  intro c hc
  subst c
  have houtLength : output.length ≤ span := by
    obtain ⟨componentFinal, eComponent, hcomponentOut⟩ := hcompute
    have h := ExecB.output_length_bound eComponent
    simp only [initial, List.length_nil, zero_add] at h
    rw [hcomponentOut] at h
    exact h.trans htime
  obtain ⟨c₁, t₁, he₁, hp₁, ht₁⟩ := strideReady_spec (S := S) c₀ hspan hlength c₀ rfl
  obtain ⟨c₂, t₂, he₂, hp₂, ht₂⟩ := strideCopy_spec hinput hlen hS c₁ hp₁
  have heCopy : ExecB S (.seq strideReady strideCopy) c₀ (t₁ + t₂) c₂ := .seq he₁ he₂
  have hz₂ : ∀ r, r ∉ wregs program → c₂.reg (rl 0 r) = 0 := by
    intro r hr
    have hnot : rl 0 r ∉ wregs (.seq strideReady strideCopy) := by
      have hw : ∀ a ∈ wregs (.seq strideReady strideCopy), a % 4 ≠ 0 := by decide
      intro hmem
      exact hw _ hmem (rl_mod (by decide) r)
    exact (heCopy.reg_frame hnot).trans (hzero r hr)
  have ha₂ : Arr c₂.mem (4 * span + 4) input := by
    rw [hp₂.2.1]
    exact BoundedCost.ArrayBlocks.prefixMemory_array c₀.mem (4 * span + 4) input
  have hcall := reusableCall_spec (S := S) program input output hcompute htime (by omega)
    (4 * span + 4) span (by omega) (by omega) (by omega) c₂ ha₂
    hp₂.1.1 hp₂.1.2.2.1 hp₂.1.2.1 hp₂.1.2.2.2.1 hz₂
  obtain ⟨c₃, t₃, he₃, hp₃, ht₃⟩ := hcall c₂ rfl
  have he : ExecB S (stridedCall program) c₀ (t₁ + (t₂ + t₃)) c₃ := .seq he₁ (.seq he₂ he₃)
  refine ⟨c₃, _, he, ?_, ?_⟩
  · refine ⟨hp₃.1, hp₃.2.1, hp₃.2.2.1.trans hp₂.2.2, hp₃.2.2.2.1, ?_, ?_, ?_⟩
    · intro r hr hclass
      have hnot : r ∉ wregs (.seq strideReady strideCopy) := by
        have hw : ∀ a ∈ wregs (.seq strideReady strideCopy), a < 180 := by decide
        intro hmem
        have := hw _ hmem
        omega
      exact (hp₃.2.2.2.2.1 r (by omega) hclass).trans (heCopy.reg_frame hnot)
    · intro a hclass ha
      rw [hp₃.2.2.2.2.2 a (Or.inl (by omega)) (Or.inl (by omega)), hp₂.2.1]
      exact BoundedCost.ArrayBlocks.prefixMemory_outside (Or.inl ha)
    · intro a ha
      rw [hp₃.memory_high a (by omega) (by omega), hp₂.2.1]
      exact BoundedCost.ArrayBlocks.prefixMemory_outside (Or.inr (by omega))
  · nlinarith only [ht₁, ht₂, ht₃, hlen]

theorem StridedCallResult.input {program : Stmt} {span : ℕ} {c₀ c : Config} {input output : List ℕ}
    (h : StridedCallResult program span c₀ output c) (hlen : input.length + 1 ≤ span)
    (hinput : StridedInput c₀.mem input) : StridedInput c.mem input := by
  intro i hi
  exact (h.2.2.2.2.2.1 _ (by omega) (by omega)).trans (hinput i hi)

end STACS2027.Runtimes.Flow

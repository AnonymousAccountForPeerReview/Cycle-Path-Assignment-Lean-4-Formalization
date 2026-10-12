module

public import Runtimes.GeneralCycles.RegisterPredicates
import Mathlib.Tactic

/-! The fixed-size representative comparison callback. Artifact date: 2026-10-12. -/

@[expose] public section

namespace STACS2027.Runtimes.GeneralCycles

open STACS2027 STACS2027.RAM

abbrev acceptanceFlag : ℕ := 40
abbrev innerValidFlag : ℕ := 41
abbrev outerIndices : ℕ := 100
def outerValues (k : ℕ) : ℕ := 100 + k
def innerIndices (k : ℕ) : ℕ := 100 + 2 * k
def innerValues (k : ℕ) : ℕ := 100 + 3 * k

def bit (b : Bool) : ℕ := if b then 1 else 0

def registers (base k : ℕ) : List ℕ := (List.range k).map (base + ·)

def comparisonTest (k : ℕ) : RegTest := .both
  (sameCycleTest (registers (innerValues k) k) (registers (outerValues k) k))
  (earlierTest (registers outerIndices k) (registers (outerValues k) k)
    (registers (innerIndices k) k) (registers (innerValues k) k))

def clearCounter (k : ℕ) : Stmt :=
  .ifz innerValidFlag .skip ((comparisonTest k).clear acceptanceFlag)

@[simp] theorem regValues_registers (c : Config) (base k : ℕ) :
    regValues c (registers base k) = valuesList c base k := by
  simp [regValues, registers, valuesList, List.map_map, Function.comp_def]

theorem registers_safe (base k : ℕ) (h : 20 ≤ base) : rT ∉ registers base k := by
  simp only [registers, List.mem_map]
  rintro ⟨i, _, he⟩
  simp only [rT] at he
  omega

theorem Placed.index_labels {indices values k : ℕ} {memory : ℕ → ℕ}
    {is : List ℕ} {c : Config} (hl : is.length = k)
    (h : Placed indices values memory is c) : valuesList c indices k = is := by
  apply List.ext_getElem
  · simp [valuesList, hl]
  · intro j hj hj'
    simp only [valuesList, List.getElem_map, List.getElem_range]
    have hlt : j < is.length := by simpa [valuesList, hl] using hj
    have hv := (h j hlt).1
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt] using hv

theorem comparisonTest_safe (k : ℕ) : rT ∉ (comparisonTest k).sources := by
  simp only [comparisonTest, RegTest.sources, List.mem_append, not_or]
  refine ⟨sameCycleTest_safe _ _ (registers_safe _ _ ?_) (registers_safe _ _ ?_),
    earlierTest_safe _ _ _ _ (registers_safe _ _ ?_) (registers_safe _ _ ?_)
      (registers_safe _ _ ?_) (registers_safe _ _ ?_)⟩ <;>
    simp [outerIndices, outerValues, innerIndices, innerValues] <;> omega

theorem comparisonTest_eval (g : Graph) (k : ℕ) (outer inner : List ℕ)
    (c : Config) (ho : outer.length = k) (hi : inner.length = k)
    (houter : Placed outerIndices (outerValues k) (initial (graphInput g)).mem outer c)
    (hinner : Placed (innerIndices k) (innerValues k) (initial (graphInput g)).mem inner c) :
    (comparisonTest k).eval c = decide (SameCycle (tupleLabels g inner) (tupleLabels g outer) ∧
      Earlier g outer inner) := by
  simp only [comparisonTest, RegTest.eval, sameCycleTest_eval, earlierTest_eval,
    regValues_registers, houter.emission_labels ho, hinner.emission_labels hi,
    houter.index_labels ho, hinner.index_labels hi, Earlier]
  rfl

@[simp] theorem clearCounter_loopFree (k : ℕ) : LoopFree (clearCounter k) := by
  simp only [clearCounter, LoopFree]
  exact ⟨trivial, (comparisonTest k).branch_loopFree trivial trivial⟩

@[simp] theorem clearCounter_memFree (k : ℕ) : memFree (clearCounter k) = true := by
  simp only [clearCounter, memFree]
  exact (comparisonTest k).branch_memFree rfl rfl

@[simp] theorem clearCounter_stores (k : ℕ) : stores (clearCounter k) = false := by
  simp only [clearCounter, stores]
  exact (comparisonTest k).branch_stores rfl rfl

@[simp] theorem clearCounter_writes (k : ℕ) : writes (clearCounter k) = false := by
  simp only [clearCounter, writes]
  exact (comparisonTest k).branch_writes rfl rfl

theorem clearCounter_wregs (k r : ℕ) (h : r ∈ wregs (clearCounter k)) :
    r = rT ∨ r = acceptanceFlag := by
  simp only [clearCounter, wregs, List.nil_append, RegTest.clear] at h
  rcases (comparisonTest k).branch_wregs h with h | h | h
  · exact Or.inl h
  · exact Or.inr (List.mem_singleton.mp h)
  · simp [wregs] at h

theorem clearCounter_agree (k : ℕ) (c : Config) :
    Agree [rT, acceptanceFlag] c (run (clearCounter k) c) := by
  apply (run_frame (clearCounter_loopFree k) c).agree
      (clearCounter_stores k) (clearCounter_writes k) |>.mono
  intro r hr
  rcases clearCounter_wregs k r hr with rfl | rfl <;> simp

theorem clearCounter_value (g : Graph) (k : ℕ) (outer inner : List ℕ) (b : Bool)
    (c : Config) (ho : outer.length = k) (hi : inner.length = k)
    (houter : Placed outerIndices (outerValues k) (initial (graphInput g)).mem outer c)
    (hinner : Placed (innerIndices k) (innerValues k) (initial (graphInput g)).mem inner c)
    (hv : c.reg innerValidFlag = bit (decide (Valid g k inner)))
    (hb : c.reg acceptanceFlag = bit b) :
    (run (clearCounter k) c).reg acceptanceFlag = bit (rejectStep g k outer b inner) := by
  simp only [clearCounter, run]
  by_cases hvalid : Valid g k inner
  · simp only [hvalid, decide_true, bit, ↓reduceIte, hv, one_ne_zero]
    rw [RegTest.run_clear _ (comparisonTest_safe k) (by decide), comparisonTest_eval g k outer inner c ho hi houter hinner, hb]
    simp [rejectStep, Counterexample, hvalid, bit]
    by_cases hs : SameCycle (tupleLabels g inner) (tupleLabels g outer) <;>
      by_cases he : Earlier g outer inner <;> cases b <;> simp [hs, he]
  · simp [hv, bit, hvalid, hb, rejectStep, Counterexample]

end STACS2027.Runtimes.GeneralCycles

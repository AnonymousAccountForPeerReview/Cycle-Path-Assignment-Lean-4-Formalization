module

public import Runtimes.BoundedCost.CoreRAM
public import Runtimes.BoundedCost.Top
import Mathlib.Tactic

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 STACS2027.RAM STACS2027.Runtimes.ZeroCost

def corePrefix (g : Graph) (k : ℕ) : List ℕ :=
  graphInput (coreOccurrenceGraph g k) ++ k :: (cycles g k).length :: verts g k

theorem coreInput_eq_prefix (g : Graph) (k budget : ℕ) :
    CoreRAM.coreInput g k budget = corePrefix g k ++ [budget] := by
  simp [CoreRAM.coreInput, corePrefix, List.append_assoc]

theorem corePrefix_length (g : Graph) (k : ℕ) :
    (corePrefix g k).length = 3 * (k * (cycles g k).length) + 3 := by
  simp [corePrefix, length_graphInput, coreOccurrenceGraph_length, length_verts]
  ring

theorem offsetInput_update_last {memory : ℕ → ℕ} {base old new : ℕ} {headWords : List ℕ}
    (h : Flow.OffsetInput memory base (headWords ++ [old])) :
    Flow.OffsetInput (upd memory (4 * (base + headWords.length) + 2) new) base (headWords ++ [new]) := by
  intro i hi
  have hil : i ≤ headWords.length := by simp only [List.length_append, List.length_singleton] at hi; omega
  by_cases he : i = headWords.length
  · subst i
    simp [upd, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
  · have hi' : i < headWords.length := by omega
    have hold : i < (headWords ++ [old]).length := by simp; omega
    have hread := h i hold
    rw [show upd memory (4 * (base + headWords.length) + 2) new (4 * (base + i) + 2) =
      memory (4 * (base + i) + 2) by simp [upd, he, show 4 * (base + i) + 2 ≠ 4 * (base + headWords.length) + 2 by omega]]
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi'] using hread

theorem coreInput_update_budget {memory : ℕ → ℕ} {base old new : ℕ} {g : Graph} {k : ℕ}
    (h : Flow.OffsetInput memory base (CoreRAM.coreInput g k old)) :
    Flow.OffsetInput (upd memory (4 * (base + 3 * (k * (cycles g k).length) + 3) + 2) new)
      base (CoreRAM.coreInput g k new) := by
  rw [coreInput_eq_prefix] at h ⊢
  have hx := offsetInput_update_last (new := new) h
  simpa only [corePrefix_length, Nat.add_assoc] using hx

theorem coreAnswer_transfer (g : Graph) (k budget : ℕ) (output : List ℕ) :
    BoundedCostAnswer (coreOccurrenceGraph g k) k budget output ↔ BoundedCostAnswer g k budget output := by
  simp only [BoundedCostAnswer, coreOccurrenceGraph_hasAssignment, coreOccurrenceGraph_cycles]

theorem BoundedCostAnswer.negative {g : Graph} {k budget : ℕ} {output : List ℕ}
    (h : BoundedCostAnswer g k budget output) (hn : ¬ HasAssignment g k budget) : output = [0] := by
  rcases h with h | ⟨pos, he, hlen, hpos, hv, hc⟩
  · exact h.2
  · exact False.elim (hn ⟨_, hv, hc⟩)

theorem BoundedCostAnswer.positive {g : Graph} {k budget : ℕ} {output : List ℕ}
    (h : BoundedCostAnswer g k budget output) (hp : HasAssignment g k budget) :
    ∃ pos, output = 1 :: pos := by
  rcases h with h | ⟨pos, he, _⟩
  · exact False.elim (h.1 hp)
  · exact ⟨pos, he⟩

theorem BoundedCostAnswer.head {g : Graph} {k budget : ℕ} {output : List ℕ}
    (h : BoundedCostAnswer g k budget output) :
    output ≠ [] ∧ (output.getD 0 0 = 0 ∨ output.getD 0 0 = 1) := by
  rcases h with ⟨_, rfl⟩ | ⟨pos, rfl, _⟩ <;> simp

end STACS2027.Runtimes.BoundedCost

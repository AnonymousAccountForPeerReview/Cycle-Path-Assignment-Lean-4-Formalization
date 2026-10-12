module

public import ApproximationHardness.Embed.DFSRAM
import Mathlib.Tactic.IntervalCases
import Lean.Elab.Tactic.Omega

/-! # Memory refinement for the cached depth-first search -/

@[expose] public section

namespace STACS2027.Embed.DFSRAM

open RAM

def dsArray (s : DS) (j : Nat) : Nat → Nat :=
  if j = 6 then s.par else if j = 7 then s.depth else if j = 8 then s.ptr else s.st

def setArray (s : DS) (j a value : Nat) : DS := { s with
  par := if j = 6 then upd s.par a value else s.par
  depth := if j = 7 then upd s.depth a value else s.depth
  ptr := if j = 8 then upd s.ptr a value else s.ptr
  st := if j = 9 then upd s.st a value else s.st }

structure MemoryRep (L : Layout) (G : DG) (memory : Nat → Nat) (s : DS) : Prop where
  arrays : ∀ j, 6 ≤ j → j < 10 → ∀ v, v < 2 * G.E → memory (L.cell j v) = dsArray s j v
  post : ∀ i, i < s.post.length → memory (L.cell 10 i) = s.post.getD i 0

theorem Rep.memory {L : Layout} {G : DG} {c : Config} {s : DS} (h : Rep L G c s) :
    MemoryRep L G c.mem s := by
  constructor
  · intro j hj hk v hv
    interval_cases j
    · simpa [dsArray] using h.parents v hv
    · simpa [dsArray] using h.depths v hv
    · simpa [dsArray] using h.pointers v hv
    · simpa [dsArray] using h.states v hv
  · exact h.post

theorem array_set {j k : Nat} (s : DS) (a value v : Nat)
    (hj : 6 ≤ j) (hj' : j < 10) (hk : 6 ≤ k) (hk' : k < 10) :
    dsArray (setArray s j a value) k v =
      if k = j ∧ v = a then value else dsArray s k v := by
  interval_cases j <;> interval_cases k <;> simp [dsArray, setArray, upd]

theorem MemoryRep.update {L : Layout} {G : DG} {memory : Nat → Nat} {s : DS}
    (h : MemoryRep L G memory s) {j a value : Nat}
    (hj : 6 ≤ j) (hj' : j < 10) (ha : a < 2 * G.E)
    (hw : 2 * G.E ≤ L.width) (hpost : s.post.length ≤ L.width) :
    MemoryRep L G (upd memory (L.cell j a) value) (setArray s j a value) := by
  constructor
  · intro k hk hk' v hv
    rw [update_cell L memory k j v a value (by omega) (by omega), array_set s a value v hj hj' hk hk']
    split
    · rfl
    · exact h.arrays k hk hk' v hv
  · intro i hi
    change i < s.post.length at hi
    change upd memory (L.cell j a) value (L.cell 10 i) = s.post.getD i 0
    rw [update_cell L memory 10 j i a value (by omega) (by omega)]
    simp only [show ¬(10 = j ∧ i = a) by omega, ↓reduceIte]
    exact h.post i hi

theorem MemoryRep.push {L : Layout} {G : DG} {memory : Nat → Nat} {s : DS}
    (h : MemoryRep L G memory s) (x : Nat) (hw : 2 * G.E ≤ L.width)
    (hpost : s.post.length < L.width) :
    MemoryRep L G (upd memory (L.cell 10 s.post.length) x) {s with post := s.post ++ [x]} := by
  constructor
  · intro j hj hj' v hv
    rw [update_cell L memory j 10 v s.post.length x (by omega) hpost]
    simp only [show ¬(j = 10 ∧ v = s.post.length) by omega, ↓reduceIte]
    exact h.arrays j hj hj' v hv
  · intro i hi
    have hi' : i < s.post.length + 1 := by simpa using hi
    change upd memory (L.cell 10 s.post.length) x (L.cell 10 i) = (s.post ++ [x]).getD i 0
    rw [update_cell L memory 10 10 i s.post.length x (by omega) hpost]
    by_cases hil : i < s.post.length
    · have hne : i ≠ s.post.length := by omega
      simp only [true_and, hne, ↓reduceIte]
      rw [h.post i hil]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hil]
    · have hie : i = s.post.length := by omega
      subst i
      simp [List.getD_eq_getElem?_getD]

theorem MemoryRep.of_regs {L : Layout} {G : DG} {memory : Nat → Nat} {s : DS}
    {c : Config} (hm : MemoryRep L G memory s) (hc : c.mem = memory)
    (hb : Bases L G c) (hr : c.reg scan = s.r) (hcur : c.reg current = s.cur)
    (hi : c.reg inner = if s.inner then 1 else 0) (hH : c.reg height = s.H)
    (hp : c.reg postLength = s.post.length) : Rep L G c s := by
  refine ⟨hb, hr, hcur, hi, hH, hp, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv; rw [hc]; simpa [dsArray] using hm.arrays 6 (by decide) (by decide) v hv
  · intro v hv; rw [hc]; simpa [dsArray] using hm.arrays 7 (by decide) (by decide) v hv
  · intro v hv; rw [hc]; simpa [dsArray] using hm.arrays 8 (by decide) (by decide) v hv
  · intro v hv; rw [hc]; simpa [dsArray] using hm.arrays 9 (by decide) (by decide) v hv
  · intro i hi; rw [hc]; exact hm.post i hi

/-- A mutable cache update preserves all six graph-table blocks. -/
theorem Tables.update {L : Layout} {G : DG} {c d : Config}
    (h : Tables L G c) (j a value : Nat) (hj : 6 ≤ j) (hj' : j < 11)
    (ha : a < L.width) (hw : 2 * G.E ≤ L.width)
    (hm : d.mem = upd c.mem (L.cell j a) value) : Tables L G d := by
  constructor
  · intro i hi
    rw [hm, update_cell L c.mem 0 j i a value (by omega) ha]
    simp only [show ¬(0 = j ∧ i = a) by omega, ↓reduceIte]
    exact h.representatives i hi
  · intro i hi
    rw [hm, update_cell L c.mem 1 j i a value (by omega) ha]
    simp only [show ¬(1 = j ∧ i = a) by omega, ↓reduceIte]
    exact h.partners i hi
  · intro i hi
    rw [hm, update_cell L c.mem 2 j i a value (by omega) ha]
    simp only [show ¬(2 = j ∧ i = a) by omega, ↓reduceIte]
    exact h.degrees i hi
  · intro k hk i hi
    rw [hm, update_cell L c.mem (3 + k) j i a value (by omega) ha]
    simp only [show ¬(3 + k = j ∧ i = a) by omega, ↓reduceIte]
    exact h.adjacent k hk i hi

end STACS2027.Embed.DFSRAM

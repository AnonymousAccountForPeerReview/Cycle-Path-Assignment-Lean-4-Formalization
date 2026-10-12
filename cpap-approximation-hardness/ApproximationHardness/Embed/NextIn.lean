module

public import ApproximationHardness.Embed.FirstReturn
import Lean.Elab.Tactic.Omega

/-!
# The first dart of a set along an orbit

`nextIn p S y` is the first dart of `S` among `y, p y, p² y, …` (`y` itself if the orbit never
meets `S`). It satisfies the two defining equations `nextIn_of_mem` and `nextIn_of_not`, and the
first-return map is `firstReturn p S x = nextIn p S (p x)` on `S`. For `T ⊆ S`, walking along the
first-return map to `S` meets `T` in the same order as walking along `p`
(`nextIn_firstReturn`).
-/

@[expose] public section

namespace STACS2027.Embed

open Complexity Complexity.Planar STACS2027.PlanarGluing

variable {n : Nat}

/-- The orbit of `y` meets `S` (at a time `≥ 0`). -/
def MeetsFrom (p : Fin n → Fin n) (S : Fin n → Bool) (y : Fin n) : Prop := ∃ k, S (iterate p k y) = true

/-- The first time `≥ 0` at which the orbit of `y` meets `S` (`0` if never). -/
noncomputable def hitTime0 (p : Fin n → Fin n) (S : Fin n → Bool) (y : Fin n) : Nat :=
  open Classical in
  if h : MeetsFrom p S y then Classical.choose (exists_least h) else 0

theorem hitTime0_spec {p : Fin n → Fin n} {S : Fin n → Bool} {y : Fin n} (h : MeetsFrom p S y) :
    S (iterate p (hitTime0 p S y) y) = true ∧ ∀ k, k < hitTime0 p S y → S (iterate p k y) = false := by
  unfold hitTime0
  rw [dite_eq_left h]
  obtain ⟨h1, h2⟩ := Classical.choose_spec (exists_least h)
  refine ⟨h1, fun k hk => ?_⟩
  cases hs : S (iterate p k y)
  · rfl
  · exact absurd hs (h2 k hk)

/-- The first dart of `S` on the orbit of `y`. -/
noncomputable def nextIn (p : Fin n → Fin n) (S : Fin n → Bool) (y : Fin n) : Fin n :=
  iterate p (hitTime0 p S y) y

theorem nextIn_mem {p : Fin n → Fin n} {S : Fin n → Bool} {y : Fin n} (h : MeetsFrom p S y) :
    S (nextIn p S y) = true := (hitTime0_spec h).1

theorem hitTime0_of_mem {p : Fin n → Fin n} {S : Fin n → Bool} {y : Fin n} (hy : S y = true) :
    hitTime0 p S y = 0 := by
  have h : MeetsFrom p S y := ⟨0, hy⟩
  have := (hitTime0_spec h).2 0
  rcases Nat.eq_zero_or_pos (hitTime0 p S y) with h0 | h0
  · exact h0
  · have := this h0
    simp [iterate, hy] at this

theorem nextIn_of_mem {p : Fin n → Fin n} {S : Fin n → Bool} {y : Fin n} (hy : S y = true) :
    nextIn p S y = y := by
  unfold nextIn; rw [hitTime0_of_mem hy]; rfl

theorem meetsFrom_step {p : Fin n → Fin n} {S : Fin n → Bool} {y : Fin n} (hy : S y = false)
    (h : MeetsFrom p S y) : MeetsFrom p S (p y) := by
  obtain ⟨k, hk⟩ := h
  cases k with
  | zero => exact absurd hk (by simp [iterate, hy])
  | succ k => exact ⟨k, hk⟩

theorem iterate_succ_apply {p : Fin n → Fin n} (k : Nat) (y : Fin n) :
    iterate p (k + 1) y = iterate p k (p y) := rfl

theorem hitTime0_of_not {p : Fin n → Fin n} {S : Fin n → Bool} {y : Fin n} (hy : S y = false)
    (h : MeetsFrom p S y) : hitTime0 p S y = hitTime0 p S (p y) + 1 := by
  have h' := meetsFrom_step hy h
  obtain ⟨a1, a2⟩ := hitTime0_spec h
  obtain ⟨b1, b2⟩ := hitTime0_spec h'
  have hpos : 0 < hitTime0 p S y := by
    rcases Nat.eq_zero_or_pos (hitTime0 p S y) with h0 | h0
    · rw [h0] at a1; simp [iterate, hy] at a1
    · exact h0
  have e1 : iterate p (hitTime0 p S y) y = iterate p (hitTime0 p S y - 1) (p y) := by
    rw [← iterate_succ_apply, show hitTime0 p S y - 1 + 1 = hitTime0 p S y by omega]
  rcases Nat.lt_trichotomy (hitTime0 p S y) (hitTime0 p S (p y) + 1) with hl | he | hl
  · have := b2 (hitTime0 p S y - 1) (by omega)
    rw [← e1, a1] at this
    exact absurd this (by simp)
  · exact he
  · have := a2 (hitTime0 p S (p y) + 1) hl
    rw [iterate_succ_apply, b1] at this
    exact absurd this (by simp)

theorem nextIn_of_not {p : Fin n → Fin n} {S : Fin n → Bool} {y : Fin n} (hy : S y = false)
    (h : MeetsFrom p S y) : nextIn p S y = nextIn p S (p y) := by
  unfold nextIn
  rw [hitTime0_of_not hy h]
  rfl

theorem meetsFrom_of_perm {p : Fin n → Fin n} (_hp : ∀ a b, p a = p b → a = b) {S : Fin n → Bool}
    {x y : Fin n} (hx : S x = true) (hr : Reaches p y x) : MeetsFrom p S y := by
  obtain ⟨k, rfl⟩ := hr
  exact ⟨k, hx⟩

theorem meetsFrom_of_meets {p : Fin n → Fin n} {S : Fin n → Bool} {x : Fin n} (h : Meets p S x) :
    MeetsFrom p S (p x) := by
  obtain ⟨k, hk, hs⟩ := h
  refine ⟨k - 1, ?_⟩
  rw [← iterate_succ_apply, show k - 1 + 1 = k by omega]
  exact hs

theorem hitTime_eq_hitTime0 {p : Fin n → Fin n} {S : Fin n → Bool} {x : Fin n} (h : Meets p S x) :
    hitTime p S x = hitTime0 p S (p x) + 1 := by
  have h' := meetsFrom_of_meets h
  obtain ⟨a1, a2, a3⟩ := hitTime_spec h
  obtain ⟨b1, b2⟩ := hitTime0_spec h'
  rcases Nat.lt_trichotomy (hitTime p S x) (hitTime0 p S (p x) + 1) with hl | he | hl
  · have := b2 (hitTime p S x - 1) (by omega)
    rw [← iterate_succ_apply, show hitTime p S x - 1 + 1 = hitTime p S x by omega, a2] at this
    exact absurd this (by simp)
  · exact he
  · have := a3 (hitTime0 p S (p x) + 1) (by omega) hl
    rw [iterate_succ_apply, b1] at this
    exact absurd this (by simp)

/-- On `S`, the first-return map is the first dart of `S` after one step. -/
theorem firstReturn_eq_nextIn {p : Fin n → Fin n} (hp : ∀ a b, p a = p b → a = b) {S : Fin n → Bool}
    {x : Fin n} (hx : S x = true) : firstReturn p S x = nextIn p S (p x) := by
  rw [firstReturn_of_mem hx, hitTime_eq_hitTime0 (meets_of_perm hp S hx)]
  rfl

theorem reaches_nextIn {p : Fin n → Fin n} (S : Fin n → Bool) (y : Fin n) : Reaches p y (nextIn p S y) :=
  ⟨_, rfl⟩

/-- **Composing first darts.** For `T ⊆ S`, the first dart of `T` from `z` is the first dart of
`T` from the first dart of `S` from `z`. -/
theorem nextIn_nextIn {p : Fin n → Fin n} {S T : Fin n → Bool} (hTS : ∀ x, T x = true → S x = true)
    {z : Fin n} (hT : MeetsFrom p T z) : nextIn p T z = nextIn p T (nextIn p S z) := by
  have key : ∀ k z, hitTime0 p S z = k → MeetsFrom p T z → nextIn p T z = nextIn p T (nextIn p S z) := by
    intro k
    induction k with
    | zero =>
      intro z hk _
      unfold nextIn at *
      rw [hk]; rfl
    | succ k ih =>
      intro z hk hz
      have hzS : S z = false := by
        cases hs : S z
        · rfl
        · rw [hitTime0_of_mem hs] at hk; omega
      have hzT : T z = false := by
        cases ht : T z
        · rfl
        · rw [hTS z ht] at hzS; exact absurd hzS (by simp)
      have hSz : MeetsFrom p S z := by
        obtain ⟨j, hj⟩ := hz
        exact ⟨j, hTS _ hj⟩
      have hk' : hitTime0 p S (p z) = k := by rw [hitTime0_of_not hzS hSz] at hk; omega
      rw [nextIn_of_not hzS hSz, nextIn_of_not hzT hz]
      exact ih (p z) hk' (meetsFrom_step hzT hz)
  exact key _ z rfl hT

end STACS2027.Embed

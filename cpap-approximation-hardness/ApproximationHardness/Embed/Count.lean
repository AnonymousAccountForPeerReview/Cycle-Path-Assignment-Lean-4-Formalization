module

public import ApproximationHardness.Embed.Chord
import Lean.Elab.Tactic.Omega

/-!
# Counting lemmas for permutations

Minima of cycles through reachability; first darts and avoiding cycles of two permutations that
agree outside a set.
-/

@[expose] public section

namespace STACS2027.Embed

open Complexity Complexity.Planar STACS2027.PlanarGluing

variable {n : Nat}

theorem cycleMin_iff_reach {p : Fin n → Fin n} (hp : ∀ a b, p a = p b → a = b) (x : Fin n) :
    CycleMin p x = true ↔ ∀ y, Reaches p x y → x.val ≤ y.val := by
  constructor
  · intro h y ⟨k, hk⟩
    have := cmin_le hp x k
    rw [(cmin_eq_iff hp x).mpr h, hk] at this
    exact this
  · intro h
    apply (cmin_eq_iff hp x).mp
    apply Fin.ext
    apply Nat.le_antisymm (cmin_le_self hp x)
    obtain ⟨i, _, hi⟩ := cmin_mem (p := p) x
    exact h _ ⟨i, hi⟩

/-- Two maps agreeing outside `S` meet `S` first at the same dart. -/
theorem nextIn_congr {p q : Fin n → Fin n} {S : Fin n → Bool} (hpq : ∀ u, S u = false → p u = q u) :
    ∀ w, MeetsFrom p S w → MeetsFrom q S w ∧ nextIn p S w = nextIn q S w := by
  have key : ∀ k w, hitTime0 p S w = k → MeetsFrom p S w → MeetsFrom q S w ∧ nextIn p S w = nextIn q S w := by
    intro k
    induction k with
    | zero =>
      intro w hk hm
      have h := (hitTime0_spec hm).1
      rw [hk] at h
      have h' : S w = true := h
      exact ⟨⟨0, h'⟩, by rw [nextIn_of_mem h', nextIn_of_mem h']⟩
    | succ k ih =>
      intro w hk hm
      have hSw : S w = false := by
        cases h : S w
        · rfl
        · rw [hitTime0_of_mem h] at hk; omega
      have hk' : hitTime0 p S (p w) = k := by rw [hitTime0_of_not hSw hm] at hk; omega
      obtain ⟨hm', he⟩ := ih (p w) hk' (meetsFrom_step hSw hm)
      rw [hpq w hSw] at hm' he
      have hmq : MeetsFrom q S w := by obtain ⟨j, hj⟩ := hm'; exact ⟨j + 1, hj⟩
      refine ⟨hmq, ?_⟩
      rw [nextIn_of_not hSw hm, nextIn_of_not hSw hmq, hpq w hSw, he]
  exact fun w hm => key _ w rfl hm

/-- Iterates of two maps agreeing outside `S` agree up to the first dart of `S`. -/
theorem iterate_congr_avoid {p q : Fin n → Fin n} {S : Fin n → Bool} (hpq : ∀ u, S u = false → p u = q u)
    (z : Fin n) : ∀ k, (∀ j, j < k → S (iterate p j z) = false) → iterate p k z = iterate q k z := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro h
    rw [iterate_succ', iterate_succ', ← ih (fun j hj => h j (by omega)), hpq _ (h k (by omega))]

/-- Two permutations agreeing outside `S` have the same cycles avoiding `S`. -/
theorem avoidCount_congr {p q : Fin n → Fin n} (hp : ∀ a b, p a = p b → a = b) (hq : ∀ a b, q a = q b → a = b)
    {S : Fin n → Bool} (hpq : ∀ u, S u = false → p u = q u) : avoidCount p S = avoidCount q S := by
  unfold avoidCount
  apply countP_congr'
  intro z _
  -- does the orbit meet `S`?
  by_cases hm : ∃ k, S (iterate p k z) = true
  · obtain ⟨k, hk, hmin⟩ := exists_least hm
    have hlt : ∀ j, j < k → S (iterate p j z) = false := fun j hj => by
      cases h : S (iterate p j z)
      · rfl
      · exact absurd h (hmin j hj)
    have heq := iterate_congr_avoid hpq z k hlt
    rw [meetsB_true hp k hk, meetsB_true hq k (by rw [← heq]; exact hk)]
    simp
  · have hall : ∀ j, S (iterate p j z) = false := fun j => by
      cases h : S (iterate p j z)
      · rfl
      · exact absurd ⟨j, h⟩ hm
    have heq : ∀ k, iterate p k z = iterate q k z := fun k => iterate_congr_avoid hpq z k (fun j _ => hall j)
    have hmp : MeetsB p S z = false := meetsB_false hp hall
    have hmq : MeetsB q S z = false := meetsB_false hq (fun j => by rw [← heq]; exact hall j)
    rw [hmp, hmq]
    simp only [CycleMin, heq]

end STACS2027.Embed

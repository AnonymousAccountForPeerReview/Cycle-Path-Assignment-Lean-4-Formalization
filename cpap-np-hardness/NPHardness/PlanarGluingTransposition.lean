module

public import NPHardness.PlanarGluingCycles
import Lean.Elab.Tactic.Omega

/-!
Successor transpositions within a single finite permutation. These lemmas
count the actual split or merged orbits and are intended for graph deletion
surgery; no target Euler bound is assumed.
-/

@[expose] public section
namespace STACS2027.PlanarGluing
open Complexity Complexity.Planar

def transpose {n : Nat} (p : Fin n → Fin n) (a b x : Fin n) : Fin n := p (swap a b x)

theorem transpose_injective {n : Nat} {p : Fin n → Fin n}
    (hp : ∀ x y, p x = p y → x = y) (a b : Fin n) :
    ∀ x y, transpose p a b x = transpose p a b y → x = y := by
  intro x y h
  exact swap_injective a b (hp _ _ h)

theorem transpose_twice {n : Nat} (p : Fin n → Fin n) (a b : Fin n) :
    transpose (transpose p a b) a b = p := by
  funext x; simp only [transpose, swap_swap]

theorem transpose_a {n : Nat} (p : Fin n → Fin n) (a b : Fin n) : transpose p a b a = p b := by
  simp [transpose, swap]

theorem transpose_b {n : Nat} (p : Fin n → Fin n) {a b : Fin n} (hab : a ≠ b) :
    transpose p a b b = p a := by simp [transpose, swap, Ne.symm hab]

theorem transpose_other {n : Nat} (p : Fin n → Fin n) {a b x : Fin n}
    (ha : x ≠ a) (hb : x ≠ b) : transpose p a b x = p x := by simp [transpose, swap, ha, hb]

theorem reaches_until_invariant {α : Type} (p q : α → α) (P : α → Prop) (a : α)
    (hP : ∀ x, P x → P (p x)) (hstep : ∀ x, P x → x ≠ a → q x = p x)
    (k : Nat) (x : α) (hx : P x) (hk : iterate p k x = a) : Reaches q x a := by
  induction k generalizing x with
  | zero => exact ⟨0, hk⟩
  | succ k ih =>
    by_cases hxa : x = a
    · subst x; exact Reaches.refl _ _
    · exact (show Reaches q x (p x) from ⟨1, hstep x hx hxa⟩).trans
        (ih (p x) (hP x hx) hk)

theorem transpose_merge_markers {n : Nat} {p : Fin n → Fin n}
    (hp : ∀ x y, p x = p y → x = y) (a b : Fin n)
    (hsep : cmin p a ≠ cmin p b) : Reaches (transpose p a b) a b := by
  obtain ⟨k, hk⟩ := back hp 1 b
  have hu := reaches_until_invariant p (transpose p a b) (fun x => cmin p x = cmin p b) b
    (fun x hx => by rw [cmin_step hp]; exact hx)
    (fun x hx hxb => transpose_other p (by intro he; subst x; exact hsep hx) hxb)
    k (p b) (cmin_step hp b) hk
  exact (show Reaches (transpose p a b) a (p b) from ⟨1, transpose_a p a b⟩).trans hu

theorem transpose_merge_step {n : Nat} {p : Fin n → Fin n}
    (hp : ∀ x y, p x = p y → x = y) (a b : Fin n)
    (hsep : cmin p a ≠ cmin p b) (x : Fin n) : Reaches (transpose p a b) x (p x) := by
  have hab : a ≠ b := fun h => hsep (congrArg (cmin p) h)
  have hm := transpose_merge_markers hp a b hsep
  by_cases ha : x = a
  · subst x
    exact hm.trans ⟨1, transpose_b p hab⟩
  · by_cases hb : x = b
    · subst x
      exact (hm.symm (transpose_injective hp a b)).trans ⟨1, transpose_a p a b⟩
    · exact ⟨1, transpose_other p ha hb⟩

theorem transpose_merge_orbit {n : Nat} {p : Fin n → Fin n}
    (hp : ∀ x y, p x = p y → x = y) (a b : Fin n)
    (hsep : cmin p a ≠ cmin p b) {x y : Fin n} (h : Reaches p x y) :
    Reaches (transpose p a b) x y := by
  obtain ⟨k, rfl⟩ := h
  induction k generalizing x with
  | zero => exact Reaches.refl _ _
  | succ k ih => exact (transpose_merge_step hp a b hsep x).trans (ih (x := p x))

noncomputable def mergeRep {n : Nat} (p : Fin n → Fin n) (a b x : Fin n) : Fin n :=
  if cmin p x = cmin p a then cmin p b else cmin p x

theorem mergeRep_step {n : Nat} {p : Fin n → Fin n}
    (hp : ∀ x y, p x = p y → x = y) (a b : Fin n)
    (hsep : cmin p a ≠ cmin p b) (x : Fin n) :
    mergeRep p a b (transpose p a b x) = mergeRep p a b x := by
  have hab : a ≠ b := fun h => hsep (congrArg (cmin p) h)
  by_cases ha : x = a
  · subst x
    rw [transpose_a]
    simp [mergeRep, cmin_step hp, Ne.symm hsep]
  · by_cases hb : x = b
    · subst x
      rw [transpose_b p hab]
      simp [mergeRep, cmin_step hp, Ne.symm hsep]
    · rw [transpose_other p ha hb]
      simp [mergeRep, cmin_step hp]

theorem transpose_reaches_mergeRep {n : Nat} {p : Fin n → Fin n}
    (hp : ∀ x y, p x = p y → x = y) (a b : Fin n)
    (hsep : cmin p a ≠ cmin p b) (x : Fin n) :
    Reaches (transpose p a b) x (mergeRep p a b x) := by
  unfold mergeRep
  by_cases hx : cmin p x = cmin p a
  · rw [ite_eq_left hx]
    have hxa : Reaches p x a := by
      have hxc := reaches_cmin p x
      rw [hx] at hxc
      exact hxc.trans (from_cmin hp a)
    exact (transpose_merge_orbit hp a b hsep hxa).trans
      ((transpose_merge_markers hp a b hsep).trans
        (transpose_merge_orbit hp a b hsep (reaches_cmin p b)))
  · rw [ite_eq_right hx]
    exact transpose_merge_orbit hp a b hsep (reaches_cmin p x)

/-- A successor transposition between distinct orbits merges exactly those two orbits. -/
theorem transpose_merge_cycles {n : Nat} {p : Fin n → Fin n}
    (hp : ∀ x y, p x = p y → x = y) (a b : Fin n)
    (hsep : cmin p a ≠ cmin p b) :
    cycleCount (transpose p a b) + 1 = cycleCount p := by
  let xs := (cycleRoots p).erase (cmin p a)
  have hlen : xs.length + 1 = cycleCount p := by
    have hmem := cmin_mem_cycleRoots hp a
    have hl := List.length_erase_of_mem hmem
    have hpos : 0 < (cycleRoots p).length := List.length_pos_iff.mpr
      (fun he => by simp [he] at hmem)
    have he := cycleRoots_length p
    simp only [xs, hl]
    omega
  have hfixed : ∀ x ∈ xs, mergeRep p a b x = x := by
    intro x hx
    obtain ⟨hne, hm⟩ := (List.Nodup.mem_erase_iff (cycleRoots_nodup p)).mp hx
    simp only [mergeRep, (mem_cycleRoots hp x).mp hm, ite_eq_right hne]
  have hnd : (xs.map (mergeRep p a b)).Nodup := by
    have he : xs.map (mergeRep p a b) = xs := by
      conv => rhs; rw [← List.map_id xs]
      exact List.map_congr_left hfixed
    rw [he]
    exact (cycleRoots_nodup p).erase _
  have hlo := cycleCount_ge (transpose p a b) (mergeRep p a b) (mergeRep_step hp a b hsep) xs hnd
  have hm : ∀ x, mergeRep p a b x ∈ xs := by
    intro x
    apply (List.Nodup.mem_erase_iff (cycleRoots_nodup p)).mpr
    unfold mergeRep
    split
    · exact ⟨Ne.symm hsep, cmin_mem_cycleRoots hp b⟩
    · next hx => exact ⟨hx, cmin_mem_cycleRoots hp x⟩
  have hnd' : ((cycleRoots (transpose p a b)).map (mergeRep p a b)).Nodup := by
    apply nodup_map_of_injOn' _ (cycleRoots_nodup _)
    intro x hx y hy he
    have hx' := transpose_reaches_mergeRep hp a b hsep x
    rw [he] at hx'
    exact cycleRoots_eq_of_reaches (transpose_injective hp a b) hx hy
      (hx'.trans ((transpose_reaches_mergeRep hp a b hsep y).symm (transpose_injective hp a b)))
  have hhi := List.Nodup.length_le_of_subset hnd' (l₂ := xs) (by
    intro x hx
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
    exact hm y)
  simp only [List.length_map, cycleRoots_length] at hhi
  omega

theorem cmin_eq_iff_reaches {n : Nat} {p : Fin n → Fin n}
    (hp : ∀ x y, p x = p y → x = y) (x y : Fin n) :
    cmin p x = cmin p y ↔ Reaches p x y := by
  constructor
  · intro h
    have hx := reaches_cmin p x
    rw [h] at hx
    exact hx.trans (from_cmin hp y)
  · rintro ⟨k, hk⟩
    have h := cmin_iterate hp x k
    rw [hk] at h
    exact h.symm

theorem crank_cycle_injective {n : Nat} {p : Fin n → Fin n}
    (hp : ∀ x y, p x = p y → x = y) {x y : Fin n}
    (hc : cmin p x = cmin p y) (hr : crank p hp x = crank p hp y) : x = y := by
  have hx := (crank_spec hp x).1
  rw [hc, hr] at hx
  exact hx.symm.trans (crank_spec hp y).1

/-- The dart immediately before the least dart has greatest rank in its orbit. -/
theorem crank_max_of_wrap {n : Nat} {p : Fin n → Fin n}
    (hp : ∀ x y, p x = p y → x = y) (x y : Fin n)
    (hwrap : crank p hp (p x) = 0) (hc : cmin p y = cmin p x) :
    crank p hp y ≤ crank p hp x := by
  have hx : cmin p x = p x := by
    have h := (crank_zero_iff hp (p x)).mp hwrap
    rwa [cmin_step hp] at h
  have hperiod : iterate p (crank p hp x + 1) (cmin p y) = cmin p y := by
    rw [hc, iterate_succ', (crank_spec hp x).1, ← hx]
  apply Classical.byContradiction
  intro hlt
  have hshort : iterate p (crank p hp y - (crank p hp x + 1)) (cmin p y) = y := by
    calc iterate p (crank p hp y - (crank p hp x + 1)) (cmin p y)
        = iterate p (crank p hp y - (crank p hp x + 1))
            (iterate p (crank p hp x + 1) (cmin p y)) := by rw [hperiod]
      _ = iterate p (crank p hp y) (cmin p y) := by
        rw [← iterate_add, show crank p hp x + 1 + (crank p hp y - (crank p hp x + 1)) =
          crank p hp y by omega]
      _ = y := (crank_spec hp y).1
  exact (crank_spec hp y).2 _ (by omega) hshort

theorem crank_step_of_lt {n : Nat} {p : Fin n → Fin n}
    (hp : ∀ x y, p x = p y → x = y) (x y : Fin n)
    (hc : cmin p x = cmin p y) (hlt : crank p hp x < crank p hp y) :
    crank p hp (p x) = crank p hp x + 1 := by
  rcases crank_step hp x with h | h
  · exact h
  · have := crank_max_of_wrap hp x y h hc.symm
    omega

/-- A half-open segment of the marked orbit, used to distinguish its two new cycles. -/
noncomputable def cutLabel {n : Nat} (p : Fin n → Fin n)
    (hp : ∀ x y, p x = p y → x = y) (a b x : Fin n) : Bool :=
  decide (cmin p x = cmin p a ∧ crank p hp a < crank p hp x ∧ crank p hp x ≤ crank p hp b)

theorem cutLabel_step {n : Nat} {p : Fin n → Fin n}
    (hp : ∀ x y, p x = p y → x = y) (a b : Fin n)
    (hc : cmin p a = cmin p b) (hlt : crank p hp a < crank p hp b) (x : Fin n) :
    cutLabel p hp a b (transpose p a b x) = cutLabel p hp a b x := by
  have hab : a ≠ b := by intro h; subst b; omega
  by_cases hxa : x = a
  · subst x
    rw [transpose_a]
    apply Bool.eq_iff_iff.mpr
    simp only [cutLabel, decide_eq_true_eq, cmin_step hp]
    rcases crank_step hp b with hb | hb <;> rw [hb] <;> constructor <;> intro h <;> omega
  · by_cases hxb : x = b
    · subst x
      rw [transpose_b p hab]
      have hstep := crank_step_of_lt hp a b hc hlt
      apply Bool.eq_iff_iff.mpr
      simp only [cutLabel, decide_eq_true_eq, cmin_step hp, hstep]
      constructor
      · intro _; exact ⟨hc.symm, hlt, Nat.le_refl _⟩
      · intro _; exact ⟨True.intro, by omega, by omega⟩
    · rw [transpose_other p hxa hxb]
      by_cases hx : cmin p x = cmin p a
      · have hra : crank p hp x ≠ crank p hp a := fun h => hxa (crank_cycle_injective hp hx h)
        have hrb : crank p hp x ≠ crank p hp b :=
          fun h => hxb (crank_cycle_injective hp (hx.trans hc) h)
        rcases crank_step hp x with hs | hs
        · apply Bool.eq_iff_iff.mpr
          simp only [cutLabel, decide_eq_true_eq, cmin_step hp, hx, true_and, hs]
          omega
        · have hmax := crank_max_of_wrap hp x b hs (hc.symm.trans hx.symm)
          apply Bool.eq_iff_iff.mpr
          simp only [cutLabel, decide_eq_true_eq, cmin_step hp, hx, true_and, hs]
          omega
      · simp [cutLabel, cmin_step hp, hx]

theorem transpose_split_separate_of_rank_lt {n : Nat} {p : Fin n → Fin n}
    (hp : ∀ x y, p x = p y → x = y) (a b : Fin n)
    (hc : cmin p a = cmin p b) (hlt : crank p hp a < crank p hp b) :
    cmin (transpose p a b) a ≠ cmin (transpose p a b) b := by
  intro h
  obtain ⟨k, hk⟩ := (cmin_eq_iff_reaches (transpose_injective hp a b) a b).mp h
  have hinv := iterate_invariant (transpose p a b) (cutLabel p hp a b)
    (cutLabel_step hp a b hc hlt) k a
  rw [hk] at hinv
  have ha : cutLabel p hp a b a = false := by simp [cutLabel]
  have hb : cutLabel p hp a b b = true := by simp [cutLabel, hc.symm, hlt]
  rw [ha, hb] at hinv
  contradiction

theorem swap_comm {n : Nat} (a b x : Fin n) : swap a b x = swap b a x := by
  by_cases hab : a = b
  · subst b; rfl
  · by_cases hxa : x = a
    · subst x; simp [swap, hab]
    · by_cases hxb : x = b
      · subst x; simp [swap, Ne.symm hab]
      · simp [swap, hxa, hxb]

theorem transpose_comm {n : Nat} (p : Fin n → Fin n) (a b : Fin n) :
    transpose p a b = transpose p b a := by
  funext x; exact congrArg p (swap_comm a b x)

theorem transpose_split_separate {n : Nat} {p : Fin n → Fin n}
    (hp : ∀ x y, p x = p y → x = y) (a b : Fin n) (hab : a ≠ b)
    (hc : cmin p a = cmin p b) :
    cmin (transpose p a b) a ≠ cmin (transpose p a b) b := by
  have hr : crank p hp a ≠ crank p hp b := fun h => hab (crank_cycle_injective hp hc h)
  rcases Nat.lt_or_gt_of_ne hr with hlt | hlt
  · exact transpose_split_separate_of_rank_lt hp a b hc hlt
  · have h := transpose_split_separate_of_rank_lt hp b a hc.symm hlt
    rw [transpose_comm p b a] at h
    exact Ne.symm h

/-- A successor transposition at distinct darts of the same orbit splits it in two. -/
theorem transpose_split_cycles {n : Nat} {p : Fin n → Fin n}
    (hp : ∀ x y, p x = p y → x = y) (a b : Fin n) (hab : a ≠ b)
    (hc : cmin p a = cmin p b) :
    cycleCount (transpose p a b) = cycleCount p + 1 := by
  have h := transpose_merge_cycles (transpose_injective hp a b) a b
    (transpose_split_separate hp a b hab hc)
  rw [transpose_twice] at h
  exact h.symm

end STACS2027.PlanarGluing

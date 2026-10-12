module

public import NPHardness.PlanarGluingCycles

/-! Excision of the greatest dart of a finite permutation.  Surviving cycles
retain their least dart; the cycle count drops precisely when the removed
dart was a singleton cycle.  This is an elementary piece of edge-deletion
surgery, not a graph-planarity closure theorem by itself. -/

@[expose] public section
namespace STACS2027.PlanarPreprocess.Deletion
open Complexity Complexity.Planar STACS2027.PlanarGluing

def embed {n : Nat} (x : Fin n) : Fin (n+1) := ⟨x.val,by have := x.isLt; omega⟩
def last (n : Nat) : Fin (n+1) := ⟨n,by omega⟩

theorem embed_injective {n : Nat} {x y : Fin n} (h : embed x = embed y) : x = y :=
  Fin.ext (congrArg (fun d : Fin (n+1) => d.val) h)

theorem embed_ne_last {n : Nat} (x : Fin n) : embed x ≠ last n := by
  intro h
  have he := congrArg Fin.val h
  have hx := x.isLt
  change x.val = n at he
  omega

def skipLast {n : Nat} (p : Fin (n+1) → Fin (n+1)) (x : Fin (n+1)) : Fin (n+1) :=
  if p x = last n then p (last n) else p x

theorem skipLast_ne_last {n : Nat} {p : Fin (n+1) → Fin (n+1)}
    (hp : ∀ x y, p x = p y → x = y) (x : Fin n) : skipLast p (embed x) ≠ last n := by
  intro he
  unfold skipLast at he
  split at he
  · next hx => exact embed_ne_last x (hp _ _ (hx.trans he.symm))
  · next hx => exact hx he

def removeLast {n : Nat} (p : Fin (n+1) → Fin (n+1))
    (hp : ∀ x y, p x = p y → x = y) (x : Fin n) : Fin n :=
  ⟨(skipLast p (embed x)).val,by
    have hb := (skipLast p (embed x)).isLt
    have hn := skipLast_ne_last hp x
    have hv : (skipLast p (embed x)).val ≠ n := fun h => hn (Fin.ext h)
    omega⟩

theorem embed_removeLast {n : Nat} (p : Fin (n+1) → Fin (n+1))
    (hp : ∀ x y, p x = p y → x = y) (x : Fin n) :
    embed (removeLast p hp x) = skipLast p (embed x) := Fin.ext rfl

theorem removeLast_injective {n : Nat} {p : Fin (n+1) → Fin (n+1)}
    (hp : ∀ x y, p x = p y → x = y) : ∀ x y, removeLast p hp x = removeLast p hp y → x = y := by
  intro x y he
  have h := congrArg embed he
  simp only [embed_removeLast,skipLast] at h
  by_cases hx : p (embed x) = last n <;> by_cases hy : p (embed y) = last n
  · exact embed_injective (hp _ _ (hx.trans hy.symm))
  · simp only [hx,hy,↓reduceIte] at h
    exact False.elim (embed_ne_last y (hp _ _ h.symm))
  · simp only [hx,hy,↓reduceIte] at h
    exact False.elim (embed_ne_last x (hp _ _ h))
  · simp only [hx,hy,↓reduceIte] at h
    exact embed_injective (hp _ _ h)

theorem lift_step {n : Nat} {p : Fin (n+1) → Fin (n+1)}
    (hp : ∀ x y, p x = p y → x = y) (x : Fin n) :
    Reaches p (embed x) (embed (removeLast p hp x)) := by
  rw [embed_removeLast]
  by_cases hx : p (embed x) = last n
  · refine ⟨2,?_⟩
    simp [iterate,skipLast,hx]
  · refine ⟨1,?_⟩
    simp [iterate,skipLast,hx]

theorem lift_reaches {n : Nat} {p : Fin (n+1) → Fin (n+1)}
    (hp : ∀ x y, p x = p y → x = y) {x y : Fin n}
    (h : Reaches (removeLast p hp) x y) : Reaches p (embed x) (embed y) := by
  obtain ⟨k,rfl⟩ := h
  induction k generalizing x with
  | zero => exact Reaches.refl _ _
  | succ k ih => exact (lift_step hp x).trans (ih (x := removeLast p hp x))

theorem retract_iterate {n : Nat} {p : Fin (n+1) → Fin (n+1)}
    (hp : ∀ x y, p x = p y → x = y) (k : Nat) {x y : Fin n}
    (h : iterate p k (embed x) = embed y) : Reaches (removeLast p hp) x y := by
  induction k using Nat.strongRecOn generalizing x with
  | ind k ih =>
    cases k with
    | zero => exact ⟨0,embed_injective h⟩
    | succ k =>
      by_cases hx : p (embed x) = last n
      · cases k with
        | zero =>
          have he : last n = embed y := by simpa [iterate,hx] using h
          exact False.elim (embed_ne_last y he.symm)
        | succ k =>
          have he : embed (removeLast p hp x) = p (last n) := by simp [embed_removeLast,skipLast,hx]
          have ht : iterate p k (embed (removeLast p hp x)) = embed y := by
            rw [he]
            simpa only [iterate,hx] using h
          exact (Reaches.step _ x).trans (ih k (by omega) ht)
      · have he : embed (removeLast p hp x) = p (embed x) := by simp [embed_removeLast,skipLast,hx]
        have ht : iterate p k (embed (removeLast p hp x)) = embed y := by
          rw [he]
          exact h
        exact (Reaches.step _ x).trans (ih k (by omega) ht)

theorem removeLast_orbit {n : Nat} {p : Fin (n+1) → Fin (n+1)}
    (hp : ∀ x y, p x = p y → x = y) (x y : Fin n) :
    Reaches (removeLast p hp) x y ↔ Reaches p (embed x) (embed y) := by
  constructor
  · exact lift_reaches hp
  · rintro ⟨k,h⟩
    exact retract_iterate hp k h

theorem removeLast_cmin {n : Nat} {p : Fin (n+1) → Fin (n+1)}
    (hp : ∀ x y, p x = p y → x = y) (x : Fin n) :
    cmin p (embed x) = embed (cmin (removeLast p hp) x) := by
  have hq := removeLast_injective hp
  have hlo := cmin_le_self hp (embed x)
  have hb : (cmin p (embed x)).val < n := by
    have hx := x.isLt
    change (cmin p (embed x)).val ≤ x.val at hlo
    omega
  let y : Fin n := ⟨(cmin p (embed x)).val,hb⟩
  have hey : embed y = cmin p (embed x) := Fin.ext rfl
  have hpReach : Reaches p (embed x) (embed y) := by
    rw [hey]
    exact reaches_cmin p (embed x)
  obtain ⟨k,hk⟩ := (removeLast_orbit hp x y).mpr hpReach
  have hle := cmin_le hq x k
  rw [hk] at hle
  obtain ⟨j,hj⟩ := lift_reaches hp (reaches_cmin (removeLast p hp) x)
  have hge := cmin_le hp (embed x) j
  rw [hj] at hge
  apply Fin.ext
  exact Nat.le_antisymm hge hle

theorem removeLast_cycleMin {n : Nat} {p : Fin (n+1) → Fin (n+1)}
    (hp : ∀ x y, p x = p y → x = y) (x : Fin n) :
    CycleMin p (embed x) = CycleMin (removeLast p hp) x := by
  apply Bool.eq_iff_iff.mpr
  rw [← cmin_eq_iff hp,← cmin_eq_iff (removeLast_injective hp),removeLast_cmin hp]
  exact ⟨embed_injective,congrArg embed⟩

theorem last_cycleMin_iff {n : Nat} {p : Fin (n+1) → Fin (n+1)}
    (hp : ∀ x y, p x = p y → x = y) : CycleMin p (last n) = true ↔ p (last n) = last n := by
  rw [← cmin_eq_iff hp]
  constructor
  · intro hc
    have h := cmin_le hp (last n) 1
    rw [hc] at h
    apply Fin.ext
    have hb := (p (last n)).isLt
    change n ≤ (p (last n)).val at h
    change (p (last n)).val = n
    omega
  · intro hpfix
    have hiter : ∀ k, iterate p k (last n) = last n := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih => simpa only [iterate,hpfix] using ih
    obtain ⟨k,_,hk⟩ := cmin_mem (p := p) (last n)
    rw [hiter] at hk
    exact hk.symm

theorem finRange_snoc (n : Nat) :
    List.finRange (n+1) = (List.finRange n).map embed ++ [last n] := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    by_cases hin : i < n
    · rw [List.getElem_append_left (by simpa using hin)]
      simp only [List.getElem_map,List.getElem_finRange]
      rfl
    · have he : i = n := by simp only [List.length_finRange] at hi; omega
      subst i
      rw [List.getElem_append_right (by simp)]
      simp only [List.length_map,List.length_finRange,Nat.sub_self,List.getElem_cons_zero,List.getElem_finRange]
      rfl

/-- Excision loses exactly a singleton cycle, and no other cycle. -/
theorem removeLast_cycleCount {n : Nat} {p : Fin (n+1) → Fin (n+1)}
    (hp : ∀ x y, p x = p y → x = y) :
    cycleCount p = cycleCount (removeLast p hp) + if p (last n) = last n then 1 else 0 := by
  rw [cycleCount_eq,finRange_snoc,List.countP_append,List.countP_map]
  have he : (fun x : Fin n => CycleMin p (embed x)) = CycleMin (removeLast p hp) := by
    funext x
    exact removeLast_cycleMin hp x
  simp only [Function.comp_def,he,← cycleCount_eq,List.countP_cons,List.countP_nil,Nat.zero_add]
  by_cases hl : p (last n) = last n
  · simp [hl,(last_cycleMin_iff hp).mpr hl]
  · have hn : CycleMin p (last n) = false := by
      cases h : CycleMin p (last n)
      · rfl
      · exact False.elim (hl ((last_cycleMin_iff hp).mp h))
    simp [hl,hn]

theorem comp_injective {α : Type} {p q : α → α}
    (hp : ∀ x y, p x = p y → x = y) (hq : ∀ x y, q x = q y → x = y) :
    ∀ x y, p (q x) = p (q y) → x = y :=
  fun x y h => hq x y (hp _ _ h)

/-- A factor fixing the deleted dart commutes with restriction on the right. -/
theorem removeLast_comp_fixed {n : Nat} {p q : Fin (n+1) → Fin (n+1)}
    (hp : ∀ x y, p x = p y → x = y) (hq : ∀ x y, q x = q y → x = y)
    (hfix : q (last n) = last n) (x : Fin n) :
    removeLast (fun z => p (q z)) (comp_injective hp hq) x =
      removeLast p hp (removeLast q hq x) := by
  have hne : q (embed x) ≠ last n := by
    intro he
    exact embed_ne_last x (hq _ _ (he.trans hfix.symm))
  apply embed_injective
  simp only [embed_removeLast,skipLast,hne,↓reduceIte,hfix]

/-- The inverse permutation restricts to the inverse of the restricted map. -/
theorem removeLast_inverse {n : Nat} {p q : Fin (n+1) → Fin (n+1)}
    (hp : ∀ x y, p x = p y → x = y) (hq : ∀ x y, q x = q y → x = y)
    (hqp : ∀ x, q (p x) = x) (x : Fin n) :
    removeLast q hq (removeLast p hp x) = x := by
  apply embed_injective
  simp only [embed_removeLast,skipLast]
  by_cases hx : p (embed x) = last n
  · simp only [hx,↓reduceIte,hqp]
    have h := hqp (embed x)
    rw [hx] at h
    exact h
  · simp only [hx,↓reduceIte,hqp,embed_ne_last,↓reduceIte]

def removePair {n : Nat} (p : Fin (n+2) → Fin (n+2))
    (hp : ∀ x y, p x = p y → x = y) : Fin n → Fin n :=
  removeLast (removeLast p hp) (removeLast_injective hp)

def embedPair {n : Nat} (x : Fin n) : Fin (n+2) := embed (embed x)

end STACS2027.PlanarPreprocess.Deletion

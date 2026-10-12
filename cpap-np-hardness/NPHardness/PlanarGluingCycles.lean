module

public import Complexity.Planar.Perm
import Lean.Elab.Tactic.Omega

/-! Disjoint sums of permutations on adjacent dart intervals (`sumPerm`), with
their orbits and cycle counts, in the registered hypermap definitions. -/

@[expose] public section
namespace STACS2027.PlanarGluing
open Complexity Complexity.Planar

def left {n m : Nat} (x : Fin n) : Fin (n + m) := ⟨x.val, by omega⟩

def right {n m : Nat} (x : Fin m) : Fin (n + m) := ⟨n + x.val, by omega⟩

def split {n m : Nat} {α : Sort u} (f : Fin n → α) (g : Fin m → α)
    (x : Fin (n + m)) : α :=
  if h : x.val < n then f ⟨x.val, h⟩ else g ⟨x.val - n, by omega⟩

@[simp] theorem split_left {n m : Nat} {α : Sort u} (f : Fin n → α)
    (g : Fin m → α) (x : Fin n) : split f g (left x) = f x := by
  simp [split, left, x.isLt]

@[simp] theorem split_right {n m : Nat} {α : Sort u} (f : Fin n → α)
    (g : Fin m → α) (x : Fin m) : split f g (right x) = g x := by
  simp [split, right, show ¬n + x.val < n by omega]

theorem cases_dart {n m : Nat} (x : Fin (n + m)) :
    (∃ a : Fin n, left a = x) ∨ ∃ b : Fin m, right b = x := by
  by_cases h : x.val < n
  · exact Or.inl ⟨⟨x.val, h⟩, Fin.ext rfl⟩
  · exact Or.inr ⟨⟨x.val - n, by omega⟩, Fin.ext (by simp [right]; omega)⟩

theorem left_injective {n m : Nat} {a b : Fin n}
    (h : left (m := m) a = left b) : a = b := by
  apply Fin.ext
  exact congrArg (fun x : Fin (n + m) => x.val) h

theorem right_injective {n m : Nat} {a b : Fin m}
    (h : right (n := n) a = right b) : a = b := by
  apply Fin.ext
  have := congrArg Fin.val h
  simp only [right] at this
  omega

theorem left_ne_right {n m : Nat} (a : Fin n) (b : Fin m) : left a ≠ right b := by
  intro h
  have := congrArg Fin.val h
  simp only [left, right] at this
  have := a.isLt
  omega

def sumPerm {n m : Nat} (p : Fin n → Fin n) (q : Fin m → Fin m) :
    Fin (n + m) → Fin (n + m) := split (fun x => left (p x)) (fun x => right (q x))

@[simp] theorem sumPerm_left {n m : Nat} (p : Fin n → Fin n) (q : Fin m → Fin m)
    (x : Fin n) : sumPerm p q (left x) = left (p x) := split_left _ _ _

@[simp] theorem sumPerm_right {n m : Nat} (p : Fin n → Fin n) (q : Fin m → Fin m)
    (x : Fin m) : sumPerm p q (right x) = right (q x) := split_right _ _ _

def swap {n : Nat} (a b x : Fin n) : Fin n :=
  if x = a then b else if x = b then a else x

@[simp] theorem swap_swap {n : Nat} (a b x : Fin n) : swap a b (swap a b x) = x := by
  by_cases hab : a = b
  · subst b; simp [swap]; split <;> simp_all
  · by_cases ha : x = a
    · subst x; simp [swap, Ne.symm hab]
    · by_cases hb : x = b
      · subst x; simp [swap, Ne.symm hab]
      · simp [swap, ha, hb]

theorem swap_injective {n : Nat} (a b : Fin n) {x y : Fin n}
    (h : swap a b x = swap a b y) : x = y := by
  have := congrArg (swap a b) h
  simpa using this

def cycleRoots {n : Nat} (p : Fin n → Fin n) : List (Fin n) :=
  (List.finRange n).filter (CycleMin p)

theorem cycleRoots_nodup {n : Nat} (p : Fin n → Fin n) : (cycleRoots p).Nodup :=
  List.Pairwise.filter _ (List.nodup_finRange n)

theorem mem_cycleRoots {n : Nat} {p : Fin n → Fin n}
    (hp : ∀ a b, p a = p b → a = b) (x : Fin n) :
    x ∈ cycleRoots p ↔ cmin p x = x := by
  simp only [cycleRoots, List.mem_filter, List.mem_finRange, true_and]
  exact (cmin_eq_iff hp x).symm

theorem cmin_mem_cycleRoots {n : Nat} {p : Fin n → Fin n}
    (hp : ∀ a b, p a = p b → a = b) (x : Fin n) : cmin p x ∈ cycleRoots p := by
  rw [mem_cycleRoots hp]
  obtain ⟨k, _, hk⟩ := cmin_mem (p := p) x
  rw [← hk, cmin_iterate hp]
  exact hk.symm

theorem cycleRoots_length {n : Nat} (p : Fin n → Fin n) :
    (cycleRoots p).length = cycleCount p := by
  simp only [cycleCount_eq, List.countP_eq_length_filter, cycleRoots]

/-- Two darts belong to the same forward permutation orbit. -/
def Reaches {α : Type} (p : α → α) (x y : α) : Prop := ∃ k, iterate p k x = y

theorem Reaches.refl {α : Type} (p : α → α) (x : α) : Reaches p x x := ⟨0, rfl⟩

theorem Reaches.step {α : Type} (p : α → α) (x : α) : Reaches p x (p x) := ⟨1, rfl⟩

theorem Reaches.trans {α : Type} {p : α → α} {x y z : α}
    (hxy : Reaches p x y) (hyz : Reaches p y z) : Reaches p x z := by
  obtain ⟨k, hk⟩ := hxy
  obtain ⟨l, hl⟩ := hyz
  exact ⟨k + l, by rw [iterate_add, hk, hl]⟩

theorem Reaches.symm {n : Nat} {p : Fin n → Fin n}
    (hp : ∀ a b, p a = p b → a = b) {x y : Fin n}
    (h : Reaches p x y) : Reaches p y x := by
  obtain ⟨k, rfl⟩ := h
  exact back hp k x

theorem reaches_cmin {n : Nat} (p : Fin n → Fin n) (x : Fin n) : Reaches p x (cmin p x) := by
  obtain ⟨k, _, hk⟩ := cmin_mem (p := p) x
  exact ⟨k, hk⟩

theorem cycleRoots_eq_of_reaches {n : Nat} {p : Fin n → Fin n}
    (hp : ∀ a b, p a = p b → a = b) {x y : Fin n}
    (hx : x ∈ cycleRoots p) (hy : y ∈ cycleRoots p) (h : Reaches p x y) : x = y := by
  obtain ⟨k, hk⟩ := h
  have he := cmin_iterate hp x k
  rw [hk, (mem_cycleRoots hp y).mp hy, (mem_cycleRoots hp x).mp hx] at he
  exact he.symm

theorem sumPerm_cycles_ge {n m : Nat} {p : Fin n → Fin n} {q : Fin m → Fin m}
    (hp : ∀ a b, p a = p b → a = b) (hq : ∀ a b, q a = q b → a = b) :
    cycleCount p + cycleCount q ≤ cycleCount (sumPerm p q) := by
  let φ : Fin (n + m) → Sum (Fin n) (Fin m) :=
    split (fun x => .inl (cmin p x)) (fun y => .inr (cmin q y))
  let zs := (cycleRoots p).map (left (m := m)) ++ (cycleRoots q).map (right (n := n))
  have hφ : ∀ x, φ (sumPerm p q x) = φ x := by
    intro x
    rcases cases_dart x with ⟨x, rfl⟩ | ⟨x, rfl⟩ <;>
      simp [φ, cmin_step hp, cmin_step hq]
  have hnd : (zs.map φ).Nodup := by
    simp only [zs, List.map_append, List.map_map]
    rw [List.nodup_append]
    refine ⟨?_, ?_, ?_⟩
    · apply nodup_map_of_injOn' _ (cycleRoots_nodup p)
      intro x hx y hy he
      simpa [φ, (mem_cycleRoots hp x).mp hx, (mem_cycleRoots hp y).mp hy] using he
    · apply nodup_map_of_injOn' _ (cycleRoots_nodup q)
      intro x hx y hy he
      simpa [φ, (mem_cycleRoots hq x).mp hx, (mem_cycleRoots hq y).mp hy] using he
    · intro x hx y hy he
      obtain ⟨x', _, rfl⟩ := List.mem_map.mp hx
      obtain ⟨y', _, rfl⟩ := List.mem_map.mp hy
      simp [φ] at he
  have := cycleCount_ge (sumPerm p q) φ hφ zs hnd
  simpa only [zs, List.length_append, List.length_map, cycleRoots_length] using this

end STACS2027.PlanarGluing

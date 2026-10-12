module

public import ApproximationHardness.Embed.PlanWord
public import ApproximationHardness.Embed.CycList
import Lean.Elab.Tactic.Omega

/-!
# Depth-first forests of graphs of degree at most three

The darts of a graph with `E` edges are `0, …, 2E - 1`; dart `d` and `pair d` (`d xor 1`) are the
two ends of an edge. The vertex of a dart is its representative dart `rep d`. A forest is given by
the parent dart `par r` of every vertex `r` (a value `≥ 2E` at roots) and a depth. It is a
depth-first forest (`Forest.Valid`) when every edge outside the forest joins a vertex to one of
its ancestors.
-/

@[expose] public section

namespace STACS2027.Embed

open Complexity Complexity.Planar

/-- The other end of the edge of a dart. -/
def pair (d : Nat) : Nat := if d % 2 = 0 then d + 1 else d - 1

theorem pair_pair (d : Nat) : pair (pair d) = d := by
  unfold pair; split <;> split <;> omega

theorem pair_ne (d : Nat) : pair d ≠ d := by unfold pair; split <;> omega

theorem pair_lt {E d : Nat} (h : d < 2 * E) : pair d < 2 * E := by unfold pair; split <;> omega

theorem pair_inj {a b : Nat} (h : pair a = pair b) : a = b := by
  rw [← pair_pair a, h, pair_pair]

/-- The data of a forest on the vertices of a graph. -/
structure ForestData where
  E : Nat
  rep : Nat → Nat
  par : Nat → Nat
  depth : Nat → Nat
  H : Nat

namespace ForestData

variable (F : ForestData)

/-- `r` is a vertex: a dart that represents its own vertex. -/
def IsVertex (r : Nat) : Prop := r < 2 * F.E ∧ F.rep r = r

/-- The darts at the vertex `r`, in increasing order. -/
def dartsAt (r : Nat) : List Nat := (List.range (2 * F.E)).filter fun d => F.rep d == r

/-- A root has no parent dart. -/
def IsRoot (r : Nat) : Prop := 2 * F.E ≤ F.par r

instance (r : Nat) : Decidable (F.IsRoot r) := inferInstanceAs (Decidable (_ ≤ _))

/-- The parent of a vertex (a root is its own parent). -/
def up (r : Nat) : Nat := if F.IsRoot r then r else F.rep (pair (F.par r))

/-- `u` lies below `v` (or is `v`). -/
def Desc (v u : Nat) : Prop := ∃ k, iterate F.up k u = v

/-- The dart `d` is the parent dart of its vertex. -/
def IsUp (d : Nat) : Prop := ¬ F.IsRoot (F.rep d) ∧ F.par (F.rep d) = d

/-- The dart `d` leads to a child. -/
def IsDown (d : Nat) : Prop := F.IsUp (pair d)

/-- A dart of the forest. -/
def IsTree (d : Nat) : Prop := F.IsUp d ∨ F.IsDown d

instance (d : Nat) : Decidable (F.IsUp d) := inferInstanceAs (Decidable (_ ∧ _))
instance (d : Nat) : Decidable (F.IsDown d) := inferInstanceAs (Decidable (F.IsUp _))
instance (d : Nat) : Decidable (F.IsTree d) := inferInstanceAs (Decidable (_ ∨ _))

/-- A depth-first forest of a graph without loops in which every vertex has at most three darts. -/
structure Valid : Prop where
  rep_lt : ∀ d, d < 2 * F.E → F.rep d < 2 * F.E
  rep_rep : ∀ d, d < 2 * F.E → F.rep (F.rep d) = F.rep d
  rep_le : ∀ d, d < 2 * F.E → F.rep d ≤ d
  noloop : ∀ d, d < 2 * F.E → F.rep (pair d) ≠ F.rep d
  deg : ∀ r, (F.dartsAt r).length ≤ 3
  par_lt : ∀ r, F.IsVertex r → ¬ F.IsRoot r → F.par r < 2 * F.E
  par_rep : ∀ r, F.IsVertex r → ¬ F.IsRoot r → F.rep (F.par r) = r
  depth_up : ∀ r, F.IsVertex r → ¬ F.IsRoot r → F.depth r = F.depth (F.up r) + 1
  depth_root : ∀ r, F.IsVertex r → F.IsRoot r → F.depth r = 0
  depth_lt : ∀ r, F.IsVertex r → F.depth r < F.H
  back : ∀ d, d < 2 * F.E → ¬ F.IsTree d →
    F.Desc (F.rep (pair d)) (F.rep d) ∨ F.Desc (F.rep d) (F.rep (pair d))

variable {F}

theorem mem_dartsAt {r d : Nat} : d ∈ F.dartsAt r ↔ d < 2 * F.E ∧ F.rep d = r := by
  simp [dartsAt]

theorem dartsAt_nodup (r : Nat) : (F.dartsAt r).Nodup := List.nodup_range.filter _

theorem desc_refl (v : Nat) : F.Desc v v := ⟨0, rfl⟩

theorem desc_trans {a b c : Nat} (h1 : F.Desc a b) (h2 : F.Desc b c) : F.Desc a c := by
  obtain ⟨k, rfl⟩ := h1
  obtain ⟨j, rfl⟩ := h2
  exact ⟨j + k, by rw [iterate_add]⟩

theorem desc_up {r : Nat} : F.Desc (F.up r) r := ⟨1, rfl⟩

section valid

variable (hF : F.Valid)
include hF

theorem isVertex_rep {d : Nat} (hd : d < 2 * F.E) : F.IsVertex (F.rep d) :=
  ⟨hF.rep_lt d hd, hF.rep_rep d hd⟩

theorem up_vertex {r : Nat} (hr : F.IsVertex r) : F.IsVertex (F.up r) := by
  unfold up
  split
  · exact hr
  · exact isVertex_rep hF (pair_lt (hF.par_lt r hr ‹_›))

theorem iterate_up_vertex {r : Nat} (hr : F.IsVertex r) : ∀ k, F.IsVertex (iterate F.up k r) := by
  intro k
  induction k generalizing r with
  | zero => exact hr
  | succ k ih => exact ih (up_vertex hF hr)

omit hF in
theorem up_root {r : Nat} (h : F.IsRoot r) : F.up r = r := by simp [up, h]

theorem depth_iterate {r : Nat} (hr : F.IsVertex r) :
    ∀ k, k ≤ F.depth r → F.depth (iterate F.up k r) + k = F.depth r := by
  intro k
  induction k generalizing r with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    by_cases hroot : F.IsRoot r
    · rw [hF.depth_root r hr hroot] at hk; omega
    · have h1 := hF.depth_up r hr hroot
      have := ih (up_vertex hF hr) (by omega)
      show F.depth (iterate F.up k (F.up r)) + (k + 1) = F.depth r
      omega

theorem iterate_up_depth {r : Nat} (hr : F.IsVertex r) : ∀ k, F.depth r ≤ k →
    iterate F.up k r = iterate F.up (F.depth r) r := by
  intro k hk
  have hroot : F.IsRoot (iterate F.up (F.depth r) r) := by
    have h := depth_iterate hF hr (F.depth r) (Nat.le_refl _)
    apply Classical.byContradiction
    intro hn
    have := hF.depth_up _ (iterate_up_vertex hF hr _) hn
    omega
  obtain ⟨j, rfl⟩ : ∃ j, k = F.depth r + j := ⟨k - F.depth r, by omega⟩
  rw [iterate_add]
  induction j with
  | zero => rfl
  | succ j ih => rw [iterate_succ', ih (by omega), up_root hroot]

theorem desc_depth {v u : Nat} (hu : F.IsVertex u) (h : F.Desc v u) : F.depth v ≤ F.depth u := by
  obtain ⟨k, rfl⟩ := h
  by_cases hk : k ≤ F.depth u
  · have := depth_iterate hF hu k hk; omega
  · rw [iterate_up_depth hF hu k (by omega)]
    have := depth_iterate hF hu (F.depth u) (Nat.le_refl _); omega

/-- The ancestor of `u` at depth `j`. -/
theorem desc_eq_iterate {v u : Nat} (hu : F.IsVertex u) (h : F.Desc v u) :
    v = iterate F.up (F.depth u - F.depth v) u := by
  obtain ⟨k, rfl⟩ := h
  by_cases hk : k ≤ F.depth u
  · have := depth_iterate hF hu k hk
    rw [show F.depth u - F.depth (iterate F.up k u) = k by omega]
  · rw [iterate_up_depth hF hu k (by omega)]
    have := depth_iterate hF hu (F.depth u) (Nat.le_refl _)
    rw [show F.depth u - F.depth (iterate F.up (F.depth u) u) = F.depth u by omega]

/-- Two ancestors of a vertex at the same depth are equal. -/
theorem desc_unique {v v' u : Nat} (hu : F.IsVertex u) (h : F.Desc v u) (h' : F.Desc v' u)
    (hd : F.depth v = F.depth v') : v = v' := by
  rw [desc_eq_iterate hF hu h, desc_eq_iterate hF hu h', hd]

/-- Ancestors of `u` are linearly ordered: the deeper one lies below the other. -/
theorem desc_of_desc {a b u : Nat} (hu : F.IsVertex u) (ha : F.Desc a u) (hb : F.Desc b u)
    (hab : F.depth a ≤ F.depth b) : F.Desc a b := by
  rw [desc_eq_iterate hF hu hb]
  rw [desc_eq_iterate hF hu ha]
  have hdb := desc_depth hF hu hb
  refine ⟨F.depth b - F.depth a, ?_⟩
  rw [← iterate_add]
  congr 1
  omega

theorem desc_antisymm {a b : Nat} (hb : F.IsVertex b) (h1 : F.Desc a b) (h2 : F.Desc b a) : a = b := by
  have ha : F.IsVertex a := by obtain ⟨k, rfl⟩ := h1; exact iterate_up_vertex hF hb k
  have e1 := desc_depth hF hb h1
  have e2 := desc_depth hF ha h2
  exact desc_unique hF hb h1 (desc_refl b) (by omega)

/-- A vertex strictly below `v` lies below a child of `v`. -/
theorem desc_child {v u : Nat} (hu : F.IsVertex u) (h : F.Desc v u) (hne : u ≠ v) :
    ∃ c, F.IsVertex c ∧ ¬ F.IsRoot c ∧ F.up c = v ∧ F.Desc c u := by
  have hex : ∃ k, iterate F.up k u = v := h
  obtain ⟨k, hk, hmin⟩ := exists_least hex
  cases k with
  | zero => exact absurd hk hne
  | succ k =>
    let c := iterate F.up k u
    have hcv : c ≠ v := fun e => hmin k (by omega) e
    have hup : F.up c = v := by rw [← hk, iterate_succ']
    have hroot : ¬ F.IsRoot c := fun hr => hcv (by rw [← hup, up_root hr])
    exact ⟨c, iterate_up_vertex hF hu k, hroot, hup, ⟨k, rfl⟩⟩

theorem up_ne {c : Nat} (hc : F.IsVertex c) (hroot : ¬ F.IsRoot c) : F.up c ≠ c := by
  intro e
  have := hF.depth_up c hc hroot
  rw [e] at this; omega

theorem depth_up_lt {c : Nat} (hc : F.IsVertex c) (hroot : ¬ F.IsRoot c) :
    F.depth (F.up c) < F.depth c := by
  have := hF.depth_up c hc hroot; omega

end valid

end ForestData

end STACS2027.Embed

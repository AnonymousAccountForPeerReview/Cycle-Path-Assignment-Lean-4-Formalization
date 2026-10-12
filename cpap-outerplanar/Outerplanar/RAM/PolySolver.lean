module

public import Outerplanar.RAM.Poly1
public import Outerplanar.RAM.Poly4
import Mathlib.Tactic

/-!
# The polygon solver: the four phases composed

`polySolver k p2 p3` runs phase P1 (`P1.poly1`, structure), the phases `p2` (cycles) and `p3`
(tables), and phase P4 (`P4.poly4 k`, backtracking and output).

`polySolver_specB`: given the bounded specifications of `p2` and `p3` (`PolyPhaseB` triples
between `Poly1Post`, `Poly2Post` and `Poly3Post`, each bounding the steps and the growth of the
free pointer by `C * (n + |pg| + 1)`, every access below any bound `S` leaving room for that
growth), the composition satisfies `PolySpecB k` (linear time and space) with the constant
`P1.CP1 + CP2 + CP3 + P4.CP4 k`. The memory frames chain (each phase stores only at or above
its initial free pointer, and the free pointer never decreases); `ZeroFrom` is that of P4 (each
`…Post` also carries it, through `Poly1Post.base : PolyIn`).

`polySolver_wregs`: given the register footprints of `p2` and `p3`, the composition writes
only `rT`, `rFREE` and registers at or above `gP0`.
-/

@[expose] public section

namespace STACS2027.RAM.PolySolver

open STACS2027.Poly

/-- **The polygon solver**: phases P1, P2, P3, P4. -/
def polySolver (k : ℕ) (p2 p3 : Stmt) : Stmt := .seq P1.poly1 (.seq p2 (.seq p3 (P4.poly4 k)))

/-- **The polygon solver is correct and runs in linear time and space**: from the bounded
specifications of the phases P2 and P3 (`PolyPhaseB`), the composition appends
`(polyOut pg n k).flatten` mapped by `omap` within `(CP1 + CP2 + CP3 + CP4 k) * (n + |pg| + 1)`
steps, allocating at most that many fresh cells, every load and store below any bound `S`
leaving room for them (`PolySpecB`). Each phase runs with the same bound `S`: its own room
follows from the growth of the free pointer in the phases before it. -/
theorem polySolver_specB {k : ℕ} (hk : 3 ≤ k) {p2 p3 : Stmt} {CP2 CP3 : ℕ}
    (h2 : ∀ pg n omap, IsPolygon pg n → (∀ e ∈ pg, e.1 < e.2) → pg.Nodup →
      PolyPhaseB p2 pg n (Poly1Post pg n omap) (Poly2Post pg n k omap) CP2)
    (h3 : ∀ pg n omap, IsPolygon pg n → (∀ e ∈ pg, e.1 < e.2) → pg.Nodup →
      PolyPhaseB p3 pg n (Poly2Post pg n k omap) (Poly3Post pg n k omap) CP3) :
    PolySpecB k (polySolver k p2 p3) (P1.CP1 + CP2 + CP3 + P4.CP4 k) := by
  intro S pg n omap c₀ hP hlt hnd hS c ⟨hc, hcc⟩
  subst c
  simp only [Nat.add_mul] at hS
  obtain ⟨c₁, t₁, e₁, ⟨hp₁, ho₁, hs₁, hf₁, hm₁⟩, ht₁⟩ :=
    P1.poly1_specB pg n omap hP hlt hnd S c₀ (by omega) c₀ ⟨hc, rfl⟩
  obtain ⟨c₂, t₂, e₂, ⟨hp₂, ho₂, hs₂, hf₂, hm₂⟩, ht₂⟩ :=
    h2 pg n omap hP hlt hnd S c₁ (by omega) c₁ ⟨hp₁, rfl⟩
  obtain ⟨c₃, t₃, e₃, ⟨hp₃, ho₃, hs₃, hf₃, hm₃⟩, ht₃⟩ :=
    h3 pg n omap hP hlt hnd S c₂ (by omega) c₂ ⟨hp₂, rfl⟩
  obtain ⟨c₄, t₄, e₄, ⟨ho₄, hs₄, hz₄, hf₄, hm₄⟩, ht₄⟩ :=
    P4.poly4_specB hk pg n omap hP hlt hnd S c₃ (by omega) c₃ ⟨hp₃, rfl⟩
  refine ⟨c₄, t₁ + (t₂ + (t₃ + t₄)), ExecB.seq e₁ (ExecB.seq e₂ (ExecB.seq e₃ e₄)),
    ⟨?_, ?_, hz₄, by omega, ?_⟩, ?_⟩
  · rw [ho₄, ho₃, ho₂, ho₁]
  · refine hs₁.trans (hs₂.trans (hs₃.trans (hs₄.mono ?_) |>.mono ?_) |>.mono ?_)
    all_goals intro a (ha : a < _); show a < _; omega
  · simp only [Nat.add_mul]
    omega
  · have := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add ht₁ ht₂) ht₃) ht₄
    simp only [Nat.add_mul] at this ⊢
    omega

/-- **The polygon solver writes only `rT`, `rFREE` and registers at or above `gP0`.** -/
theorem polySolver_wregs {k : ℕ} {p2 p3 : Stmt}
    (h2W : ∀ r ∈ wregs p2, r = rT ∨ r = rFREE ∨ (gNP ≤ r ∧ r ≤ gBIDX) ∨ gPx ≤ r)
    (h3W : ∀ r ∈ wregs p3, r = rT ∨ r = rFREE ∨ (gTOFF ≤ r ∧ r ≤ gARG) ∨ gPx ≤ r) :
    ∀ r ∈ wregs (polySolver k p2 p3), r = rT ∨ r = rFREE ∨ gP0 ≤ r := by
  intro r hr
  simp only [polySolver, wregs_seq, List.mem_append] at hr
  rcases hr with h | h | h | h
  · exact P1.poly1_wregs r h
  · rcases h2W r h with h' | h' | h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr (by simp only [gNP, gP0] at h' ⊢; omega))
    · exact Or.inr (Or.inr (by simp only [gPx, gP0] at h' ⊢; omega))
  · rcases h3W r h with h' | h' | h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr (by simp only [gTOFF, gP0] at h' ⊢; omega))
    · exact Or.inr (Or.inr (by simp only [gPx, gP0] at h' ⊢; omega))
  · rcases P4.poly4_wregs k r h with h' | h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr (by simp only [gPx, gP0] at h' ⊢; omega))

end STACS2027.RAM.PolySolver

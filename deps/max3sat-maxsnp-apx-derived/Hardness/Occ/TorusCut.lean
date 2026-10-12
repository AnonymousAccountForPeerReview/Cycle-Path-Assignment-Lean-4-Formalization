module

public import Hardness.Occ.Torus

/-!
# Stage 2: the cut property of the torus gadget

Rows `C i → A(i,0) → B(i,0) → A(i,1) → … → B(i,k-1) → C i` and columns
`A(0,j) → B(0,j) → A(1,j) → … → B(k-1,j) → A(0,j)` are directed cycles; every arc lies in the
row of its tail and in the column of its tail (rows, respectively columns, are pairwise
arc-disjoint). If no arc with tail in row `i` is violated, the whole row has the value of `C i`
(`row_const`); if no arc with tail in column `j` is violated, all `A(·,j)` have the same value
(`col_const`). Hence (`torus_cut`): either at least `min(#true contacts, #false contacts)` rows
contain a violated arc, or there are a clean row with a true contact and a clean row with a
false contact, and then all `k` columns contain a violated arc.

`lReducible_torus`: `max3SATB B` L-reduces to `max3SATB 3`.
-/

@[expose] public section

set_option linter.dupNamespace false

namespace Complexity

open Complexity.PT

namespace Occ

/-- The arc `e` goes from a true node to a false node. -/
def viol (σ : N3 → Bool) (e : N3 × N3) : Bool := σ e.1 && !σ e.2

variable {k : Nat}

theorem arc_CA {i : Nat} (hi : i < k) : (((2, i, 0), (0, i, 0)) : N3 × N3) ∈ tarcs k :=
  mem_tarcs.mpr ⟨mem_tnodes.mpr ⟨by simp, hi, by simp; omega, by simp⟩, by simp [tout]⟩

theorem arc_AB {i j : Nat} (hi : i < k) (hj : j < k) :
    (((0, i, j), (1, i, j)) : N3 × N3) ∈ tarcs k :=
  mem_tarcs.mpr ⟨mem_tnodes.mpr ⟨by simp, hi, hj, by simp⟩, by simp [tout]⟩

theorem arc_BA {i j : Nat} (hi : i < k) (hj : j + 1 < k) :
    (((1, i, j), (0, i, j + 1)) : N3 × N3) ∈ tarcs k :=
  mem_tarcs.mpr ⟨mem_tnodes.mpr ⟨by simp, hi, by show j < k; omega, by simp⟩, by simp [tout, hj]⟩

theorem arc_BC {i : Nat} (hi : i < k) : (((1, i, k - 1), (2, i, 0)) : N3 × N3) ∈ tarcs k :=
  mem_tarcs.mpr ⟨mem_tnodes.mpr ⟨by simp, hi, by show k - 1 < k; omega, by simp⟩, by
    simp [tout, show ¬ (k - 1 + 1 < k) by omega]⟩

theorem arc_col {i j : Nat} (hi : i < k) (hj : j < k) :
    (((1, i, j), (0, nxt k i, j)) : N3 × N3) ∈ tarcs k :=
  mem_tarcs.mpr ⟨mem_tnodes.mpr ⟨by simp, hi, hj, by simp⟩, by simp [tout]⟩

theorem imp_of_viol (σ : N3 → Bool) {e : N3 × N3} (h : viol σ e = false) :
    σ e.1 = true → σ e.2 = true := by
  unfold viol at h
  cases h1 : σ e.1 <;> cases h2 : σ e.2 <;> simp_all

/-- A row without violated arcs is constant. -/
theorem row_const (σ : N3 → Bool) {i : Nat} (hi : i < k)
    (hc : ∀ e ∈ tarcs k, e.1.2.1 = i → viol σ e = false) :
    ∀ j < k, σ (0, i, j) = σ (2, i, 0) := by
  have step : ∀ {a b : N3}, (a, b) ∈ tarcs k → a.2.1 = i → σ a = true → σ b = true :=
    fun h ha => imp_of_viol σ (hc _ h ha)
  have fwd : σ (2, i, 0) = true → ∀ j < k, σ (0, i, j) = true := by
    intro hC j hj
    induction j with
    | zero => exact step (arc_CA hi) rfl hC
    | succ j ih =>
      have h1 := ih (by omega)
      have h2 := step (arc_AB hi (by omega)) rfl h1
      exact step (arc_BA hi hj) rfl h2
  have bwd : ∀ d j, j + d = k - 1 → σ (1, i, j) = true → σ (1, i, k - 1) = true := by
    intro d
    induction d with
    | zero =>
      intro j hj h
      obtain rfl : j = k - 1 := by omega
      exact h
    | succ d ih =>
      intro j hj h
      have h1 := step (arc_BA hi (by omega)) rfl h
      have h2 := step (arc_AB hi (by omega)) rfl h1
      exact ih (j + 1) (by omega) h2
  intro j hj
  cases hA : σ (0, i, j) <;> cases hC : σ (2, i, 0)
  · rfl
  · have := fwd hC j hj
    rw [hA] at this
    cases this
  · have h1 := step (arc_AB hi hj) rfl hA
    have h2 := bwd (k - 1 - j) j (by omega) h1
    have h3 := step (arc_BC hi) rfl h2
    rw [hC] at h3
    cases h3
  · rfl

/-- A column without violated arcs is constant on the nodes `A(·,j)`. -/
theorem col_const (σ : N3 → Bool) {j : Nat} (hj : j < k)
    (hc : ∀ e ∈ tarcs k, e.1.2.2 = j → viol σ e = false) :
    ∀ i < k, σ (0, i, j) = σ (0, 0, j) := by
  have step : ∀ {a b : N3}, (a, b) ∈ tarcs k → a.2.2 = j → σ a = true → σ b = true :=
    fun h ha => imp_of_viol σ (hc _ h ha)
  have next : ∀ i < k, σ (0, i, j) = true → σ (0, nxt k i, j) = true := fun i hi h =>
    step (arc_col hi hj) rfl (step (arc_AB hi hj) rfl h)
  have fwd : σ (0, 0, j) = true → ∀ i < k, σ (0, i, j) = true := by
    intro h0 i hi
    induction i with
    | zero => exact h0
    | succ i ih =>
      have := next i (by omega) (ih (by omega))
      rwa [show nxt k i = i + 1 by unfold nxt; split <;> omega] at this
  have bwd : ∀ d i, i + d = k - 1 → σ (0, i, j) = true → σ (0, k - 1, j) = true := by
    intro d
    induction d with
    | zero =>
      intro i hi h
      obtain rfl : i = k - 1 := by omega
      exact h
    | succ d ih =>
      intro i hi h
      have := next i (by omega) h
      rw [show nxt k i = i + 1 by unfold nxt; split <;> omega] at this
      exact ih (i + 1) (by omega) this
  intro i hi
  cases hA : σ (0, i, j) <;> cases h0 : σ (0, 0, j)
  · rfl
  · have := fwd h0 i hi
    rw [hA] at this
    cases this
  · have h1 := bwd (k - 1 - i) i (by omega) hA
    have h2 := next (k - 1) (by omega) h1
    rw [show nxt k (k - 1) = 0 by unfold nxt; split <;> omega, h0] at h2
    cases h2
  · rfl

/-- Counting the indices `i < K` for which some element `e` of `L` with `r e = i` satisfies
`p`. -/
theorem countP_any_le {α : Type} (L : List α) (r : α → Nat) (p : α → Bool) (K : Nat) :
    (List.range K).countP (fun i => L.any fun e => r e == i && p e) ≤ L.countP p := by
  induction L with
  | nil => simp
  | cons e L ih =>
    have h1 : (List.range K).countP (fun i => (e :: L).any fun e => r e == i && p e) ≤
        (List.range K).countP (fun i => r e == i && p e) +
          (List.range K).countP (fun i => L.any fun e => r e == i && p e) :=
      countP_le_countP_add fun i _ h => by simpa [List.any_cons] using h
    rw [List.countP_cons]
    cases hp : p e
    · have h2 : (List.range K).countP (fun i => r e == i && p e) = 0 :=
        List.countP_eq_zero.mpr fun i _ h => by simp [hp] at h
      simp only [Bool.false_eq_true, ↓reduceIte]
      omega
    · have h2 : (List.range K).countP (fun i => r e == i && p e) ≤ 1 := by
        have h3 : (List.range K).countP (fun i => r e == i && p e) ≤ (List.range K).count (r e) :=
          List.countP_mono_left fun i _ h => by
            simp only [Bool.and_eq_true, beq_iff_eq] at h
            simp [h.1]
        have h4 := (List.nodup_range (n := K)).count (a := r e)
        rw [h4] at h3
        split at h3 <;> omega
      simp only [↓reduceIte]
      omega

theorem clean_of_any {σ : N3 → Bool} {r : N3 × N3 → Nat} {i : Nat}
    (h : ((tarcs k).any fun e => r e == i && viol σ e) = false) :
    ∀ e ∈ tarcs k, r e = i → viol σ e = false := by
  intro e he hr
  have := List.any_eq_false.mp h e he
  simp only [hr, beq_self_eq_true, Bool.true_and] at this
  simpa using this

/-- **The cut property of the torus gadget.** -/
theorem torus_cut (σ : N3 → Bool) :
    min ((List.range k).countP fun i => σ (2, i, 0))
        ((List.range k).countP fun i => !σ (2, i, 0)) ≤
      (tarcs k).countP (viol σ) := by
  have hR := countP_any_le (tarcs k) (fun e => e.1.2.1) (viol σ) k
  have hC := countP_any_le (tarcs k) (fun e => e.1.2.2) (viol σ) k
  generalize hrow : (fun i => (tarcs k).any fun e => e.1.2.1 == i && viol σ e) = rowD at hR
  generalize hcol : (fun j => (tarcs k).any fun e => e.1.2.2 == j && viol σ e) = colD at hC
  by_cases hmin : min ((List.range k).countP fun i => σ (2, i, 0))
      ((List.range k).countP fun i => !σ (2, i, 0)) ≤ (List.range k).countP rowD
  · omega
  · -- a clean row with a true contact and a clean row with a false contact
    have ex : ∀ b : Bool, (List.range k).countP rowD < (List.range k).countP (fun i => σ (2, i, 0) == b) →
        ∃ i < k, σ (2, i, 0) = b ∧ rowD i = false := by
      intro b hb
      refine Classical.byContradiction fun hne => ?_
      have : (List.range k).countP (fun i => σ (2, i, 0) == b) ≤ (List.range k).countP rowD :=
        List.countP_mono_left fun i hi h => by
          cases hr : rowD i
          · exact absurd ⟨i, List.mem_range.mp hi, by simpa using h, hr⟩ hne
          · rfl
      omega
    have et : (List.range k).countP (fun i => σ (2, i, 0) == true) =
        (List.range k).countP fun i => σ (2, i, 0) := List.countP_congr fun i _ => by simp
    have ef : (List.range k).countP (fun i => σ (2, i, 0) == false) =
        (List.range k).countP fun i => !σ (2, i, 0) := List.countP_congr fun i _ => by simp
    obtain ⟨i₁, hi₁, hs₁, hr₁⟩ := ex true (by rw [et]; omega)
    obtain ⟨i₀, hi₀, hs₀, hr₀⟩ := ex false (by rw [ef]; omega)
    have row₁ := row_const σ hi₁ (clean_of_any (r := fun e => e.1.2.1) (by rw [← hrow] at hr₁; exact hr₁))
    have row₀ := row_const σ hi₀ (clean_of_any (r := fun e => e.1.2.1) (by rw [← hrow] at hr₀; exact hr₀))
    have hall : ∀ j ∈ List.range k, colD j = true := by
      intro j hj
      have hj' := List.mem_range.mp hj
      cases hc : colD j
      · have col := col_const σ hj' (clean_of_any (r := fun e => e.1.2.2) (by rw [← hcol] at hc; exact hc))
        have a1 := col i₁ hi₁
        have a0 := col i₀ hi₀
        rw [row₁ j hj', hs₁] at a1
        rw [row₀ j hj', hs₀] at a0
        rw [← a1] at a0
        cases a0
      · rfl
    have hk' : (List.range k).countP colD = k := by
      rw [List.countP_eq_length.mpr hall, List.length_range]
    have : (List.range k).countP (fun i => σ (2, i, 0)) ≤ k := by
      have := List.countP_le_length (p := fun i => σ (2, i, 0)) (l := List.range k)
      rwa [List.length_range] at this
    omega

/-- The torus gadget satisfies the conditions for at most `Bd` occurrences, with `B = 3` and
`M = 6 * Bd`. -/
theorem torus_good (Bd : Nat) : torus.Good (fun k => k ≤ Bd) 3 (6 * Bd) where
  cont_lt k _ _ j hj := tenc_lt (by simp) hj (by simp; omega)
  arcs_lt k _ _ e he := by
    obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
    obtain ⟨h1, h2⟩ := mem_tarcs.mp he'
    have v1 := mem_tnodes.mp h1
    have v2 := valid_of_mem_tout v1 h2
    exact ⟨tenc_lt v1.1 v1.2.1 v1.2.2.1, tenc_lt v2.1 v2.2.1 v2.2.2.1⟩
  occ_le k _ _ v := by
    show (List.range k).countP (fun j => tenc k (2, j, 0) == v) +
      ((tarcs k).map fun e => (tenc k e.1, tenc k e.2)).countP (fun e => e.1 == v) +
      ((tarcs k).map fun e => (tenc k e.1, tenc k e.2)).countP (fun e => e.2 == v) ≤ 3
    rw [List.countP_map, List.countP_map]
    have key : ∀ n : N3, Valid k n → (tenc k n == v) = (n == tdec k v) := by
      intro n hn
      rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
      constructor
      · rintro rfl
        exact (tdec_tenc hn.2.1 hn.2.2.1).symm
      · rintro rfl
        exact tenc_tdec k v
    have e0 : (List.range k).countP (fun j => tenc k (2, j, 0) == v) =
        (List.range k).countP (fun j => ((2, j, 0) : N3) == tdec k v) :=
      List.countP_congr fun j hj => by
        rw [key _ ⟨by simp, List.mem_range.mp hj, by simp; omega, by simp⟩]
    have e1 : (tarcs k).countP ((fun e => e.1 == v) ∘ fun e => (tenc k e.1, tenc k e.2)) =
        (tarcs k).countP (fun e => e.1 == tdec k v) :=
      List.countP_congr fun e he => by
        simp only [Function.comp_apply]
        rw [key _ (mem_tnodes.mp (mem_tarcs.mp he).1)]
    have e2 : (tarcs k).countP ((fun e => e.2 == v) ∘ fun e => (tenc k e.1, tenc k e.2)) =
        (tarcs k).countP (fun e => e.2 == tdec k v) :=
      List.countP_congr fun e he => by
        simp only [Function.comp_apply]
        rw [key _ (valid_of_mem_tout (mem_tnodes.mp (mem_tarcs.mp he).1) (mem_tarcs.mp he).2)]
    rw [e0, e1, e2]
    exact torus_occ_le k (tdec k v)
  length_le k _ hB := by
    show ((tarcs k).map fun e => (tenc k e.1, tenc k e.2)).length ≤ 6 * Bd * k
    rw [List.length_map]
    have h1 := length_tarcs_le k
    have h2 : 6 * (k * k) ≤ 6 * Bd * k := by
      rw [Nat.mul_assoc]
      exact Nat.mul_le_mul_left 6 (Nat.mul_le_mul_right k hB)
    omega
  cut k _ _ σ := by
    show min ((List.range k).countP fun j => σ (tenc k (2, j, 0)))
        ((List.range k).countP fun j => !σ (tenc k (2, j, 0))) ≤
      ((tarcs k).map fun e => (tenc k e.1, tenc k e.2)).countP fun e => σ e.1 && !σ e.2
    rw [List.countP_map]
    exact torus_cut fun n => σ (tenc k n)

/-- **Stage 2.** MAX-3-SAT with at most `Bd` occurrences per variable L-reduces to MAX-3-SAT
with at most three occurrences per variable. -/
theorem lReducible_torus (Bd : Nat) : LReducible (max3SATB Bd) (max3SATB 3) :=
  lReducible_gadget (torus_good Bd) torus_isPT fun f hf x _ => by
    show occ f x ≤ Bd
    rw [← occurrences_eq_occ]
    exact hf x

end Occ

end Complexity

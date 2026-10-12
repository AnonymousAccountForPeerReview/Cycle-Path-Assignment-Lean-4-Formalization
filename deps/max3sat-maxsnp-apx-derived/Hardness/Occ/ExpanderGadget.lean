module

public import Hardness.Occ.Reduction
public import Hardness.Expander.Defs

/-!
# Stage 1: bounded occurrences via expanders

For an expander family `G` (`IsExpanderFamily D c G`), the gadget of a variable with `k`
occurrences is the multigraph `G k` on `N ≥ k` nodes; the `j`-th occurrence becomes node `j`,
and every arc `v → u` gives the clause `(¬ x^(v) ∨ x^(u))` (`expGadget`). Every node has `D`
outgoing and, by symmetry, `D` incoming arcs, so every new variable occurs at most `2 * D + 1`
times. The cut property: if at most half of the nodes are true, the expansion of the true set
gives as many violated arcs as true nodes; otherwise the expansion of the false set, together
with the symmetry of the arc list under reversal (`expArcs_swap_perm`), gives as many violated
arcs as false nodes.

`lReducible_max3SAT_expander`: MAX-3-SAT L-reduces to `max3SATB (2 * D + 1)`.
-/

@[expose] public section

set_option linter.dupNamespace false

namespace Complexity

open Complexity.PT

namespace Occ

/-! ### Sums over ranges -/

theorem sum_range_ite (N v a : Nat) :
    ((List.range N).map fun w => if w = v then a else 0).sum = if v < N then a else 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    by_cases h : N = v
    · subst h; simp
    · by_cases h' : v < N
      · simp [h, h', show v < N + 1 by omega]
      · simp [h, h', show ¬ v < N + 1 by omega]

theorem sum_filter_eq {α : Type} (l : List α) (p : α → Bool) (u : α → Nat) :
    ((l.filter p).map u).sum = (l.map fun x => if p x then u x else 0).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases h : p a <;> simp [h, ih]

/-! ### The gadget -/

variable {D c : Nat} {G : Nat → List (List Nat)}

/-- The arcs of `G k`, with multiplicities. -/
def expArcs (G : Nat → List (List Nat)) (k : Nat) : List (Nat × Nat) :=
  (List.range (G k).length).flatMap fun v => ((G k).getD v []).map fun u => (v, u)

/-- The expander gadget family. -/
def expGadget (G : Nat → List (List Nat)) : Gadget where
  nodes k := (G k).length
  cont _ j := j
  arcs := expArcs G

theorem expGadget_isPT (hG : PT G) : (expGadget G).IsPT := by
  refine ⟨?_, ?_, ?_⟩
  · show PT fun k => (G k).length
    fun_prop
  · show PT fun p : Nat × Nat => p.2
    fun_prop
  · show PT (expArcs G)
    unfold expArcs
    fun_prop

theorem getD_eq_nil {k v : Nat} (h : (G k).length ≤ v) : (G k).getD v [] = [] := by
  simp [List.getD_eq_getElem?_getD, h]

theorem getD_mem {k v : Nat} (h : v < (G k).length) : (G k).getD v [] ∈ G k := by
  simp [List.getD_eq_getElem?_getD, h]

theorem mem_expArcs {k : Nat} {e : Nat × Nat} :
    e ∈ expArcs G k ↔ e.1 < (G k).length ∧ e.2 ∈ (G k).getD e.1 [] := by
  obtain ⟨v, u⟩ := e
  simp only [expArcs, List.mem_flatMap, List.mem_range, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨w, hw, u', hu', rfl, rfl⟩
    exact ⟨hw, hu'⟩
  · rintro ⟨hv, hu⟩
    exact ⟨v, hv, u, hu, rfl, rfl⟩

theorem countP_expArcs (k : Nat) (p : Nat → Nat → Bool) :
    (expArcs G k).countP (fun e => p e.1 e.2) =
      ((List.range (G k).length).map fun v => ((G k).getD v []).countP (p v)).sum := by
  unfold expArcs
  rw [List.countP_flatMap]
  congr 1
  refine List.map_congr_left fun v _ => ?_
  simp only [Function.comp_apply, List.countP_map]
  rfl

theorem count_expArcs (k v u : Nat) :
    (expArcs G k).count (v, u) = ((G k).getD v []).count u := by
  have h := countP_expArcs (G := G) k fun a b => (a, b) == (v, u)
  have e : ∀ w, ((G k).getD w []).countP (fun b => (w, b) == (v, u)) =
      if w = v then ((G k).getD v []).count u else 0 := by
    intro w
    by_cases hw : w = v
    · subst hw
      simp only [ite_true, List.count]
      refine List.countP_congr fun b _ => ?_
      simp
    · simp only [hw, ite_false]
      refine List.countP_eq_zero.mpr fun b _ hb => ?_
      simp only [beq_iff_eq, Prod.mk.injEq] at hb
      exact hw hb.1
  simp only [e, sum_range_ite] at h
  rw [List.count]
  refine (Eq.trans (List.countP_congr fun e _ => ?_) h).trans ?_
  · obtain ⟨a, b⟩ := e
    rfl
  · split
    · rfl
    · next hv => rw [getD_eq_nil (by omega)]; rfl

theorem countP_fst_expArcs (k v : Nat) :
    (expArcs G k).countP (fun e => e.1 == v) = ((G k).getD v []).length := by
  have h := countP_expArcs (G := G) k fun a _ => a == v
  have e : ∀ w, ((G k).getD w []).countP (fun _ => w == v) =
      if w = v then ((G k).getD v []).length else 0 := by
    intro w
    by_cases hw : w = v
    · subst hw
      simp
    · simp [hw]
  simp only [e, sum_range_ite] at h
  rw [h]
  split
  · rfl
  · next hv => rw [getD_eq_nil (by omega)]; rfl

/-- The arc list is symmetric under reversal of the arcs. -/
theorem expArcs_swap_perm (hE : IsExpanderFamily D c G) (k : Nat) :
    ((expArcs G k).map Prod.swap).Perm (expArcs G k) := by
  rw [List.perm_iff_count]
  rintro ⟨a, b⟩
  have e : List.count (a, b) ((expArcs G k).map Prod.swap) = List.count (b, a) (expArcs G k) := by
    simp only [List.count, List.countP_map]
    refine List.countP_congr fun e _ => ?_
    obtain ⟨x, y⟩ := e
    simp only [Function.comp_apply, Prod.swap_prod_mk, beq_iff_eq, Prod.mk.injEq]
    tauto
  rw [e, count_expArcs, count_expArcs, hE.symm]

theorem countP_swap (hE : IsExpanderFamily D c G) (k : Nat) (p : Nat × Nat → Bool) :
    (expArcs G k).countP (fun e => p e.swap) = (expArcs G k).countP p := by
  rw [← (expArcs_swap_perm hE k).countP_eq p, List.countP_map]
  rfl

theorem length_getD_le (hE : IsExpanderFamily D c G) (k v : Nat) :
    ((G k).getD v []).length ≤ D := by
  by_cases hv : v < (G k).length
  · exact Nat.le_of_eq (hE.degree k _ (getD_mem hv))
  · rw [getD_eq_nil (by omega)]
    exact Nat.zero_le _

theorem lt_of_mem_getD (hE : IsExpanderFamily D c G) {k v u : Nat}
    (h : u ∈ (G k).getD v []) : u < (G k).length := by
  by_cases hv : v < (G k).length
  · exact hE.range k _ (getD_mem hv) u h
  · rw [getD_eq_nil (by omega)] at h
    simp at h

/-- The arcs leaving the set of nodes where `p` holds. -/
theorem leaving_eq (hE : IsExpanderFamily D c G) (k : Nat) (p : Nat → Bool) :
    (((List.range (G k).length).filter p).flatMap fun v => ((G k).getD v []).filter
        fun u => decide (u ∉ (List.range (G k).length).filter p)).length =
      (expArcs G k).countP fun e => p e.1 && !p e.2 := by
  rw [List.length_flatMap, sum_filter_eq, countP_expArcs (G := G) k fun a b => p a && !p b]
  congr 1
  refine List.map_congr_left fun v _ => ?_
  by_cases hv : p v
  · simp only [hv, ite_true, Bool.true_and]
    rw [← List.countP_eq_length_filter]
    refine List.countP_congr fun u hu => ?_
    have hu' := lt_of_mem_getD hE hu
    simp [List.mem_filter, hu']
  · simp only [hv, Bool.false_eq_true, ite_false, Bool.false_and]
    simp

theorem expGadget_good (hE : IsExpanderFamily D c G) :
    (expGadget G).Good (fun _ => True) (2 * D + 1) (c * D) where
  cont_lt k hk _ j hj := Nat.lt_of_lt_of_le hj (hE.size_ge k hk)
  arcs_lt k _ _ e he := by
    obtain ⟨h1, h2⟩ := mem_expArcs.mp he
    exact ⟨h1, lt_of_mem_getD hE h2⟩
  occ_le k _ _ v := by
    show (List.range k).countP (fun j => j == v) + (expArcs G k).countP (fun e => e.1 == v) +
      (expArcs G k).countP (fun e => e.2 == v) ≤ 2 * D + 1
    have h1 : (List.range k).countP (fun j => j == v) ≤ 1 := by
      have := (List.nodup_range (n := k)).count (a := v)
      rw [List.count] at this
      rw [this]
      split <;> omega
    have h2 : (expArcs G k).countP (fun e => e.2 == v) = (expArcs G k).countP (fun e => e.1 == v) :=
      (countP_swap hE k fun e => e.2 == v).symm
    rw [h2, countP_fst_expArcs]
    have := length_getD_le hE k v
    omega
  length_le k hk _ := by
    show (expArcs G k).length ≤ c * D * k
    have h := countP_expArcs (G := G) k fun _ _ => true
    rw [List.countP_true] at h
    rw [h]
    have h1 : ((List.range (G k).length).map fun v => ((G k).getD v []).countP fun _ => true).sum ≤
        ((List.range (G k).length).map fun _ => D).sum :=
      sum_map_le_sum_map _ _ _ fun v _ => by
        rw [List.countP_true]
        exact length_getD_le hE k v
    have h2 : ((List.range (G k).length).map fun _ => D).sum = (G k).length * D := by
      simp
    have h3 := Nat.mul_le_mul_right D (hE.size_le k hk)
    rw [Nat.mul_right_comm] at h3
    omega
  cut k hk _ σ := by
    show min ((List.range k).countP σ) ((List.range k).countP fun j => !σ j) ≤
      (expArcs G k).countP fun e => σ e.1 && !σ e.2
    have hkN := hE.size_ge k hk
    have hsub : (List.range k).Sublist (List.range (G k).length) := List.range_sublist.mpr hkN
    -- the true and the false nodes
    have hT := hsub.countP_le (p := σ)
    have hF := hsub.countP_le (p := fun j => !σ j)
    have hsum : (List.range (G k).length).countP σ +
        (List.range (G k).length).countP (fun j => !σ j) = (G k).length := by
      have := List.length_eq_countP_add_countP σ (l := List.range (G k).length)
      rw [List.length_range] at this
      have e : (List.range (G k).length).countP (fun j => decide ¬(σ j = true)) =
          (List.range (G k).length).countP (fun j => !σ j) :=
        List.countP_congr fun j _ => by cases σ j <;> simp
      rw [e] at this
      omega
    have hexp : ∀ p : Nat → Bool, 2 * (List.range (G k).length).countP p ≤ (G k).length →
        (List.range (G k).length).countP p ≤ (expArcs G k).countP fun e => p e.1 && !p e.2 := by
      intro p hp
      rw [List.countP_eq_length_filter] at hp ⊢
      rw [← leaving_eq hE k p]
      exact hE.expand k _ (List.nodup_range.filter p)
        (fun v hv => List.mem_range.mp (List.mem_filter.mp hv).1) hp
    by_cases h2 : 2 * (List.range (G k).length).countP σ ≤ (G k).length
    · have := hexp σ h2
      omega
    · have := hexp (fun j => !σ j) (by omega)
      have e : ((expArcs G k).countP fun e => !σ e.1 && !!σ e.2) =
          (expArcs G k).countP fun e => σ e.1 && !σ e.2 := by
        rw [← countP_swap hE k]
        refine List.countP_congr fun e _ => ?_
        obtain ⟨a, b⟩ := e
        simp only [Prod.swap_prod_mk, Bool.not_not]
        cases σ a <;> cases σ b <;> rfl
      omega

/-- **Stage 1.** MAX-3-SAT L-reduces to MAX-3-SAT with at most `2 * D + 1` occurrences per
variable, for a polynomial-time expander family of degree `D`. -/
theorem lReducible_max3SAT_expander (hG : PT G) (hE : IsExpanderFamily D c G) :
    LReducible max3SAT (max3SATB (2 * D + 1)) :=
  lReducible_max3SAT_max3SATQ_true.trans
    (lReducible_gadget (expGadget_good hE) (expGadget_isPT hG) fun _ _ _ _ => trivial)

end Occ

end Complexity

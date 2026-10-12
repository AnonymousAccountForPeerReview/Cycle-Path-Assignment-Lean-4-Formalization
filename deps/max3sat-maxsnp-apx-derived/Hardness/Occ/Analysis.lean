module

public import Hardness.Occ.Gadget

/-!
# Consistency gadgets: conditions and occurrence counting

`Gadget.Good Adm B M`: contacts and arc endpoints are nodes, every node has at most `B`
occurrences counting its contact uses, a gadget for `k` occurrences has at most `M * k` arcs,
and the cut property holds: under every assignment the arcs from true to false nodes are at
least as many as the minority of the contacts. For a formula `f` whose numbers of occurrences
are admissible:

* `isThreeCNF_red`: `red f` is a 3-CNF formula (for `f` a 3-CNF formula);
* `occurrences_red_le`: every variable of `red f` occurs at most `B` times (the new variable
  `x * W + v` occurs exactly as often as node `v` in the gadget of `x`).

The rounding and lifting inequalities are in `Hardness.Occ.Rounding`.
-/

@[expose] public section

set_option linter.dupNamespace false

namespace Complexity.Occ

open Complexity.PT

/-! ### Sums of lists of numbers -/

theorem sum_map_add {α : Type} (l : List α) (u v : α → Nat) :
    (l.map fun x => u x + v x).sum = (l.map u).sum + (l.map v).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; omega

theorem sum_map_le_sum_map {α : Type} (l : List α) (u v : α → Nat) (h : ∀ x ∈ l, u x ≤ v x) :
    (l.map u).sum ≤ (l.map v).sum := by
  induction l with
  | nil => exact Nat.le_refl _
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (h a List.mem_cons_self) (ih fun x hx => h x (List.mem_cons_of_mem _ hx))

theorem sum_map_mul_left {α : Type} (l : List α) (M : Nat) (u : α → Nat) :
    (l.map fun x => M * u x).sum = M * (l.map u).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih, Nat.mul_add]

theorem sum_map_eq_zero {α : Type} (l : List α) (u : α → Nat) (h : ∀ x ∈ l, u x = 0) :
    (l.map u).sum = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, h a List.mem_cons_self,
      ih fun x hx => h x (List.mem_cons_of_mem _ hx)]

theorem le_sum_map_of_mem {α : Type} {l : List α} (u : α → Nat) {a : α} (h : a ∈ l) :
    u a ≤ (l.map u).sum := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := ih h; omega

/-- A sum with at most one nonzero term. -/
theorem sum_map_le_of_single {α : Type} [DecidableEq α] {l : List α} (hl : l.Nodup) (u : α → Nat)
    (x₀ : α) {B : Nat} (h0 : ∀ x ∈ l, x ≠ x₀ → u x = 0) (hB : x₀ ∈ l → u x₀ ≤ B) :
    (l.map u).sum ≤ B := by
  induction l with
  | nil => simp
  | cons a l ih =>
    obtain ⟨ha, hl⟩ := List.nodup_cons.mp hl
    simp only [List.map_cons, List.sum_cons]
    by_cases hax : a = x₀
    · subst hax
      have : (l.map u).sum = 0 :=
        sum_map_eq_zero l u fun x hx => h0 x (List.mem_cons_of_mem _ hx) fun e => ha (e ▸ hx)
      have := hB List.mem_cons_self
      omega
    · have := h0 a List.mem_cons_self hax
      have := ih hl (fun x hx => h0 x (List.mem_cons_of_mem _ hx))
        (fun hx => hB (List.mem_cons_of_mem _ hx))
      omega

/-! ### Names of nodes -/

theorem name_eq_iff {W x c n : Nat} (hc : c < W) : x * W + c = n ↔ x = n / W ∧ c = n % W := by
  have hW : 0 < W := Nat.lt_of_le_of_lt (Nat.zero_le _) hc
  constructor
  · rintro rfl
    refine ⟨?_, ?_⟩
    · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hW, Nat.div_eq_of_lt hc, Nat.zero_add]
    · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]
  · rintro ⟨rfl, rfl⟩
    exact Nat.div_add_mod' n W

theorem name_div {W x c : Nat} (hc : c < W) : (x * W + c) / W = x :=
  ((name_eq_iff hc).mp rfl).1.symm

/-! ### Conditions on a gadget family -/

namespace Gadget

/-- The conditions on a gadget family, for the admissible numbers of occurrences `k ≥ 1`. -/
structure Good (g : Gadget) (Adm : Nat → Prop) (B M : Nat) : Prop where
  cont_lt : ∀ k, 1 ≤ k → Adm k → ∀ j < k, g.cont k j < g.nodes k
  arcs_lt : ∀ k, 1 ≤ k → Adm k → ∀ e ∈ g.arcs k, e.1 < g.nodes k ∧ e.2 < g.nodes k
  occ_le : ∀ k, 1 ≤ k → Adm k → ∀ v,
    (List.range k).countP (fun j => g.cont k j == v) + (g.arcs k).countP (fun e => e.1 == v) +
      (g.arcs k).countP (fun e => e.2 == v) ≤ B
  length_le : ∀ k, 1 ≤ k → Adm k → (g.arcs k).length ≤ M * k
  cut : ∀ k, 1 ≤ k → Adm k → ∀ σ : Nat → Bool,
    min ((List.range k).countP fun j => σ (g.cont k j))
        ((List.range k).countP fun j => !σ (g.cont k j)) ≤
      (g.arcs k).countP fun e => σ e.1 && !σ e.2

variable {g : Gadget} {Adm : Nat → Prop} {B M : Nat}

theorem nodes_lt_width (f : SAT.CNF) {x : Nat} (hx : x < SAT.variableBound f) :
    g.nodes (occ f x) < g.width f :=
  Nat.lt_succ_of_le (le_sum_map_of_mem (fun x => g.nodes (occ f x)) (List.mem_range.mpr hx))

/-! ### Formulas -/

theorem relabel_flatten (f : SAT.CNF) :
    (g.relabel f).flatten = (annC [] f.flatten).map (g.newLit f) := by
  rw [relabel, ← List.map_flatten, flatten_ann]

theorem length_block (f : SAT.CNF) (x : Nat) :
    (g.block f x).length = if occ f x = 0 then 0 else (g.arcs (occ f x)).length := by
  unfold block
  split <;> simp

theorem length_gadgetCNF (f : SAT.CNF) :
    (g.gadgetCNF f).length = ((List.range (SAT.variableBound f)).map fun x => (g.block f x).length).sum := by
  rw [gadgetCNF, List.length_flatMap]

theorem satCount_gadgetCNF (σ : SAT.Assignment) (f : SAT.CNF) :
    SAT.satCount σ (g.gadgetCNF f) =
      ((List.range (SAT.variableBound f)).map fun x => SAT.satCount σ (g.block f x)).sum := by
  unfold gadgetCNF SAT.satCount
  rw [List.countP_flatMap]
  rfl

theorem isThreeCNF_red (f : SAT.CNF) (h3 : SAT.IsThreeCNF f) : SAT.IsThreeCNF (g.red f) := by
  intro cl hcl
  rcases List.mem_append.mp hcl with h | h
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp h
    have hc' : c.map Prod.fst ∈ f := by
      rw [← ann_map_fst f]
      exact List.mem_map_of_mem hc
    have := h3 _ hc'
    simpa using this
  · obtain ⟨x, -, hx⟩ := List.mem_flatMap.mp h
    unfold block at hx
    split at hx
    · simp at hx
    · obtain ⟨e, -, rfl⟩ := List.mem_map.mp hx
      simp [arcClause]

/-! ### Occurrences -/

theorem cnt_flatten_flatMap (l : List Nat) (h : Nat → SAT.CNF) (n : Nat) :
    cnt (l.flatMap h).flatten n = (l.map fun x => cnt (h x).flatten n).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, List.flatten_append, cnt_append, ih]; rfl

theorem cnt_flatten_arcClause (W x : Nat) (L : List (Nat × Nat)) (n : Nat) :
    cnt (L.map (arcClause W x)).flatten n =
      L.countP (fun e => x * W + e.1 == n) + L.countP (fun e => x * W + e.2 == n) := by
  induction L with
  | nil => rfl
  | cons e L ih =>
    rw [List.map_cons, List.flatten_cons, cnt_append, ih]
    simp only [arcClause, cnt, List.countP_cons, List.countP_nil]
    omega

theorem cnt_relabel (f : SAT.CNF) (n : Nat) :
    cnt (g.relabel f).flatten n =
      ((List.range (SAT.variableBound f)).map fun x =>
        (List.range (occ f x)).countP fun j => x * g.width f + g.cont (occ f x) j == n).sum := by
  rw [relabel_flatten, cnt, List.countP_map]
  exact countP_annC (fun _ hl => var_lt_of_mem_flatten hl)
    (fun p => p.1 * g.width f + g.cont (occ f p.1) p.2 == n)

theorem occurrences_red_le (hg : g.Good Adm B M) (f : SAT.CNF)
    (hA : ∀ x, 1 ≤ occ f x → Adm (occ f x)) (n : Nat) : SAT.occurrences (g.red f) n ≤ B := by
  rw [occurrences_eq_occ, occ, red, List.flatten_append, cnt_append, cnt_relabel, gadgetCNF,
    cnt_flatten_flatMap, ← sum_map_add]
  refine sum_map_le_of_single List.nodup_range _ (n / g.width f) ?_ ?_
  · intro x hx hne
    have hxV := List.mem_range.mp hx
    have hW := nodes_lt_width (g := g) f hxV
    unfold block
    split
    · next h0 => simp [h0, cnt]
    · next h0 =>
      have hk : 1 ≤ occ f x := by omega
      have hadm := hA x hk
      rw [cnt_flatten_arcClause]
      have e1 : (List.range (occ f x)).countP
          (fun j => x * g.width f + g.cont (occ f x) j == n) = 0 := by
        refine List.countP_eq_zero.mpr fun j hj h => ?_
        have hc := hg.cont_lt _ hk hadm j (List.mem_range.mp hj)
        exact hne ((name_eq_iff (Nat.lt_trans hc hW)).mp (beq_iff_eq.mp h)).1
      have e2 : ∀ (p : Nat × Nat → Nat), (∀ e ∈ g.arcs (occ f x), p e < g.nodes (occ f x)) →
          (g.arcs (occ f x)).countP (fun e => x * g.width f + p e == n) = 0 := by
        intro p hp
        refine List.countP_eq_zero.mpr fun e he h => ?_
        exact hne ((name_eq_iff (Nat.lt_trans (hp e he) hW)).mp (beq_iff_eq.mp h)).1
      rw [e1, e2 Prod.fst fun e he => (hg.arcs_lt _ hk hadm e he).1,
        e2 Prod.snd fun e he => (hg.arcs_lt _ hk hadm e he).2]
  · intro hx
    have hxV := List.mem_range.mp hx
    have hW := nodes_lt_width (g := g) f hxV
    unfold block
    split
    · next h0 => simp [h0, cnt]
    · next h0 =>
      have hk : 1 ≤ occ f (n / g.width f) := by omega
      have hadm := hA _ hk
      rw [cnt_flatten_arcClause]
      have := hg.occ_le _ hk hadm (n % g.width f)
      have e1 : (List.range (occ f (n / g.width f))).countP
          (fun j => n / g.width f * g.width f + g.cont (occ f (n / g.width f)) j == n) =
          (List.range (occ f (n / g.width f))).countP
            (fun j => g.cont (occ f (n / g.width f)) j == n % g.width f) := by
        refine List.countP_congr fun j hj => ?_
        have hc := hg.cont_lt _ hk hadm j (List.mem_range.mp hj)
        simp only [beq_iff_eq, name_eq_iff (Nat.lt_trans hc hW), true_and]
      have e2 : ∀ (p : Nat × Nat → Nat),
          (∀ e ∈ g.arcs (occ f (n / g.width f)), p e < g.nodes (occ f (n / g.width f))) →
          (g.arcs (occ f (n / g.width f))).countP (fun e => n / g.width f * g.width f + p e == n) =
            (g.arcs (occ f (n / g.width f))).countP (fun e => p e == n % g.width f) := by
        intro p hp
        refine List.countP_congr fun e he => ?_
        simp only [beq_iff_eq, name_eq_iff (Nat.lt_trans (hp e he) hW), true_and]
      rw [e1, e2 Prod.fst fun e he => (hg.arcs_lt _ hk hadm e he).1,
        e2 Prod.snd fun e he => (hg.arcs_lt _ hk hadm e he).2]
      omega

end Gadget

end Complexity.Occ

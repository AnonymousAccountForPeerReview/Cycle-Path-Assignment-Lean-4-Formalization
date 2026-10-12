module

public import Hardness.Expander.Defs
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.List.Range
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Neighbour lists of a rotation map

For a rotation map `rot` on `Fin n × Fin q` (vertex, port), `nbrs rot` lists for every vertex the
heads of its `q` darts. This file translates involutivity and a `Finset` cut bound for `rot`
into plain `List`/`Nat` statements about `nbrs rot`. It depends on Mathlib only.
-/

@[expose] public section

namespace Complexity.Expander

variable {n q : Nat}

/-- Neighbour lists of a rotation map: row `v` lists the vertices `(rot (v, i)).1`. -/
def nbrs (rot : Fin n × Fin q → Fin n × Fin q) : List (List Nat) :=
  (List.finRange n).map fun v => (List.finRange q).map fun i => (rot (v, i)).1.val

variable (rot : Fin n × Fin q → Fin n × Fin q)

@[simp] theorem length_nbrs : (nbrs rot).length = n := by simp [nbrs]

theorem length_of_mem_nbrs {row : List Nat} (h : row ∈ nbrs rot) : row.length = q := by
  simp only [nbrs, List.mem_map] at h
  obtain ⟨v, -, rfl⟩ := h
  simp

theorem lt_of_mem_nbrs {row : List Nat} (h : row ∈ nbrs rot) {u : Nat} (hu : u ∈ row) :
    u < (nbrs rot).length := by
  simp only [nbrs, List.mem_map] at h
  obtain ⟨v, -, rfl⟩ := h
  simp only [List.mem_map] at hu
  obtain ⟨i, -, rfl⟩ := hu
  simp

/-- `nbrs` as a program on plain ranges. -/
theorem nbrs_eq_range (g : Nat → Nat → Nat)
    (hg : ∀ (v : Fin n) (i : Fin q), g v.val i.val = (rot (v, i)).1.val) :
    nbrs rot = (List.range n).map fun v => (List.range q).map fun i => g v i := by
  unfold nbrs
  rw [← List.map_coe_finRange_eq_range (n := n), List.map_map]
  refine List.map_congr_left fun v _ => ?_
  rw [Function.comp_apply, ← List.map_coe_finRange_eq_range (n := q), List.map_map]
  exact List.map_congr_left fun i _ => (hg v i).symm

theorem getD_nbrs (v : Fin n) :
    (nbrs rot).getD v.val [] = (List.finRange q).map fun i => (rot (v, i)).1.val := by
  simp [nbrs, List.getD_eq_getElem?_getD]

theorem getD_nbrs_of_le {v : Nat} (h : n ≤ v) : (nbrs rot).getD v [] = [] := by
  simp [nbrs, List.getD_eq_getElem?_getD, h]

theorem mem_getD_nbrs_lt {v u : Nat} (h : u ∈ (nbrs rot).getD v []) : u < n := by
  by_cases hv : v < n
  · have := getD_nbrs rot ⟨v, hv⟩
    simp only at this
    rw [this, List.mem_map] at h
    obtain ⟨i, -, rfl⟩ := h
    exact Fin.isLt _
  · rw [getD_nbrs_of_le rot (Nat.le_of_not_lt hv)] at h
    simp at h

theorem length_filter_finRange (p : Fin q → Bool) :
    ((List.finRange q).filter p).length = (Finset.univ.filter fun i => p i = true).card := by
  rw [← List.toFinset_card_of_nodup ((List.nodup_finRange q).filter _)]
  congr 1
  ext i
  simp

theorem count_getD_nbrs (v u : Fin n) :
    ((nbrs rot).getD v.val []).count u.val =
      (Finset.univ.filter fun e : Fin n × Fin q => e.1 = v ∧ (rot e).1 = u).card := by
  rw [getD_nbrs, List.count_eq_countP, List.countP_map, List.countP_eq_length_filter,
    length_filter_finRange]
  refine Finset.card_bij (fun i _ => (v, i)) ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply,
      beq_iff_eq] at hi
    simp [Fin.ext_iff, hi]
  · intro i _ j _ h
    simpa using h
  · rintro ⟨w, i⟩ he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
    obtain ⟨rfl, h2⟩ := he
    exact ⟨i, by simp [h2], rfl⟩

/-- Symmetry: an involutive rotation map has as many darts from `v` to `u` as from `u` to
`v`. -/
theorem count_nbrs_symm (hrot : Function.Involutive rot) (v u : Nat) :
    ((nbrs rot).getD v []).count u = ((nbrs rot).getD u []).count v := by
  by_cases hv : v < n
  · by_cases hu : u < n
    · have h1 := count_getD_nbrs rot ⟨v, hv⟩ ⟨u, hu⟩
      have h2 := count_getD_nbrs rot ⟨u, hu⟩ ⟨v, hv⟩
      simp only at h1 h2
      rw [h1, h2]
      refine Finset.card_bij (fun e _ => rot e) ?_ ?_ ?_
      · intro e he
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
        exact ⟨he.2, by rw [hrot e]; exact he.1⟩
      · intro e _ e' _ h
        exact hrot.injective h
      · intro e he
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
        refine ⟨rot e, ?_, hrot e⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨he.2, by rw [hrot e]; exact he.1⟩
    · rw [getD_nbrs_of_le rot (Nat.le_of_not_lt hu), List.count_nil]
      refine List.count_eq_zero.mpr fun h => hu (mem_getD_nbrs_lt rot h)
  · rw [getD_nbrs_of_le rot (Nat.le_of_not_lt hv), List.count_nil]
    exact (List.count_eq_zero.mpr fun h => hv (mem_getD_nbrs_lt rot h)).symm

/-- The number of arcs leaving a duplicate-free list of vertices, as the cardinality of a
`Finset` cut. -/
theorem length_boundary (S : List Nat) (hS : S.Nodup) (hlt : ∀ v ∈ S, v < n) :
    (S.flatMap fun v => ((nbrs rot).getD v []).filter fun u => decide (u ∉ S)).length =
      (Finset.univ.filter fun e : Fin n × Fin q =>
        e.1 ∈ (Finset.univ.filter fun v : Fin n => v.val ∈ S) ∧
          (rot e).1 ∉ (Finset.univ.filter fun v : Fin n => v.val ∈ S)).card := by
  classical
  set Sf : Finset (Fin n) := Finset.univ.filter fun v : Fin n => v.val ∈ S with hSf
  have hmap : Sf.map Fin.valEmbedding = S.toFinset := by
    ext v
    simp only [Finset.mem_map, hSf, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply, List.mem_toFinset]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact hw
    · intro hv
      exact ⟨⟨v, hlt v hv⟩, hv, rfl⟩
  rw [List.length_flatMap, ← List.sum_toFinset _ hS, ← hmap, Finset.sum_map]
  have hcut : (Finset.univ.filter fun e : Fin n × Fin q => e.1 ∈ Sf ∧ (rot e).1 ∉ Sf) =
      (Sf.sigma (fun v => Finset.univ.filter fun i : Fin q => (rot (v, i)).1 ∉ Sf)).map
        (Equiv.sigmaEquivProd (Fin n) (Fin q)).toEmbedding := by
    ext ⟨v, i⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Finset.mem_sigma, Equiv.coe_toEmbedding, Equiv.sigmaEquivProd_apply, Sigma.exists,
      Prod.mk.injEq]
    constructor
    · intro h
      exact ⟨v, i, h, rfl, rfl⟩
    · rintro ⟨v', i', h, rfl, rfl⟩
      exact h
  rw [hcut, Finset.card_map, Finset.card_sigma]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Fin.valEmbedding_apply, getD_nbrs, List.filter_map, List.length_map,
    length_filter_finRange]
  congr 1
  ext i
  simp [hSf]

/-- Edge expansion in list form, from a `Finset` cut bound. -/
theorem boundary_ge (c : Nat)
    (hcut : ∀ S : Finset (Fin n), 2 * S.card ≤ n →
      c * S.card ≤ (Finset.univ.filter fun e : Fin n × Fin q => e.1 ∈ S ∧ (rot e).1 ∉ S).card)
    (S : List Nat) (hS : S.Nodup) (hlt : ∀ v ∈ S, v < n) (hsmall : 2 * S.length ≤ n) :
    c * S.length ≤
      (S.flatMap fun v => ((nbrs rot).getD v []).filter fun u => decide (u ∉ S)).length := by
  classical
  have hcard : (Finset.univ.filter fun v : Fin n => v.val ∈ S).card = S.length := by
    rw [← List.toFinset_card_of_nodup hS, ← Finset.card_map Fin.valEmbedding]
    congr 1
    ext v
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply, List.mem_toFinset]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact hw
    · intro hv
      exact ⟨⟨v, hlt v hv⟩, hv, rfl⟩
  rw [length_boundary rot S hS hlt, ← hcard]
  exact hcut _ (by rw [hcard]; exact hsmall)

/-- A family of involutive rotation maps on `Fin (N k) × Fin D` with `k ≤ N k ≤ c * k` and the
cut bound `2 |S| ≤ |∂S|` for `2 |S| ≤ N k` gives an expander family in list form, with the
stronger expansion bound `2 * S.length ≤ …`. -/
theorem isExpanderFamily_nbrs (D c : Nat) (N : Nat → Nat)
    (rot : ∀ k, Fin (N k) × Fin D → Fin (N k) × Fin D)
    (hge : ∀ k, 1 ≤ k → k ≤ N k) (hle : ∀ k, 1 ≤ k → N k ≤ c * k)
    (hinv : ∀ k, Function.Involutive (rot k))
    (hcut : ∀ k (S : Finset (Fin (N k))), 2 * S.card ≤ N k →
      2 * S.card ≤
        (Finset.univ.filter fun e : Fin (N k) × Fin D => e.1 ∈ S ∧ (rot k e).1 ∉ S).card) :
    IsExpanderFamily D c (fun k => nbrs (rot k)) ∧
      ∀ k (S : List Nat), S.Nodup → (∀ v ∈ S, v < (nbrs (rot k)).length) →
        2 * S.length ≤ (nbrs (rot k)).length →
        2 * S.length ≤
          (S.flatMap fun v => ((nbrs (rot k)).getD v []).filter fun u => decide (u ∉ S)).length := by
  have hstrong : ∀ k (S : List Nat), S.Nodup → (∀ v ∈ S, v < (nbrs (rot k)).length) →
      2 * S.length ≤ (nbrs (rot k)).length →
      2 * S.length ≤
        (S.flatMap fun v => ((nbrs (rot k)).getD v []).filter fun u => decide (u ∉ S)).length := by
    intro k S hS hlt hsmall
    simp only [length_nbrs] at hlt hsmall
    exact boundary_ge (rot k) 2 (hcut k) S hS hlt hsmall
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, hstrong⟩
  · intro k hk
    simpa using hge k hk
  · intro k hk
    simpa using hle k hk
  · intro k row hrow
    exact length_of_mem_nbrs (rot k) hrow
  · intro k row hrow u hu
    exact lt_of_mem_nbrs (rot k) hrow hu
  · intro k v u
    exact count_nbrs_symm (rot k) (hinv k) v u
  · intro k S hS hlt hsmall
    have := hstrong k S hS hlt hsmall
    omega

end Complexity.Expander

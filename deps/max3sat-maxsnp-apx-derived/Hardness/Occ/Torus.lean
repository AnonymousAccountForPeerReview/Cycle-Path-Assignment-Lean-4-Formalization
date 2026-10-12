module

public import Hardness.Occ.Reduction

/-!
# Stage 2: the torus gadget

For a variable with `k` occurrences the gadget has the nodes `A(i,j) = (0,i,j)`,
`B(i,j) = (1,i,j)` (`i, j < k`) and the contacts `C i = (2,i,0)`, and the arcs

* `A(i,j) → B(i,j)`, `B(i,j) → A(i,j+1)` (`j + 1 < k`), `B(i,k-1) → C i → A(i,0)` (row `i`),
* `B(i,j) → A(i+1 mod k, j)` (column `j`).

Every node has in-degree plus out-degree plus contact uses at most `3`
(`torus_occ_le`): this file gives the nodes as triples, the successor lists `tout`, the
predecessor lists `tin`, and proves that every arc `m → w` has `m ∈ tin w`. Triples are coded
as numbers by `tenc k (t, i, j) = t * k² + i * k + j` (`torus`).
-/

@[expose] public section

set_option linter.dupNamespace false

namespace Complexity

open Complexity.PT

namespace Occ

/-- Nodes of the torus gadget: `(type, row, column)`. -/
abbrev N3 := Nat × Nat × Nat

/-- The next row index, cyclically. -/
def nxt (k i : Nat) : Nat := if i + 1 < k then i + 1 else 0

/-- The previous row index, cyclically. -/
def prv (k i : Nat) : Nat := if i = 0 then k - 1 else i - 1

/-- The successors of a node. -/
def tout (k : Nat) (n : N3) : List N3 :=
  if n.1 = 0 then [(1, n.2.1, n.2.2)]
  else if n.1 = 1 then
    [if n.2.2 + 1 < k then (0, n.2.1, n.2.2 + 1) else (2, n.2.1, 0), (0, nxt k n.2.1, n.2.2)]
  else [(0, n.2.1, 0)]

/-- The predecessors of a node. -/
def tin (k : Nat) (n : N3) : List N3 :=
  if n.1 = 0 then
    [if n.2.2 = 0 then (2, n.2.1, 0) else (1, n.2.1, n.2.2 - 1), (1, prv k n.2.1, n.2.2)]
  else if n.1 = 1 then [(0, n.2.1, n.2.2)]
  else [(1, n.2.1, k - 1)]

/-- The code of a node. -/
def tenc (k : Nat) (n : N3) : Nat := n.1 * (k * k) + (n.2.1 * k + n.2.2)

/-- The node of a code. -/
def tdec (k v : Nat) : N3 := (v / (k * k), v % (k * k) / k, v % (k * k) % k)

/-- The triples that are nodes (contacts have column `0`). -/
def isNode (n : N3) : Bool := decide (n.1 ≤ 1) || decide (n.2.2 = 0)

/-- The nodes of the gadget. -/
def tnodes (k : Nat) : List N3 := ((List.range (3 * (k * k))).map (tdec k)).filter isNode

/-- The arcs of the gadget. -/
def tarcs (k : Nat) : List (N3 × N3) := (tnodes k).flatMap fun m => (tout k m).map fun w => (m, w)

/-- The torus gadget family. -/
def torus : Gadget where
  nodes k := 3 * (k * k)
  cont k i := tenc k (2, i, 0)
  arcs k := (tarcs k).map fun e => (tenc k e.1, tenc k e.2)

theorem torus_isPT : torus.IsPT := by
  refine ⟨?_, ?_, ?_⟩
  · show PT fun k => 3 * (k * k)
    fun_prop
  · show PT fun p : Nat × Nat => tenc p.1 (2, p.2, 0)
    unfold tenc
    fun_prop
  · show PT fun k => (tarcs k).map fun e => (tenc k e.1, tenc k e.2)
    unfold tarcs tnodes tout tdec tenc isNode nxt
    fun_prop

/-! ### Codes of nodes -/

theorem mul_add_lt {k i j : Nat} (hi : i < k) (hj : j < k) : i * k + j < k * k :=
  Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj _)
    (by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right k hi)

theorem tdec_tenc {k : Nat} {n : N3} (hi : n.2.1 < k) (hj : n.2.2 < k) : tdec k (tenc k n) = n := by
  obtain ⟨t, i, j⟩ := n
  have h := mul_add_lt hi hj
  simp only [tdec, tenc]
  rw [name_div h, ← ((name_eq_iff h).mp rfl).2, name_div hj, ← ((name_eq_iff hj).mp rfl).2]

theorem tenc_tdec (k v : Nat) : tenc k (tdec k v) = v := by
  simp only [tdec, tenc]
  rw [Nat.div_add_mod' (v % (k * k)) k, Nat.div_add_mod' v (k * k)]

theorem tenc_lt {k : Nat} {n : N3} (ht : n.1 < 3) (hi : n.2.1 < k) (hj : n.2.2 < k) :
    tenc k n < 3 * (k * k) := by
  obtain ⟨t, i, j⟩ := n
  simp only at ht hi hj
  have h := mul_add_lt hi hj
  have h2 : t * (k * k) ≤ 2 * (k * k) := Nat.mul_le_mul_right _ (by omega)
  simp only [tenc]
  omega

/-- A node is a triple of type below `3`, row and column below `k`, and column `0` for a
contact. -/
def Valid (k : Nat) (n : N3) : Prop := n.1 < 3 ∧ n.2.1 < k ∧ n.2.2 < k ∧ (n.1 ≤ 1 ∨ n.2.2 = 0)

theorem mem_tnodes {k : Nat} {n : N3} : n ∈ tnodes k ↔ Valid k n := by
  simp only [tnodes, List.mem_filter, List.mem_map, List.mem_range, isNode, Bool.or_eq_true,
    decide_eq_true_eq, Valid]
  constructor
  · rintro ⟨⟨v, hv, rfl⟩, hn⟩
    have hk : 0 < k := by
      rcases Nat.eq_zero_or_pos k with rfl | h
      · simp at hv
      · exact h
    have hkk : 0 < k * k := Nat.mul_pos hk hk
    refine ⟨?_, ?_, ?_, hn⟩
    · show v / (k * k) < 3
      exact (Nat.div_lt_iff_lt_mul hkk).mpr hv
    · show v % (k * k) / k < k
      exact (Nat.div_lt_iff_lt_mul hk).mpr (Nat.mod_lt _ hkk)
    · show v % (k * k) % k < k
      exact Nat.mod_lt _ hk
  · rintro ⟨ht, hi, hj, hn⟩
    exact ⟨⟨tenc k n, tenc_lt ht hi hj, tdec_tenc hi hj⟩, hn⟩

theorem nodup_tnodes (k : Nat) : (tnodes k).Nodup := by
  refine (List.Nodup.map (fun a b h => ?_) List.nodup_range).filter _
  have := congrArg (tenc k) h
  rwa [tenc_tdec, tenc_tdec] at this

theorem mem_tarcs {k : Nat} {e : N3 × N3} : e ∈ tarcs k ↔ e.1 ∈ tnodes k ∧ e.2 ∈ tout k e.1 := by
  obtain ⟨m, w⟩ := e
  simp only [tarcs, List.mem_flatMap, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨m', hm', w', hw', rfl, rfl⟩
    exact ⟨hm', hw'⟩
  · rintro ⟨hm, hw⟩
    exact ⟨m, hm, w, hw, rfl, rfl⟩

theorem nxt_lt {k i : Nat} (hi : i < k) : nxt k i < k := by
  unfold nxt; split <;> omega

theorem prv_nxt {k i : Nat} (hi : i < k) : prv k (nxt k i) = i := by
  unfold nxt prv; split <;> split <;> omega

/-- The successors of a node are nodes. -/
theorem valid_of_mem_tout {k : Nat} {m w : N3} (hm : Valid k m) (hw : w ∈ tout k m) :
    Valid k w := by
  obtain ⟨t, i, j⟩ := m
  obtain ⟨ht, hi, hj, hn⟩ := hm
  simp only at ht hi hj hn
  have hk : 0 < k := by omega
  unfold tout at hw
  simp only at hw
  split at hw
  · simp only [List.mem_singleton] at hw
    subst hw
    exact ⟨by simp, hi, hj, by simp⟩
  · split at hw
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · split
        · next h => exact ⟨by simp, hi, h, by simp⟩
        · exact ⟨by simp, hi, hk, by simp⟩
      · exact ⟨by simp, nxt_lt hi, hj, by simp⟩
    · simp only [List.mem_singleton] at hw
      subst hw
      exact ⟨by simp, hi, hk, by simp⟩

/-- Every arc `m → w` has `m` among the predecessors of `w`. -/
theorem mem_tin_of_mem_tout {k : Nat} {m w : N3} (hm : Valid k m) (hw : w ∈ tout k m) :
    m ∈ tin k w := by
  obtain ⟨t, i, j⟩ := m
  obtain ⟨ht, hi, hj, hn⟩ := hm
  simp only at ht hi hj hn
  unfold tout at hw
  simp only at hw
  split at hw
  · next h0 =>
    simp only [List.mem_singleton] at hw
    subst hw h0
    simp [tin]
  · next h0 =>
    split at hw
    · next h1 =>
      subst h1
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · split
        · next h => simp [tin]
        · next h =>
          have : j = k - 1 := by omega
          subst this
          simp [tin]
      · simp [tin, prv_nxt hi]
    · next h1 =>
      have ht2 : t = 2 := by omega
      have hj0 : j = 0 := by omega
      subst ht2 hj0
      simp only [List.mem_singleton] at hw
      subst hw
      simp [tin]

theorem nodup_tout {k : Nat} (n : N3) : (tout k n).Nodup := by
  unfold tout
  split
  · simp
  · split
    · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil,
        not_false_eq_true, and_true]
      split
      · simp
      · simp
    · simp

theorem length_tout (k : Nat) (n : N3) :
    (tout k n).length = if n.1 = 1 then 2 else 1 := by
  unfold tout
  split
  · next h => simp [h]
  · split <;> simp_all

theorem length_tin (k : Nat) (n : N3) :
    (tin k n).length = if n.1 = 0 then 2 else 1 := by
  unfold tin
  split
  · simp_all
  · split <;> simp_all

theorem length_tnodes_le (k : Nat) : (tnodes k).length ≤ 3 * (k * k) := by
  have := List.length_filter_le isNode ((List.range (3 * (k * k))).map (tdec k))
  simp only [List.length_map, List.length_range] at this
  exact this

/-! ### Occurrences -/

/-- A duplicate-free list contained in `L` is no longer than `L`. -/
theorem length_le_of_nodup_subset {α : Type} [DecidableEq α] {l L : List α} (hl : l.Nodup)
    (h : ∀ x ∈ l, x ∈ L) : l.length ≤ L.length := by
  induction l generalizing L with
  | nil => simp
  | cons a l ih =>
    obtain ⟨ha, hl⟩ := List.nodup_cons.mp hl
    have haL := h a List.mem_cons_self
    have h1 := ih hl (L := L.erase a) fun x hx =>
      (List.mem_erase_of_ne (by rintro rfl; exact ha hx)).mpr (h x (List.mem_cons_of_mem _ hx))
    rw [List.length_erase_of_mem haL] at h1
    have h2 : 0 < L.length := List.length_pos_of_mem haL
    simp only [List.length_cons]
    omega

theorem sum_ite_eq_countP {α : Type} (l : List α) (p : α → Bool) :
    (l.map fun x => if p x then 1 else 0).sum = l.countP p := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, ih, List.countP_cons]
    omega

theorem countP_tarcs (k : Nat) (p : N3 × N3 → Bool) :
    (tarcs k).countP p = ((tnodes k).map fun m => (tout k m).countP fun w => p (m, w)).sum := by
  unfold tarcs
  rw [List.countP_flatMap]
  congr 1
  refine List.map_congr_left fun m _ => ?_
  simp only [Function.comp_apply, List.countP_map]
  rfl

theorem tails_le (k : Nat) (n : N3) :
    (tarcs k).countP (fun e => e.1 == n) ≤ (tout k n).length := by
  rw [countP_tarcs]
  refine sum_map_le_of_single (nodup_tnodes k) _ n (fun m _ hmn => ?_) (fun _ => ?_)
  · exact List.countP_eq_zero.mpr fun w _ h => hmn (beq_iff_eq.mp h)
  · exact List.countP_le_length

theorem heads_le (k : Nat) (n : N3) :
    (tarcs k).countP (fun e => e.2 == n) ≤ (tin k n).length := by
  rw [countP_tarcs]
  have h1 : ∀ m ∈ tnodes k, (tout k m).countP (fun w => (m, w).2 == n) ≤
      if decide (m ∈ tin k n) then 1 else 0 := by
    intro m hm
    have e : (tout k m).countP (fun w => (m, w).2 == n) = (tout k m).count n := rfl
    rw [e, (nodup_tout m).count]
    split
    · next h =>
      have := mem_tin_of_mem_tout (mem_tnodes.mp hm) h
      simp [this]
    · exact Nat.zero_le _
  refine Nat.le_trans (sum_map_le_sum_map _ _ _ h1) ?_
  rw [sum_ite_eq_countP, List.countP_eq_length_filter]
  exact length_le_of_nodup_subset ((nodup_tnodes k).filter _)
    fun x hx => by simpa using (List.mem_filter.mp hx).2

theorem contacts_le (k : Nat) (n : N3) :
    (List.range k).countP (fun i => ((2, i, 0) : N3) == n) ≤ if n.1 = 2 then 1 else 0 := by
  split
  · next h =>
    have : (List.range k).countP (fun i => ((2, i, 0) : N3) == n) ≤
        (List.range k).countP (fun i => i == n.2.1) :=
      List.countP_mono_left fun i _ hi => by
        obtain ⟨t, a, b⟩ := n
        simp only [beq_iff_eq, Prod.mk.injEq] at hi ⊢
        exact hi.2.1
    have h2 := (List.nodup_range (n := k)).count (a := n.2.1)
    rw [List.count] at h2
    rw [h2] at this
    split at this <;> omega
  · next h =>
    refine Nat.le_of_eq (List.countP_eq_zero.mpr fun i _ hi => h ?_)
    obtain ⟨t, a, b⟩ := n
    simp only [beq_iff_eq, Prod.mk.injEq] at hi
    exact hi.1.symm

/-- Every node occurs at most three times: in-degree, out-degree and contact uses. -/
theorem torus_occ_le (k : Nat) (n : N3) :
    (List.range k).countP (fun i => ((2, i, 0) : N3) == n) +
      (tarcs k).countP (fun e => e.1 == n) + (tarcs k).countP (fun e => e.2 == n) ≤ 3 := by
  have h1 := contacts_le k n
  have h2 := tails_le k n
  have h3 := heads_le k n
  rw [length_tout] at h2
  rw [length_tin] at h3
  split at h1 <;> split at h2 <;> split at h3 <;> omega

theorem length_tarcs_le (k : Nat) : (tarcs k).length ≤ 6 * (k * k) := by
  have h := countP_tarcs k fun _ => true
  rw [List.countP_true] at h
  rw [h]
  have h1 : ((tnodes k).map fun m => (tout k m).countP fun _ => true).sum ≤
      ((tnodes k).map fun _ => 2).sum :=
    sum_map_le_sum_map _ _ _ fun m _ => by
      rw [List.countP_true, length_tout]
      split <;> omega
  have h2 : ((tnodes k).map fun _ => 2).sum = (tnodes k).length * 2 := by simp
  have h3 := length_tnodes_le k
  omega

end Occ

end Complexity

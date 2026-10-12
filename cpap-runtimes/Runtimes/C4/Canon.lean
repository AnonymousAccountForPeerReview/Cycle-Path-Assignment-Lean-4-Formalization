module

public import Runtimes.C4.Spec
public import NPHardness.CycleStructure
import Mathlib.Tactic

/-!
# Four-cycle listing: canonical 4-cycles and the formal cycle list

* **4-cycles as lists.** `cycleEdges4`, `mem_edges4`; two vertices of a simple 4-cycle are
  non-adjacent iff they are opposite (`nonedge4`); two simple 4-cycles with the same edges
  have the same pair of diagonals (`diagonals`).
* **The canonical form** `canon4` (`Spec.lean`): it has the same edges as its argument
  (`canon4_same`), the same entries (`mem_canon4`), no repetitions (`canon4_nodup`), is
  canonical (`canon4_isCanon`), is lexicographically at most its argument (`canon4_le`), and a
  canonical simple 4-cycle is determined by its edges (`canon4_unique`).
* **The formal list `cycles g 4`** (`NPHardness/Enumerate.lean`) is lexicographically sorted
  before deduplication (`rawCycles_sorted`), so the representative it keeps of each edge set
  is the least member (`cycleRepresentatives_min`). **Characterization** (`mem_cycles4`): `c ∈ cycles g 4 ↔ IsCycle g 4 c ∧ IsCanon4 c`.
-/

@[expose] public section

namespace STACS2027.Runtimes.C4

open STACS2027

/-! ### Edges of a 4-cycle -/

theorem cycleEdges4 (a b c d : ℕ) :
    cycleEdges [a, b, c, d] = [edge a b, edge b c, edge c d, edge d a] := rfl

theorem mem_edges4 {x y p q r s : ℕ} :
    edge x y ∈ cycleEdges [p, q, r, s] ↔
      edge x y = edge p q ∨ edge x y = edge q r ∨ edge x y = edge r s ∨ edge x y = edge s p := by
  simp [cycleEdges4]

/-- Two vertices of a simple 4-cycle are non-adjacent iff they are opposite. -/
theorem nonedge4 {p q r s u v : ℕ} (h : [p, q, r, s].Nodup) (hu : u ∈ [p, q, r, s])
    (hv : v ∈ [p, q, r, s]) (huv : u ≠ v) :
    edge u v ∉ cycleEdges [p, q, r, s] ↔
      (u = p ∧ v = r ∨ u = r ∧ v = p) ∨ (u = q ∧ v = s ∨ u = s ∧ v = q) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at h hu hv
  rw [mem_edges4]
  simp only [edge_eq_iff]
  rcases hu with rfl | rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl | rfl <;> simp_all <;>
    omega

theorem mem4_of_same {p q r s p' q' r' s' u : ℕ} (hs : SameCycle [p, q, r, s] [p', q', r', s'])
    (hu : u ∈ [p, q, r, s]) : u ∈ [p', q', r', s'] := by
  have key : ∀ a b, edge a b ∈ cycleEdges [p', q', r', s'] → a ∈ [p', q', r', s'] := by
    intro a b hab
    rw [mem_edges4] at hab
    simp only [edge_eq_iff] at hab
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl
  · exact key _ q (hs.1 _ (by simp [cycleEdges4]))
  · exact key _ r (hs.1 _ (by simp [cycleEdges4]))
  · exact key _ s (hs.1 _ (by simp [cycleEdges4]))
  · exact key _ p (hs.1 _ (by simp [cycleEdges4]))

/-- **Diagonals**: two simple 4-cycles with the same edges have the same pair of
diagonals. -/
theorem diagonals {x z y z' x' w y' w' : ℕ}
    (h1 : [x, z, y, z'].Nodup) (h2 : [x', w, y', w'].Nodup)
    (hs : SameCycle [x, z, y, z'] [x', w, y', w']) :
    ((x = x' ∧ y = y' ∨ x = y' ∧ y = x') ∧ (z = w ∧ z' = w' ∨ z = w' ∧ z' = w)) ∨
    ((x = w ∧ y = w' ∨ x = w' ∧ y = w) ∧ (z = x' ∧ z' = y' ∨ z = y' ∧ z' = x')) := by
  have hx := mem4_of_same hs (u := x) (by simp)
  have hy := mem4_of_same hs (u := y) (by simp)
  have hz := mem4_of_same hs (u := z) (by simp)
  have hz' := mem4_of_same hs (u := z') (by simp)
  have hn1 := h1
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hn1
  have dxy : edge x y ∉ cycleEdges [x', w, y', w'] := fun h =>
    ((nonedge4 h1 (by simp) (by simp) (by omega)).mpr (by omega)) (hs.2 _ h)
  have dzz : edge z z' ∉ cycleEdges [x', w, y', w'] := fun h =>
    ((nonedge4 h1 (by simp) (by simp) (by omega)).mpr (by omega)) (hs.2 _ h)
  have a1 := (nonedge4 h2 hx hy (by omega)).mp dxy
  have a2 := (nonedge4 h2 hz hz' (by omega)).mp dzz
  have hn2 := h2
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hn2
  rcases a1 with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
    rcases a2 with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp_all

/-! ### The canonical form -/

/-- Two 4-lists with the same four edges (up to orientation) have the same edges. -/
theorem sameCycle4 {a b c d p q r s : ℕ}
    (h : ∀ e, e = edge a b ∨ e = edge b c ∨ e = edge c d ∨ e = edge d a ↔
      e = edge p q ∨ e = edge q r ∨ e = edge r s ∨ e = edge s p) :
    SameCycle [a, b, c, d] [p, q, r, s] := by
  constructor <;> intro e he <;> simp only [cycleEdges4, List.mem_cons, List.not_mem_nil,
    or_false] at he ⊢
  · exact (h e).mp he
  · exact (h e).mpr he

/-- The canonical form has the same edges. -/
theorem canon4_same (a b c d : ℕ) : SameCycle [a, b, c, d] (canon4 a b c d) := by
  unfold canon4
  split_ifs <;> refine sameCycle4 fun e => ?_ <;> constructor <;>
    rintro (rfl | rfl | rfl | rfl) <;> simp [edge_comm]

theorem mem_canon4 {a b c d x : ℕ} : x ∈ canon4 a b c d ↔ x ∈ [a, b, c, d] := by
  unfold canon4
  split_ifs <;> simp only [List.mem_cons, List.not_mem_nil, or_false] <;> tauto

theorem canon4_nodup {a b c d : ℕ} (h : [a, b, c, d].Nodup) : (canon4 a b c d).Nodup := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  unfold canon4
  split_ifs <;> simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, not_false_eq_true, and_true] at h ⊢ <;> omega

theorem canon4_perm {a b c d : ℕ} (h : [a, b, c, d].Nodup) : (canon4 a b c d).Perm [a, b, c, d] :=
  (List.perm_ext_iff_of_nodup (canon4_nodup h) h).mpr fun _ => mem_canon4

theorem canon4_isCanon {a b c d : ℕ} (h : [a, b, c, d].Nodup) : IsCanon4 (canon4 a b c d) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  unfold canon4
  split_ifs <;> simp only [IsCanon4] <;> omega

/-- The canonical form is lexicographically at most its argument. -/
theorem canon4_le {a b c d : ℕ} (h : [a, b, c, d].Nodup) : canon4 a b c d ≤ [a, b, c, d] := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil,
    not_false_eq_true, and_true] at h
  unfold canon4
  split_ifs
  · exact le_refl _
  all_goals exact le_of_lt (by
    simp only [List.cons_lt_cons_iff, lt_self_iff_false, and_false, or_false, false_or,
      true_and]; omega)

theorem isCanon4_iff {a b c d : ℕ} : IsCanon4 [a, b, c, d] ↔ a < b ∧ a < c ∧ a < d ∧ b < d :=
  Iff.rfl

theorem canon4_eq_self {a b c d : ℕ} (h : IsCanon4 [a, b, c, d]) : canon4 a b c d = [a, b, c, d] := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp [canon4, h1, h2, h3, h4]

/-- A canonical simple 4-cycle is determined by its edges. -/
theorem canon4_unique {a b c d p q r s : ℕ} (h2 : [p, q, r, s].Nodup)
    (hc1 : IsCanon4 [a, b, c, d]) (hc2 : IsCanon4 [p, q, r, s])
    (hs : SameCycle [a, b, c, d] [p, q, r, s]) : [a, b, c, d] = [p, q, r, s] := by
  obtain ⟨hab, hac, had, hbd⟩ := hc1
  obtain ⟨hpq, hpr, hps, hqs⟩ := hc2
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at h2
  have e1 := hs.1 (edge a b) (by simp [cycleEdges4])
  have e2 := hs.1 (edge b c) (by simp [cycleEdges4])
  have e4 := hs.1 (edge d a) (by simp [cycleEdges4])
  have f1 := hs.2 (edge p q) (by simp [cycleEdges4])
  rw [mem_edges4] at e1 e2 e4 f1
  simp only [edge_eq_iff] at e1 e2 e4 f1
  have hap : a = p := by omega
  subst hap
  have hbq : b = q := by omega
  subst hbq
  have hds : d = s := by omega
  subst hds
  have hcr : c = r := by omega
  subst hcr
  rfl

/-- A list with the same edges as a simple `k`-cycle, of length `k` and without repetitions,
is a simple `k`-cycle. -/
theorem IsCycle.of_same {g : Graph} {k : ℕ} {c d : Cycle} (hc : IsCycle g k c)
    (hs : SameCycle c d) (hl : d.length = k) (hd : d.Nodup) : IsCycle g k d :=
  ⟨hc.1, hl, hd, fun e he => hc.2.2.2 e (hs.2 e he)⟩

theorem isCycle_canon4 {g : Graph} {a b c d : ℕ} (h : IsCycle g 4 [a, b, c, d]) :
    IsCycle g 4 (canon4 a b c d) :=
  IsCycle.of_same h (canon4_same a b c d) (length_canon4 a b c d) (canon4_nodup h.2.2.1)

/-! ### The formal cycle list is sorted -/

theorem vertices_sorted (g : Graph) : (vertices g).Pairwise (· < ·) := by
  unfold vertices
  exact List.pairwise_lt_range.filter _

theorem neighbors_sorted (g : Graph) (v : ℕ) : (neighbors g v).Pairwise (· < ·) :=
  (vertices_sorted g).filter _

theorem walksFrom_zero (g : Graph) (u : ℕ) : walksFrom g u 0 = [[u]] := rfl

theorem walksFrom_succ (g : Graph) (u k : ℕ) :
    walksFrom g u (k + 1) = (neighbors g u).flatMap fun w => (walksFrom g w k).map (u :: ·) :=
  rfl

theorem head_walksFrom (g : Graph) (u k : ℕ) : ∀ c ∈ walksFrom g u k, c.head? = some u := by
  cases k with
  | zero => simp [walksFrom_zero]
  | succ k =>
    intro c hc
    rw [walksFrom_succ] at hc
    simp only [List.mem_flatMap, List.mem_map] at hc
    obtain ⟨w, -, d, -, rfl⟩ := hc
    rfl

theorem walksFrom_sorted (g : Graph) (k : ℕ) : ∀ u, (walksFrom g u k).Pairwise (· < ·) := by
  induction k with
  | zero => intro u; simp [walksFrom_zero]
  | succ k ih =>
    intro u
    rw [walksFrom_succ, List.pairwise_flatMap]
    refine ⟨fun w _ => ?_, ?_⟩
    · rw [List.pairwise_map]
      exact (ih w).imp fun h => List.cons_lt_cons_iff.mpr (Or.inr ⟨rfl, h⟩)
    · refine (neighbors_sorted g u).imp fun {w w'} hww' => ?_
      intro x hx y hy
      simp only [List.mem_map] at hx hy
      obtain ⟨c, hc, rfl⟩ := hx
      obtain ⟨d, hd, rfl⟩ := hy
      have h1 := head_walksFrom g w k c hc
      have h2 := head_walksFrom g w' k d hd
      cases c with
      | nil => simp at h1
      | cons a c =>
        cases d with
        | nil => simp at h2
        | cons b d =>
          simp only [List.head?_cons, Option.some.injEq] at h1 h2
          subst h1; subst h2
          exact List.cons_lt_cons_iff.mpr
            (Or.inr ⟨rfl, List.cons_lt_cons_iff.mpr (Or.inl hww')⟩)

theorem rawCycles_sorted (g : Graph) (k : ℕ) : (rawCycles g k).Pairwise (· < ·) := by
  unfold rawCycles
  apply List.Pairwise.filter
  rw [List.pairwise_flatMap]
  refine ⟨fun v _ => walksFrom_sorted g _ v, ?_⟩
  refine (vertices_sorted g).imp fun {v v'} hvv' => ?_
  intro x hx y hy
  have h1 := head_walksFrom g v _ x hx
  have h2 := head_walksFrom g v' _ y hy
  cases x with
  | nil => simp at h1
  | cons a x =>
    cases y with
    | nil => simp at h2
    | cons b y =>
      simp only [List.head?_cons, Option.some.injEq] at h1 h2
      subst h1; subst h2
      exact List.cons_lt_cons_iff.mpr (Or.inl hvv')

/-- In a lexicographically sorted list, the representative kept of each edge set is the least
member of its class. -/
theorem cycleRepresentatives_min : ∀ (n : ℕ) (cs : List Cycle), cs.length ≤ n →
    cs.Pairwise (· < ·) → ∀ c ∈ cycleRepresentatives cs, ∀ d ∈ cs, SameCycle d c → c ≤ d
  | _, [], _, _ => by simp [cycleRepresentatives]
  | 0, _ :: _, h, _ => by simp at h
  | n + 1, a :: cs, hl, hs => by
    rw [cycleRepresentatives_cons]
    intro c hc d hd hdc
    rcases List.mem_cons.mp hc with rfl | hc
    · rcases List.mem_cons.mp hd with rfl | hd
      · exact le_refl _
      · exact le_of_lt (List.rel_of_pairwise_cons hs hd)
    · have hf := cycleRepresentatives_subset _ c hc
      have hca : ¬ SameCycle c a := by simpa using (List.mem_filter.mp hf).2
      have hda : d ≠ a := by rintro rfl; exact hca hdc.symm
      have hd' : d ∈ cs := by simpa [hda] using hd
      have hdf : d ∈ cs.filter fun d => !decide (SameCycle d a) := by
        simp only [List.mem_filter, hd', true_and, Bool.not_eq_eq_eq_not, Bool.not_true,
          decide_eq_false_iff_not]
        exact fun h => hca (hdc.symm.trans h)
      have hlen : (cs.filter fun d => !decide (SameCycle d a)).length ≤ n :=
        le_trans (List.length_filter_le _ _) (by simp at hl; omega)
      exact cycleRepresentatives_min n _ hlen ((List.pairwise_cons.mp hs).2.filter _) c hc d
        hdf hdc

/-! ### Characterization of `cycles g 4` -/

theorem eq4_of_isCycle {g : Graph} {c : Cycle} (h : IsCycle g 4 c) :
    ∃ a b x d, c = [a, b, x, d] := by
  match c, h.2.1 with
  | [a, b, x, d], _ => exact ⟨a, b, x, d, rfl⟩

theorem isCanon4_of_mem_cycles {g : Graph} {c : Cycle} (hc : c ∈ cycles g 4) : IsCanon4 c := by
  have hraw := cycleRepresentatives_subset _ c hc
  have hcyc := raw_enumerated_isCycle hraw
  obtain ⟨a, b, x, d, rfl⟩ := eq4_of_isCycle hcyc
  have hnd := hcyc.2.2.1
  have hcan := isCycle_canon4 hcyc
  have h1 : [a, b, x, d] ≤ canon4 a b x d :=
    cycleRepresentatives_min _ (rawCycles g 4) le_rfl (rawCycles_sorted g 4) _ hc _
      (isCycle_raw_enumerated hcan) (canon4_same a b x d).symm
  have h2 := canon4_le hnd
  have h3 : canon4 a b x d = [a, b, x, d] := le_antisymm h2 h1
  have := canon4_isCanon hnd
  rwa [h3] at this

/-- **Characterization**: the members of `cycles g 4` are exactly the canonical
simple 4-cycles of `g`. -/
theorem mem_cycles4 {g : Graph} {c : Cycle} : c ∈ cycles g 4 ↔ IsCycle g 4 c ∧ IsCanon4 c := by
  constructor
  · intro hc
    exact ⟨enumerated_isCycle hc, isCanon4_of_mem_cycles hc⟩
  · rintro ⟨hcyc, hcan⟩
    obtain ⟨d, hd, hcd⟩ := isCycle_represented hcyc
    have hdc := enumerated_isCycle hd
    have hdcan := isCanon4_of_mem_cycles hd
    obtain ⟨a, b, x, y, rfl⟩ := eq4_of_isCycle hcyc
    obtain ⟨p, q, r, s, rfl⟩ := eq4_of_isCycle hdc
    rwa [canon4_unique hdc.2.2.1 hcan hdcan hcd]

end STACS2027.Runtimes.C4

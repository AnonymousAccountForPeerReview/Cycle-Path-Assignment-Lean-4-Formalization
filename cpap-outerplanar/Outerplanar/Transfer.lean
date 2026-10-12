module

public import Outerplanar.DPCorrect
import Mathlib.Tactic

/-!
# From an outerplanar Hamiltonian cycle to a polygon

A graph `g` with a Hamiltonian cycle `ham` with respect to which no two edges cross
(`OuterplanarHam g ham`) is, after renaming its vertices by their positions on `ham`, a
polygon with non-crossing chords on `0, …, n - 1` (`posGraph g ham`, `isPolygon_posGraph`).
The cycle-path assignment problem depends only on the simple graph (`hasAssignment_proper`)
and is invariant under the renaming (`hasAssignment_posGraph`), so the optimum of `g` is
that of the polygon (`isMinCost_posGraph`).
-/

@[expose] public section

namespace STACS2027

/-- `CPAP(g, k)` depends only on the simple graph of `g`. -/
theorem hasAssignment_proper {g h : Graph} (he : ∀ a b, a ≠ b → (edge a b ∈ g ↔ edge a b ∈ h))
    (k B : ℕ) : HasAssignment g k B ↔ HasAssignment h k B := by
  have hcyc : ∀ c, IsCycle g k c ↔ IsCycle h k c := by
    have key : ∀ g h : Graph, (∀ a b, a ≠ b → (edge a b ∈ g ↔ edge a b ∈ h)) →
        ∀ c, IsCycle g k c → IsCycle h k c := by
      intro g h he c hc
      refine ⟨hc.1, hc.2.1, hc.2.2.1, fun e hce => ?_⟩
      have hne := hc.edge_endpoints_ne hce
      have hn := pathEdges_normalized _ e hce
      rw [← hn] at hce ⊢
      exact (he _ _ hne).mp (by rw [hn]; exact hc.2.2.2 e (by rw [← hn]; exact hce))
    intro c
    exact ⟨key g h he c, key h g (fun a b hab => (he a b hab).symm) c⟩
  have hv : ∀ c ∈ cycles g k, IsCycle h k c := fun c hc => (hcyc c).mp (enumerated_isCycle hc)
  have hcover : ∀ c, IsCycle h k c → ∃ d ∈ cycles g k, SameCycle c d :=
    fun c hc => isCycle_represented ((hcyc c).mpr hc)
  exact (hasAssignment_iff_enumerated_family g k B).trans
    (hasAssignment_iff_complete_family hv (cycles_pairwise_different g k) hcover).symm

theorem isMinCost_proper {g h : Graph} (he : ∀ a b, a ≠ b → (edge a b ∈ g ↔ edge a b ∈ h))
    (k C : ℕ) : IsMinCost g k C ↔ IsMinCost h k C := by
  simp only [IsMinCost, hasAssignment_proper he]

/-- The polygon of `g` on the positions of `ham`: the pairs `i < j` of positions whose
vertices are adjacent. -/
def posGraph (g : Graph) (ham : List ℕ) : Graph :=
  (List.range ham.length).flatMap fun i => (List.range ham.length).filterMap fun j =>
    if i < j ∧ Adj g (ham.getD i 0) (ham.getD j 0) then some (i, j) else none

theorem mem_posGraph {g : Graph} {ham : List ℕ} {i j : ℕ} :
    (i, j) ∈ posGraph g ham ↔ i < j ∧ j < ham.length ∧ Adj g (ham.getD i 0) (ham.getD j 0) := by
  simp only [posGraph, List.mem_flatMap, List.mem_range, List.mem_filterMap, Option.ite_none_right_eq_some,
    Option.some.injEq, Prod.mk.injEq]
  constructor
  · rintro ⟨i', hi', j', hj', ⟨hlt, hadj⟩, rfl, rfl⟩
    exact ⟨hlt, hj', hadj⟩
  · rintro ⟨hlt, hj, hadj⟩
    exact ⟨i, by omega, j, hj, ⟨hlt, hadj⟩, rfl, rfl⟩

theorem posGraph_normalized {g : Graph} {ham : List ℕ} : ∀ e ∈ posGraph g ham, edge e.1 e.2 = e := by
  rintro ⟨i, j⟩ he
  have := (mem_posGraph.mp he).1
  simp [edge, Nat.min_eq_left this.le, Nat.max_eq_right this.le]

theorem adj_posGraph {g : Graph} {ham : List ℕ} {i j : ℕ} :
    Adj (posGraph g ham) i j ↔ i < ham.length ∧ j < ham.length ∧ Adj g (ham.getD i 0) (ham.getD j 0) := by
  constructor
  · rintro ⟨hne, he⟩
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · rw [show edge i j = (i, j) by simp [edge, Nat.min_eq_left h.le, Nat.max_eq_right h.le]] at he
      obtain ⟨-, hj, hadj⟩ := mem_posGraph.mp he
      exact ⟨by omega, hj, hadj⟩
    · rw [show edge i j = (j, i) by simp [edge, Nat.min_eq_right h.le, Nat.max_eq_left h.le]] at he
      obtain ⟨-, hj, hadj⟩ := mem_posGraph.mp he
      exact ⟨hj, by omega, hadj.symm⟩
  · rintro ⟨hi, hj, hadj⟩
    have hne : i ≠ j := by
      intro h; subst h; exact hadj.1 rfl
    refine ⟨hne, ?_⟩
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · rw [show edge i j = (i, j) by simp [edge, Nat.min_eq_left h.le, Nat.max_eq_right h.le]]
      exact mem_posGraph.mpr ⟨h, hj, hadj⟩
    · rw [show edge i j = (j, i) by simp [edge, Nat.min_eq_right h.le, Nat.max_eq_left h.le]]
      exact mem_posGraph.mpr ⟨h, hi, hadj.symm⟩

/-- Consecutive entries of a list are its consecutive positions. -/
theorem edge_getD_mem_pathEdges {l : List ℕ} {i : ℕ} (hi : i + 1 < l.length) :
    edge (l.getD i 0) (l.getD (i + 1) 0) ∈ pathEdges l := by
  induction l generalizing i with
  | nil => simp at hi
  | cons x l ih =>
    cases i with
    | zero =>
      cases l with
      | nil => simp at hi
      | cons y l => simp [pathEdges]
    | succ i =>
      cases l with
      | nil => simp at hi
      | cons y l =>
        simp only [pathEdges]
        apply List.mem_cons_of_mem
        have := ih (i := i) (by simpa using hi)
        simpa using this

theorem OuterplanarHam.adj_succ {g : Graph} {ham : List ℕ} (h : OuterplanarHam g ham) {i : ℕ}
    (hi : i + 1 < ham.length) : Adj g (ham.getD i 0) (ham.getD (i + 1) 0) := by
  have hc := h.1
  have hnd := hc.2.2.1
  refine ⟨?_, hc.2.2.2 _ ?_⟩
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < ham.length by omega),
      List.getElem?_eq_getElem hi, Option.getD_some]
    intro heq
    have := (List.Nodup.getElem_inj_iff hnd).mp heq
    omega
  · exact pathEdges_infix ⟨[], ham.take 1, by simp⟩ (edge_getD_mem_pathEdges hi)

theorem OuterplanarHam.adj_wrap {g : Graph} {ham : List ℕ} (h : OuterplanarHam g ham) :
    Adj g (ham.getD 0 0) (ham.getD (ham.length - 1) 0) := by
  have hc := h.1
  have hk := hc.1
  have hne : ham ≠ [] := by rintro rfl; simp at hk
  have hu := edge_last_head_mem_cycleEdges hne
  have hlast : ham.getLast hne = ham.getD (ham.length - 1) 0 := by
    rw [List.getLast_eq_getElem, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by omega), Option.getD_some]
  have hhead : ham.head hne = ham.getD 0 0 := by
    rw [List.head_eq_getElem, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by omega), Option.getD_some]
  rw [hlast, hhead] at hu
  refine ⟨?_, by rw [edge_comm]; exact hc.2.2.2 _ hu⟩
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show 0 < ham.length by omega),
    List.getElem?_eq_getElem (show ham.length - 1 < ham.length by omega), Option.getD_some]
  intro heq
  have := (List.Nodup.getElem_inj_iff hc.2.2.1).mp heq
  omega

/-- The positions of an outerplanar Hamiltonian cycle form a polygon. -/
theorem isPolygon_posGraph {g : Graph} {ham : List ℕ} (h : OuterplanarHam g ham) :
    IsPolygon (posGraph g ham) ham.length := by
  have hk := h.1.1
  refine ⟨⟨by simpa using hk, by simp, List.nodup_range, ?_⟩, ?_, ?_⟩
  · intro e he
    obtain ⟨xs, a, b, ys, hsplit, rfl⟩ := mem_pathEdges_iff.mp he
    -- consecutive positions, or the closing pair
    have hab : (b = a + 1 ∧ b < ham.length) ∨ (a = ham.length - 1 ∧ b = 0) := by
      have hr : List.range ham.length ++ List.take 1 (List.range ham.length) =
          List.range ham.length ++ [0] := by
        congr 1
        cases hl : ham.length with
        | zero => omega
        | succ m => simp [List.range_succ_eq_map]
      rw [hr] at hsplit
      have hlen := congrArg List.length hsplit
      simp only [List.length_append, List.length_range, List.length_cons, List.length_nil] at hlen
      have ha : (List.range ham.length ++ [0])[xs.length]? = some a := by
        rw [hsplit]; simp
      have hb : (List.range ham.length ++ [0])[xs.length + 1]? = some b := by
        rw [hsplit]; simp
      by_cases hx : xs.length + 1 < ham.length
      · left
        rw [List.getElem?_append_left (by simp; omega), List.getElem?_range (by omega)] at ha hb
        simp at ha hb
        omega
      · right
        have hx' : xs.length + 1 = ham.length := by omega
        rw [List.getElem?_append_left (by simp; omega), List.getElem?_range (by omega)] at ha
        rw [List.getElem?_append_right (by simp; omega)] at hb
        simp only [List.length_range, show xs.length + 1 - ham.length = 0 by omega] at hb
        simp at ha hb
        constructor <;> omega
    rcases hab with ⟨rfl, hb⟩ | ⟨rfl, rfl⟩
    · have := h.adj_succ hb
      rw [show edge a (a + 1) = (a, a + 1) by simp [edge]]
      exact mem_posGraph.mpr ⟨by omega, hb, this⟩
    · rw [show edge (ham.length - 1) 0 = (0, ham.length - 1) by simp [edge]]
      exact mem_posGraph.mpr ⟨by omega, by omega, h.adj_wrap⟩
  · intro v ⟨u, huv⟩
    have := (adj_posGraph.mp huv).2.1
    simpa using this
  · intro i j k l hij hjk hkl hl hc
    have hl' : l < ham.length := by simpa using hl
    rw [IsPolygon.getD_range (by omega), IsPolygon.getD_range (by omega),
      IsPolygon.getD_range (by omega), IsPolygon.getD_range hl'] at hc
    obtain ⟨h1, h2⟩ := hc
    exact h.2.2 i j k l hij hjk hkl hl' ⟨(adj_posGraph.mp h1).2.2, (adj_posGraph.mp h2).2.2⟩

/-- Renaming the positions by the vertices of `ham` gives back the simple graph of `g`. -/
theorem posGraph_relabel {g : Graph} {ham : List ℕ} (h : OuterplanarHam g ham) :
    ∀ a b, a ≠ b → (edge a b ∈ mapGraph (fun i => ham.getD i 0) (posGraph g ham) ↔ edge a b ∈ g) := by
  intro a b hab
  have hnd := h.1.2.2.1
  constructor
  · intro hm
    obtain ⟨⟨i, j⟩, he, heq⟩ := List.mem_map.mp hm
    obtain ⟨hij, hj, hadj⟩ := mem_posGraph.mp he
    simp only [mapEdge] at heq
    rw [← heq]; exact hadj.2
  · intro hm
    have hadj : Adj g a b := ⟨hab, hm⟩
    have ha : a ∈ ham := h.2.1 a ⟨b, hadj.symm⟩
    have hb : b ∈ ham := h.2.1 b ⟨a, hadj⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb
    have hgi : ham.getD i 0 = ham[i] := by simp [List.getD_eq_getElem?_getD, hi]
    have hgj : ham.getD j 0 = ham[j] := by simp [List.getD_eq_getElem?_getD, hj]
    have hij : i ≠ j := by intro e; subst e; exact hab rfl
    apply List.mem_map.mpr
    rcases Nat.lt_or_gt_of_ne hij with hlt | hlt
    · refine ⟨(i, j), mem_posGraph.mpr ⟨hlt, hj, by rw [hgi, hgj]; exact hadj⟩, ?_⟩
      simp only [mapEdge, hgi, hgj]
    · refine ⟨(j, i), mem_posGraph.mpr ⟨hlt, hi, by rw [hgi, hgj]; exact hadj.symm⟩, ?_⟩
      simp only [mapEdge, hgi, hgj, edge_comm]

/-- The cycle-path assignment problem of `g` is that of its polygon. -/
theorem hasAssignment_posGraph {g : Graph} {ham : List ℕ} (h : OuterplanarHam g ham) (k B : ℕ) :
    HasAssignment g k B ↔ HasAssignment (posGraph g ham) k B := by
  have hb : VerticesBelow (posGraph g ham) ham.length := by
    rintro ⟨i, j⟩ he
    obtain ⟨hij, hj, -⟩ := mem_posGraph.mp he
    exact ⟨by omega, hj⟩
  have hinj : ∀ a, a < ham.length → ∀ b, b < ham.length →
      ham.getD a 0 = ham.getD b 0 → a = b := by
    intro a ha b hb' heq
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ha,
      List.getElem?_eq_getElem hb', Option.getD_some] at heq
    exact (List.Nodup.getElem_inj_iff h.1.2.2.1).mp heq
  rw [← hasAssignment_relabel hb posGraph_normalized _ hinj k B]
  exact (hasAssignment_proper (fun a b hab => (posGraph_relabel h a b hab).symm) k B)

theorem isMinCost_posGraph {g : Graph} {ham : List ℕ} (h : OuterplanarHam g ham) (k C : ℕ) :
    IsMinCost g k C ↔ IsMinCost (posGraph g ham) k C := by
  simp only [IsMinCost, hasAssignment_posGraph h]

end STACS2027

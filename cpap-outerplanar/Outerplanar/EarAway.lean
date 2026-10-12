module

public import Outerplanar.Degenerate
public import Outerplanar.OuterplanarSym
public import Mathlib.Data.List.GetD
import Mathlib.Tactic

@[expose] public section

namespace STACS2027
namespace IsPolygon

/-- A polygon has a degree-two vertex distinct from its first position. -/
theorem ear_away_first {g : Graph} {n : ℕ} (hP : IsPolygon g n) :
    ∃ u ∈ List.range n, 0 < u ∧ AtMostTwo g (List.range n) u := by
  classical
  let U := List.range n
  let S : Finset (ℕ × ℕ) := (U.toFinset ×ˢ U.toFinset).filter fun e =>
    e.1 < e.2 ∧ Adj g e.1 e.2 ∧ ∃ z ∈ U, e.1 < z ∧ z < e.2
  have hn := hP.three_le
  have hS : S.Nonempty := by
    refine ⟨(0, n - 1), ?_⟩
    simp only [S, Finset.mem_filter, Finset.mem_product, List.mem_toFinset]
    exact ⟨⟨by simp [U]; omega, by simp [U]; omega⟩, by omega, hP.adj_wrap,
      1, by simp [U]; omega, by omega, by omega⟩
  obtain ⟨⟨a, b⟩, hab, hmin⟩ := S.exists_min_image (fun e => e.2 - e.1) hS
  simp only [S, Finset.mem_filter, Finset.mem_product, List.mem_toFinset] at hab
  obtain ⟨⟨haU, hbU⟩, hlt, hadj, hz⟩ := hab
  let I : Finset ℕ := U.toFinset.filter fun z => a < z ∧ z < b
  have hI : I.Nonempty := by
    obtain ⟨z, hzU, hz1, hz2⟩ := hz
    exact ⟨z, by simp [I, hzU, hz1, hz2]⟩
  let x := I.min' hI
  have hxI : x ∈ I := I.min'_mem hI
  simp only [I, Finset.mem_filter, List.mem_toFinset] at hxI
  have hxmin : ∀ z ∈ U, a < z → z < b → x ≤ z := by
    intro z hzU h1 h2
    exact I.min'_le z (by simp [I, hzU, h1, h2])
  refine ⟨x, hxI.1, by omega, atMostTwo_of_gaps ?_⟩
  intro y hyU hxy z hzU hz
  have hyab : a ≤ y ∧ y ≤ b := by
    by_contra hc
    rcases (show y < a ∨ b < y by omega) with h | h
    · exact hP.noncross h hxI.2.1 hxI.2.2 hxy.symm hadj
    · exact hP.noncross hxI.2.1 hxI.2.2 h hadj hxy
  rcases Nat.lt_or_gt_of_ne hxy.1 with h | h
  · -- `y > x`: a shorter spanning edge `xy` would contradict the choice of `ab`
    have hmem : (x, y) ∈ S := by
      simp only [S, Finset.mem_filter, Finset.mem_product, List.mem_toFinset]
      exact ⟨⟨hxI.1, hyU⟩, h, hxy, z, hzU, by omega, by omega⟩
    have := hmin _ hmem
    simp only at this
    omega
  · -- `y < x`: a vertex of `U` between `y` and `x` would precede `x` inside `ab`
    have := hxmin z hzU (by omega) (by omega)
    omega

end IsPolygon

/-- At most two distinct adjacent vertices, without a supplied vertex list. -/
def LowDegree (g : Graph) (u : ℕ) : Prop :=
  ∀ a b c, Adj g u a → Adj g u b → Adj g u c → a = b ∨ a = c ∨ b = c

/-- Every position on the Hamiltonian outer boundary is a graph vertex. -/
theorem OuterplanarHam.position_isVertex {g : Graph} {K : List ℕ}
    (h : OuterplanarHam g K) {i : ℕ} (hi : i < K.length) :
    IsVertex g (K.getD i 0) := by
  by_cases hn : i + 1 < K.length
  · exact ⟨K.getD (i + 1) 0, (h.adj_succ hn).symm⟩
  · have he : i = K.length - 1 := by omega
    exact ⟨K.getD 0 0, he ▸ h.adj_wrap⟩

/-- A Hamiltonian outer boundary has a degree-two vertex away from its first entry. -/
theorem OuterplanarHam.ear_away_head {g : Graph} {K : List ℕ}
    (h : OuterplanarHam g K) :
    ∃ u, IsVertex g u ∧ u ∈ K ∧ u ≠ K.getD 0 0 ∧ LowDegree g u := by
  classical
  obtain ⟨i, hi, hip, hlow⟩ := (isPolygon_posGraph h).ear_away_first
  have hil : i < K.length := List.mem_range.mp hi
  have hzero : 0 < K.length := by have := h.1.1; omega
  let u := K.getD i 0
  have hu : u ∈ K := by
    dsimp [u]
    rw [List.getD_eq_getElem K 0 hil]
    exact List.getElem_mem hil
  refine ⟨u, h.position_isVertex hil, hu, ?_, ?_⟩
  · dsimp [u]
    rw [List.getD_eq_getElem K 0 hil, List.getD_eq_getElem K 0 hzero]
    intro he
    have := (List.Nodup.getElem_inj_iff h.1.2.2.1).mp he
    omega
  · intro a b c hua hub huc
    let pos : ℕ → ℕ := K.idxOf
    have hpos : ∀ v, IsVertex g v → K.getD (pos v) 0 = v ∧ pos v < K.length := by
      intro v hv
      have hlt := List.idxOf_lt_length_iff.mpr (h.2.1 v hv)
      refine ⟨?_, hlt⟩
      rw [List.getD_eq_getElem K 0 hlt]
      exact List.getElem_idxOf hlt
    have ha := hpos a ⟨u, hua⟩
    have hb := hpos b ⟨u, hub⟩
    have hc := hpos c ⟨u, huc⟩
    have hpa : Adj (posGraph g K) i (pos a) :=
      adj_posGraph.mpr ⟨hil, ha.2, by rw [ha.1]; exact hua⟩
    have hpb : Adj (posGraph g K) i (pos b) :=
      adj_posGraph.mpr ⟨hil, hb.2, by rw [hb.1]; exact hub⟩
    have hpc : Adj (posGraph g K) i (pos c) :=
      adj_posGraph.mpr ⟨hil, hc.2, by rw [hc.1]; exact huc⟩
    rcases hlow (pos a) (pos b) (pos c) (List.mem_range.mpr ha.2)
      (List.mem_range.mpr hb.2) (List.mem_range.mpr hc.2) hpa hpb hpc with he | he | he
    · exact Or.inl (by rw [← ha.1, ← hb.1, he])
    · exact Or.inr (Or.inl (by rw [← ha.1, ← hc.1, he]))
    · exact Or.inr (Or.inr (by rw [← hb.1, ← hc.1, he]))

/-- A Hamiltonian outer boundary has a degree-two vertex avoiding any one vertex. -/
theorem OuterplanarHam.ear_away_vertex {g : Graph} {K : List ℕ}
    (h : OuterplanarHam g K) (z : ℕ) :
    ∃ u, IsVertex g u ∧ u ≠ z ∧ LowDegree g u := by
  by_cases hz : z ∈ K
  · obtain ⟨C, hr, _⟩ := h.oham.rotate_to (fun _ _ hab => hab.symm) hz
    obtain ⟨u, hu, _, hne, hlo⟩ := (h.isRotated hr).ear_away_head
    exact ⟨u, hu, by simpa using hne, hlo⟩
  · obtain ⟨u, hu, hum, _, hlo⟩ := h.ear_away_head
    exact ⟨u, hu, fun he => hz (he ▸ hum), hlo⟩

end STACS2027

module

public import Outerplanar.PlanarMinor

/-! The registered planar graph model is closed under branch-set minors. -/

@[expose] public section
namespace STACS2027.PlanarMinor
open STACS2027.OuterplanarMinor

theorem planar_of_listMinor_const {es : List (ℕ × ℕ)} {size : ℕ}
    {h : Graph} {branch : ℕ → List ℕ} (hh : ∀ e ∈ h, e.1 < size ∧ e.2 < size)
    (ho : Complexity.PlanarGraph es) (hm : ListMinor es size h branch)
    (hc : ∀ i, i < size → ∀ p ∈ branch i, ∀ q ∈ branch i, p = q) :
    Complexity.PlanarGraph (STACS2027.simpleEdges h) := by
  obtain ⟨hne, hdisj, -, hedges⟩ := hm
  let t : ℕ → ℕ := fun i => (branch i).headD 0
  have ht : ∀ i, i < size → t i ∈ branch i := by
    intro i hi
    have := hne i hi
    simp only [t]
    cases hb : branch i with
    | nil => exact absurd hb this
    | cons a l => simp
  have htw : ∀ i, i < size → ∀ w ∈ branch i, w = t i :=
    fun i hi w hw => hc i hi w hw (t i) (ht i hi)
  have htinj : ∀ i j, i < size → j < size → t i = t j → i = j := by
    intro i j hi hj hij
    by_contra hne
    exact hdisj i j hi hj hne _ (ht i hi) (hij ▸ ht j hj)
  have hedge : ∀ e ∈ h, e.1 ≠ e.2 → LAdj es (t e.1) (t e.2) := by
    intro e he hne'
    obtain ⟨u, hu, v, hv, huv⟩ := hedges e he hne'
    rwa [← htw e.1 (hh e he).1 u hu, ← htw e.2 (hh e he).2 v hv]
  let T : List ℕ := (List.range size).map t
  have hT : ∀ w, w ∈ T ↔ ∃ i, i < size ∧ t i = w := by
    intro w
    simp only [T, List.mem_map, List.mem_range]
  have hTnd : T.Nodup := by
    apply List.Nodup.map_on _ List.nodup_range
    intro i hi j hj hij
    exact htinj i j (List.mem_range.mp hi) (List.mem_range.mp hj) hij
  have hσ : ∀ i, i < size → T.idxOf (t i) = i := by
    intro i hi
    have hiT : i < T.length := by simp [T, hi]
    have h1 : T[i] = t i := by simp [T]
    have h2 := List.get_idxOf hTnd ⟨i, hiT⟩
    simp only [List.get_eq_getElem, h1] at h2
    exact h2
  let es1 := es.filter fun f => decide (f.1 ∈ T ∧ f.2 ∈ T)
  have ho1 : Complexity.PlanarGraph es1 := ho.sublist List.filter_sublist
  have hends : ∀ a, (∃ e ∈ es1, a = e.1 ∨ a = e.2) → a ∈ T := by
    rintro a ⟨e, he, hae⟩
    have he' := (List.mem_filter.mp he).2
    simp only [decide_eq_true_eq] at he'
    rcases hae with rfl | rfl
    · exact he'.1
    · exact he'.2
  have ho2 := ho1.map_injOn (fun w => T.idxOf w) (by
    intro a b ha hb hab
    obtain ⟨i, hi, rfl⟩ := (hT a).mp (hends a ha)
    obtain ⟨j, hj, rfl⟩ := (hT b).mp (hends b hb)
    simp only [hσ i hi, hσ j hj] at hab
    rw [hab])
  have ho3 := ho2.canonical
  apply ho3.subperm
  apply (simpleEdges_nodup h).subperm
  intro e he
  obtain ⟨f, hf, hfne, rfl⟩ := exists_of_mem_simpleEdges he
  have h1 := (hh f hf).1
  have h2 := (hh f hf).2
  have hT1 : t f.1 ∈ T := (hT _).mpr ⟨_, h1, rfl⟩
  have hT2 : t f.2 ∈ T := (hT _).mpr ⟨_, h2, rfl⟩
  simp only [List.map_map, List.mem_map, Function.comp_apply]
  rcases (hedge f hf hfne).2 with hm | hm
  · refine ⟨(t f.1, t f.2), List.mem_filter.mpr ⟨hm, by simp [hT1, hT2]⟩, ?_⟩
    simp only [hσ _ h1, hσ _ h2]
  · refine ⟨(t f.2, t f.1), List.mem_filter.mpr ⟨hm, by simp [hT1, hT2]⟩, ?_⟩
    simp only [hσ _ h1, hσ _ h2, edge]
    rw [Nat.min_comm, Nat.max_comm]

/-- **Minors of outerplanar embeddings**, on edge lists, by induction on the total size of
the branch sets. -/
theorem planar_of_listMinor {size : ℕ} {h : Graph}
    (hh : ∀ e ∈ h, e.1 < size ∧ e.2 < size) :
    ∀ (N : ℕ) (es : List (ℕ × ℕ)) (branch : ℕ → List ℕ), weight size branch = N →
      Complexity.PlanarGraph es → ListMinor es size h branch →
        Complexity.PlanarGraph (STACS2027.simpleEdges h) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro es branch hw ho hm
    by_cases hc : ∃ i, i < size ∧ ∃ p ∈ branch i, ∃ q ∈ branch i, p ≠ q
    · obtain ⟨i, hi, p, hp, q, hq, hpq⟩ := hc
      obtain ⟨s, t, hs, ht, hst, hmem⟩ : ∃ s t, s ∈ branch i ∧ t ∈ branch i ∧ s ≠ t ∧
          (s, t) ∈ es := by
        rcases Relation.ReflTransGen.cases_head (hm.2.2.1 i hi p hp q hq) with he | ⟨c, hc, -⟩
        · exact absurd he hpq
        · obtain ⟨hp', hc', hne, hpc | hcp⟩ := hc
          · exact ⟨p, c, hp', hc', hne, hpc⟩
          · exact ⟨c, p, hc', hp', Ne.symm hne, hcp⟩
      exact ih _ (hw ▸ weight_contract_lt hi ht) _ _ rfl (ho.contract hst hmem)
        (listMinor_contract hm hh hi hs ht hst)
    · refine planar_of_listMinor_const hh ho hm ?_
      intro i hi p hp q hq
      by_contra hpq
      exact hc ⟨i, hi, p, hp, q, hq, hpq⟩


end STACS2027.PlanarMinor

namespace Complexity.PlanarGraph
open STACS2027 STACS2027.OuterplanarMinor

theorem of_hasMinor {g h : Graph} {size : ℕ}
    (hg : Complexity.PlanarGraph g) (hm : HasMinor g size h)
    (hh : ∀ e ∈ h, e.1 < size ∧ e.2 < size) : Complexity.PlanarGraph (STACS2027.simpleEdges h) := by
  obtain ⟨branch, h1, h2, h3, h4⟩ := hm
  have hladj : ∀ u v, Adj g u v → LAdj (STACS2027.simpleEdges g) u v := by
    intro u v huv
    refine ⟨huv.1, ?_⟩
    have he := edge_mem_simpleEdges huv
    by_cases hle : u ≤ v
    · left
      have : edge u v = (u, v) := by simp [edge, Nat.min_eq_left hle, Nat.max_eq_right hle]
      rwa [this] at he
    · right
      have : edge u v = (v, u) := by
        simp [edge, Nat.min_eq_right (by omega : v ≤ u), Nat.max_eq_left (by omega : v ≤ u)]
      rwa [this] at he
  refine STACS2027.PlanarMinor.planar_of_listMinor hh _ (STACS2027.simpleEdges g) branch rfl hg.simpleEdges ⟨h1, h2, ?_, ?_⟩
  · intro i hi u hu v hv
    obtain ⟨w, hw1, hw2, hw⟩ := h3 i hi u v hu hv
    have hmono : ∀ a b, (a ∈ branch i ∧ b ∈ branch i ∧ Adj g a b) →
        BStep (STACS2027.simpleEdges g) (branch i) a b :=
      fun a b hab => ⟨hab.1, hab.2.1, hladj a b hab.2.2⟩
    exact Relation.ReflTransGen.mono hmono u v (reflTransGen_of_walk w u v hw hw1 hw2)
  · intro e he _
    obtain ⟨u, v, hu, hv, huv⟩ := h4 e he
    exact ⟨u, hu, v, hv, hladj u v huv⟩


end Complexity.PlanarGraph

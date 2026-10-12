module

public import Outerplanar.PlanarNeighbour
public import Outerplanar.TriangleEdgeCount
import Mathlib.Tactic

/-! A planar graph has an edge with at most two common neighbours. -/

@[expose] public section
namespace STACS2027.PlanarTriangleGeometry
open Complexity STACS2027.TriangleMatching

/-- A finite set with no three distinct elements has cardinality at most two. -/
theorem finset_card_le_two_of_repetitions {S : Finset Nat}
    (h : ∀ a∈S,∀ b∈S,∀ c∈S,a=b ∨ a=c ∨ b=c) : S.card≤2 := by
  classical
  by_cases he : S.Nonempty
  · obtain ⟨a,ha⟩ := he
    by_cases hh : ∀ b∈S,b=a
    · have hs : S⊆{a} := by intro b hb; simp [hh b hb]
      have hc := Finset.card_le_card hs
      simp only [Finset.card_singleton] at hc
      omega
    · push Not at hh
      obtain ⟨b,hb,hba⟩ := hh
      have hs : S⊆{a,b} := by
        intro c hc
        rcases h a ha b hb c hc with hab | hac | hbc
        · exact False.elim (hba hab.symm)
        · simp [hac]
        · simp [hbc]
      exact (Finset.card_le_card hs).trans Finset.card_le_two
  · have hs : S=∅ := Finset.not_nonempty_iff_eq_empty.mp he
    simp [hs]

/-- On a nonempty planar canonical edge set, some proper edge has at most two
common neighbours. No degree or connectedness hypothesis is supplied. -/
theorem planar_light_edge {E : Finset Edge} (hp : PlanarGraph E.toList)
    (hcanonical : ∀ e∈E,e.1<e.2) (hne : E.Nonempty) :
    ∃ u v,u<v ∧ edge u v∈E ∧ (commonVertices E u v).card≤2 := by
  classical
  obtain ⟨e,he⟩ := hne
  have heproper := hcanonical e he
  have hea : Adj E.toList e.1 e.2 :=
    ⟨Nat.ne_of_lt heproper,by simpa only [canonicalEdge_eq heproper,Finset.mem_toList] using he⟩
  let U : List Nat := (vset E.toList).toList.filter fun v => decide (Adj E.toList e.1 v)
  have memU : ∀ v,v∈U ↔ Adj E.toList e.1 v := by
    intro v
    simp only [U,List.mem_filter,Finset.mem_toList,decide_eq_true_eq]
    exact ⟨fun h=>h.2,fun h=>⟨mem_vset.mpr ⟨e.1,h⟩,h⟩⟩
  have hU : U≠[] := by
    intro h
    have hv := (memU e.2).mpr hea
    simp [h] at hv
  obtain ⟨v,hv,hlow⟩ := outerplanarDrawing_degenerate
    (planar_neighbours_outerplanar hp e.1) hU
  have hav := (memU v).mp hv
  have hsmall : (commonVertices E e.1 v).card≤2 := by
    apply finset_card_le_two_of_repetitions
    intro a ha b hb c hc
    have hcommon : ∀ w,w∈commonVertices E e.1 v →
        Adj E.toList e.1 w ∧ Adj (neighbourGraph E.toList e.1) v w := by
      intro w hw
      obtain ⟨hwa,hwv,hew,hevw⟩ := mem_commonVertices_iff.mp hw
      have haw : Adj E.toList e.1 w := ⟨hwa.symm,Finset.mem_toList.mpr hew⟩
      have hvw : Adj E.toList v w := ⟨hwv.symm,Finset.mem_toList.mpr hevw⟩
      exact ⟨haw,adj_neighbourGraph.mpr ⟨hvw,hav,haw⟩⟩
    exact hlow a b c ((memU a).mpr (hcommon a ha).1)
      ((memU b).mpr (hcommon b hb).1) ((memU c).mpr (hcommon c hc).1)
      (hcommon a ha).2 (hcommon b hb).2 (hcommon c hc).2
  rcases Nat.lt_or_gt_of_ne hav.1 with hl | hl
  · exact ⟨e.1,v,hl,Finset.mem_toList.mp hav.2,hsmall⟩
  · refine ⟨v,e.1,hl,?_,?_⟩
    · simpa only [edge_comm] using Finset.mem_toList.mp hav.2
    · have hs : commonVertices E v e.1 = commonVertices E e.1 v := by
        ext w
        simp only [mem_commonVertices_iff]
        tauto
      simpa only [hs] using hsmall

end STACS2027.PlanarTriangleGeometry

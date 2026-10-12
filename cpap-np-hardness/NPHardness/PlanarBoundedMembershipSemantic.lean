module
public import NPHardness.PlanarBoundedMembershipCheck
import Lean.Elab.Tactic.Omega
@[expose] public section
namespace STACS2027.PlanarBoundedMembership
open Complexity Complexity.SAT Complexity.Planar

theorem lit_eq_pos (t : ParseTables) (i v : Nat) :
    t.lit i = (⟨v,true⟩ : Literal) ↔ t.V i = v ∧ t.S i = 1 := by
  simp [ParseTables.lit, Literal.mk.injEq]

theorem lit_eq_neg (t : ParseTables) (i v : Nat) :
    t.lit i = (⟨v,false⟩ : Literal) ↔ t.V i = v ∧ t.S i ≠ 1 := by
  simp [ParseTables.lit, Literal.mk.injEq]

/-- The finite additional checks are exactly Definition 7 on the decoded formula. -/
theorem tableCaps_iff {L : Nat} {xb : Nat → Option Bool} {t : ParseTables}
    (hp : ParseOK L xb t) (hthree : ∀j,j<t.m→t.kk j≤3) :
    TableCaps t ↔ BoundedOccurrence t.fml := by
  rw [boundedOccurrence_iff_registered]
  simp only [IsLeOneLeTwoCNF, Restricted.filter_pos_count, Restricted.filter_neg_count]
  have hf := parse_flatten hp
  have hpos (v : Nat) : t.fml.flatten.count ⟨v,true⟩ ≤ 1 ↔
      ∀i j,i<t.M→j<t.M→t.V i=v→t.S i=1→t.V j=v→t.S j=1→i=j := by
    rw [count_le_one_iff, hf]
    simp only [List.length_map,List.length_range,List.getElem_map,List.getElem_range,lit_eq_pos]
    constructor
    · intro h i j hi hj hv hs hv' hs'; exact h i j hi hj ⟨hv,hs⟩ ⟨hv',hs'⟩
    · intro h i j hi hj hei hej; exact h i j hi hj hei.1 hei.2 hej.1 hej.2
  have hneg (v : Nat) : t.fml.flatten.count ⟨v,false⟩ ≤ 2 ↔
      ∀i j k,i<t.M→j<t.M→k<t.M→t.V i=v→t.S i≠1→t.V j=v→t.S j≠1→
        t.V k=v→t.S k≠1→i=j∨i=k∨j=k := by
    rw [count_le_two_iff, hf]
    simp only [List.length_map,List.length_range,List.getElem_map,List.getElem_range,lit_eq_neg]
    constructor
    · intro h i j k hi hj hk hv hs hv' hs' hv'' hs''
      exact h i j k hi hj hk ⟨hv,hs⟩ ⟨hv',hs'⟩ ⟨hv'',hs''⟩
    · intro h i j k hi hj hk hei hej hek
      exact h i j k hi hj hk hei.1 hei.2 hej.1 hej.2 hek.1 hek.2
  constructor
  · intro h
    refine ⟨?_,fun v => ⟨?_,?_⟩⟩
    · intro c hc
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hc
      have hj' := List.mem_range.mp hj
      simpa only [ParseTables.clause,List.length_map,List.length_range] using ⟨h.two j hj',hthree j hj'⟩
    · apply (hpos v).mpr
      intro i j hi hj hv hs hv' hs'
      exact h.positive i j hi hj hs hs' (hv.trans hv'.symm)
    · apply (hneg v).mpr
      intro i j k hi hj hk hv hs hv' hs' hv'' hs''
      exact h.negative i j k hi hj hk hs hs' hs'' (hv.trans hv'.symm) (hv.trans hv''.symm)
  · rintro ⟨hc,hcounts⟩
    refine ⟨?_,?_,?_⟩
    · intro j hj
      have := (hc (t.clause j) (List.mem_map.mpr ⟨j,List.mem_range.mpr hj,rfl⟩)).1
      simpa only [ParseTables.clause,List.length_map,List.length_range] using this
    · intro i j hi hj hsi hsj hv
      exact (hpos (t.V i)).mp (hcounts (t.V i)).1 i j hi hj rfl hsi hv.symm hsj
    · intro i j k hi hj hk hsi hsj hsk hvj hvk
      exact (hneg (t.V i)).mp (hcounts (t.V i)).2 i j k hi hj hk rfl hsi hvj.symm hsj hvk.symm hsk

end STACS2027.PlanarBoundedMembership

module

public import ApproximationHardness.Embed.SolverNodeRAM
import Mathlib.Tactic.IntervalCases
import Lean.Elab.Tactic.Omega

/-! Actual bounded part-result reads and singleton initializations. -/

@[expose] public section

set_option maxHeartbeats 1500000

namespace STACS2027.Embed.RAMSolver

open RAM

/-- Replace the represented arrays while preserving the live scalar frame. -/
theorem Rep.transfer {L : Layout} {c d : Config} {s : SMS} {m : SMem} (hr : Rep L c s)
    (hs : ∀ i, i < 20 → d.reg i = c.reg i)
    (hb : ∀ i, 50 ≤ i → d.reg i = c.reg i)
    (hm : ∀ j, j < 12 → ∀ i, i < L.width → d.mem (L.cell j i) = memField m j i) :
    Rep L d {s with m := m} := by
  constructor
  · refine ⟨(hs 0 (by decide)).trans hr.bases.1,
      (hs 1 (by decide)).trans hr.bases.2.1,
      (hs 2 (by decide)).trans hr.bases.2.2.1,
      (hs 3 (by decide)).trans hr.bases.2.2.2.1, ?_⟩
    intro j hj
    exact (hb _ (by omega)).trans (hr.bases.2.2.2.2 j hj)
  · exact hm
  · exact (hs 6 (by decide)).trans hr.index
  · exact (hs 7 (by decide)).trans hr.mode
  · exact (hs 8 (by decide)).trans hr.node
  · exact (hs 9 (by decide)).trans hr.group
  · exact (hs 10 (by decide)).trans hr.upperLow
  · exact (hs 11 (by decide)).trans hr.resultLow
  · exact (hs 12 (by decide)).trans hr.upperHead
  · exact (hs 13 (by decide)).trans hr.lowerHead
  · exact (hs 14 (by decide)).trans hr.positiveHead
  · exact (hs 15 (by decide)).trans hr.positiveTail
  · exact (hs 16 (by decide)).trans hr.negativeHead
  · exact (hs 17 (by decide)).trans hr.negativeTail
  · exact (hs 18 (by decide)).trans hr.lowerClassHead
  · exact (hs 19 (by decide)).trans hr.lowerClassTail

/-- Item result code refines `Sol.itRes`, including its finite singleton-array writes. -/
theorem itemResultInto_rep {L : Layout} {c : Config} {s : SMS} {S : Sol} {post : List Nat}
    {vertexBound dartBound typ value head low : Nat} (hr : Rep L c s)
    (ht : Tables L c S post vertexBound dartBound) (it : Item)
    (hit : match it with | .node w => w < vertexBound | .dart e => e < dartBound)
    (hh : 20 ≤ head ∧ head < 30) (hl : 20 ≤ low ∧ low < 30)
    (hv : value < 30) (hvh : value ≠ head) (hvl : value ≠ low) (hhl : head ≠ low)
    (htyp : c.reg typ = itemType it) (hval : c.reg value = itemValue it) :
    let out := run (itemResultInto typ value head low) c
    out.reg head = (S.itRes s.m it).2.1 ∧ out.reg low = (S.itRes s.m it).2.2 ∧
      Rep L out {s with m := (S.itRes s.m it).1} ∧
      Tables L out S post vertexBound dartBound := by
  obtain ⟨hhead, hlow, hmem, hframe, hout⟩ :=
    itemResultInto_raw (typ := typ) c hh hl hv hvh hvl hhl hr.bases.1 hr.bases.2.1
  have hbase := hr.bases.2.2.2.2
  cases it with
  | node w =>
    have hw : w < L.width := hit.trans_le ht.vertices
    simp only [itemType, itemValue] at htyp hval
    simp [htyp, hval] at hhead hlow hmem
    have hrs : c.mem (c.reg 56 + w) = s.m.rs w := by
      simpa [hbase 6 (by decide), Layout.cell, memField] using hr.arrays 6 (by decide) w hw
    have hrl : c.mem (c.reg 57 + w) = s.m.rl w := by
      simpa [hbase 7 (by decide), Layout.cell, memField] using hr.arrays 7 (by decide) w hw
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [Sol.itRes, hrs] using hhead
    · simpa [Sol.itRes, hrl] using hlow
    · exact hr.frame (fun i hi => hframe i (Or.inl hi)) (fun i hi => hframe i (Or.inr hi)) hmem
    · exact ht.frame (hframe 4 (Or.inl (by decide))) (hframe 5 (Or.inl (by decide)))
        (by rw [hmem]; exact TableMemEq.refl L c.mem)
  | dart e =>
    have he : e < L.width := hit.trans_le ht.darts
    simp only [itemType, itemValue] at htyp hval
    simp [htyp, hval] at hhead hlow hmem
    let m₁ := upd c.mem (L.cell 1 e) (e + 1)
    let m₂ := upd m₁ (L.cell 2 e) (e + 1)
    let m₃ := upd m₂ (L.cell 3 e) 0
    let m₄ := upd m₃ (L.cell 5 e) 0
    have hm' : (run (itemResultInto typ value head low) c).mem = m₄ := by
      simpa only [m₄, m₃, m₂, m₁, Layout.cell,
        hbase 1 (by decide), hbase 2 (by decide), hbase 3 (by decide), hbase 5 (by decide)] using hmem
    have h₁ := TableMemEq.update L c.mem 1 e (e + 1) (by decide) he
    have h₂ := (TableMemEq.update L m₁ 2 e (e + 1) (by decide) he).trans h₁
    have h₃ := (TableMemEq.update L m₂ 3 e 0 (by decide) he).trans h₂
    have h₄ : TableMemEq L m₄ c.mem := (TableMemEq.update L m₃ 5 e 0 (by decide) he).trans h₃
    have hkey : m₄ (L.cell 12 e) = S.key e :=
      (h₄ 12 (by decide) (by decide) e he).trans (ht.keys e hit)
    have hlow₀ : (run (itemResultInto typ value head low) c).reg low = m₄ (L.cell 12 e) + 1 := by
      simpa only [m₄, m₃, m₂, m₁, Layout.cell,
        hbase 1 (by decide), hbase 2 (by decide), hbase 3 (by decide), hbase 5 (by decide),
        hbase 12 (by decide)] using hlow
    have hlow' : (run (itemResultInto typ value head low) c).reg low = S.key e + 1 := by
      simpa only [hkey] using hlow₀
    refine ⟨?_, hlow', ?_, ?_⟩
    · simpa [Sol.itRes] using hhead
    · apply hr.transfer (fun i hi => hframe i (Or.inl hi)) (fun i hi => hframe i (Or.inr hi))
      intro j hj i hi
      rw [hm']
      dsimp only [m₄, m₃, m₂, m₁]
      simp only [update_cell L _ j 5 i e _ hi he,
        update_cell L _ j 3 i e _ hi he, update_cell L _ j 2 i e _ hi he,
        update_cell L _ j 1 i e _ hi he]
      interval_cases j
      · simp [Sol.itRes, memField, upd, hr.arrays 0 (by decide) i hi]
      · simp [Sol.itRes, memField, upd, hr.arrays 1 (by decide) i hi]
      · simp [Sol.itRes, memField, upd, hr.arrays 2 (by decide) i hi]
      · simp [Sol.itRes, memField, upd, hr.arrays 3 (by decide) i hi]
      · simp [Sol.itRes, memField, upd, hr.arrays 4 (by decide) i hi]
      · simp [Sol.itRes, memField, upd, hr.arrays 5 (by decide) i hi]
      · simp [Sol.itRes, memField, upd, hr.arrays 6 (by decide) i hi]
      · simp [Sol.itRes, memField, upd, hr.arrays 7 (by decide) i hi]
      · simp [Sol.itRes, memField, upd, hr.arrays 8 (by decide) i hi]
      · simp [Sol.itRes, memField, upd, hr.arrays 9 (by decide) i hi]
      · simp [Sol.itRes, memField, upd, hr.arrays 10 (by decide) i hi]
      · simp [Sol.itRes, memField, upd, hr.arrays 11 (by decide) i hi]
    · apply ht.frame (hframe 4 (Or.inl (by decide))) (hframe 5 (Or.inl (by decide)))
      rw [hm']
      exact h₄

end STACS2027.Embed.RAMSolver

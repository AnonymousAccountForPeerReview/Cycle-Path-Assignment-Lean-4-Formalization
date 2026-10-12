module

public import ApproximationHardness.Embed.SolverCloseRAM
public import ApproximationHardness.Embed.SolverItemRAM
import Mathlib.Tactic.IntervalCases
import Lean.Elab.Tactic.Omega

/-! Finite-layout refinement of the linked target closing operation. -/

@[expose] public section

set_option maxHeartbeats 1500000

namespace STACS2027.Embed.RAMSolver

open RAM

/-- The close operation uses the represented linked arrays and preserves formula tables. -/
theorem closeResultProgram_rep {L : Layout} {c : Config} {s : SMS} {S : Sol} {post : List Nat}
    {vertexBound dartBound e h l : Nat} (hr : Rep L c s)
    (ht : Tables L c S post vertexBound dartBound) (he : e < dartBound) (hh : h ≤ L.width)
    (hec : c.reg 23 = e) (hhc : c.reg 24 = h) (hlc : c.reg 25 = l) :
    let out := run closeResultProgram c
    out.reg 24 = (S.closeM s.m e h l).2.1 ∧ out.reg 25 = (S.closeM s.m e h l).2.2 ∧
      Rep L out {s with m := (S.closeM s.m e h l).1} ∧
      Tables L out S post vertexBound dartBound := by
  obtain ⟨hhead, hlow, hmem, hframe, hout⟩ := closeResultProgram_raw c hr.bases.1 hr.bases.2.1
  have hbase := hr.bases.2.2.2.2
  have hew : e < L.width := he.trans_le ht.darts
  by_cases hhzero : h = 0
  · simp only [hhc, hhzero, if_pos rfl] at hhead hlow hmem
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [Sol.closeM, hhzero] using hhead
    · simpa [Sol.closeM, hhzero, ht.infinity] using hlow
    · simpa [Sol.closeM, hhzero] using hr.frame (fun i hi => hframe i (Or.inl hi))
        (fun i hi => hframe i (Or.inr (Or.inr (Or.inr (Or.inr hi))))) hmem
    · apply ht.frame (hframe 4 (Or.inl (by decide))) (hframe 5 (Or.inl (by decide)))
      rw [hmem]; exact TableMemEq.refl L c.mem
  · let g := h - 1
    have hg : g < L.width := by dsimp [g]; omega
    have hph : c.mem (L.cell 1 g) = s.m.ph g := hr.arrays 1 (by decide) g hg
    have hpt : c.mem (L.cell 2 g) = s.m.pt g := hr.arrays 2 (by decide) g hg
    have hmh : c.mem (L.cell 3 g) = s.m.mh g := hr.arrays 3 (by decide) g hg
    have hmt : c.mem (L.cell 4 g) = s.m.mt g := hr.arrays 4 (by decide) g hg
    have hnx : c.mem (L.cell 0 e) = s.m.nx e := hr.arrays 0 (by decide) e hew
    simp only [Layout.cell, g] at hph hpt hmh hmt hnx
    let mnew : SMem := if s.m.ph g = e + 1 then
        {s.m with ph := upd s.m.ph g (if s.m.ph g = s.m.pt g then 0 else s.m.nx e)}
      else {s.m with mh := upd s.m.mh g (if s.m.mh g = s.m.mt g then 0 else s.m.nx e)}
    let rawnew := if s.m.ph g = e + 1 then
        upd c.mem (L.cell 1 g) (if s.m.ph g = s.m.pt g then 0 else s.m.nx e)
      else upd c.mem (L.cell 3 g) (if s.m.mh g = s.m.mt g then 0 else s.m.nx e)
    have hmem' : (run closeResultProgram c).mem = rawnew := by
      simpa only [hec, hhc, hlc, if_neg hhzero, hbase 0 (by decide), hbase 1 (by decide),
        hbase 2 (by decide), hbase 3 (by decide), hbase 4 (by decide),
        Layout.cell, g, hph, hpt, hmh, hmt, hnx, rawnew] using hmem
    have hr' : Rep L (run closeResultProgram c) {s with m := mnew} := by
      apply hr.transfer (fun i hi => hframe i (Or.inl hi))
        (fun i hi => hframe i (Or.inr (Or.inr (Or.inr (Or.inr hi)))))
      intro j hj i hi
      rw [hmem']
      have harr := hr.arrays j hj i hi
      dsimp only [rawnew, mnew]
      by_cases hp : s.m.ph g = e + 1
      · simp only [if_pos hp, update_cell L _ j 1 i g _ hi hg]
        interval_cases j <;> simp [memField, upd, eq_comm, harr]
      · simp only [if_neg hp, update_cell L _ j 3 i g _ hi hg]
        interval_cases j <;> simp [memField, upd, eq_comm, harr]
    have hte : TableMemEq L rawnew c.mem := by
      dsimp only [rawnew]
      split
      · exact TableMemEq.update L c.mem 1 g _ (by decide) hg
      · exact TableMemEq.update L c.mem 3 g _ (by decide) hg
    have ht' : Tables L (run closeResultProgram c) S post vertexBound dartBound := by
      apply ht.frame (hframe 4 (Or.inl (by decide))) (hframe 5 (Or.inl (by decide)))
      rw [hmem']; exact hte
    have hresult : (S.closeM s.m e h l).1 = mnew := by simp [Sol.closeM, hhzero, mnew, g]
    have hrawhead : (run closeResultProgram c).reg 24 =
        if (run closeResultProgram c).mem (L.cell 1 g) = 0 ∧
          (run closeResultProgram c).mem (L.cell 3 g) = 0 then
          (run closeResultProgram c).mem (L.cell 5 g) else h := by
      rw [hmem']
      convert hhead using 1
      simp only [hec, hhc, hlc, if_neg hhzero, hbase 0 (by decide), hbase 1 (by decide),
        hbase 2 (by decide), hbase 3 (by decide), hbase 4 (by decide), hbase 5 (by decide),
        Layout.cell, g, hph, hpt, hmh, hmt, hnx, rawnew]
      rfl
    have hrawlow : (run closeResultProgram c).reg 25 =
        if l = (run closeResultProgram c).mem (L.cell 12 e) + 1 then c.reg 5 else l := by
      rw [hmem']
      convert hlow using 1
      simp only [hec, hhc, hlc, if_neg hhzero, hbase 0 (by decide), hbase 1 (by decide),
        hbase 2 (by decide), hbase 3 (by decide), hbase 4 (by decide), hbase 12 (by decide),
        Layout.cell, g, hph, hpt, hmh, hmt, hnx, rawnew]
      rfl
    refine ⟨?_, ?_, ?_, ht'⟩
    · simpa [Sol.closeM, hhzero, mnew, g,
        hr'.arrays 1 (by decide) g hg, hr'.arrays 3 (by decide) g hg,
        hr'.arrays 5 (by decide) g hg, memField] using hrawhead
    · simpa [Sol.closeM, hhzero, ht'.keys e he, ht.infinity] using hrawlow
    · rw [hresult]; exact hr'

end STACS2027.Embed.RAMSolver

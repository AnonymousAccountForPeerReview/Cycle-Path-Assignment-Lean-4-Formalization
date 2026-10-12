module

public import ApproximationHardness.Embed.SolverExecution
public import ApproximationHardness.Embed.DFSRAM
public import ApproximationHardness.Embed.DefaultRotationLoop
public import ApproximationHardness.Embed.OrientationKeyMaterialization

/-! # Finite-state frames between the solver and its read-only output passes -/

@[expose] public section

set_option maxRecDepth 10000

namespace STACS2027.Embed.RAMSolver

open RAM

theorem Bases.finiteFrame {L : Layout} {c d : Config} (h : Bases L c)
    (hr : ∀ r,r<72 → d.reg r=c.reg r) : Bases L d := by
  rcases h with ⟨hz,ho,hb,hw,hblocks⟩
  exact ⟨(hr 0 (by decide)).trans hz,(hr 1 (by decide)).trans ho,
    (hr 2 (by decide)).trans hb,(hr 3 (by decide)).trans hw,
    fun j hj=>(hr (50+j) (by omega)).trans (hblocks j hj)⟩

theorem Rep.finiteFrame {L : Layout} {c d : Config} {s : SMS} (h : Rep L c s)
    (hr : ∀ r,r<72 → d.reg r=c.reg r)
    (hm : ∀ a,a<L.limit → d.mem a=c.mem a) : Rep L d s := by
  refine ⟨h.bases.finiteFrame hr,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro j hj i hi
    rw [hm _ (L.cell_lt (by omega) hi)]
    exact h.arrays j hj i hi
  all_goals rw [hr _ (by decide)]
  all_goals first | exact h.index | exact h.mode | exact h.node | exact h.group |
    exact h.upperLow | exact h.resultLow | exact h.upperHead | exact h.lowerHead |
    exact h.positiveHead | exact h.positiveTail | exact h.negativeHead |
    exact h.negativeTail | exact h.lowerClassHead | exact h.lowerClassTail

theorem Tables.prefixFrame {L : Layout} {c d : Config} {S : Sol} {post : List Nat}
    {vertices darts : Nat} (h : Tables L c S post vertices darts)
    (hr : ∀ r,r<72 → d.reg r=c.reg r)
    (hm : ∀ a,a<L.limit → d.mem a=c.mem a) : Tables L d S post vertices darts := by
  apply h.frame (hr 4 (by decide)) (hr 5 (by decide))
  intro j hj hk i hi;exact hm _ (L.cell_lt hk hi)

theorem defaultRotationProgram_regs {bound : Nat} {c d : Config} {t : Nat}
    (he : ExecB bound defaultRotationProgram c t d) (r : Nat)
    (hr : r<240 ∨ r=261 ∨ r=262 ∨ 265<r) : d.reg r=c.reg r := by
  apply he.reg_frame
  have H : (regsW defaultRotationProgram).all
    (fun r=>decide (240≤r ∧ r≤265 ∧ r≠261 ∧ r≠262))=true := by decide
  intro hm;have := of_decide_eq_true ((List.all_eq_true.mp H) r hm);omega

theorem orientationLoop_regs {bound : Nat} {c d : Config} {t : Nat}
    (he : ExecB bound orientationLoop c t d) (r : Nat) (hr : r<100 ∨ 111<r) :
    d.reg r=c.reg r := by
  apply he.reg_frame
  have H : (regsW orientationLoop).all (fun r=>decide (100≤r ∧ r≤111))=true := by decide
  intro hm;have := of_decide_eq_true ((List.all_eq_true.mp H) r hm);omega

end STACS2027.Embed.RAMSolver

namespace STACS2027.Embed.DFSRAM

open RAM

theorem Bases.phaseFrame {L : Layout} {G : DG} {c d : Config} (hb : Bases L G c)
    (hr : ∀ r,r=0 ∨ r=1 ∨ (140≤r ∧ r≤170) → d.reg r=c.reg r) : Bases L G d := by
  apply hb.frame
  intro r h
  simp only [dartCount,baseRegister,widthRegister] at h
  apply hr
  rcases h with h | h | h | h | h | h <;> omega

theorem Bases.solverFrame {L : Layout} {G : DG} {c d : Config} {S : RAMSolver.Layout}
    (hb : Bases L G c) (hs : RAMSolver.Bases S d)
    (hr : ∀ r,81<r → d.reg r=c.reg r) : Bases L G d := by
  apply hb.phaseFrame
  intro r h
  rcases h with rfl | rfl | h
  · exact hs.1.trans hb.1.symm
  · exact hs.2.1.trans hb.2.1.symm
  · exact hr r (by omega)

theorem Tables.prefixFrame {L : Layout} {G : DG} {c d : Config}
    (h : Tables L G c) (hw : 2*G.E≤L.width)
    (hm : ∀ a,a<L.limit → d.mem a=c.mem a) : Tables L G d := by
  constructor
  · intro i hi;rw [hm _ (L.cell_lt (by decide) (hi.trans_le hw))];exact h.representatives i hi
  · intro i hi;rw [hm _ (L.cell_lt (by decide) (hi.trans_le hw))];exact h.partners i hi
  · intro i hi;rw [hm _ (L.cell_lt (by decide) (hi.trans_le hw))];exact h.degrees i hi
  · intro k hk i hi;rw [hm _ (L.cell_lt (by omega) (hi.trans_le hw))];exact h.adjacent k hk i hi

end STACS2027.Embed.DFSRAM

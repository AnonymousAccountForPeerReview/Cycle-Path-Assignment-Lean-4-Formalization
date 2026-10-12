module

public import ApproximationHardness.Embed.PlanVertexBounds
import Lean.Elab.Tactic.Omega

/-! The complete actual bounded scan constructing all forest-plan node tables. -/

@[expose] public section
namespace STACS2027.Embed.PlanRAM
open RAM

attribute [local simp] zBase vertex degree vertexParent dart opposite child childParent
  itemType itemValue distinguished vertexBound partCount topVertex remaining slot
  address test otherTest exclusion representative constant

/-- One actual instruction extends the completed prefix by precisely its two node entries. -/
theorem vertexTableStep_prefix {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config} {r : Nat}
    (h : VertexPrefix L G s r c) (hG : G.Ok) (hF : (G.fd s).Valid)
    (hr : r<2*G.E) (hv : c.reg vertex=r) (hw : 4*G.E≤L.width) :
    AddrOK (zLimit L) vertexTableStep c ∧ VertexPrefix L G s (r+1) (run vertexTableStep c) := by
  have ha := vertexTableStep_addrOK h.context hG hF hr hv hw
  obtain ⟨hc,hz,he,hframe⟩ := vertexTableStep_values h.context h.mutable hG hF hr hv h.groupBound hw
  refine ⟨ha,hc,hz,?_,?_⟩
  · exact (run_reg_frame vertexTableStep c vertexBound (by decide)).trans h.groupBound
  · intro q hq
    by_cases hqr : q=r
    · subst q;exact he
    · have hlt : q<r := by omega
      exact (h.entries q hlt).frame hr hlt hw hframe

/-- All distinguished entries and both halves of all vertex tables are compiled in linear RAM time. -/
theorem vertexTablesProgram_complete {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) (hz : MutableZero L c) (hg : c.reg vertexBound=4*G.E)
    (hG : G.Ok) (hF : (G.fd s).Valid) (hw : 4*G.E≤L.width) :
    ∃t d,ExecB (zLimit L) vertexTablesProgram c t d ∧ t≤1004*(2*G.E)+4 ∧
      VertexPrefix L G s (2*G.E) d ∧ d.reg vertex=2*G.E ∧ d.out=c.out ∧
      (∀r,r<281 → d.reg r=c.reg r) := by
  exact vertexTablesProgram_spec hc hz hg (fun j d hj hp hv => vertexTableStep_prefix hp hG hF hj hv hw)

/-- The two-node prefix representation supplies every solver-plan node table entry. -/
theorem VertexPrefix.nodeValues {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (h : VertexPrefix L G s (2*G.E) c) {v : Nat} (hv : v<4*G.E) :
    c.mem ((solverLayout L).cell 15 v)=(G.fd s).gid v ∧
    c.mem ((solverLayout L).cell 16 v)=((G.fd s).parts v).length ∧
    PartSlots (solverLayout L) c.mem v ((G.fd s).parts v) := by
  by_cases hlow : v<2*G.E
  · have he := h.entries v hlow
    exact ⟨he.ordinaryGroup,he.ordinaryCount,he.ordinarySlots⟩
  · have hr : v-2*G.E<2*G.E := by omega
    have he := h.entries (v-2*G.E) hr
    have hEq : 2*G.E+(v-2*G.E)=v := by omega
    have hEqF : 2*(G.fd s).E+(v-2*G.E)=v := hEq
    exact hEqF ▸ And.intro he.topGroup (And.intro he.topCount he.topSlots)

end STACS2027.Embed.PlanRAM

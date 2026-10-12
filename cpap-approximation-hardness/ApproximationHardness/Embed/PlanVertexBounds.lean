module

public import ApproximationHardness.Embed.PlanVertexRefine
import Lean.Elab.Tactic.Omega

/-! Address-safe bounded execution of the complete one-vertex plan instruction. -/

@[expose] public section
namespace STACS2027.Embed.PlanRAM
open RAM

attribute [local simp] zBase vertex degree vertexParent dart opposite child childParent
  itemType itemValue distinguished vertexBound partCount topVertex remaining slot
  address test otherTest exclusion representative constant

theorem vertexBounds_run_skip (c : Config) : run .skip c=c := rfl

/-- Address safety composes the distinguished scan, two-node header, and representative branch. -/
theorem vertexTableStep_addr_split (S : Nat) (c : Config) :
    AddrOK S vertexTableStep c ↔ AddrOK S distinguishedProgram c ∧
      AddrOK S vertexHeader (run distinguishedProgram c) ∧
      AddrOK S vertexFinish (run vertexHeader (run distinguishedProgram c)) := by
  simp only [vertexTableStep,vertexHeader,storeVertexGroups,vertexLookup,vertexFinish,
    seqs,addrOK_seq,addrOK_skip,run_seq,vertexBounds_run_skip,and_true,and_assoc]

/-- Every load and store in the actual one-vertex compiler uses a bounded installed cell. -/
theorem vertexTableStep_addrOK {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) (hG : G.Ok) (hF : (G.fd s).Valid) {r : Nat}
    (hr : r<2*G.E) (hv : c.reg vertex=r) (hw : 4*G.E≤L.width) :
    AddrOK (zLimit L) vertexTableStep c := by
  rw [vertexTableStep_addr_split]
  refine ⟨distinguishedProgram_addrOK hc hG hr hv,?_⟩
  generalize heD : run distinguishedProgram c=d
  have hd : Context L G s d := heD ▸ hc.distinguishedProgram
  have hi := distinguishedProgram_inputs hc hG hF hr hv
  rw [heD] at hi
  obtain ⟨hvd,hdd,hpd,hzd⟩ := hi
  have htw : 2*G.E+r<L.width := by omega
  refine ⟨vertexHeader_addrOK hd (by rw [hvd];exact hr) (by rw [hvd];exact htw),?_⟩
  generalize heH : run vertexHeader d=e
  have he : Context L G s e := heH ▸ hd.vertexHeader
  have hve : e.reg vertex=r := by rw [←heH];exact (vertexHeader_reg d vertex (by decide)).trans hvd
  have hde : e.reg degree=(G.darts r).length := by rw [←heH];exact (vertexHeader_reg d degree (by decide)).trans hdd
  have hpe : e.reg vertexParent=s.par r := by rw [←heH];exact (vertexHeader_reg d vertexParent (by decide)).trans hpd
  have hze : e.reg distinguished=(G.fd s).zOf r := by rw [←heH];exact (vertexHeader_reg d distinguished (by decide)).trans hzd
  have hte : e.reg topVertex=2*G.E+r := by rw [←heH,vertexHeader_top hd,hvd]
  have htest := vertexHeader_test hd hr hvd
  rw [heH] at htest
  change (e.reg test=0 → AddrOK (zLimit L) (seqs [ordinaryParts,topParts]) e) ∧
    (e.reg test≠0 → AddrOK (zLimit L) .skip e)
  refine ⟨?_,fun _=>trivial⟩
  intro hzero
  have hver : (G.fd s).IsVertex r := ⟨hr,htest.mp hzero⟩
  have ho := (ordinaryParts_values he hG hF hve hde hpe hze hr hver).1
  have hto : (run ordinaryParts e).reg topVertex=2*G.E+r :=
    (ordinaryParts_reg e topVertex (by decide)).trans hte
  change AddrOK (zLimit L) ordinaryParts e ∧
    AddrOK (zLimit L) topParts (run ordinaryParts e) ∧ True
  exact ⟨ordinaryParts_addrOK he hG hr hve hde,
    topParts_addrOK ho hG (by rw [hto];exact htw),trivial⟩

/-- A fixed constant bounds the actual complete one-vertex instruction. -/
theorem vertexTableStep_exec {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) (hG : G.Ok) (hF : (G.fd s).Valid) {r : Nat}
    (hr : r<2*G.E) (hv : c.reg vertex=r) (hw : 4*G.E≤L.width) :
    ∃t,ExecB (zLimit L) vertexTableStep c t (run vertexTableStep c) ∧ t≤1000 :=
  ⟨_,execB_run _ vertexTableStep_loopFree c (vertexTableStep_addrOK hc hG hF hr hv hw),
    (cost_le_size _ _).trans vertexTableStep_size⟩

end STACS2027.Embed.PlanRAM

module

public import ApproximationHardness.Embed.PlanDistinguishedBounds
import Lean.Elab.Tactic.Omega

/-! Exact scalar inputs retained by the distinguished-dart compiler. -/

@[expose] public section
namespace STACS2027.Embed.PlanRAM
open RAM

attribute [local simp] zBase vertex degree vertexParent dart opposite child childParent
  itemType itemValue distinguished vertexBound partCount topVertex remaining slot
  address test otherTest exclusion representative constant

theorem distinguishedValues_run_skip (c : Config) : run .skip c=c := rfl

/-- Computing the distinguished entry also retains the exact degree, parent, and vertex index. -/
theorem distinguishedProgram_inputs {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) (hG : G.Ok) (hF : (G.fd s).Valid) {r : Nat}
    (hr : r<2*G.E) (hv : c.reg vertex=r) :
    (run distinguishedProgram c).reg vertex=r ∧
    (run distinguishedProgram c).reg degree=(G.darts r).length ∧
    (run distinguishedProgram c).reg vertexParent=s.par r ∧
    (run distinguishedProgram c).reg distinguished=(G.fd s).zOf r := by
  let tail := seqs [.const constant 3,.sub test degree constant,.sub otherTest constant degree,
    .add test test otherTest,.ifz test
      (seqs [readForest distinguished 5 vertex,distinguishedSlot 0,distinguishedSlot 1,distinguishedSlot 2])
      (.add distinguished DFSRAM.dartCount 0)]
  generalize he₀ : run (readForest degree 2 vertex) c=c₀
  have hc₀ : Context L G s c₀ := he₀ ▸ hc.readForest degree 2 vertex (by decide)
  have hv₀ : c₀.reg vertex=r := by rw [←he₀];simpa [readForest,seqs,run] using hv
  have hd₀ : c₀.reg degree=(G.darts r).length := by
    rw [←he₀]
    have hx := hc.tables.degrees r hr
    simpa [readForest,seqs,run,hv,hc.forest.bases.2.2.2.2.2 2 (by decide),DFSRAM.Layout.cell] using hx
  generalize he₁ : run (readForest vertexParent 6 vertex) c₀=c₁
  have hv₁ : c₁.reg vertex=r := by rw [←he₁];simpa [readForest,seqs,run] using hv₀
  have hd₁ : c₁.reg degree=(G.darts r).length := by rw [←he₁];simpa [readForest,seqs,run] using hd₀
  have hp₁ : c₁.reg vertexParent=s.par r := by
    rw [←he₁]
    have hx := hc₀.forest.parents r hr
    simpa [readForest,seqs,run,hv₀,hc₀.forest.bases.2.2.2.2.2 6 (by decide),DFSRAM.Layout.cell] using hx
  have hread : run distinguishedRead c=run tail c₁ := by
    simp only [distinguishedRead,seqs,run_seq,distinguishedValues_run_skip,he₀,he₁,tail]
  have hframe (q : Nat) (hq : q∈[vertex,degree,vertexParent]) : (run tail c₁).reg q=c₁.reg q := by
    apply run_reg_frame
    have hw : (regsW tail).all (fun q => decide (q∉[vertex,degree,vertexParent]))=true := by decide
    intro hn; exact (of_decide_eq_true ((List.all_eq_true.mp hw) q hn)) hq
  have hz := distinguishedRead_value hc hG hF hr hv
  rw [distinguishedProgram_run]
  have hstore := (zStore_raw (run distinguishedRead c) vertex distinguished (by decide)).2.1
  refine ⟨?_,?_,?_,?_⟩
  · rw [hstore vertex (by decide),hread,hframe vertex (by decide)];exact hv₁
  · rw [hstore degree (by decide),hread,hframe degree (by decide)];exact hd₁
  · rw [hstore vertexParent (by decide),hread,hframe vertexParent (by decide)];exact hp₁
  · exact (hstore distinguished (by decide)).trans hz

end STACS2027.Embed.PlanRAM

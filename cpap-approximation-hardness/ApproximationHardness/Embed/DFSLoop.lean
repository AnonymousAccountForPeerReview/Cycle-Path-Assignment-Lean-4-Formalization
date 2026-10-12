module

public import ApproximationHardness.Embed.DFSFrame
import Lean.Elab.Tactic.Omega

/-! # Fixed-budget execution of the cached forest search -/

@[expose] public section

namespace STACS2027.Embed.DFSRAM

open RAM Complexity Complexity.Planar

attribute [local simp] dartCount scan current inner height postLength remaining
  baseRegister widthRegister address pointer degree nextDart opposite nextVertex
  parent value needHeight test otherTest repValue

theorem Rep.setCounter {L : Layout} {G : DG} {c : Config} {s : DS}
    (h : Rep L G c s) (n : Nat) : Rep L G (c.setReg remaining n) s := by
  apply h.memory.of_regs (c := c.setReg remaining n) rfl
  · apply h.bases.frame
    intro r hr
    have hn : r ≠ remaining := by
      change r ≠ 146
      simp only [dartCount, baseRegister, widthRegister] at hr
      rcases hr with hr | hr | hr | hr | hr | hr <;> omega
    simp [Config.setReg, hn]
  · simpa [Config.setReg] using h.scan
  · simpa [Config.setReg] using h.current
  · simpa [Config.setReg] using h.inner
  · simpa [Config.setReg] using h.height
  · simpa [Config.setReg] using h.postLength

theorem stepProgram_high (c : Config) (r : Nat) (hr : 191 < r) :
    (run stepProgram c).reg r = c.reg r := by
  apply run_reg_frame
  have hh : (regsW stepProgram).all (fun r => decide (r ≤ 191)) = true := by decide
  intro hm
  have := of_decide_eq_true ((List.all_eq_true.mp hh) r hm)
  omega

theorem boundedRun_memAbove {S : Nat} {p : Stmt} {c d : Config} {t : Nat}
    (he : ExecB S p c t d) : ∀ a, S ≤ a → d.mem a = c.mem a := by
  induction he with
  | skip c | const r v c | add r a b c | sub r a b c | load r a c h | write r c =>
    intro a ha; rfl
  | store address r c h =>
    intro a ha
    simp [Config.setMem, show a ≠ c.reg address by omega]
  | seq he he' ih ih' => intro a ha; exact (ih' a ha).trans (ih a ha)
  | ifzTrue hz he ih | ifzFalse hn he ih => exact ih
  | loopDone hz => intro a ha; rfl
  | loopNext hn he he' ih ih' => intro a ha; exact (ih' a ha).trans (ih a ha)

theorem program_refines {L : Layout} {G : DG}
    (hG : G.Ok) (hw : 4 * G.E + 2 ≤ L.width)
    (haddr : ∀ c s, Rep L G c s → Tables L G c → G.Inv s →
      AddrOK L.limit stepProgram c)
    (c : Config) (hr : Rep L G c DG.init) (ht : Tables L G c)
    (hc : c.reg remaining = 10 * G.E + 1) :
    ∃ t d, ExecB L.limit program c t d ∧ t ≤ 3000 * (G.E + 1) ∧
      Rep L G d G.final ∧ Tables L G d ∧ d.out = c.out ∧
      (∀ r, 191 < r → d.reg r = c.reg r) ∧
      (∀ a, a < L.block 6 → d.mem a = c.mem a) ∧
      (∀ a, L.limit ≤ a → d.mem a = c.mem a) := by
  let budget := 10 * G.E + 1
  let I : Nat → Config → Prop := fun j d =>
    Rep L G d (Complexity.iterate G.step j DG.init) ∧ Tables L G d ∧ d.out = c.out ∧
      (∀ r, 191 < r → d.reg r = c.reg r) ∧
      (∀ a, a < L.block 6 → d.mem a = c.mem a) ∧
      (∀ a, L.limit ≤ a → d.mem a = c.mem a)
  have Hstep : ∀ j d, j < budget → I j d → d.reg remaining = budget - j →
      ∃ t d', ExecB L.limit loopBody d t d' ∧ t ≤ 251 ∧ I (j + 1) d' ∧
        d'.reg remaining + 1 = d.reg remaining := by
    intro j d hj hd hcount
    obtain ⟨Hdr, Hdt, Hout, Hreg, Hbelow, Habove⟩ := hd
    have hInv := DG.inv_iterate hG j
    have He := execB_run stepProgram stepProgram_loopFree d (haddr d _ Hdr Hdt hInv)
    have Ht := Nat.le_trans (cost_le_size stepProgram d) stepProgram_size
    have Hr := stepProgram_refines Hdr Hdt hG hInv hw
    have Htable := Hdt.run_step Hdr.bases (by omega)
    let d' := (run stepProgram d).setReg remaining ((run stepProgram d).reg remaining -
      (run stepProgram d).reg 1)
    have Hone : (run stepProgram d).reg 1 = 1 := Hr.bases.2.1
    have Hcount : (run stepProgram d).reg remaining = d.reg remaining := stepProgram_remaining d
    have Hrep : Rep L G d' (G.step (Complexity.iterate G.step j DG.init)) := Hr.setCounter _
    have Htable' : Tables L G d' := Htable.mem_congr rfl
    refine ⟨RAM.cost stepProgram d + 1, d', .seq He (.sub remaining remaining 1 _),
      by omega, ?_, ?_⟩
    · refine ⟨?_, Htable', ?_, ?_, ?_, ?_⟩
      · simpa only [iterate_succ'] using Hrep
      · exact (stepProgram_out d).trans Hout
      · intro r hrr
        change d'.reg r = c.reg r
        simp only [d', Config.setReg]
        rw [ite_eq_right (show r ≠ remaining by simp only [remaining]; omega), stepProgram_high d r hrr]
        exact Hreg r hrr
      · intro a ha
        exact ((stepProgram_cacheFrame L G d Hdr.bases).2 a ha).trans (Hbelow a ha)
      · intro a ha
        exact (boundedRun_memAbove He a ha).trans (Habove a ha)
    · change ((run stepProgram d).setReg remaining _).reg remaining + 1 = _
      simp only [Config.setReg, ↓reduceIte]
      rw [Hone, Hcount]
      dsimp only [budget] at hj hcount
      omega
  obtain ⟨t, d, He, Ht, Hfinal⟩ := exec_countLoop budget I 251 Hstep c
    ⟨hr, ht, rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩ hc
  refine ⟨t, d, He, ?_, Hfinal⟩
  dsimp only [budget] at Ht
  omega

end STACS2027.Embed.DFSRAM

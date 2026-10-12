module

public import ApproximationHardness.Embed.DFSLoop
public import ApproximationHardness.Embed.DFSAddress
public import ApproximationHardness.Embed.IncidencePreparation
import Lean.Elab.Tactic.Omega

/-! # A complete linear RAM forest search from the formula input -/

@[expose] public section

namespace STACS2027.Embed.DFSRAM

open RAM

theorem program_spec {L : Layout} {G : DG}
    (hG : G.Ok) (hw : 4 * G.E + 2 ≤ L.width)
    (c : Config) (hr : Rep L G c DG.init) (ht : Tables L G c)
    (hc : c.reg 146 = 10 * G.E + 1) :
    ∃ t d, ExecB L.limit program c t d ∧ t ≤ 3000 * (G.E + 1) ∧
      Rep L G d G.final ∧ Tables L G d ∧ d.out = c.out ∧
      (∀ r, 191 < r → d.reg r = c.reg r) ∧
      (∀ a, a < L.block 6 → d.mem a = c.mem a) ∧
      (∀ a, L.limit ≤ a → d.mem a = c.mem a) :=
  program_refines hG hw (fun _ _ hr ht hi => stepProgram_addrOK hr ht hG hi hw) c hr ht hc

end STACS2027.Embed.DFSRAM

namespace STACS2027.Embed.IncidenceRAM

open RAM Complexity.SAT

def prepareForest : Stmt := .seq prepareDFS DFSRAM.program

theorem prepareForest_spec (f : CNF) (hf : BoundedOccurrence f) :
    ∃ t c, ExecB (cacheLayout f).limit prepareForest (initial (ramInput f)) t c ∧
      t ≤ 4000 * ((ramInput f).length + variableBound f + 1) ∧
      DFSRAM.Rep (cacheLayout f) (incDG f) c (incDG f).final ∧
      DFSRAM.Tables (cacheLayout f) (incDG f) c ∧ c.out = [] ∧
      (∀ a, (cacheLayout f).limit ≤ a → c.mem a = 0) ∧
      (∀ a, a < (ramInput f).length → c.mem a = (ramInput f).getD a 0) := by
  obtain ⟨tA,cA,eA,htA,hbases,htables,hrep,hcount,hout,hfree,hinput⟩ :=
    prepareDFS_spec f hf (Nat.le_refl _)
  have hwidth : 4 * (incDG f).E + 2 ≤ (cacheLayout f).width := by
    dsimp [incDG,cacheLayout];omega
  obtain ⟨tB,cB,eB,htB,hrep',htables',hout',_,hbelow,habove⟩ :=
    DFSRAM.program_spec (incOk hf) hwidth cA hrep htables hcount
  refine ⟨tA+tB,cB,.seq eA eB,?_,hrep',htables',hout'.trans hout,?_,?_⟩
  · have hpre := (prepareDFS_linear f).2
    have hlen := ramInput_length_eq f
    dsimp only [incDG] at htB
    omega
  · intro a ha
    rw [habove a ha,hfree a ha]
  · intro a ha
    rw [hbelow a (by
      dsimp [cacheLayout,DFSRAM.Layout.block]
      omega),hinput a ha]

end STACS2027.Embed.IncidenceRAM

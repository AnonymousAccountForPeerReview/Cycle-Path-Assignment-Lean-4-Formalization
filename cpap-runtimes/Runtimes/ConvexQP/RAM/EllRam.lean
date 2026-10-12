module

public import Runtimes.ConvexQP.RAM.EllBound
import Mathlib.Tactic

/-!
# Lemma 16, Phase E on the RAM: the program and its specification

`ellProg = setup; while eCnt ≠ 0 do iterB`: the rational central-cut ellipsoid method
(`EllPhase.lean`) on the add/subtract RAM, reproducing `ellRun` exactly. From `QIn I` it reaches
`QMid I Xs` for `ellRun I (consts I.t I.k) = some Xs` in at most `ellC · (t k + 2)^10` steps,
by a run that touches only the addresses below any bound
`S ≥ reg rFREE + ellC · (t k + 2)^10` (`phaseE_ramB : PhaseERamB ellProg`): the layout `layOf`
above the initial free address and the scratch tables of the arithmetic (`ellSc` cells above the
final free address) fit (`ellSpace_le`).

* `setup` (`EllInit.lean`): allocation, globals, `ellInit`, `eCnt := N`;
* `iterB` (`EllIter.lean`): E1 `scan` (`EllScan.lean`), E2 `feas` (`EllFeas.lean`,
  `EllGap.lean`), the cut `gLoop` (`EllGrad.lean`), E4 `upd` (`EllUpd*.lean`);
* the loop (`EllLoop.lean`), the bit lengths (`EllCost.lean`) and the step bound
  (`EllBound.lean`).
-/

@[expose] public section

namespace STACS2027.Runtimes.QPRam

open STACS2027 STACS2027.RAM STACS2027.Runtimes.Arith STACS2027.Runtimes.ConvexQP

/-- **Phase E on the RAM.** -/
def ellProg : Stmt := .seq setup (.loop eCnt iterB)

theorem ellProg_writes : writes ellProg = false := by decide +kernel

/-- The registers written by Phase E: `rT`, `rFREE`, `qBX`, the arithmetic library's block
`400–449` and Phase E's scratch block `470–499`. -/
theorem ellProg_wregs : ∀ r ∈ wregs ellProg, r = rT ∨ r = rFREE ∨ r = qBX ∨
    (400 ≤ r ∧ r < 450) ∨ (470 ≤ r ∧ r < 500) := by decide +kernel

/-- **Phase E on the RAM within polynomial space** reproduces `ellRun` in
`O((t k + 2)^10)` steps, by a run below any bound `S ≥ reg rFREE + ellC · (t k + 2)^10`: the
layout `layOf` above the initial free address and the scratch tables of the arithmetic
(`ellSc` cells above the final free address) fit (`ellSpace_le`). -/
theorem phaseE_ramB : PhaseERamB ellProg := by
  refine ⟨ellC, fun I hI ht Xs hrun S c₀ hin hS => ?_⟩
  have hL := layOf_ok hI ht hin.2.2.1
  have hout : c₀.out = [] := hin.2.2.2.2
  have hsp := ellSpace_le I hI.1 ht (c₀.reg qBH) (c₀.reg rFREE)
  have hLS : (layOf I (c₀.reg qBH) (c₀.reg rFREE)).F + ellSc I.t I.k ≤ S := by omega
  have h1 := setup_specB I hI ht c₀ hin hLS
  have h2 := loop_specB I (layOf I (c₀.reg qBH) (c₀.reg rFREE)) hL hI hLS
  have h3 := (h1.seq (h2.pre fun c ⟨hE, hSt, hH, hz, hc⟩ =>
    ⟨⟨hE, hH, hz, 0, Nat.zero_le _, by unfold MSt; exact ⟨by rw [hc]; rfl, hSt⟩⟩,
      by rw [hc]⟩)).frame (F := fun c => c.out = [])
    (fun c c' hfr hF => (hfr.out ellProg_writes).trans hF)
  exact (h3.pre fun c hc => ⟨hc, by rw [hc]; exact hout⟩).mono (fun _ h => h)
    (fun c ⟨⟨hI', h0⟩, ho⟩ => ⟨mid_of_inv I _ hL hrun hI' h0 ho, by
      rw [hI'.1.free]; omega⟩) (total_le I hI.1 ht)

end STACS2027.Runtimes.QPRam

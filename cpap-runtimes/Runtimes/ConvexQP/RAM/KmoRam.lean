module

public import Runtimes.ConvexQP.RAM.KmoCost
import Mathlib.Tactic

/-!
# Lemma 16, Phases K, M, O on the RAM: the program and its specification

`kmoProg = kProg; mLoop; oProg` reproduces `Inst.exactFrom Xs 2^p` exactly:
from `QMid I Xs` (with `Xs/2^p ∈ 𝒳` and `gap ≤ ε²`) it writes
`outList (I.exactFrom Xs (2 ^ prec I.t I.k))` within `kmoC · (t k + 2)^10` steps, by a run that
touches only the addresses below any bound `S ≥ reg rFREE + kmoC · (t k + 2)^10`
(`phaseKMO_ramB : PhaseKMORamB kmoProg`): the layout `lay I F₀` above the initial free address
`F₀` and the scratch tables of the arithmetic above its end fit (`kmoSpace_le`); `H` and `Xs`
lie below `F₀`.

* Phase K (`kProg`, `KmoK1.lean` … `KmoK7.lean`): the layout, `Zn₀ = kktZn` (`Xs`, then
  `π = min_j L` with `L = H Xs`), the rows of `G = kktG (kktZ Xs)` with the column `h` (the test
  `Xs ≤ L − π` decides `kktZ`), `h' = E h + 1`, `Δ = 1`, `q = 2^p`;
* Phase M (`mLoop`, `KmoStep*.lean`, `KmoArg.lean`): `d` steps `moveStep`;
* Phase O (`oProg`, `KmoOut.lean`): `|Δ|` and the weights `(sign Δ · Aj h_T)⁺`;
* the bit lengths (`KmoBits.lean`) and the step and space bounds (`KmoCost.lean`).
-/

@[expose] public section

namespace STACS2027.Runtimes.QPRam

open STACS2027 STACS2027.RAM STACS2027.Runtimes.Arith STACS2027.Runtimes.ConvexQP

/-- **Phases K, M, O on the RAM.** -/
def kmoProg : Stmt := .seq Kmo.kProg (.seq Kmo.mLoop Kmo.oProg)

theorem kProg_writes : writes Kmo.kProg = false := by decide +kernel

theorem mLoop_writes : writes Kmo.mLoop = false := by decide +kernel

/-- The registers written by Phases K, M, O: `rT`, `rFREE`, the arithmetic library's block
`400–449` and the scratch block `500–539` of Phases K, M, O. -/
theorem kmoProg_wregs : ∀ r ∈ wregs kmoProg, r = rT ∨ r = rFREE ∨ (400 ≤ r ∧ r < 450) ∨
    (500 ≤ r ∧ r < 540) := by decide +kernel

/-- **Phases K, M, O on the RAM within polynomial space** reproduce `Inst.exactFrom`
and write its result in `O((t k + 2)^10)` steps, by a run below any bound
`S ≥ reg rFREE + kmoC · (t k + 2)^10`; the free address ends at the end of the layout. -/
theorem phaseKMO_ramB : PhaseKMORamB kmoProg := by
  refine ⟨Kmo.kmoC, fun I hI ht Xs hX hgap S c₀ hmid hS => ?_⟩
  obtain ⟨hq, hH, hbh, hXs, hbx, hZ, hout⟩ := hmid
  have hsp := Kmo.kmoSpace_le ht hI.1 (c₀.reg rFREE)
  have hK := Kmo.kScratch_le I
  have hLS : (Kmo.lay I (c₀.reg rFREE)).fe + 16 * Kmo.bitM I + 6 ≤ S := by omega
  have h1 := Kmo.kProg_spec (S := S) hI (c₀.reg rFREE) (c₀.reg qBH) (c₀.reg qBX) c₀.mem hH hXs
    hbh hbx hZ (prec I.t I.k + 1) (fun j _ => Kmo.xs_bits_kmo hX j) (by omega)
  have h2 := Kmo.mLoop_spec hI ht hX hgap (c₀.reg rFREE) (Kmo.bitM I)
    (fun r hr s hs => Kmo.stepBits_of hI ht hX hgap hr s hs) hLS
  have h3 := (Kmo.oProg_spec (S := S) hI hX hgap (c₀.reg rFREE) (by omega)).frameReg
    (F := fun c => c.reg rFREE = (Kmo.lay I (c₀.reg rFREE)).fe) (by indep)
  have hF : ∀ {st : Stmt}, writes st = false → ∀ c c', Frame st c c' → c.out = [] →
      c'.out = [] := fun hw c c' hfr h => (hfr.out hw).trans h
  have h1' := h1.frame (F := fun c => c.out = []) (hF kProg_writes)
  have h2' := h2.frame (F := fun c => c.out = []) (hF mLoop_writes)
  exact ((h1'.pre fun c hc => by subst hc; exact ⟨⟨hq, rfl, rfl, rfl, rfl⟩, hout⟩).seq
    (h2'.seq (h3.pre fun c ⟨⟨hM, _, _⟩, ho⟩ => ⟨⟨hM, ho⟩, by
      obtain ⟨_, _, _, hg, _⟩ := hM
      exact hg.free⟩))).mono (fun _ h => h) (fun c ⟨ho, hfe⟩ => ⟨ho, by omega⟩)
    (Kmo.kmo_total_le ht hI.1)

end STACS2027.Runtimes.QPRam

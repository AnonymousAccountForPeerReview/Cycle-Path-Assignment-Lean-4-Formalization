module

public import Outerplanar.RAM.R3Prog
import Mathlib.Tactic

/-!
# Phase R3 (blocks): the main triple

`r3_spec`: from an `R2Post g` configuration `c₀` with first free address `F`, the program
`r3` halts within `C3 * (g.length + 1)` steps (`C3 = 100`), accessing only the addresses below
any `S ≥ endL g F` (`endL_le`: `≤ F + 8 (m + 1)`), in a configuration satisfying `R3Post g`
whose first free address is `endL g F`:

* the blocks `blocksOf g`, concatenated, as two arrays of edge ends `BU` (`gBU`) and `BV`
  (`gBV`) (bucket `h` holds the edges of key `h`, in the order of `idEdges g`), and their start
  offsets `blockStarts g` at `gBST` (`N + 1` cells, the last one is `|E|`), all freshly
  allocated at the old `rFREE`;
* everything of `GraphBase g` (the registers below `gR2` other than `rT`, `rFREE` are not
  written, `r3_wregs`; the memory below the initial `rFREE` is unchanged; in particular all
  of `R2Post g` other than the registers `rT`, `rFREE` survives);

with the output unchanged (`r3_writes`) and only the registers `rT`, `rFREE`, `40–49` and the
scratch registers written (`r3_wregs`).

Time: `17` (allocation) `+ 26 |E| + 3` (counting) `+ 11 N + 4` (prefix sums) `+ 33 |E| + 3`
(filling), with `N ≤ 2m`, `|E| ≤ m`.
-/

@[expose] public section

namespace STACS2027.RAM.R3

open STACS2027.Algo

variable {S : ℕ}

/-- The constant of the running time of R3. -/
def C3 : ℕ := 100

/-- The registers written by `r3`: the macro temporary, `rFREE`, the R3 block `40–49`, and
scratch registers. -/
theorem r3_wregs : ∀ r ∈ wregs r3, r = rT ∨ r = rFREE ∨ (gR3 ≤ r ∧ r < gR4) ∨ rS ≤ r := by
  have h₁ : ∀ r ∈ wregs r3Alloc, r = rT ∨ r = rFREE ∨ (gR3 ≤ r ∧ r < gR4) ∨ rS ≤ r := by decide
  have h₂ : ∀ r ∈ wregs stepCnt, r = rT ∨ r = rFREE ∨ (gR3 ≤ r ∧ r < gR4) ∨ rS ≤ r := by decide
  have h₃ : ∀ r ∈ wregs stepPre, r = rT ∨ r = rFREE ∨ (gR3 ≤ r ∧ r < gR4) ∨ rS ≤ r := by decide
  have h₄ : ∀ r ∈ wregs stepFill, r = rT ∨ r = rFREE ∨ (gR3 ≤ r ∧ r < gR4) ∨ rS ≤ r := by
    decide
  intro r hr
  simp only [r3, wregs_seq, List.mem_append] at hr
  rcases hr with h | h | h | h
  exacts [h₁ r h, h₂ r h, h₃ r h, h₄ r h]

/-- `r3` does not write output. -/
theorem r3_writes : writes r3 = false := by decide

/-- R3 without the frame facts. -/
theorem r3_core (g : Graph) (c₀ : Config) (hR : R2Post g c₀) (hS : endL g (c₀.reg rFREE) ≤ S) :
    HTB S r3 (fun c => c = c₀) (FillInv g c₀ (idEdges g).length)
      (17 + (((idEdges g).length * 26 + 3) + ((1 + (numV g * 11 + 3)) +
        ((idEdges g).length * 33 + 3)))) := by
  have h₃ := (stepPre_spec g c₀ hR hS).post (Q' := fun c => FillInv g c₀ 0 c ∧
      c.reg gNE = (idEdges g).length) fun c ⟨⟨hG, _, hM⟩, _, _⟩ => by
    have hL := layout_eqs g (c₀.reg rFREE)
    refine ⟨⟨hG, hM.same, hM.bst.congr_fun fun i hi => by simp [show i ≤ numV g by omega], ?_,
      fun v _ => by simp [bk_zero], fun v _ => by simp [bk_zero], fun v _ => by simp [bk_zero],
      hM.zero.mono (by omega)⟩, hG.ne⟩
    simpa [bk_zero] using hM.zero.tab (b := bFIL g (c₀.reg rFREE)) le_rfl (numV g)
  have h₄ := (stepFill_spec g c₀ hR hS).post (Q' := FillInv g c₀ (idEdges g).length)
    fun c h => h.1
  exact (r3Alloc_spec g c₀ hR).seq ((stepCnt_spec g c₀ hR hS).seq (h₃.seq h₄))

/-- The registers below `gR2` other than `rT`, `rFREE` are not written by `r3`. -/
theorem r3_reg {r : ℕ} (hr : r < gR2) (hT : r ≠ rT) (hF : r ≠ rFREE) : r ∉ wregs r3 := by
  intro hm
  rcases r3_wregs r hm with h | h | ⟨h, _⟩ | h
  · exact hT h
  · exact hF h
  · exact absurd hr (Nat.not_lt.mpr (le_trans (by decide) h))
  · exact absurd hr (Nat.not_lt.mpr (le_trans (by decide) h))

/-- The final state of the passes satisfies the interface `R3Post`. -/
theorem post_of_fill {g : Graph} {c₀ c : Config} (hR : R2Post g c₀)
    (hF : FillInv g c₀ (idEdges g).length c) (hfr : Frame r3 c₀ c) :
    R3Post g c ∧ c.out = c₀.out ∧ SameOn (· < c₀.reg rFREE) c₀.mem c.mem ∧
      c₀.reg rFREE ≤ c.reg rFREE := by
  obtain ⟨hG, hM⟩ := hF
  have hL := layout_eqs g (c₀.reg rFREE)
  have hfree := hG.free
  have hlen := length_flatten g
  refine ⟨⟨R2.base_transfer hR.r1.base (fun r hr hT hF => hfr.reg r (r3_reg hr hT hF)) hM.same
      (by omega) (by rw [hfree]; exact hM.zero), ?_, ?_, ?_, ?_⟩,
    hfr.out r3_writes, hM.same, by omega⟩
  · rw [hG.bst, blockStarts_eq]; exact hM.bst.toArr
  · rw [hG.bu, flatten_fst]
    exact arr_flatMap_parts _ _ fun h hh => by simpa only [bs, List.length_map] using hM.bu h hh
  · rw [hG.bv, flatten_snd]
    exact arr_flatMap_parts _ _ fun h hh => by simpa only [bs, List.length_map] using hM.bv h hh
  · rw [hG.bst, hG.bu, hG.bv, hfree, hlen]; omega

/-- **Phase R3 within linear space**: from an `R2Post g` configuration `c₀` with first free
address `F`, the program `r3` buckets the id edges by the head of their lower end (a stable
counting sort), storing the blocks `blocksOf g` concatenated and their starts `blockStarts g` in
fresh arrays, within `C3 * (g.length + 1)` steps, accessing only the addresses below any
`S ≥ endL g F` (`endL_le`), without output, allocating fresh memory only; its first free address
is then `endL g F`. -/
theorem r3_spec (g : Graph) (c₀ : Config) (hS : endL g (c₀.reg rFREE) ≤ S) :
    HTB S r3 (fun c => R2Post g c ∧ c = c₀)
      (fun c => R3Post g c ∧ c.out = c₀.out ∧ SameOn (· < c₀.reg rFREE) c₀.mem c.mem ∧
        c₀.reg rFREE ≤ c.reg rFREE ∧ c.reg rFREE = endL g (c₀.reg rFREE))
      (C3 * (g.length + 1)) := by
  intro c ⟨hR, hc⟩
  subst hc
  obtain ⟨c', t, he, ⟨hF, hfr⟩, ht⟩ := (r3_core g c hR hS).withFrame c c ⟨rfl, rfl⟩
  obtain ⟨hP, hout, hsame, hle⟩ := post_of_fill hR hF hfr
  refine ⟨c', t, he, ⟨hP, hout, hsame, hle, hF.1.free⟩, ?_⟩
  have h1 := R0.numV_le g
  have h2 := R0.length_idEdges_le g
  simp only [C3]
  omega

end STACS2027.RAM.R3

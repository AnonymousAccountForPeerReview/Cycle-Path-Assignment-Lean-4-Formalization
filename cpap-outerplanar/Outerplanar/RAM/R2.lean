module

public import Outerplanar.RAM.R2Prog
import Mathlib.Tactic

/-!
# Phase R2 (low points and heads): the head pass and the main triple

`r2_spec`: from an `R1Post g` configuration `c₀` with first free address `F`, the program
`r2` halts within `C2 * (g.length + 1)` steps (`C2 = 240`), accessing only the addresses below
any `S ≥ endL g F = F + 2N` (`endL_le`: `≤ F + 4 (m + 1)`), in a configuration satisfying
`R2Post g` whose first free address is `endL g F`:

* the low points `lowsOf g` in the table `LOW` (`gLOW`, `N` cells) and the heads `headsOf g`
  in the table `HEAD` (`gHEAD`, `N` cells), both freshly allocated at the old `rFREE`;
* everything of `R1Post g` (the registers below `gR2` other than `rT`, `rFREE` are not
  written, `r2_wregs`; the memory below the initial `rFREE` is unchanged);

with the output unchanged (`r2_writes`) and only the registers `rT`, `rFREE`, `30–39` and the
scratch registers written (`r2_wregs`).

Time: `6` (allocation) `+ 90 |E| + 33 N + 3` (low points: each vertex `45 |nb v| + 29`
steps, `sum_deg`) `+ 38 N + 3` (heads), with `N ≤ 2m`, `|E| ≤ m`.
-/

@[expose] public section

namespace STACS2027.RAM.R2

open STACS2027.Algo

variable {S : ℕ}

/-! ### Step 3: the heads -/

/-- The memory during the head pass, with the heads `hf`. -/
structure HeadMem (g : Graph) (c₀ : Config) (hf : ℕ → ℕ) (m : ℕ → ℕ) : Prop where
  same : SameOn (· < c₀.reg rFREE) c₀.mem m
  low : Tab m (c₀.reg rFREE) (numV g) (lowsOf g)
  head : Tab m (c₀.reg rFREE + numV g) (numV g) hf
  zero : ZeroFrom m (c₀.reg rFREE + numV g + numV g)

/-- Storing a head. -/
theorem HeadMem.upd {g : Graph} {c₀ : Config} {hf : ℕ → ℕ} {m : ℕ → ℕ} (h : HeadMem g c₀ hf m)
    {v : ℕ} (hv : v < numV g) (x : ℕ) :
    HeadMem g c₀ (Function.update hf v x) (RAM.upd m (c₀.reg rFREE + numV g + v) x) :=
  ⟨h.same.upd_of_ge (by omega) _, h.low.upd_of_disjoint (by omega), h.head.upd rfl,
    h.zero.upd (by omega)⟩

/-- The invariant of the head pass after `i` vertices. -/
def HeadInv (g : Graph) (c₀ : Config) (i : ℕ) (c : Config) : Prop :=
  Glob g c₀ c ∧ HeadMem g c₀ (headF g (lowsOf g) i) c.mem

/-- The effect of one round of the head pass on the memory. -/
theorem headBody_mem {c : Config} {v p : ℕ} (hv : c.mem (c.reg gORD + c.reg rI) = v)
    (hp : c.mem (c.reg gPAR + v) = p) :
    (run headBody c).mem = upd c.mem (c.reg gHEAD + v)
      (if p = v then v else if c.mem (c.reg gPRE + p) ≤ c.mem (c.reg gLOW + v) then v
        else c.mem (c.reg gHEAD + p)) := by
  simp +decide only [headBody, headElse, run_seq', run_ld,
    run_ifEq (show rP ≠ rT by decide) (show rV ≠ rT by decide), run_ifLe,
    run_st (show rV ≠ rT by decide), run_st (show rX ≠ rT by decide), setReg_reg, setReg_mem,
    ↓reduceIte, hv, hp]
  by_cases h1 : p = v
  · simp only [h1, ↓reduceIte, setReg_mem, setMem_mem_upd]
  · by_cases h2 : c.mem (c.reg gPRE + p) ≤ c.mem (c.reg gLOW + v)
    · simp +decide only [h1, h2, ↓reduceIte, setReg_mem, setMem_mem_upd]
    · simp +decide only [h1, h2, ↓reduceIte, setReg_mem, setMem_mem_upd]

theorem headBody_spec (g : Graph) (c₀ : Config) (hR : R1Post g c₀)
    (hS : endL g (c₀.reg rFREE) ≤ S) (i : ℕ) (hi : i < numV g) :
    HTB S headBody (fun c => HeadInv g c₀ i c ∧ c.reg rI = i ∧ c.reg gN = numV g)
      (fun c => HeadInv g c₀ (i + 1) c ∧ c.reg rI = i ∧ c.reg gN = numV g) 34 :=
  HTB.of_HT_addrOK (by decide) (fun c ⟨⟨hG, hM⟩, hI, _⟩ => by
    have hv : (dfsOf g).ord.getD i 0 < numV g := ord_getD_lt hi
    have hp : (dfsOf g).par ((dfsOf g).ord.getD i 0) < numV g := par_lt hv
    have hord : c.mem (c₀.reg gORD + i) = (dfsOf g).ord.getD i 0 := rd_ord hR hM.same hi
    have hpar : c.mem (c₀.reg gPAR + (dfsOf g).ord.getD i 0) =
        (dfsOf g).par ((dfsOf g).ord.getD i 0) := rd_par hR hM.same hv
    have := fits hR hS
    addr_ok [headBody, headElse, hG.ord, hG.par, hG.pre, hG.low, hG.head, hI, hord, hpar]) <| by
  refine HT.run_le (by decide) (by decide) fun c ⟨⟨hG, hM⟩, hI, hn⟩ => ?_
  have hv : (dfsOf g).ord.getD i 0 < numV g := ord_getD_lt hi
  have hp : (dfsOf g).par ((dfsOf g).ord.getD i 0) < numV g := par_lt hv
  have hord : c.mem (c.reg gORD + c.reg rI) = (dfsOf g).ord.getD i 0 := by
    rw [hG.ord, hI]; exact rd_ord hR hM.same hi
  have hpar : c.mem (c.reg gPAR + (dfsOf g).ord.getD i 0) =
      (dfsOf g).par ((dfsOf g).ord.getD i 0) := by
    rw [hG.par]; exact rd_par hR hM.same hv
  have hpre : c.mem (c.reg gPRE + (dfsOf g).par ((dfsOf g).ord.getD i 0)) =
      (dfsOf g).pre ((dfsOf g).par ((dfsOf g).ord.getD i 0)) := by
    rw [hG.pre]; exact rd_pre hR hM.same hp
  have hlow : c.mem (c.reg gLOW + (dfsOf g).ord.getD i 0) = lowsOf g ((dfsOf g).ord.getD i 0) := by
    rw [hG.low]; exact hM.low.get hv
  have hhd : c.mem (c.reg gHEAD + (dfsOf g).par ((dfsOf g).ord.getD i 0)) =
      headF g (lowsOf g) i ((dfsOf g).par ((dfsOf g).ord.getD i 0)) := by
    rw [hG.head]; exact hM.head.get hp
  have hmem := headBody_mem hord hpar
  rw [hpre, hlow, hhd, hG.head] at hmem
  refine ⟨⟨(Glob.regIndep g c₀).run_of_sub (by decide) (by decide) hG, ?_⟩, ?_, ?_⟩
  · rw [hmem, headF_succ g _ hi]
    exact hM.upd hv _
  · rw [run_reg_of_not_mem (s := headBody) (r := rI) (by decide) (by decide) c, hI]
  · rw [run_reg_of_not_mem (s := headBody) (r := gN) (by decide) (by decide) c, hn]

/-- **Step 3**: the heads, in `38 N + 3` steps. -/
theorem stepHead_spec (g : Graph) (c₀ : Config) (hR : R1Post g c₀)
    (hS : endL g (c₀.reg rFREE) ≤ S) :
    HTB S stepHead (fun c => HeadInv g c₀ 0 c ∧ c.reg gN = numV g)
      (fun c => HeadInv g c₀ (numV g) c ∧ c.reg rI = numV g ∧ c.reg gN = numV g)
      (numV g * 38 + 3) :=
  HTB.forUpC (i := rI) (n := gN) (N := numV g) (body := headBody) (HeadInv g c₀) 34
    (by decide) (by decide) (by decide) (fun j => by indep [HeadInv, glob_iff])
    (fun j hj => headBody_spec g c₀ hR hS j hj)

/-! ### The phase -/

/-- The constant of the running time of R2. -/
def C2 : ℕ := 240

/-- The registers written by `r2`: the macro temporary, `rFREE`, the R2 block `30–39`, and
scratch registers. -/
theorem r2_wregs : ∀ r ∈ wregs r2, r = rT ∨ r = rFREE ∨ (gR2 ≤ r ∧ r < gR3) ∨ rS ≤ r := by
  have h₁ : ∀ r ∈ wregs r2Alloc, r = rT ∨ r = rFREE ∨ (gR2 ≤ r ∧ r < gR3) ∨ rS ≤ r := by decide
  have h₂ : ∀ r ∈ wregs stepLow, r = rT ∨ r = rFREE ∨ (gR2 ≤ r ∧ r < gR3) ∨ rS ≤ r := by decide
  have h₃ : ∀ r ∈ wregs stepHead, r = rT ∨ r = rFREE ∨ (gR2 ≤ r ∧ r < gR3) ∨ rS ≤ r := by
    decide
  intro r hr
  simp only [r2, wregs_seq, List.mem_append] at hr
  rcases hr with h | h | h
  exacts [h₁ r h, h₂ r h, h₃ r h]

/-- `r2` does not write output. -/
theorem r2_writes : writes r2 = false := by decide

/-- R2 without the frame facts. -/
theorem r2_core (g : Graph) (c₀ : Config) (hR : R1Post g c₀) (hS : endL g (c₀.reg rFREE) ≤ S) :
    HTB S r2 (fun c => c = c₀) (HeadInv g c₀ (numV g))
      (6 + ((90 * (idEdges g).length + 33 * numV g + 3) + (numV g * 38 + 3))) := by
  have h₂ := (stepLow_spec g c₀ hR hS).post (Q' := fun c => HeadInv g c₀ 0 c ∧ c.reg gN = numV g)
    fun c ⟨⟨hG, hM⟩, _, hn⟩ => by
      refine ⟨⟨hG, hM.same, by rw [← lowF_full]; exact hM.low, ?_, hM.zero.mono (by omega)⟩, hn⟩
      rw [headF_zero]
      exact hM.zero.tab le_rfl _
  have h₃ := (stepHead_spec g c₀ hR hS).post (Q' := HeadInv g c₀ (numV g)) fun c h => h.1
  exact (r2Alloc_spec g c₀ hR).seq (h₂.seq h₃)

/-- The registers below `gR2` other than `rT`, `rFREE` are not written by `r2`. -/
theorem r2_reg {r : ℕ} (hr : r < gR2) (hT : r ≠ rT) (hF : r ≠ rFREE) : r ∉ wregs r2 := by
  intro hm
  rcases r2_wregs r hm with h | h | ⟨h, _⟩ | h
  · exact hT h
  · exact hF h
  · exact absurd hr (Nat.not_lt.mpr h)
  · exact absurd hr (Nat.not_lt.mpr (le_trans (by decide) h))

/-- The final state of the passes satisfies the interface `R2Post`. -/
theorem post_of_headInv {g : Graph} {c₀ c : Config} (hR : R1Post g c₀)
    (hH : HeadInv g c₀ (numV g) c) (hfr : Frame r2 c₀ c) :
    R2Post g c ∧ c.out = c₀.out ∧ SameOn (· < c₀.reg rFREE) c₀.mem c.mem ∧
      c₀.reg rFREE ≤ c.reg rFREE := by
  obtain ⟨hG, hM⟩ := hH
  have hfree := hG.free
  refine ⟨⟨r1_transfer hR (fun r hr hT hF => hfr.reg r (r2_reg hr hT hF)) hM.same
      (by omega) (by rw [hfree]; exact hM.zero), ?_, ?_, ?_⟩,
    hfr.out r2_writes, hM.same, by omega⟩
  · rw [hG.low]; exact hM.low
  · rw [hG.head, ← headF_full]; exact hM.head
  · rw [hG.low, hG.head, hfree]; omega

/-- **Phase R2 within linear space**: from an `R1Post g` configuration `c₀` with first free
address `F`, the program `r2` computes the low points `lowsOf g` and the heads `headsOf g` of
the search into fresh tables, within `C2 * (g.length + 1)` steps, accessing only the addresses
below any `S ≥ endL g F` (`endL_le`), without output, allocating fresh memory only; its first free
address is then `endL g F`. -/
theorem r2_spec (g : Graph) (c₀ : Config) (hS : endL g (c₀.reg rFREE) ≤ S) :
    HTB S r2 (fun c => R1Post g c ∧ c = c₀)
      (fun c => R2Post g c ∧ c.out = c₀.out ∧ SameOn (· < c₀.reg rFREE) c₀.mem c.mem ∧
        c₀.reg rFREE ≤ c.reg rFREE ∧ c.reg rFREE = endL g (c₀.reg rFREE))
      (C2 * (g.length + 1)) := by
  intro c ⟨hR, hc⟩
  subst hc
  obtain ⟨c', t, he, ⟨hH, hfr⟩, ht⟩ := (r2_core g c hR hS).withFrame c c ⟨rfl, rfl⟩
  obtain ⟨hP, hout, hsame, hle⟩ := post_of_headInv hR hH hfr
  refine ⟨c', t, he, ⟨hP, hout, hsame, hle, hH.1.free⟩, ?_⟩
  have h1 := R0.numV_le g
  have h2 := R0.length_idEdges_le g
  simp only [C2]
  omega

end STACS2027.RAM.R2

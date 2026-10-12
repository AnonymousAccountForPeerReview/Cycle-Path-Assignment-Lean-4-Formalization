module

public import Outerplanar.RAM.R1Dfs
import Mathlib.Tactic

/-!
# Phase R1 (neighbour lists and depth-first search): the main triple

`r1_spec`: from a `GraphBase g` configuration `c₀` with first free address `F`, the program
`r1` halts within `C1 * (g.length + 1)` steps (`C1 = 600`), accessing only the addresses below
any `S ≥ endL g F` (`endL_le`: `endL g F ≤ F + 18 (m + 1)`), in a configuration satisfying
`R1Post g` whose first free address is `endL g F`:

* the CSR offsets `csrOff (idEdges g) N` at `gOFF` and neighbour entries `csrAdj (idEdges g) N`
  at `gADJ` (the neighbour lists `nbOf (idEdges g) v`, in the order of the edges);
* the preorder numbers and parents of `dfsOf g` (tables of `N` cells at `gPRE`, `gPAR`) and
  its preorder list at `gORD`;
* everything of `GraphBase g` (the registers `rZERO rONE gM gN gNE gLB gEU gEV` are not
  written; the memory below the initial `rFREE` is unchanged), all regions below `rFREE`, and
  `ZeroFrom c.mem (c.reg rFREE)`;

with the output unchanged (`r1_writes`) and only the registers `rT`, `rFREE`, `20–29` and the
scratch registers written (`r1_wregs`).

Time: `O(|E| + N)` for the CSR passes, and at most `DFS.mu (init) = 3 N + 2 |E|` rounds of the
search loop, each of at most `60` steps; with `N ≤ 2m`, `|E| ≤ m`.
-/

@[expose] public section

namespace STACS2027.RAM.R1

open STACS2027.Algo

variable {S : ℕ}

/-- The constant of the running time of R1. -/
def C1 : ℕ := 600

/-- The registers written by `r1`: the macro temporary, `rFREE`, the R1 block `20–29`, and
scratch registers. -/
theorem r1_wregs : ∀ r ∈ wregs r1, r = rT ∨ r = rFREE ∨ (gR1 ≤ r ∧ r < gR2) ∨ rS ≤ r := by
  have h₁ : ∀ r ∈ wregs stepCsr, r = rT ∨ r = rFREE ∨ (gR1 ≤ r ∧ r < gR2) ∨ rS ≤ r := by decide
  have h₂ : ∀ r ∈ wregs stepDfs, r = rT ∨ r = rFREE ∨ (gR1 ≤ r ∧ r < gR2) ∨ rS ≤ r := by decide
  intro r hr
  rw [r1, wregs_seq] at hr
  rcases List.mem_append.mp hr with h | h
  exacts [h₁ r h, h₂ r h]

/-- `r1` does not write output. -/
theorem r1_writes : writes r1 = false := by decide

/-- R1 without the frame facts. -/
theorem r1_core (g : Graph) (c₀ : Config) (hB : GraphBase g c₀) (hS : endL g (c₀.reg rFREE) ≤ S) :
    HTB S r1 (fun c => c = c₀) (DfsRep g c₀ (dfsOf g))
      ((34 + ((idEdges g).length * 20 + 3 + (1 + (numV g * 11 + 3) +
        ((idEdges g).length * 32 + 3)))) +
        (3 + (2 + ((3 * numV g + 2 * (idEdges g).length) * (60 + 1) + 1)))) :=
  (stepCsr_spec g c₀ hB hS).seq (stepDfs_spec g c₀ hS)

/-- The final state of the search satisfies the interface `R1Post`. -/
theorem post_of_dfsRep {g : Graph} {c₀ c : Config} (hB : GraphBase g c₀)
    (hR : DfsRep g c₀ (dfsOf g) c) (hfr : Frame r1 c₀ c) :
    R1Post g c ∧ c.out = c₀.out ∧ SameOn (· < c₀.reg rFREE) c₀.mem c.mem ∧
      c₀.reg rFREE ≤ c.reg rFREE := by
  have hG := hR.glob
  have hL := layout_eqs g (c₀.reg rFREE)
  have hS := hR.mem.csr.same
  have hps := idEdges_ps g
  have hord := length_ord_le (DFS.final_inv (ok_idEdges g)) (DFS.final_ordInv (vs := List.range (numV g)))
  have hnv : numV g = (labels g).length := rfl
  have hb := hB.below
  have hfree : c.reg rFREE = endL g (c₀.reg rFREE) := hG.free
  have hLB : c.reg gLB = c₀.reg gLB := hfr.reg gLB (by decide)
  refine ⟨⟨⟨(hfr.reg rZERO (by decide)).trans hB.zero, (hfr.reg rONE (by decide)).trans hB.one,
    (hfr.reg gM (by decide)).trans hB.m, (hfr.reg gN (by decide)).trans hB.n,
    (hfr.reg gNE (by decide)).trans hB.ne, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    hfr.out r1_writes, hS, by rw [hfree]; omega⟩
  · rw [hLB]; exact hB.lb.of_below hS (by omega)
  · rw [hG.eu]; exact hB.eu.of_below hS (by simpa using hb.2.1)
  · rw [hG.ev]; exact hB.ev.of_below hS (by simpa using hb.2.2)
  · rw [hfree]; exact hR.mem.zero
  · rw [hLB, hG.eu, hG.ev, hfree]; omega
  · rw [hG.off, csrOff_eq]; exact hR.mem.csr.off.toArr
  · rw [hG.adj]; exact arr_csrAdj hR.mem.csr.adj
  · rw [hG.pre]; exact hR.mem.pre
  · rw [hG.par]; exact hR.mem.par
  · rw [hG.ord]; exact hR.mem.ord
  · rw [hG.off, hG.adj, hG.pre, hG.par, hG.ord, hfree, length_csrAdj, hps]
    unfold dfsOf
    omega

/-- **Phase R1 within linear space**: from a `GraphBase g` configuration `c₀` with first free
address `F = c₀.reg rFREE`, the program `r1` halts within `C1 * (g.length + 1)` steps,
accessing only the addresses below any `S ≥ endL g F` (`endL g F ≤ F + 18 (m + 1)`), in a
configuration satisfying `R1Post g` whose first free address is `endL g F`. -/
theorem r1_spec (g : Graph) (c₀ : Config) (hS : endL g (c₀.reg rFREE) ≤ S) :
    HTB S r1 (fun c => GraphBase g c ∧ c = c₀)
      (fun c => R1Post g c ∧ c.out = c₀.out ∧ SameOn (· < c₀.reg rFREE) c₀.mem c.mem ∧
        c₀.reg rFREE ≤ c.reg rFREE ∧ c.reg rFREE = endL g (c₀.reg rFREE))
      (C1 * (g.length + 1)) := by
  intro c ⟨hB, hc⟩
  subst hc
  obtain ⟨c', t, he, ⟨hR, hfr⟩, ht⟩ := (r1_core g c hB hS).withFrame c c ⟨rfl, rfl⟩
  obtain ⟨hP, hout, hsame, hle⟩ := post_of_dfsRep hB hR hfr
  refine ⟨c', t, he, ⟨hP, hout, hsame, hle, hR.glob.free⟩, ?_⟩
  have h1 := R0.numV_le g
  have h2 := R0.length_idEdges_le g
  simp only [C1]
  omega

end STACS2027.RAM.R1

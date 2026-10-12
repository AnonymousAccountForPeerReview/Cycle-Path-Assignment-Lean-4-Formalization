module

public import Outerplanar.RAM.MainLoop
public import Outerplanar.RAM.Block
public import Outerplanar.RAM.EarMain
public import Outerplanar.RAM.PolySolver
public import Outerplanar.RAM.Poly2
public import Outerplanar.RAM.Poly3
import Mathlib.Tactic

/-!
# The machine of Theorem 21: the whole program

`k23Prog k` runs the phases

* R0 (`R0.r0`, parsing: labels, ids, id edges), R1 (`R1.r1`, neighbour lists and depth-first
  search), R2 (`R2.r2`, low points and heads), R3 (`R3.r3`, the blocks bucketed by head);
* the block loop (`blockLoop`, `MainLoop.lean`) with the block solver `solverProg k`
  (`Block.blockProg`: copies, vertices, local ids, then nothing / the `K₄` patterns / the
  polygon branch with the ear elimination `EarR.earProg` and the polygon solver
  `PolySolver.polySolver k (P2.poly2 k) (P3.poly3 k)`).

`k23Prog_spec`: given Lemma 19, for `k ≥ 3` and a `K_{2,3}`-minor-free graph
`g`, started on `initial (graphInput g)` the program halts within `Ck23 k * (m + 1)` steps
(`m = |g|`, the number of input entries) with output exactly `Algo.solve k g`, touching only the
addresses below `Ck23 k * (labelBound g + m + 1)` (an `HTB` triple). The phase triples chain
through the
interfaces `R0Post → GraphBase → R1Post → R2Post → R3Post` (`Iface.lean`), each phase's layout
end bounding the next one's free address (`R0.endR0_le`, `R1.endL_le`, `R2.endL_le`,
`R3.endL_le`, `loopEnd_le`); the block solver satisfies `BlockSpec` (`solverProg_spec`, from
`Block.blockProg_spec`, `EarR.earProg_spec` and the linear-space specification of the polygon
solver `polyProg_spec : PolySpecB`) with the footprint `solverProg_wregs`,
and every block is `BlockGood` (`blockGood_blocksOf`). `k23Prog_computes` restates it with
`ComputesIn` (time `Ck23 k * (m + 1)`, space `Ck23 k * (labelBound g + m + 1)`).
-/

@[expose] public section

namespace STACS2027.RAM.Main

open STACS2027.Algo

/-! ### The program -/

/-- The polygon solver of the machine: phases P1–P4. -/
def polyProg (k : ℕ) : Stmt := PolySolver.polySolver k (P2.poly2 k) (P3.poly3 k)

/-- The block solver of the machine. -/
def solverProg (k : ℕ) : Stmt := Block.blockProg k EarR.earProg (polyProg k)

/-- **The program of Theorem 21** (for cycle length `k`): the phases R0–R3 and the block
loop. -/
def k23Prog (k : ℕ) : Stmt :=
  .seq R0.r0 (.seq R1.r1 (.seq R2.r2 (.seq R3.r3 (blockLoop (solverProg k)))))

/-- The constant of the polygon solver. -/
def CP (k : ℕ) : ℕ := P1.CP1 + P2.CP2 k + P3.CP3 k + P4.CP4 k

/-- The constant of the block solver. -/
def CBk (k : ℕ) : ℕ := Block.CB k EarR.CE (CP k)

/-- **The constant of the running time of the whole program.** -/
def Ck23 (k : ℕ) : ℕ := R0.C0 + R1.C1 + R2.C2 + R3.C3 + CL (CBk k)

/-! ### The solvers -/

/-- **The polygon solver runs in linear time and space** (`PolySpecB`, phases P1–P4). -/
theorem polyProg_spec {k : ℕ} (hk : 3 ≤ k) : PolySpecB k (polyProg k) (CP k) :=
  PolySolver.polySolver_specB hk
    (fun pg n omap hP hlt hnd => P2.poly2_specB hk pg n omap hP hlt hnd)
    (fun pg n omap hP hlt hnd => P3.poly3_specB hk pg n omap hP hlt hnd)

/-- The registers written by the polygon solver: `rT`, `rFREE`, registers `≥ gP0`. -/
theorem polyProg_wregs (k : ℕ) : ∀ r ∈ wregs (polyProg k), r = rT ∨ r = rFREE ∨ gP0 ≤ r :=
  PolySolver.polySolver_wregs (P2.poly2_wregs k) (P3.poly3_wregs k)

/-- The block solver satisfies `BlockSpec` (linear time and space). -/
theorem solverProg_spec {k : ℕ} (hk : 3 ≤ k) : BlockSpec k (solverProg k) (CBk k) :=
  Block.blockProg_spec hk EarR.earProg_spec EarR.earProg_wregs EarR.earProg_writes
    (polyProg_spec hk) (polyProg_wregs k)

/-- The registers written by the block solver: `rT`, `rFREE`, registers `≥ gVN`. -/
theorem solverProg_wregs (k : ℕ) : ∀ r ∈ wregs (solverProg k), r = rT ∨ r = rFREE ∨ gVN ≤ r :=
  Block.blockProg_wregs EarR.earProg_wregs (polyProg_wregs k)

/-! ### The whole program -/

/-- **The memory of the whole program**: the layout ends of the phases, chained from R0's
(`endR0 g ≤ 20 (L + m + 1)`; R1–R3 add at most `30 (m + 1)`, the block loop
`CL (CBk k) (m + 1)`), are within `Ck23 k * (labelBound g + |g| + 1)`. -/
theorem space_le (k : ℕ) (g : Graph) :
    loopEnd g (R3.endL g (R2.endL g (R1.endL g (R0.endR0 g)))) (CBk k) ≤
      Ck23 k * (labelBound g + g.length + 1) := by
  have h0 := R0.endR0_le g
  have h1 := R1.endL_le g (R0.endR0 g)
  have h2 := R2.endL_le g (R1.endL g (R0.endR0 g))
  have h3 := R3.endL_le g (R2.endL g (R1.endL g (R0.endR0 g)))
  have h4 := loopEnd_le g (R3.endL g (R2.endL g (R1.endL g (R0.endR0 g)))) (CBk k)
  have h5 : CL (CBk k) * (g.length + 1) ≤ CL (CBk k) * (labelBound g + g.length + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  have h6 : Ck23 k * (labelBound g + g.length + 1) =
      1240 * (labelBound g + g.length + 1) + CL (CBk k) * (labelBound g + g.length + 1) := by
    simp only [Ck23, R0.C0, R1.C1, R2.C2, R3.C3]; ring
  omega

/-- **The program of Theorem 21 computes `solve k g` in linear time and
space**: given Lemma 19, for `k ≥ 3` and every `K_{2,3}`-minor-free graph `g`,
from the initial configuration on `graphInput g` the program `k23Prog k` halts within
`Ck23 k * (|g| + 1)` steps with output `Algo.solve k g`, touching only the addresses below
`Ck23 k * (labelBound g + |g| + 1)`. -/
theorem k23Prog_spec (hL : TwoConnectedK23Structure) {k : ℕ} (hk : 3 ≤ k) {g : Graph} (hg : K23MinorFree g) :
    HTB (Ck23 k * (labelBound g + g.length + 1)) (k23Prog k)
      (fun c => c = initial (graphInput g)) (fun c => c.out = solve k g)
      (Ck23 k * (g.length + 1)) := by
  have hsp := space_le k g
  have l1 : R0.endR0 g ≤ R1.endL g (R0.endR0 g) := by
    have := R1.layout_eqs g (R0.endR0 g); omega
  have l2 : R1.endL g (R0.endR0 g) ≤ R2.endL g (R1.endL g (R0.endR0 g)) := by
    simp only [R2.endL]; omega
  have l3 : R2.endL g (R1.endL g (R0.endR0 g)) ≤
      R3.endL g (R2.endL g (R1.endL g (R0.endR0 g))) := by
    have := R3.layout_eqs g (R2.endL g (R1.endL g (R0.endR0 g))); omega
  have l4 : R3.endL g (R2.endL g (R1.endL g (R0.endR0 g))) ≤
      loopEnd g (R3.endL g (R2.endL g (R1.endL g (R0.endR0 g)))) (CBk k) := by
    simp only [loopEnd]; omega
  intro c hc
  obtain ⟨c₁, t₁, e₁, h₁, ht₁⟩ := R0.r0_spec (S := Ck23 k * (labelBound g + g.length + 1)) g
    (by omega) c hc
  have hf₁ : c₁.reg rFREE = R0.endR0 g := h₁.fin
  obtain ⟨c₂, t₂, e₂, ⟨h₂, ho₂, -, -, hf₂⟩, ht₂⟩ :=
    R1.r1_spec (S := Ck23 k * (labelBound g + g.length + 1)) g c₁ (by rw [hf₁]; omega) c₁
      ⟨h₁.base, rfl⟩
  rw [hf₁] at hf₂
  obtain ⟨c₃, t₃, e₃, ⟨h₃, ho₃, -, -, hf₃⟩, ht₃⟩ :=
    R2.r2_spec (S := Ck23 k * (labelBound g + g.length + 1)) g c₂ (by rw [hf₂]; omega) c₂
      ⟨h₂, rfl⟩
  rw [hf₂] at hf₃
  obtain ⟨c₄, t₄, e₄, ⟨h₄, ho₄, -, -, hf₄⟩, ht₄⟩ :=
    R3.r3_spec (S := Ck23 k * (labelBound g + g.length + 1)) g c₃ (by rw [hf₃]; omega) c₃
      ⟨h₃, rfl⟩
  rw [hf₃] at hf₄
  obtain ⟨c₅, t₅, e₅, ⟨ho₅, -⟩, ht₅⟩ := blockLoop_spec (S := Ck23 k * (labelBound g + g.length + 1))
    (solverProg_spec hk) (solverProg_wregs k) g c₄ (blockGood_blocksOf hL hg)
    (by rw [hf₄]; omega) c₄ ⟨h₄, rfl⟩
  refine ⟨c₅, t₁ + (t₂ + (t₃ + (t₄ + t₅))),
    ExecB.seq e₁ (ExecB.seq e₂ (ExecB.seq e₃ (ExecB.seq e₄ e₅))), ?_, ?_⟩
  · show c₅.out = solve k g
    rw [ho₅, ho₄, ho₃, ho₂, h₁.out, List.nil_append]
  · simp only [Ck23, Nat.add_mul]
    omega

/-- **The program of Theorem 21**, with `ComputesIn`: on the input
`graphInput g` of a `K_{2,3}`-minor-free graph `g` (given Lemma 19, and
`k ≥ 3`), `k23Prog k` outputs exactly `Algo.solve k g` within `Ck23 k * (|g| + 1)` steps and
the space `Ck23 k * (labelBound g + |g| + 1)`. -/
theorem k23Prog_computes (hL : TwoConnectedK23Structure) {k : ℕ} (hk : 3 ≤ k) {g : Graph}
    (hg : K23MinorFree g) :
    ∃ t, ComputesIn (k23Prog k) (graphInput g) (solve k g) t
        (Ck23 k * (labelBound g + g.length + 1)) ∧ t ≤ Ck23 k * (g.length + 1) := by
  obtain ⟨t, ht, hc⟩ := (k23Prog_spec hL hk hg).computesIn
  exact ⟨t, hc, ht⟩

end STACS2027.RAM.Main

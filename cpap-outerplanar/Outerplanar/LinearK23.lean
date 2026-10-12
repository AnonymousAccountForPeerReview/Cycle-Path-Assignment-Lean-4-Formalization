module

public import Outerplanar.RAM.Main
public import Outerplanar.Algo.SolveOptimal
public import Outerplanar.TwoConnectedK23Structure
public import Outerplanar.OuterplanarCharacterization

/-!
# Theorem 21 and Lemma 35: linear time and space on the RAM

The headline theorems of Section 8 and Appendix F. The machine is the unit-cost RAM of
Section 6 (`STACS2027.RAM`: registers and memory `ℕ → ℕ`, instructions `const add sub load store
write`, sequencing, a zero test and a `while ≠ 0` loop, no multiplication; every instruction and
every test is one step). A graph `g` (a list of `m = |g|` entries, each a pair of vertex labels)
is given to the machine as `RAM.graphInput g = m :: e₁.1 :: e₁.2 :: … :: eₘ.1 :: eₘ.2` (the
number of entries, then the endpoints of each entry), stored at the memory cells `0, 1, …` of
the initial configuration; `RAM.ComputesIn prog input out T space` says that `prog` halts on
`input` after exactly `T` steps with output `out`, by a run that reads and writes only the
memory addresses below `space` (the input included).

* `k23_linear_ram` (**Theorem 21**): for every `k ≥ 3` there is one program and one constant `C`
  such that, on every `K_{2,3}`-minor-free graph `g`, the program halts within `C (m + 1)` steps,
  using the memory addresses below `C (L + m + 1)` (`L = RAM.labelBound g`, one more than the
  largest vertex label: the vertex labels index a dictionary, which is never initialized, so
  the time does not depend on `L`; for the usual labels `0, …, n - 1`, `L = n ≤ 2m`), and
  outputs an optimal cycle-path assignment of `CPAP(g, k)` (`OptimalAssignmentOutput`): linear
  time and space.
* `outerplanar_linear_ram` (**Lemma 35**): the same for outerplanar graphs, in the sense of Lemma 19
  (`OuterplanarDrawing`: a planar drawing with every vertex on the outer face), which are
  `K_{2,3}`-minor-free (`outerplanarDrawing_iff_outerplanar`).
* `k23_linear_ram_solve`: the same program outputs exactly `Algo.solve k g`.

They use the second sentence of **Lemma 19** (ANONYMIZED, ANONYMIZED, ANONYMIZED, ANONYMIZED 2016: every
2-connected `K_{2,3}`-minor-free graph is a `K₄` or has a Hamiltonian cycle with respect to which
no two edges cross), which is proved here (`twoConnectedK23_structure`, `Outerplanar/TwoConnectedK23Structure.lean`); the
versions `…_of_structure` take it as a hypothesis.

The program is `RAM.Main.k23Prog k` (`Outerplanar/RAM/Main.lean`, with the constant
`RAM.Main.Ck23 k`); its output is `Algo.solve k g` (`RAM.Main.k23Prog_computes`),
which is optimal (`Algo.solve_optimal`, `Outerplanar/Algo/SolveOptimal.lean`). Every phase of the
program, the polygon solver included (`RAM.Main.polyProg_spec : RAM.PolySpecB …`), is proved in
linear time and space.
-/

@[expose] public section

namespace STACS2027

/-- **The machine outputs the algorithm's answer, in linear time and space**, from Lemma 19
(second sentence, `TwoConnectedK23Structure`) as a hypothesis: for `k ≥ 3` there are a RAM program and a
constant `C` such that on the input encoding `RAM.graphInput g` of every `K_{2,3}`-minor-free
graph `g` the program halts within `C * (|g| + 1)` steps, using the memory below
`C * (RAM.labelBound g + |g| + 1)`, with output exactly `Algo.solve k g` (which is optimal,
`Algo.solve_optimal`). -/
theorem k23_linear_ram_solve_of_structure (hL : TwoConnectedK23Structure) {k : ℕ} (hk : 3 ≤ k) :
    ∃ (prog : RAM.Stmt) (C : ℕ), ∀ g : Graph, K23MinorFree g →
      ∃ T : ℕ, RAM.ComputesIn prog (RAM.graphInput g) (Algo.solve k g) T
          (C * (RAM.labelBound g + g.length + 1)) ∧ T ≤ C * (g.length + 1) :=
  ⟨RAM.Main.k23Prog k, RAM.Main.Ck23 k, fun _ hg => RAM.Main.k23Prog_computes hL hk hg⟩

/-- **Theorem 21 (linear time and space on the unit-cost RAM)**, from Lemma 19 (second sentence,
`TwoConnectedK23Structure`) as a hypothesis: for every `k ≥ 3` there are a RAM program and a constant `C` such
that for every `K_{2,3}`-minor-free graph `g`, on the input `RAM.graphInput g` (the number `|g|`
of entries, then the endpoints of each entry) the program halts after `T ≤ C * (|g| + 1)` steps,
using the memory below `C * (RAM.labelBound g + |g| + 1)`, with an output `out` that writes an
optimal cycle-path assignment of `CPAP(g, k)`. -/
theorem k23_linear_ram_of_structure (hL : TwoConnectedK23Structure) {k : ℕ} (hk : 3 ≤ k) :
    ∃ (prog : RAM.Stmt) (C : ℕ), ∀ g : Graph, K23MinorFree g →
      ∃ (out : List ℕ) (T : ℕ), RAM.ComputesIn prog (RAM.graphInput g) out T
          (C * (RAM.labelBound g + g.length + 1)) ∧
        T ≤ C * (g.length + 1) ∧ OptimalAssignmentOutput g k out := by
  obtain ⟨prog, C, h⟩ := k23_linear_ram_solve_of_structure hL hk
  exact ⟨prog, C, fun g hg => by
    obtain ⟨T, hc, hT⟩ := h g hg
    exact ⟨_, T, hc, hT, Algo.solve_optimal hL hk hg⟩⟩

/-! ### Without Lemma 19 as a hypothesis (it is proved, `twoConnectedK23_structure`) -/

/-- **The output of the algorithm is optimal**: for every `k ≥ 3` and every
`K_{2,3}`-minor-free graph `g`, `Algo.solve k g` writes an optimal cycle-path assignment. -/
theorem solve_optimal {k : ℕ} (hk : 3 ≤ k) {g : Graph} (hg : K23MinorFree g) :
    OptimalAssignmentOutput g k (Algo.solve k g) :=
  Algo.solve_optimal twoConnectedK23_structure hk hg

/-- **The machine outputs the algorithm's answer, in linear time and space**: for `k ≥ 3` there
are a RAM program and a constant `C` such that on the input encoding `RAM.graphInput g` of every
`K_{2,3}`-minor-free graph `g` the program halts within `C * (|g| + 1)` steps, using the memory
below `C * (RAM.labelBound g + |g| + 1)`, with output exactly `Algo.solve k g`. -/
theorem k23_linear_ram_solve {k : ℕ} (hk : 3 ≤ k) :
    ∃ (prog : RAM.Stmt) (C : ℕ), ∀ g : Graph, K23MinorFree g →
      ∃ T : ℕ, RAM.ComputesIn prog (RAM.graphInput g) (Algo.solve k g) T
          (C * (RAM.labelBound g + g.length + 1)) ∧ T ≤ C * (g.length + 1) :=
  k23_linear_ram_solve_of_structure twoConnectedK23_structure hk

/-- **Theorem 21 (linear time and space on the unit-cost RAM)**: for every `k ≥ 3` there are a
RAM program and a constant `C` such that for every `K_{2,3}`-minor-free graph `g`, on the input
`RAM.graphInput g` (the number `|g|` of entries, then the endpoints of each entry) the program
halts after `T ≤ C * (|g| + 1)` steps, using the memory below `C * (RAM.labelBound g + |g| + 1)`,
with an output `out` that writes an optimal cycle-path assignment of `CPAP(g, k)`. -/
theorem k23_linear_ram {k : ℕ} (hk : 3 ≤ k) :
    ∃ (prog : RAM.Stmt) (C : ℕ), ∀ g : Graph, K23MinorFree g →
      ∃ (out : List ℕ) (T : ℕ), RAM.ComputesIn prog (RAM.graphInput g) out T
          (C * (RAM.labelBound g + g.length + 1)) ∧
        T ≤ C * (g.length + 1) ∧ OptimalAssignmentOutput g k out :=
  k23_linear_ram_of_structure twoConnectedK23_structure hk

/-- **Lemma 35 (outerplanar graphs, linear time and space on the unit-cost RAM)**: for every
`k ≥ 3` there are a RAM program and a constant `C` such that for every outerplanar graph `g`
(`OuterplanarDrawing g`: a planar drawing with every vertex on the outer face, the definition of
Lemma 19), on the input `RAM.graphInput g` the program halts after `T ≤ C * (|g| + 1)` steps,
using the memory below `C * (RAM.labelBound g + |g| + 1)`, with an output `out` that writes an
optimal cycle-path assignment of `CPAP(g, k)`. -/
theorem outerplanar_linear_ram {k : ℕ} (hk : 3 ≤ k) :
    ∃ (prog : RAM.Stmt) (C : ℕ), ∀ g : Graph, OuterplanarDrawing g →
      ∃ (out : List ℕ) (T : ℕ), RAM.ComputesIn prog (RAM.graphInput g) out T
          (C * (RAM.labelBound g + g.length + 1)) ∧
        T ≤ C * (g.length + 1) ∧ OptimalAssignmentOutput g k out := by
  obtain ⟨prog, C, h⟩ := k23_linear_ram hk
  exact ⟨prog, C, fun g hg => h g ((outerplanarDrawing_iff_outerplanar g).mp hg).2⟩

end STACS2027

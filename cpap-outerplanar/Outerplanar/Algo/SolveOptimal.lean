module

public import Outerplanar.Algo.SolveCorrect
public import Outerplanar.Algo.EarCorrect
public import Outerplanar.Algo.PolyPool
public import Outerplanar.Algo.PolyOut

/-!
# Theorem 21: the output of the algorithm is optimal

`solve_optimal`: given Lemma 19 as a hypothesis (it is proved as `twoConnectedK23_structure`, and
`STACS2027.solve_optimal` in `Outerplanar/LinearK23.lean` is the unconditional form), for every
`k ≥ 3` and every `K_{2,3}`-minor-free graph `g`, the output `solve k g` of the algorithm
(`Outerplanar.Algo.Solve`) writes an optimal cycle-path assignment of `CPAP(g, k)`
(`OptimalAssignmentOutput`). The pieces: the block
decomposition and the combination over blocks (`solve_correct`), the ear elimination
(`Ear.earHam_correct`), and the dynamic program on a polygon
(`Poly.optimalAssignmentOutput_polyOut` with `Poly.polyFacts`).
-/

@[expose] public section

namespace STACS2027.Algo

/-- **Correctness of the algorithm of Theorem 21** (and of Lemma 35 for outerplanar
graphs): given Lemma 19, `solve k g` is an optimal output of `CPAP(g, k)` for every
`K_{2,3}`-minor-free graph `g` and every `k ≥ 3`. -/
theorem solve_optimal (hL : TwoConnectedK23Structure) {k : ℕ} (hk : 3 ≤ k) {g : Graph} (hg : K23MinorFree g) :
    OptimalAssignmentOutput g k (solve k g) :=
  solve_correct hL hk hg (fun hP => Poly.optimalAssignmentOutput_polyOut hP hk (Poly.polyFacts hP hk))
    (fun hL hnd hN _ h0 hv => Ear.earHam_correct hL hnd hN h0 hv)

/-- Lemma 35's case: outerplanar graphs are `K_{2,3}`-minor-free. -/
theorem solve_optimal_outerplanar (hL : TwoConnectedK23Structure) {k : ℕ} (hk : 3 ≤ k) {g : Graph}
    (hg : Outerplanar g) : OptimalAssignmentOutput g k (solve k g) :=
  solve_optimal hL hk hg.2

end STACS2027.Algo

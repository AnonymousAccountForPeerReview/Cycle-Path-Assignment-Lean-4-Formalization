module

public import ComplexityExt.Approx.Defs

/-!
# MAX-3-SAT with unbounded assignments

The auxiliary problem `max3SATu`: MAX-3-SAT in which every word is an assignment of every
formula.  The reductions of `Hardness.MaxSNP` and `Hardness.APX` are proved for `max3SATu`
and transferred to `max3SAT` (assignments no longer than the instance) in
`Hardness.APX.Membership`: the two problems have the same optima and are L-reducible to each
other.  Since its solutions are not polynomially bounded, `max3SATu` is not in `NPO`
(`not_npo_max3SATu` in `Hardness.APX.Membership`).
-/

@[expose] public section

namespace Complexity

/-- MAX-3-SAT with assignments of unrestricted length (an auxiliary problem used in proofs). -/
def max3SATu : OptProblem where
  maximize := true
  Sol x y v := ∃ f, SAT.encode f = x ∧ SAT.IsThreeCNF f ∧ v = SAT.satCount (SAT.assignmentOf y) f

end Complexity

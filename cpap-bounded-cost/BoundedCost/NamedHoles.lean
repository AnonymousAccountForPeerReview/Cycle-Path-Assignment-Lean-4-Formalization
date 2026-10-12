module

public import BoundedCost.Sizes

/-!
# Named claims added by the paper

The paper of the manuscript adds to the proof of Corollary 5 an exact count of the prefix
encoding: "For an edge occurring in `p ≥ 2` cycles, the encoding uses `p − 1` auxiliary
variables and `3p − 4` clauses." The retained proposition name identifies that claim.
`prefixEncodingClauseCount` proves it using the exact lengths of the three clause families.
`prefixAuxiliaryVariables_count` proves the auxiliary-variable count and distinctness.
-/

@[expose] public section

namespace STACS2027

/-- Named claim from the proof of Corollary 5: for an edge `e` on `p ≥ 2`
enumerated cycles, the prefix encoding of `e` has exactly `3p − 4` clauses. -/
def PrefixEncodingClauseCount : Prop :=
  ∀ (g : Graph) (k : Nat) (e : Edge), 2 ≤ (cyclesThrough g k e).length →
    (prefixClauses g k e).length = 3 * (cyclesThrough g k e).length - 4

/-- The exact prefix-encoding clause count added by manuscript the paper. -/
theorem prefixEncodingClauseCount : PrefixEncodingClauseCount := by
  intro g k e hp
  exact prefixClauses_length g k e hp

end STACS2027

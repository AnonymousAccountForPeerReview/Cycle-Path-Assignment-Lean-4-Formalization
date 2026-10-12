module

public import Hardness.Occ.Abstract
public import Hardness.Expander.Main

/-!
# 3-OCCURRENCE MAX-3-SAT is MaxSNP-complete and APX-complete

ANONYMIZED–ANONYMIZED (1991); ANONYMIZED, *Computational Complexity* (1994),
Theorem 13.10. For the problem `max3SAT3` of `Complexity.Approx.Defs`:

* `max3SAT3_maxSNPComplete`: 3-OCCURRENCE MAX-3-SAT is MaxSNP-complete;
* `max3SAT3_inAPX` (`Hardness.Occ.Membership`): it is in APX;
* `max3SAT3_apxComplete_of_witnessGap`: it is APX-complete, given the witness-recovering gap
  form of the PCP theorem (`WitnessGap`, with a positive gap).

The L-reduction from MAX-3-SAT (`lReducible_max3SAT_max3SAT3`) uses the explicit expander
family of `Hardness.Expander.Main` (`exists_expanderFamily`) for the reduction to bounded
occurrences, and the torus gadget for the reduction to three occurrences.
-/

@[expose] public section

namespace Complexity

/-- MAX-3-SAT L-reduces to 3-OCCURRENCE MAX-3-SAT. -/
theorem lReducible_max3SAT_max3SAT3 : LReducible max3SAT max3SAT3 := by
  obtain ⟨D, c, G, hG, hE⟩ := exists_expanderFamily
  exact lReducible_max3SAT_max3SAT3_of hG hE

/-- 3-OCCURRENCE MAX-3-SAT is MaxSNP-hard. -/
theorem max3SAT3_maxSNPHard : MaxSNPHard max3SAT3 :=
  MaxSNPHard.of_lReducible max3SAT_maxSNPHard lReducible_max3SAT_max3SAT3

/-- **3-OCCURRENCE MAX-3-SAT is MaxSNP-complete.** -/
theorem max3SAT3_maxSNPComplete : MaxSNPComplete max3SAT3 :=
  ⟨max3SAT3_inMaxSNP, max3SAT3_maxSNPHard⟩

/-- **3-OCCURRENCE MAX-3-SAT is APX-complete**, given the witness-recovering gap theorem. -/
theorem max3SAT3_apxComplete_of_witnessGap {num den : Nat} (hnum : 0 < num)
    (h : WitnessGap num den) : APXComplete max3SAT3 :=
  ⟨max3SAT3_inAPX, apxHard_of_lReducible_max3SAT hnum h lReducible_max3SAT_max3SAT3⟩

end Complexity

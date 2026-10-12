module

public import Hardness.Final.Main
public import Hardness.Final.Max3SAT
public import Hardness.MaxSNP.NPO
public import Hardness.Occ.Main
public import Hardness.Witness.Main

/-!
Completed solution, loaded separately from `Challenge.lean`.

The imported modules prove the compared theorems `Complexity.pcp_gap`,
`Complexity.pcp_theorem`, `Complexity.npo_maxSNP0`, `Complexity.maxSNPHard_no_ptas`,
`Complexity.maxSNPHard_not_hasPTAS`, `Complexity.max3SAT_maxSNPComplete`,
`Complexity.max3SAT3_maxSNPComplete`, `Complexity.max3SAT_apxComplete` and
`Complexity.max3SAT3_apxComplete`, with exactly the statements of `Challenge.lean`. Solution does not import `Challenge.lean` or its intentional
holes.
-/

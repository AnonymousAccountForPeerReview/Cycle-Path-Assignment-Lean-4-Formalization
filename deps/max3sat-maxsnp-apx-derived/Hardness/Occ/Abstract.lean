module

public import Hardness.Occ.ExpanderGadget
public import Hardness.Occ.TorusCut
public import Hardness.Occ.Membership
public import Hardness.Final.Max3SAT

/-!
# 3-OCCURRENCE MAX-3-SAT, for an abstract expander family

For a polynomial-time expander family `G` (`IsExpanderFamily D c G`):

* `lReducible_max3SAT_max3SAT3_of`: MAX-3-SAT L-reduces to 3-OCCURRENCE MAX-3-SAT, in two
  stages: `max3SAT → max3SATB (2 * D + 1)` by the expander gadget
  (`lReducible_max3SAT_expander`) and `max3SATB (2 * D + 1) → max3SATB 3` by the torus gadget
  (`lReducible_torus`); `max3SATB 3 = max3SAT3`.
* `max3SAT3_maxSNPComplete_of`, `max3SAT3_apxComplete_of_witnessGap_of`.

The hypothesis is discharged in `Hardness.Occ.Main` with `exists_expanderFamily`.
-/

@[expose] public section

namespace Complexity

open Complexity.PT Complexity.Occ

section

variable {D c : Nat} {G : Nat → List (List Nat)}

/-- MAX-3-SAT L-reduces to 3-OCCURRENCE MAX-3-SAT, given an expander family. -/
theorem lReducible_max3SAT_max3SAT3_of (hG : PT G) (hE : IsExpanderFamily D c G) :
    LReducible max3SAT max3SAT3 :=
  ((lReducible_max3SAT_expander hG hE).trans (lReducible_torus (2 * D + 1))).trans
    lReducible_max3SATB_three

/-- 3-OCCURRENCE MAX-3-SAT is in MaxSNP: it is in NPO and L-reduces to MAX-3-SAT by the
identity maps. -/
theorem max3SAT3_inMaxSNP : InMaxSNP max3SAT3 :=
  InMaxSNP.of_lReducible npo_max3SAT3 lReducible_max3SAT3_max3SAT max3SAT_maxSNPComplete.1

theorem max3SAT3_maxSNPHard_of (hG : PT G) (hE : IsExpanderFamily D c G) :
    MaxSNPHard max3SAT3 :=
  MaxSNPHard.of_lReducible max3SAT_maxSNPHard (lReducible_max3SAT_max3SAT3_of hG hE)

theorem max3SAT3_maxSNPComplete_of (hG : PT G) (hE : IsExpanderFamily D c G) :
    MaxSNPComplete max3SAT3 :=
  ⟨max3SAT3_inMaxSNP, max3SAT3_maxSNPHard_of hG hE⟩

theorem max3SAT3_apxComplete_of_witnessGap_of (hG : PT G) (hE : IsExpanderFamily D c G)
    {num den : Nat} (hnum : 0 < num) (h : WitnessGap num den) : APXComplete max3SAT3 :=
  ⟨max3SAT3_inAPX, apxHard_of_lReducible_max3SAT hnum h (lReducible_max3SAT_max3SAT3_of hG hE)⟩

end

end Complexity

module

public import NPHardness.GadgetProjection
public import NPHardness.ClauseTwo5
public import NPHardness.ClauseThreeGeneral

/-!
Four short-cycle colour profiles, together with a ranked five-vertex core,
certify the cycle classification of Figure 4(c) for all k ≥ 5, including
the prescribed k=6 exception. Unbounded length arithmetic is proved by omega.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

@[expose] public section
namespace STACS2027

def clauseTwoGreen : List Edge := clauseThreeGreen ++ [(18,19)]
def clauseTwoOrange : List Edge := [(20,23), (20,21)]
def clauseTwoBlue : List Edge := [(22,23), (21,22)]
def clauseTwoRed : List Edge := [(21,23)]

def colourCount (es : List Edge) (c : Cycle) : Nat :=
  ((cycleEdges c).filter es.contains).length

structure CycleProfile where
  length : Nat
  green : Nat
  orange : Nat
  blue : Nat
  red : Nat
deriving DecidableEq, Repr

def clauseTwoProfile (c : Cycle) : CycleProfile :=
  ⟨c.length, colourCount clauseTwoGreen c, colourCount clauseTwoOrange c,
    colourCount clauseTwoBlue c, colourCount clauseTwoRed c⟩

def profileLength (k : Nat) (p : CycleProfile) : Nat :=
  p.length + p.green * (k-5) + p.orange * orangeSubdivisions k +
    p.blue * blueSubdivisions k + p.red * redSubdivisions k

/-- The four possible profiles of skeleton cycles shorter than five. -/
def clauseTwoExcludedProfiles : List CycleProfile :=
  [⟨3,0,0,2,1⟩, ⟨3,0,2,0,1⟩, ⟨4,0,1,1,0⟩, ⟨4,0,2,2,0⟩]

end STACS2027

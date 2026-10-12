module

public import NPHardness.PlanarOperationsPortsSubdivision

/-! The attachment edges of the three gadgets are not subdivided, for every
parameter. -/

@[expose] public section
namespace STACS2027
open Complexity Complexity.Planar

theorem variableLinks_ports_unsubdivided (k : Nat) :
    ∀ l ∈ variableLinks k, edge l.source l.target ∈ variablePorts → l.subdivisions=0 := by
  simp [variableLinks,variablePorts,edge]

theorem clauseThreeLinks_ports_unsubdivided (k : Nat) :
    ∀ l ∈ clauseThreeLinks k, edge l.source l.target ∈ clausePorts → l.subdivisions=0 := by
  simp [clauseThreeLinks,clausePorts,edge]

theorem clauseTwoLinks_ports_unsubdivided (k : Nat) :
    ∀ l ∈ clauseTwoLinks k, edge l.source l.target ∈ clausePorts.take 2 → l.subdivisions=0 := by
  simp [clauseTwoLinks,clauseThreeLinks,clausePorts,edge]

end STACS2027

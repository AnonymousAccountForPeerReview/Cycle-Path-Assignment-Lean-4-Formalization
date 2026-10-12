module

public import NPHardness.OrientedGluing

/-! Explicit endpoint bits for the occurrence-ring source. The implication
clauses use the fixed pair of bits false/true. With the Appendix C, Step 4
allocation of variable ports (first negative occurrence on e(x,False,1)), a
literal keeps the default endpoint order exactly when its sign differs from the
source sign of its variable. -/

@[expose] public section
namespace STACS2027.PlanarSource

def sourceEndpointChoices (signs : Nat → Bool) : EndpointChoices :=
  fun p => !(p.literal.positive == signs p.literal.var)

theorem sourceEndpointChoices_negative (signs : Nat → Bool) (v r : Nat) :
    sourceEndpointChoices signs ⟨⟨v,false⟩,r⟩=signs v := by
  unfold sourceEndpointChoices
  cases signs v <;> rfl

theorem sourceEndpointChoices_first (signs : Nat → Bool) (v r : Nat) :
    sourceEndpointChoices signs ⟨⟨v,signs v⟩,r⟩=false := by
  unfold sourceEndpointChoices
  cases signs v <;> rfl

theorem sourceEndpointChoices_second (signs : Nat → Bool) (v r : Nat) :
    sourceEndpointChoices signs ⟨⟨v,!(signs v)⟩,r⟩=true := by
  unfold sourceEndpointChoices
  cases signs v <;> rfl

end STACS2027.PlanarSource

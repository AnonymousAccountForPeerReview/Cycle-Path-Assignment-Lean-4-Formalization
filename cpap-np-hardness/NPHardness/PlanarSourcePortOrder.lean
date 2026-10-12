module

public import NPHardness.PlanarAssemblyPortTables
public import NPHardness.PlanarSourceEmbedding
public import NPHardness.PlanarSourcePlacement
public import NPHardness.PlanarSourceEndpointChoices

/-! The three incidences at an occurrence-copy variable have a fixed role
order. Their allocated gadget port numbers depend only on the source sign,
so the required reflection and resulting endpoint flips are explicit Booleans. -/

@[expose] public section
namespace STACS2027.PlanarSource
open Complexity Complexity.SAT Complexity.Planar PlanarGluing PlanarAssembly
open Embedding Embedding.BipartiteRotation

def variableRoleDart {E : Nat} (B : BipartiteRotation E) (i : Fin E) (role : Fin 3) : Fin (6*E) :=
  if role=0 then d6 i 0 else if role=1 then d6 i 2 else d6 (B.varRot.invFun i) 5

def clauseRoleDart {E : Nat} (i : Fin E) (role : Fin 2) : Fin (6*E) :=
  if role=0 then d6 i 3 else d6 i 4

theorem variableRoleDart_predecessor {E : Nat} (B : BipartiteRotation E)
    (i : Fin E) (role : Fin 3) :
    B.expanded.face (B.expanded.edge (variableRoleDart B i role)) =
      variableRoleDart B i (clauseThreePortNext role) := by
  rcases (by decide : ∀ r : Fin 3, r=0 ∨ r=1 ∨ r=2) role with rfl | rfl | rfl
  all_goals simp [variableRoleDart,clauseThreePortNext,expanded,newFace,newEdge,d6,B.varRot.right_inv]

theorem clauseRoleDart_predecessor {E : Nat} (B : BipartiteRotation E)
    (i : Fin E) (role : Fin 2) :
    B.expanded.face (B.expanded.edge (clauseRoleDart i role)) =
      clauseRoleDart i (clauseTwoPortNext role) := by
  rcases (by decide : ∀ r : Fin 2, r=0 ∨ r=1) role with rfl | rfl
  all_goals simp [clauseRoleDart,clauseTwoPortNext,expanded,newFace,newEdge,d6]

theorem copiedClause_predecessor {E : Nat} (B : BipartiteRotation E) (i : Fin E) :
    B.expanded.face (B.expanded.edge (d6 i 1))=d6 (B.clause.invFun i) 1 := by
  simp [expanded,newFace,newEdge,d6]

/-- Role 0 is the copied negative literal; role 1 is the outgoing ring
literal; role 2 is the incoming ring literal. -/
def variableRolePort (sign : Bool) (role : Fin 3) : Fin 3 :=
  if role=0 then 1 else if role=1 then (if sign then 0 else 2) else (if sign then 2 else 0)

def reflectedVariableNext (sign : Bool) (port : Fin 3) : Fin 3 :=
  if sign then variablePortPrev port else variablePortNext port

/-- Keeping the base variable rotation for a negative source sign, and
reflecting it for a positive source sign, realizes the actual source order. -/
theorem variableRolePort_predecessor (sign : Bool) (role : Fin 3) :
    variableRolePort sign (clauseThreePortNext role)=
      reflectedVariableNext sign (variableRolePort sign role) :=
  (by decide : ∀ s : Bool, ∀ r : Fin 3,
    variableRolePort s (clauseThreePortNext r)=reflectedVariableNext s (variableRolePort s r)) sign role

def rolePlacedLiteral (v : Nat) (sign : Bool) (role : Fin 3) : PlacedLiteral :=
  if role=0 then ⟨⟨v,false⟩,0⟩
  else
    let positive := if role=1 then sign else !sign
    ⟨⟨v,positive⟩,if positive then 0 else 1⟩

theorem rolePlacedLiteral_port (v : Nat) (sign : Bool) (role : Fin 3) :
    (rolePlacedLiteral v sign role).port=(variableRolePort sign role).val := by
  rcases (by decide : ∀ r : Fin 3, r=0 ∨ r=1 ∨ r=2) role with rfl | rfl | rfl <;>
    cases sign <;> rfl

end STACS2027.PlanarSource

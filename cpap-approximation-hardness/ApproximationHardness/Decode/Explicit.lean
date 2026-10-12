module

public import ApproximationHardness.Decode.Transport
import Lean.Elab.Tactic.Omega

/-!
# An explicit decoding map for Theorem 11

The decoding map of the L-reduction reads the chosen paths `ps`. For every variable `v` and
port `i`, it counts the load at the port edge `portEdgeG k v i` of the paths that leave the
vertex block of `v` (`clauseLoad`): these are exactly the paths of the clause gadgets, since a
variable gadget's paths stay in its block and a clause gadget's path through the port has an
edge leaving it. The variable is set true iff the weighted load of its true state, `W₁ + W₂`, is
at most that of its false state, `W₀` (`decodeAssign`). `decode_error_bound_explicit` proves the
second L-reduction inequality for this assignment.
-/

@[expose] public section
namespace STACS2027
open Complexity.SAT

/-- The block of a vertex. -/
def blockOf (k x : Nat) : Nat := x / gadgetWidth k

/-- The path `p` has an edge with an endpoint outside the block of variable `v`. -/
def outsideBlock (k v : Nat) (p : List Edge) : Bool := p.any fun e => !(blockOf k e.1 == v && blockOf k e.2 == v)

/-- The port edge `i` of variable `v` in the glued graph. -/
def portEdgeG (k v i : Nat) : Edge := mapEdge (blockVertex (gadgetWidth k) v) (variablePortEdge i)

/-- The load put on port `i` of variable `v` by the paths leaving the block of `v`. -/
def clauseLoad (k : Nat) (ps : List (List Edge)) (v i : Nat) : Nat :=
  (ps.map fun p => if outsideBlock k v p then p.count (portEdgeG k v i) else 0).sum

/-- **The decoding map**: `v` is true iff the clause loads satisfy `W₁ + W₂ ≤ W₀`. -/
def decodeAssign (k : Nat) (ps : List (List Edge)) : Assignment :=
  fun v => decide (clauseLoad k ps v 1 + clauseLoad k ps v 2 ≤ clauseLoad k ps v 0)

/-! ### Invariance under reordering -/

theorem outsideBlock_perm (k v : Nat) {p q : List Edge} (h : p.Perm q) : outsideBlock k v p = outsideBlock k v q := by
  unfold outsideBlock
  cases hp : p.any (fun e => !(blockOf k e.1 == v && blockOf k e.2 == v)) <;>
    cases hq : q.any (fun e => !(blockOf k e.1 == v && blockOf k e.2 == v))
  · rfl
  · obtain ⟨e, he, h'⟩ := List.any_eq_true.mp hq
    have := List.any_eq_false.mp hp e (h.mem_iff.mpr he)
    simp_all
  · obtain ⟨e, he, h'⟩ := List.any_eq_true.mp hp
    have := List.any_eq_false.mp hq e (h.mem_iff.mp he)
    simp_all
  · rfl

/-! ### Blocks -/

theorem blockOf_block {k v u : Nat} (hu : u < gadgetWidth k) : blockOf k (blockVertex (gadgetWidth k) v u) = v := by
  unfold blockOf blockVertex
  have hw : 0 < gadgetWidth k := by omega
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hw, Nat.div_eq_of_lt hu, Nat.zero_add]

theorem variableRegion_of_blockOf {k v x : Nat} (h : blockOf k x = v) : VariableRegion k v x := by
  have hw : 0 < gadgetWidth k := by have := gadgetWidth_ge k; omega
  refine ⟨x % gadgetWidth k, Nat.mod_lt _ hw, ?_⟩
  unfold blockVertex
  unfold blockOf at h
  rw [← h]
  exact (Nat.div_add_mod' x (gadgetWidth k)).symm

theorem blockOf_of_variableRegion {k v x : Nat} (h : VariableRegion k v x) : blockOf k x = v := by
  obtain ⟨u, hu, rfl⟩ := h
  exact blockOf_block hu

theorem edge_normal (a b : Nat) : edge (edge a b).1 (edge a b).2 = edge a b := by
  unfold edge
  apply Prod.ext <;> simp only <;> omega

theorem mem_mapGraph_edge {t : Nat → Nat} {g : Graph} {e : Edge} (h : e ∈ mapGraph t g) : e = edge e.1 e.2 := by
  obtain ⟨d, _, rfl⟩ := List.mem_map.mp h
  exact (edge_normal _ _).symm

theorem portEdgeG_eq (k v i : Nat) : portEdgeG k v i =
    edge (blockVertex (gadgetWidth k) v (variablePortEdge i).1) (blockVertex (gadgetWidth k) v (variablePortEdge i).2) := rfl

theorem variablePortEdge_lt (i : Nat) : (variablePortEdge i).1 < 7 ∧ (variablePortEdge i).2 < 7 := by
  unfold variablePortEdge edge variableEndpoint
  by_cases h0 : i = 0 <;> by_cases h1 : i = 1 <;> simp [h0, h1]

theorem portEdgeG_blocks (k v i : Nat) : blockOf k (portEdgeG k v i).1 = v ∧ blockOf k (portEdgeG k v i).2 = v := by
  have hw := gadgetWidth_ge k
  have hlt := variablePortEdge_lt i
  rw [portEdgeG_eq]
  simp only [edge]
  constructor
  · by_cases h : blockVertex (gadgetWidth k) v (variablePortEdge i).1 ≤ blockVertex (gadgetWidth k) v (variablePortEdge i).2
    · rw [Nat.min_eq_left h]; exact blockOf_block (by omega)
    · rw [Nat.min_eq_right (by omega)]; exact blockOf_block (by omega)
  · by_cases h : blockVertex (gadgetWidth k) v (variablePortEdge i).1 ≤ blockVertex (gadgetWidth k) v (variablePortEdge i).2
    · rw [Nat.max_eq_right h]; exact blockOf_block (by omega)
    · rw [Nat.max_eq_left (by omega)]; exact blockOf_block (by omega)

theorem portEdgeG_mem (k v : Nat) {i : Nat} (hi : i < 3) : portEdgeG k v i ∈ placedVariableGraph k v :=
  List.mem_map.mpr ⟨_, variableGraph_ports k hi, rfl⟩

theorem variablePortEdge_inj3 : ∀ a b : Fin 3, (variablePortEdge a.val).1 = (variablePortEdge b.val).1 →
    (variablePortEdge a.val).2 = (variablePortEdge b.val).2 → a = b := by decide

theorem variablePortEdge_swap3 : ∀ a b : Fin 3, (variablePortEdge a.val).1 = (variablePortEdge b.val).2 →
    (variablePortEdge a.val).2 = (variablePortEdge b.val).1 → a = b := by decide

theorem portEdgeG_inj {k v i i' : Nat} (hi : i < 3) (hi' : i' < 3) (h : portEdgeG k v i = portEdgeG k v i') : i = i' := by
  have hw := gadgetWidth_ge k
  have ha := variablePortEdge_lt i
  have hb := variablePortEdge_lt i'
  rw [portEdgeG_eq, portEdgeG_eq] at h
  rcases (edge_eq_iff ..).mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have e1 := (blockVertex_injective (by omega) (by omega) h1).2
    have e2 := (blockVertex_injective (by omega) (by omega) h2).2
    exact congrArg Fin.val (variablePortEdge_inj3 ⟨i, hi⟩ ⟨i', hi'⟩ e1 e2)
  · have e1 := (blockVertex_injective (by omega) (by omega) h1).2
    have e2 := (blockVertex_injective (by omega) (by omega) h2).2
    exact congrArg Fin.val (variablePortEdge_swap3 ⟨i, hi⟩ ⟨i', hi'⟩ e1 e2)

end STACS2027

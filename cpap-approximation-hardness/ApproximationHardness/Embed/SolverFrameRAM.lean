module

public import ApproximationHardness.Embed.SolverStepRAM
import Lean.Elab.Tactic.Omega

/-! Frame rules for the read-only solver tables. -/

@[expose] public section

namespace STACS2027.Embed.RAMSolver

open RAM

/-- Agreement on all read-only blocks of the solver layout. -/
def TableMemEq (L : Layout) (m n : Nat → Nat) : Prop :=
  ∀ j, 12 ≤ j → j < 22 → ∀ i, i < L.width → m (L.cell j i) = n (L.cell j i)

theorem TableMemEq.refl (L : Layout) (m : Nat → Nat) : TableMemEq L m m :=
  fun _ _ _ _ _ => rfl

theorem TableMemEq.trans {L : Layout} {m n p : Nat → Nat}
    (h : TableMemEq L m n) (h' : TableMemEq L n p) : TableMemEq L m p :=
  fun j hj hk i hi => (h j hj hk i hi).trans (h' j hj hk i hi)

/-- A bounded mutable-array write cannot change a plan table. -/
theorem TableMemEq.update (L : Layout) (m : Nat → Nat) (j a value : Nat)
    (hj : j < 12) (ha : a < L.width) :
    TableMemEq L (upd m (L.cell j a) value) m := by
  intro k hk hk' i hi
  rw [update_cell L m k j i a value hi ha]
  have hne : k ≠ j := by omega
  simp [hne]

/-- A bounded linked tail update cannot change a plan table. -/
theorem TableMemEq.append (L : Layout) (m : Nat → Nat) (h t u : Nat)
    (ht : t ≤ L.width) (hw : 0 < L.width) :
    TableMemEq L (appendMem m (L.block 0) h t u) m := by
  intro j hj hj' i hi
  exact appendMem_foreign L m h t u j i ht hw hi (by omega)

/-- Tables depend only on their two header registers and read-only memory cells. -/
theorem Tables.frame {L : Layout} {c d : Config} {S : Sol} {post : List Nat}
    {vertexBound dartBound : Nat} (ht : Tables L c S post vertexBound dartBound)
    (hl : d.reg 4 = c.reg 4) (hi : d.reg 5 = c.reg 5)
    (hm : TableMemEq L d.mem c.mem) : Tables L d S post vertexBound dartBound := by
  refine { ht with
    length := hl.trans ht.length
    infinity := hi.trans ht.infinity
    keys := ?_
    partners := ?_
    target := ?_
    groupIds := ?_
    counts := ?_
    leftType := ?_
    leftValue := ?_
    rightType := ?_
    rightValue := ?_
    order := ?_ }
  · intro e he
    exact (hm 12 (by decide) (by decide) e (Nat.lt_of_lt_of_le he ht.darts)).trans (ht.keys e he)
  · intro e he
    exact (hm 13 (by decide) (by decide) e (Nat.lt_of_lt_of_le he ht.darts)).trans (ht.partners e he)
  · intro e he
    exact (hm 14 (by decide) (by decide) e (Nat.lt_of_lt_of_le he ht.darts)).trans (ht.target e he)
  · intro v hv
    exact (hm 15 (by decide) (by decide) v (Nat.lt_of_lt_of_le hv ht.vertices)).trans (ht.groupIds v hv)
  · intro v hv
    exact (hm 16 (by decide) (by decide) v (Nat.lt_of_lt_of_le hv ht.vertices)).trans (ht.counts v hv)
  · intro v hv
    exact (hm 17 (by decide) (by decide) v (Nat.lt_of_lt_of_le hv ht.vertices)).trans (ht.leftType v hv)
  · intro v hv
    exact (hm 18 (by decide) (by decide) v (Nat.lt_of_lt_of_le hv ht.vertices)).trans (ht.leftValue v hv)
  · intro v hv
    exact (hm 19 (by decide) (by decide) v (Nat.lt_of_lt_of_le hv ht.vertices)).trans (ht.rightType v hv)
  · intro v hv
    exact (hm 20 (by decide) (by decide) v (Nat.lt_of_lt_of_le hv ht.vertices)).trans (ht.rightValue v hv)
  · intro i hi
    exact (hm 21 (by decide) (by decide) i (Nat.lt_of_lt_of_le hi ht.orderBound)).trans (ht.order i hi)

end STACS2027.Embed.RAMSolver

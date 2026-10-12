module

public import ApproximationHardness.RAM.Orient.Program
import Lean.Elab.Tactic.Omega

/-!
# The orientation bits in terms of the literal list

The explicit bits of `ApproximationHardness.Planar.ExplicitOrientation` are stated on the allocated
occurrences `occList f = (placeFormula [] f).flatten`. The RAM program reads the literals
`f.flatten` one by one; this file restates the occurrence data on prefixes of that list.
-/

@[expose] public section

namespace STACS2027.RAM

open Complexity.SAT Complexity.Planar.Comb PlanarAssembly

theorem placeLiterals_getElem? : ∀ (past ls : List Literal) (i : Nat),
    (placeLiterals past ls)[i]? = ls[i]?.map fun l => (⟨l, (past ++ ls.take i).count l⟩ : PlacedLiteral)
  | past, [], i => by simp [placeLiterals]
  | past, l :: ls, 0 => by simp [placeLiterals]
  | past, l :: ls, i + 1 => by
    simp only [placeLiterals, List.getElem?_cons_succ, List.take_succ_cons]
    rw [placeLiterals_getElem? (past ++ [l]) ls i]
    simp [List.append_assoc]

theorem occList_getElem? (f : CNF) (i : Nat) :
    (occList f)[i]? = f.flatten[i]?.map fun l => (⟨l, (f.flatten.take i).count l⟩ : PlacedLiteral) := by
  unfold occList
  rw [placeFormula_flatten, placeLiterals_getElem?]
  simp

theorem occList_length (f : CNF) : (occList f).length = f.flatten.length := by
  unfold occList
  rw [placeFormula_flatten]
  have := congrArg List.length (placeLiterals_forget [] f.flatten)
  simpa using this

/-- The port of the literal `l` read after the literals `past`. -/
def litPort (past : List Literal) (l : Literal) : Nat := if l.positive then 0 else past.count l + 1

theorem occPort_flat (f : CNF) (i : Nat) :
    occPort f i = (f.flatten[i]?.map (litPort (f.flatten.take i))).getD 0 := by
  unfold occPort
  rw [occList_getElem?]
  cases f.flatten[i]? <;> simp [PlacedLiteral.port, litPort]

theorem occVar_flat (f : CNF) (i : Nat) : occVar f i = (f.flatten[i]?.map Literal.var).getD 0 := by
  unfold occVar
  rw [occList_getElem?]
  cases f.flatten[i]? <;> simp

theorem positiveIndex_flat (f : CNF) (v : Nat) : positiveIndex f v = f.flatten.idxOf ⟨v, true⟩ := by
  unfold positiveIndex occList
  rw [placeFormula_flatten]
  conv => rhs; rw [← placeLiterals_forget [] f.flatten]
  rw [List.idxOf, List.findIdx_map]
  rfl

/-- One more than the index of the first positive occurrence of `v` in `past` (`0` if none). -/
def posCode (past : List Literal) (v : Nat) : Nat :=
  if (⟨v, true⟩ : Literal) ∈ past then past.idxOf ⟨v, true⟩ + 1 else 0

theorem posCode_snoc (past : List Literal) (l : Literal) (v : Nat) :
    posCode (past ++ [l]) v =
      if posCode past v = 0 ∧ l = ⟨v, true⟩ then past.length + 1 else posCode past v := by
  unfold posCode
  by_cases h : (⟨v, true⟩ : Literal) ∈ past
  · have : (⟨v, true⟩ : Literal) ∈ past ++ [l] := List.mem_append_left _ h
    simp only [this, h, ↓reduceIte, List.idxOf_append, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
      false_and]
  · by_cases hl : l = ⟨v, true⟩
    · subst hl
      have : (⟨v, true⟩ : Literal) ∈ past ++ [⟨v, true⟩] := by simp
      simp only [this, h, ↓reduceIte, List.idxOf_append, and_self]
      simp
    · have : (⟨v, true⟩ : Literal) ∉ past ++ [l] := by
        simp only [List.mem_append, List.mem_singleton, not_or]
        exact ⟨h, fun e => hl e.symm⟩
      simp [this, h, hl]

theorem posCode_eq (f : CNF) (v : Nat) :
    posCode f.flatten v = if positiveIndex f v < (occList f).length then positiveIndex f v + 1 else 0 := by
  rw [positiveIndex_flat, occList_length]
  unfold posCode
  by_cases h : (⟨v, true⟩ : Literal) ∈ f.flatten
  · rw [ite_eq_left h, ite_eq_left (List.idxOf_lt_length_iff.mpr h)]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h (List.idxOf_lt_length_iff.mp h'))]

/-! ### Clauses as blocks of occurrences -/

theorem off_prefix {f pre suf : CNF} (h : pre ++ suf = f) : off f pre.length = pre.flatten.length := by
  subst h
  unfold off lens
  rw [List.map_append, List.take_append_of_le_length (by simp), List.take_of_length_le (by simp),
    List.length_flatten]

theorem kl_prefix {f pre suf : CNF} {cc : Clause} (h : pre ++ cc :: suf = f) : kl f pre.length = cc.length := by
  subst h
  simp [kl, Complexity.Planar.Comb.cl]

theorem prefix_lt {f pre suf : CNF} {cc : Clause} (h : pre ++ cc :: suf = f) : pre.length < f.length := by
  subst h; simp

theorem oj_prefix {f pre suf : CNF} {cc : Clause} (h : pre ++ cc :: suf = f) {t : Nat} (ht : t < cc.length) :
    oj f (pre.flatten.length + t) = pre.length := by
  have hj := prefix_lt h
  have hk := kl_prefix h
  rw [← off_prefix (show pre ++ (cc :: suf) = f from h)]
  exact (occ_eq f pre.length t hj (by rw [hk]; exact ht)).1

theorem flatten_prefix {f pre suf : CNF} {cc : Clause} (h : pre ++ cc :: suf = f) (lpre : List Literal)
    {l : Literal} {lsuf : List Literal} (hc : lpre ++ l :: lsuf = cc) :
    (pre.flatten ++ lpre) ++ l :: (lsuf ++ suf.flatten) = f.flatten := by
  subst h; subst hc; simp

theorem getElem_prefix {ls past rest : List Literal} {l : Literal} (h : past ++ l :: rest = ls) :
    ls[past.length]? = some l ∧ ls.take past.length = past := by
  subst h; simp

/-- The clause-sign bit of occurrence `i`. -/
def csBit (f : CNF) (rot : List Nat) (i : Nat) : Nat := if clauseSign f (rotFun rot) (oj f i) then 1 else 0

end STACS2027.RAM

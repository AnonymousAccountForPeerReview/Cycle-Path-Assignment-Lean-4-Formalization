module

public import NPHardness.PlanarSourceRotationTable
public import Complexity.Planar.GridDef

/-! Local arithmetic behind the grid's constant-size incidence neighborhoods.
Only two successive cells can share a chain variable; all other relative
positions belong to a unique cell and every column occupies a disjoint block.
-/

@[expose] public section
namespace STACS2027.PlanarSource.RotationTable
open Complexity Complexity.SAT Complexity.Planar Complexity.Planar.Grid

/-- Literal positions in one registered cell, retaining their actual order. -/
def cellPositions (odd : Bool) : List Nat :=
  ((cellT false false).map (inst 0 odd)).flatten.map Literal.var

theorem cellPositions_length (odd : Bool) : (cellPositions odd).length = 48 := by
  cases odd <;> decide

theorem cellPositions_lt (odd : Bool) : ∀ p ∈ cellPositions odd, p < 10 := by
  cases odd <;> decide

/-- A fixed local table, with the exact registered literal order and multiplicity. -/
theorem cell_variables (W j idx : Nat) (odd : Bool) (bp bn : Bool) :
    (cellCNF W j idx odd (bp,bn)).flatten.map Literal.var =
      (cellPositions odd).map (cellOff W j idx + ·) := by
  cases odd <;> cases bp <;> cases bn <;> rfl

/-- Disjoint column blocks uniquely determine both column and position. -/
theorem column_position_eq {W j j' p p' : Nat}
    (hp : p < colLen W) (hp' : p' < colLen W)
    (he : colBase W j + p = colBase W j' + p') : j = j' ∧ p = p' := by
  have hd := congrArg (fun x => x / colLen W) he
  have hm := congrArg (fun x => x % colLen W) he
  have hpos : 0 < colLen W := by unfold colLen; omega
  simp only [colBase, Nat.mul_comm j (colLen W), Nat.mul_comm j' (colLen W), Nat.mul_add_div hpos, Nat.div_eq_of_lt hp,
    Nat.div_eq_of_lt hp', Nat.add_zero] at hd
  simp only [colBase, Nat.add_mod, Nat.mul_mod_left, Nat.zero_add,
    Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt hp'] at hm
  exact ⟨hd,hm⟩

/-- Within a column only neighboring cells meet, at position 9 / position 0. -/
theorem cell_position_eq {W j i i' p p' : Nat}
    (hp : p ≤ 9) (hp' : p' ≤ 9)
    (he : cellOff W j i + p = cellOff W j i' + p') :
    (i = i' ∧ p = p') ∨ (i + 1 = i' ∧ p = 9 ∧ p' = 0) ∨
      (i' + 1 = i ∧ p = 0 ∧ p' = 9) := by
  unfold cellOff at he
  omega

/-- A non-chain position has no incidence in a neighboring cell. -/
theorem cell_interior_eq {W j i i' p p' : Nat}
    (hp0 : 0 < p) (hp9 : p < 9) (hp' : p' ≤ 9)
    (he : cellOff W j i + p = cellOff W j i' + p') : i = i' ∧ p = p' := by
  rcases cell_position_eq (by omega) hp' he with h | h | h
  · exact h
  · omega
  · omega

/-- The chain input is found in the cell itself or the previous cell's output. -/
theorem cell_chain_eq {W j i i' p' : Nat} (hp' : p' ≤ 9)
    (he : cellOff W j i = cellOff W j i' + p') :
    (i = i' ∧ p' = 0) ∨ (i' + 1 = i ∧ p' = 9) := by
  have hh := cell_position_eq (p := 0) (by decide) hp' (by simpa using he)
  omega

/-- Grid-cell occurrences stay within their column, including the output chain. -/
theorem cell_position_lt {W idx p : Nat} (hi : idx < W) (hp : p ≤ 9) :
    1 + 9 * idx + p < colLen W := by
  unfold colLen
  omega

theorem cell_columns_eq {W j j' i i' p p' : Nat}
    (hi : i < W) (hi' : i' < W) (hp : p ≤ 9) (hp' : p' ≤ 9)
    (he : cellOff W j i + p = cellOff W j' i' + p') : j = j' := by
  apply (column_position_eq (cell_position_lt hi hp) (cell_position_lt hi' hp') ?_).1
  simpa only [cellOff, Nat.add_assoc] using he

/-- Interior occurrence neighborhoods contain exactly the local cell's occurrences. -/
theorem cell_interior_unique {W j j' i i' p p' : Nat}
    (hi : i < W) (hi' : i' < W) (hp0 : 0 < p) (hp9 : p < 9) (hp' : p' ≤ 9)
    (he : cellOff W j i + p = cellOff W j' i' + p') :
    j = j' ∧ i = i' ∧ p = p' := by
  have hj := cell_columns_eq hi hi' (by omega) hp' he
  subst j'
  exact ⟨rfl,cell_interior_eq hp0 hp9 hp' he⟩

theorem cell_literal_position {W j idx : Nat} {odd bp bn : Bool} {l : Literal}
    (hl : l ∈ (cellCNF W j idx odd (bp,bn)).flatten) :
    ∃ p, p < 10 ∧ l.var = cellOff W j idx + p := by
  have hh : l.var ∈ (cellCNF W j idx odd (bp,bn)).flatten.map Literal.var :=
    List.mem_map.mpr ⟨l,hl,rfl⟩
  rw [cell_variables] at hh
  obtain ⟨p,hp,he⟩ := List.mem_map.mp hh
  exact ⟨p,cellPositions_lt odd p hp,he.symm⟩

theorem start_literal {W j : Nat} {l : Literal}
    (hl : l ∈ (startG W j).flatten) : l.var = colBase W j ∨ l.var = colBase W j + 1 := by
  simp only [startG,List.flatten_cons,List.flatten_nil,List.append_nil,List.mem_append,
    List.mem_cons,List.not_mem_nil,or_false] at hl
  rcases hl with (rfl | rfl) | (rfl | rfl) <;> simp

theorem end_literal {W j : Nat} {l : Literal}
    (hl : l ∈ (endG W j).flatten) : l.var = cellOff W j W ∨ l.var = cellOff W j W + 1 := by
  simp only [endG,List.flatten_cons,List.flatten_nil,List.append_nil,List.mem_append,
    List.mem_cons,List.not_mem_nil,or_false] at hl
  rcases hl with (rfl | rfl) | (rfl | rfl) <;> simp

theorem rainbowEven_literal {W j v : Nat} {l : Literal}
    (hl : l ∈ (rbEven W j v).flatten) :
    l.var = cellOff W j v + 8 ∨ l.var = cellOff W (j+1) (W-1-v) + 1 := by
  simp only [rbEven,List.flatten_cons,List.flatten_nil,List.append_nil,List.mem_append,
    List.mem_cons,List.not_mem_nil,or_false] at hl
  rcases hl with (rfl | rfl) | (rfl | rfl) <;> simp

theorem rainbowOdd_literal {W j v : Nat} {l : Literal}
    (hl : l ∈ (rbOdd W j v).flatten) :
    l.var = cellOff W (j+1) v + 1 ∨ l.var = cellOff W j (W-1-v) + 8 := by
  simp only [rbOdd,List.flatten_cons,List.flatten_nil,List.append_nil,List.mem_append,
    List.mem_cons,List.not_mem_nil,or_false] at hl
  rcases hl with (rfl | rfl) | (rfl | rfl) <;> simp

/-- Only relative positions 1 and 8 can meet a rainbow block. -/
theorem rainbowEven_incident {W j i p j' v : Nat} {l : Literal}
    (hi : i < W) (hv : v < W) (hp0 : 0 < p) (hp9 : p < 9)
    (hl : l ∈ (rbEven W j' v).flatten) (he : cellOff W j i + p = l.var) :
    (j = j' ∧ i = v ∧ p = 8) ∨ (j = j' + 1 ∧ i = W - 1 - v ∧ p = 1) := by
  rcases rainbowEven_literal hl with hl | hl
  · exact Or.inl (cell_interior_unique hi hv hp0 hp9 (by decide) (he.trans hl))
  · exact Or.inr (cell_interior_unique hi (by omega) hp0 hp9 (by decide) (he.trans hl))

theorem rainbowOdd_incident {W j i p j' v : Nat} {l : Literal}
    (hi : i < W) (hv : v < W) (hp0 : 0 < p) (hp9 : p < 9)
    (hl : l ∈ (rbOdd W j' v).flatten) (he : cellOff W j i + p = l.var) :
    (j = j' + 1 ∧ i = v ∧ p = 1) ∨ (j = j' ∧ i = W - 1 - v ∧ p = 8) := by
  rcases rainbowOdd_literal hl with hl | hl
  · exact Or.inl (cell_interior_unique hi hv hp0 hp9 (by decide) (he.trans hl))
  · exact Or.inr (cell_interior_unique hi (by omega) hp0 hp9 (by decide) (he.trans hl))

/-- The start gadget has no literal at a cell's interior position. -/
theorem cell_interior_not_start {W j i p j' : Nat} {l : Literal}
    (hi : i < W) (hp0 : 0 < p) (hp9 : p < 9)
    (hl : l ∈ (startG W j').flatten) : cellOff W j i + p ≠ l.var := by
  intro he
  rcases start_literal hl with hs | hs
  · have hh := column_position_eq (cell_position_lt (p := p) hi (by omega))
      (p' := 0) (show 0 < colLen W by unfold colLen; omega)
      (by simpa only [cellOff,Nat.add_assoc,Nat.add_zero] using he.trans hs)
    omega
  · have hh := column_position_eq (cell_position_lt (p := p) hi (by omega))
      (p' := 1) (show 1 < colLen W by unfold colLen; omega)
      (by simpa only [cellOff,Nat.add_assoc] using he.trans hs)
    omega

/-- The end gadget has no literal at a cell's interior position. -/
theorem cell_interior_not_end {W j i p j' : Nat} {l : Literal}
    (hi : i < W) (hp0 : 0 < p) (hp9 : p < 9)
    (hl : l ∈ (endG W j').flatten) : cellOff W j i + p ≠ l.var := by
  intro he
  rcases end_literal hl with hs | hs
  · have hh := column_position_eq (cell_position_lt (p := p) hi (by omega))
      (p' := 1+9*W) (show 1+9*W < colLen W by unfold colLen; omega)
      (by simpa only [cellOff,Nat.add_assoc] using he.trans hs)
    omega
  · have hh := column_position_eq (cell_position_lt (p := p) hi (by omega))
      (p' := 1+9*W+1) (show 1+9*W+1 < colLen W by unfold colLen; omega)
      (by simpa only [cellOff,Nat.add_assoc] using he.trans hs)
    omega

/-- A chain vertex has no incidence in any rainbow. -/
theorem chain_not_rainbow_endpoint {W j i j' i' p' : Nat}
    (hi : i ≤ W) (hi' : i' < W) (hp' : p' = 1 ∨ p' = 8) :
    cellOff W j i ≠ cellOff W j' i' + p' := by
  intro he
  have hpos : 1+9*i < colLen W := by unfold colLen; omega
  have hh := column_position_eq hpos (cell_position_lt (p := p') hi' (by omega))
    (by simpa only [cellOff,Nat.add_assoc] using he)
  rcases hp' with rfl | rfl <;> omega

theorem chain_not_rainbowEven {W j i j' v : Nat} {l : Literal}
    (hi : i ≤ W) (hv : v < W) (hl : l ∈ (rbEven W j' v).flatten) :
    cellOff W j i ≠ l.var := by
  intro he
  rcases rainbowEven_literal hl with hs | hs
  · exact chain_not_rainbow_endpoint hi hv (Or.inr rfl) (he.trans hs)
  · exact chain_not_rainbow_endpoint hi (by omega) (Or.inl rfl) (he.trans hs)

theorem chain_not_rainbowOdd {W j i j' v : Nat} {l : Literal}
    (hi : i ≤ W) (hv : v < W) (hl : l ∈ (rbOdd W j' v).flatten) :
    cellOff W j i ≠ l.var := by
  intro he
  rcases rainbowOdd_literal hl with hs | hs
  · exact chain_not_rainbow_endpoint hi hv (Or.inl rfl) (he.trans hs)
  · exact chain_not_rainbow_endpoint hi (by omega) (Or.inr rfl) (he.trans hs)

/-- Only the first chain vertex occurs in the start gadget. -/
theorem chain_start_incident {W j i j' : Nat} {l : Literal}
    (hi : i ≤ W) (hl : l ∈ (startG W j').flatten)
    (he : cellOff W j i = l.var) : j = j' ∧ i = 0 := by
  have hpos : 1+9*i < colLen W := by unfold colLen; omega
  rcases start_literal hl with hs | hs
  · have hh := column_position_eq hpos
      (p' := 0) (show 0 < colLen W by unfold colLen; omega)
      (by simpa only [cellOff,Nat.add_assoc,Nat.add_zero] using he.trans hs)
    omega
  · have hh := column_position_eq hpos
      (p' := 1) (show 1 < colLen W by unfold colLen; omega)
      (by simpa only [cellOff,Nat.add_assoc] using he.trans hs)
    exact ⟨hh.1,by omega⟩

/-- Only the last chain vertex occurs in the end gadget, also for `W = 0`. -/
theorem chain_end_incident {W j i j' : Nat} {l : Literal}
    (hi : i ≤ W) (hl : l ∈ (endG W j').flatten)
    (he : cellOff W j i = l.var) : j = j' ∧ i = W := by
  have hpos : 1+9*i < colLen W := by unfold colLen; omega
  rcases end_literal hl with hs | hs
  · have hh := column_position_eq hpos
      (p' := 1+9*W) (show 1+9*W < colLen W by unfold colLen; omega)
      (by simpa only [cellOff,Nat.add_assoc] using he.trans hs)
    exact ⟨hh.1,by omega⟩
  · have hh := column_position_eq hpos
      (p' := 1+9*W+1) (show 1+9*W+1 < colLen W by unfold colLen; omega)
      (by simpa only [cellOff,Nat.add_assoc] using he.trans hs)
    omega

end STACS2027.PlanarSource.RotationTable

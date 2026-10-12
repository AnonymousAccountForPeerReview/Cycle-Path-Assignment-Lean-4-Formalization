module

public import NPHardness.PlanarSourceRotationTableGeometry
public import NPHardness.PlanarSourcePackedLayout

/-! Completeness of the finite geometric block neighborhoods used by the
compiled successor program. Block addresses here are the actual registered
grid family addresses, with explicit boundary validity conditions. -/

@[expose] public section
namespace STACS2027.PlanarSource.RotationTable
open Complexity Complexity.SAT Complexity.Planar Complexity.Planar.Grid

inductive GridBlock where
  | start (k : Nat) (odd : Bool)
  | cell (k idx : Nat) (odd : Bool)
  | finish (k : Nat) (odd : Bool)
  | rainbow (k v : Nat) (odd : Bool)
  deriving DecidableEq

def columnIndex (k : Nat) (odd : Bool) : Nat := 2*k + if odd then 1 else 0

def GridBlock.Valid (W m : Nat) : GridBlock → Prop
  | .start k odd | .finish k odd => columnIndex k odd < m
  | .cell k idx odd => columnIndex k odd < m ∧ idx < W
  | .rainbow k v odd => columnIndex k odd+1 < m ∧ v < W

instance (W m : Nat) (b : GridBlock) : Decidable (b.Valid W m) := by
  cases b <;> unfold GridBlock.Valid <;> infer_instance

def GridBlock.formula (W : Nat) (bits : Nat → Nat → Bool×Bool) : GridBlock → CNF
  | .start k odd => startG W (columnIndex k odd)
  | .cell k idx odd => cellCNF W (columnIndex k odd) idx odd (bits (columnIndex k odd) (row W odd idx))
  | .finish k odd => endG W (columnIndex k odd)
  | .rainbow k v odd => if odd then rbOdd W (columnIndex k odd) v else rbEven W (columnIndex k odd) v

def interiorNeighborhood (W k idx : Nat) (odd : Bool) (position : Nat) : List GridBlock :=
  [.cell k idx odd] ++
  if position = 1 then
    if odd then [.rainbow k (W-1-idx) false]
    else if 0 < k then [.rainbow (k-1) idx true] else []
  else if position = 8 then [.rainbow k (if odd then W-1-idx else idx) odd] else []

theorem columnIndex_injective {k k' : Nat} {odd odd' : Bool}
    (h : columnIndex k odd = columnIndex k' odd') : k = k' ∧ odd = odd' := by
  cases odd <;> cases odd' <;> simp_all [columnIndex] <;> omega

/-- Every source block containing a literal at a cell interior is explicitly
included in the compiler's own-cell / incoming / outgoing rainbow neighborhood. -/
theorem interiorNeighborhood_complete {W m k idx position : Nat} {odd : Bool}
    (bits : Nat → Nat → Bool×Bool) (hi : idx < W) (hp0 : 0 < position) (hp9 : position < 9)
    (b : GridBlock) (hb : b.Valid W m) (l : Literal) (hl : l ∈ (b.formula W bits).flatten)
    (he : cellOff W (columnIndex k odd) idx + position = l.var) :
    b ∈ interiorNeighborhood W k idx odd position := by
  cases b with
  | start k' odd' =>
    exact False.elim (cell_interior_not_start hi hp0 hp9 hl he)
  | finish k' odd' =>
    exact False.elim (cell_interior_not_end hi hp0 hp9 hl he)
  | cell k' idx' odd' =>
    obtain ⟨p,hp,hvar⟩ := cell_literal_position hl
    obtain ⟨hj,hi',hp'⟩ := cell_interior_unique hi hb.2 hp0 hp9 (by omega) (he.trans hvar)
    obtain ⟨hk,ho⟩ := columnIndex_injective hj
    subst k'; subst odd'; subst idx'
    simp [interiorNeighborhood]
  | rainbow k' v odd' =>
    cases odd' with
    | false =>
      have hl' : l ∈ (rbEven W (2*k') v).flatten := hl
      have hh := rainbowEven_incident hi hb.2 hp0 hp9 hl' he
      rcases hh with ⟨hj,hi',hp⟩ | ⟨hj,hi',hp⟩
      · have hh' := columnIndex_injective (k := k) (odd := odd) (k' := k') (odd' := false)
          (by simpa [columnIndex] using hj)
        obtain ⟨hk,ho⟩ := hh'
        subst k'; subst odd; subst v; subst position
        simp [interiorNeighborhood]
      · have hh' := columnIndex_injective (k := k) (odd := odd) (k' := k') (odd' := true)
          (by simpa [columnIndex] using hj)
        obtain ⟨hk,ho⟩ := hh'
        subst k'; subst odd; subst position
        have hv : v = W-1-idx := by have := hb.2; omega
        subst v
        simp [interiorNeighborhood]
    | true =>
      have hl' : l ∈ (rbOdd W (2*k'+1) v).flatten := hl
      have hh := rainbowOdd_incident hi hb.2 hp0 hp9 hl' he
      rcases hh with ⟨hj,hi',hp⟩ | ⟨hj,hi',hp⟩
      · have hj' : columnIndex k odd = columnIndex (k'+1) false := by
          simpa [columnIndex,Nat.mul_add,Nat.add_assoc] using hj
        obtain ⟨hk,ho⟩ := columnIndex_injective hj'
        subst odd; subst k; subst v; subst position
        simp [interiorNeighborhood]
      · have hh' := columnIndex_injective (k := k) (odd := odd) (k' := k') (odd' := true)
          (by simpa [columnIndex] using hj)
        obtain ⟨hk,ho⟩ := hh'
        subst k'; subst odd; subst position
        have hv : v = W-1-idx := by have := hb.2; omega
        subst v
        simp [interiorNeighborhood]

def chainNeighborhood (W k idx : Nat) (odd : Bool) : List GridBlock :=
  [.cell k idx odd] ++ (if 0 < idx then [.cell k (idx-1) odd] else []) ++
    (if idx = 0 then [.start k odd] else []) ++ (if idx = W then [.finish k odd] else [])

/-- A chain node meets precisely the present cell, preceding cell, and the
applicable boundary gadgets. The zero-width case retains both boundaries. -/
theorem chainNeighborhood_complete {W m k idx : Nat} {odd : Bool}
    (bits : Nat → Nat → Bool×Bool) (hi : idx ≤ W)
    (b : GridBlock) (hb : b.Valid W m) (l : Literal) (hl : l ∈ (b.formula W bits).flatten)
    (he : cellOff W (columnIndex k odd) idx = l.var) :
    b ∈ chainNeighborhood W k idx odd := by
  cases b with
  | start k' odd' =>
    obtain ⟨hj,hi'⟩ := chain_start_incident hi hl he
    obtain ⟨hk,ho⟩ := columnIndex_injective hj
    subst k'; subst odd'; subst idx
    simp [chainNeighborhood]
  | finish k' odd' =>
    obtain ⟨hj,hi'⟩ := chain_end_incident hi hl he
    obtain ⟨hk,ho⟩ := columnIndex_injective hj
    subst k'; subst odd'; subst idx
    simp [chainNeighborhood]
  | cell k' idx' odd' =>
    obtain ⟨p,hp,hvar⟩ := cell_literal_position hl
    have hj := (column_position_eq
      (p := 1+9*idx) (show 1+9*idx < colLen W by unfold colLen; omega)
      (cell_position_lt (p := p) hb.2 (by omega))
      (by simpa only [cellOff,Nat.add_assoc] using he.trans hvar)).1
    obtain ⟨hk,ho⟩ := columnIndex_injective hj
    subst k'; subst odd'
    have hh := cell_chain_eq (by omega) (he.trans hvar)
    rcases hh with ⟨hi',hp'⟩ | ⟨hi',hp'⟩
    · subst idx'; simp [chainNeighborhood]
    · have hpos : 0 < idx := by omega
      have heq : idx' = idx-1 := by omega
      subst idx'
      simp [chainNeighborhood,hpos]
  | rainbow k' v odd' =>
    cases odd'
    · exact False.elim (chain_not_rainbowEven hi hb.2 hl he)
    · exact False.elim (chain_not_rainbowOdd hi hb.2 hl he)

theorem startAux_ne_cell {W j j' idx p : Nat} (hi : idx < W) (hp : p ≤ 9) :
    colBase W j ≠ cellOff W j' idx+p := by
  intro he
  have hh := column_position_eq
    (p := 0) (show 0 < colLen W by unfold colLen; omega)
    (cell_position_lt hi hp)
    (by simpa only [cellOff,Nat.add_assoc,Nat.add_zero] using he)
  omega

theorem endAux_ne_cell {W j j' idx p : Nat} (hi : idx < W) (hp : p ≤ 9) :
    cellOff W j W+1 ≠ cellOff W j' idx+p := by
  intro he
  have hh := column_position_eq
    (p := 1+9*W+1) (show 1+9*W+1 < colLen W by unfold colLen; omega)
    (cell_position_lt hi hp)
    (by simpa only [cellOff,Nat.add_assoc] using he)
  omega

/-- The auxiliary start variable appears only in its own start block. -/
theorem startNeighborhood_complete {W m k : Nat} {odd : Bool}
    (bits : Nat → Nat → Bool×Bool)
    (b : GridBlock) (hb : b.Valid W m) (l : Literal) (hl : l ∈ (b.formula W bits).flatten)
    (he : colBase W (columnIndex k odd) = l.var) : b = .start k odd := by
  cases b with
  | start k' odd' =>
    rcases start_literal hl with hs | hs
    · have hj : columnIndex k odd = columnIndex k' odd' :=
        (column_position_eq (p := 0) (p' := 0)
          (by unfold colLen; omega) (by unfold colLen; omega)
          (by simpa only [Nat.add_zero] using he.trans hs)).1
      obtain ⟨hk,ho⟩ := columnIndex_injective hj
      subst k'; subst odd'; rfl
    · have hh := column_position_eq (p := 0) (p' := 1)
        (show 0 < colLen W by unfold colLen; omega) (show 1 < colLen W by unfold colLen; omega)
        (by simpa only [Nat.add_zero] using he.trans hs)
      omega
  | finish k' odd' =>
    rcases end_literal hl with hs | hs
    · have hh := column_position_eq (p := 0) (p' := 1+9*W)
        (show 0 < colLen W by unfold colLen; omega) (show 1+9*W < colLen W by unfold colLen; omega)
        (by simpa only [cellOff,Nat.add_assoc,Nat.add_zero] using he.trans hs)
      omega
    · have hh := column_position_eq (p := 0) (p' := 1+9*W+1)
        (show 0 < colLen W by unfold colLen; omega) (show 1+9*W+1 < colLen W by unfold colLen; omega)
        (by simpa only [cellOff,Nat.add_assoc,Nat.add_zero] using he.trans hs)
      omega
  | cell k' idx' odd' =>
    obtain ⟨p,hp,hvar⟩ := cell_literal_position hl
    exact False.elim (startAux_ne_cell hb.2 (by omega) (he.trans hvar))
  | rainbow k' v odd' =>
    cases odd'
    · rcases rainbowEven_literal hl with hs | hs
      · exact False.elim (startAux_ne_cell hb.2 (by decide) (he.trans hs))
      · exact False.elim (startAux_ne_cell (by have := hb.2; omega) (by decide) (he.trans hs))
    · rcases rainbowOdd_literal hl with hs | hs
      · exact False.elim (startAux_ne_cell hb.2 (by decide) (he.trans hs))
      · exact False.elim (startAux_ne_cell (by have := hb.2; omega) (by decide) (he.trans hs))

/-- The auxiliary end variable appears only in its own end block. -/
theorem endNeighborhood_complete {W m k : Nat} {odd : Bool}
    (bits : Nat → Nat → Bool×Bool)
    (b : GridBlock) (hb : b.Valid W m) (l : Literal) (hl : l ∈ (b.formula W bits).flatten)
    (he : cellOff W (columnIndex k odd) W+1 = l.var) : b = .finish k odd := by
  cases b with
  | start k' odd' =>
    rcases start_literal hl with hs | hs
    · have hh := column_position_eq (p := 1+9*W+1) (p' := 0)
        (show 1+9*W+1 < colLen W by unfold colLen; omega) (show 0 < colLen W by unfold colLen; omega)
        (by simpa only [cellOff,Nat.add_assoc,Nat.add_zero] using he.trans hs)
      omega
    · have hh := column_position_eq (p := 1+9*W+1) (p' := 1)
        (show 1+9*W+1 < colLen W by unfold colLen; omega) (show 1 < colLen W by unfold colLen; omega)
        (by simpa only [cellOff,Nat.add_assoc] using he.trans hs)
      omega
  | finish k' odd' =>
    rcases end_literal hl with hs | hs
    · have hh := column_position_eq (p := 1+9*W+1) (p' := 1+9*W)
        (show 1+9*W+1 < colLen W by unfold colLen; omega) (show 1+9*W < colLen W by unfold colLen; omega)
        (by simpa only [cellOff,Nat.add_assoc] using he.trans hs)
      omega
    · have hj := (column_position_eq (p := 1+9*W+1) (p' := 1+9*W+1)
        (show 1+9*W+1 < colLen W by unfold colLen; omega) (show 1+9*W+1 < colLen W by unfold colLen; omega)
        (by simpa only [cellOff,Nat.add_assoc] using he.trans hs)).1
      obtain ⟨hk,ho⟩ := columnIndex_injective hj
      subst k'; subst odd'; rfl
  | cell k' idx' odd' =>
    obtain ⟨p,hp,hvar⟩ := cell_literal_position hl
    exact False.elim (endAux_ne_cell hb.2 (by omega) (he.trans hvar))
  | rainbow k' v odd' =>
    cases odd'
    · rcases rainbowEven_literal hl with hs | hs
      · exact False.elim (endAux_ne_cell hb.2 (by decide) (he.trans hs))
      · exact False.elim (endAux_ne_cell (by have := hb.2; omega) (by decide) (he.trans hs))
    · rcases rainbowOdd_literal hl with hs | hs
      · exact False.elim (endAux_ne_cell hb.2 (by decide) (he.trans hs))
      · exact False.elim (endAux_ne_cell (by have := hb.2; omega) (by decide) (he.trans hs))

def cellNeighborhood (W k idx : Nat) (odd : Bool) (p : Nat) : List GridBlock :=
  if p = 0 then chainNeighborhood W k idx odd
  else if p = 9 then chainNeighborhood W k (idx+1) odd
  else interiorNeighborhood W k idx odd p

def startNeighborhood (W k : Nat) (odd : Bool) (p : Nat) : List GridBlock :=
  if p = 0 then [.start k odd] else chainNeighborhood W k 0 odd

def endNeighborhood (W k : Nat) (odd : Bool) (p : Nat) : List GridBlock :=
  if p = 0 then chainNeighborhood W k W odd else [.finish k odd]

def rainbowNeighborhood (W k v : Nat) (odd : Bool) (p : Nat) : List GridBlock :=
  if odd then
    if p = 0 then cellNeighborhood W (k+1) v false 1
    else cellNeighborhood W k (W-1-v) true 8
  else if p = 0 then cellNeighborhood W k v false 8
    else cellNeighborhood W k (W-1-v) true 1

theorem cellNeighborhood_complete {W m k idx p : Nat} {odd : Bool}
    (bits : Nat → Nat → Bool×Bool) (hi : idx < W) (hp : p < 10)
    (b : GridBlock) (hb : b.Valid W m) (l : Literal) (hl : l ∈ (b.formula W bits).flatten)
    (he : cellOff W (columnIndex k odd) idx+p = l.var) :
    b ∈ cellNeighborhood W k idx odd p := by
  by_cases hp0 : p=0
  · subst p
    simp only [cellNeighborhood,ite_true]
    exact chainNeighborhood_complete bits (by omega) b hb l hl (by simpa using he)
  · by_cases hp9 : p=9
    · subst p
      simp only [cellNeighborhood,show (9:Nat)≠0 by decide,ite_false,ite_true]
      apply chainNeighborhood_complete bits (by omega) b hb l hl
      simpa only [cellOff,Nat.mul_add,Nat.mul_one,Nat.add_assoc] using he
    · simp only [cellNeighborhood,hp0,hp9,ite_false]
      exact interiorNeighborhood_complete bits hi (by omega) (by omega) b hb l hl he

theorem startNeighborhood_cover {W m k p : Nat} {odd : Bool}
    (bits : Nat → Nat → Bool×Bool) (hp : p < 2)
    (b : GridBlock) (hb : b.Valid W m) (l : Literal) (hl : l ∈ (b.formula W bits).flatten)
    (he : colBase W (columnIndex k odd)+p = l.var) :
    b ∈ startNeighborhood W k odd p := by
  by_cases hp0 : p=0
  · subst p
    have hb' := startNeighborhood_complete bits b hb l hl (by simpa using he)
    simp [startNeighborhood,hb']
  · have hp1 : p=1 := by omega
    subst p
    simp only [startNeighborhood,show (1:Nat)≠0 by decide,ite_false]
    apply chainNeighborhood_complete bits (Nat.zero_le _) b hb l hl
    simpa only [cellOff,Nat.mul_zero,Nat.add_zero] using he

theorem endNeighborhood_cover {W m k p : Nat} {odd : Bool}
    (bits : Nat → Nat → Bool×Bool) (hp : p < 2)
    (b : GridBlock) (hb : b.Valid W m) (l : Literal) (hl : l ∈ (b.formula W bits).flatten)
    (he : cellOff W (columnIndex k odd) W+p = l.var) :
    b ∈ endNeighborhood W k odd p := by
  by_cases hp0 : p=0
  · subst p
    simp only [endNeighborhood,ite_true]
    exact chainNeighborhood_complete bits (Nat.le_refl _) b hb l hl (by simpa using he)
  · have hp1 : p=1 := by omega
    subst p
    have hb' := endNeighborhood_complete bits b hb l hl he
    simp [endNeighborhood,hb']

theorem interiorNeighborhood_nodup (W k idx : Nat) (odd : Bool) (p : Nat) :
    (interiorNeighborhood W k idx odd p).Nodup := by
  unfold interiorNeighborhood
  split <;> split <;> simp_all
  split <;> simp

theorem chainNeighborhood_nodup (W k idx : Nat) (odd : Bool) :
    (chainNeighborhood W k idx odd).Nodup := by
  unfold chainNeighborhood
  by_cases hi : 0<idx <;> by_cases hz : idx=0 <;> by_cases hw : idx=W <;>
    simp_all <;> omega

theorem cellNeighborhood_nodup (W k idx : Nat) (odd : Bool) (p : Nat) :
    (cellNeighborhood W k idx odd p).Nodup := by
  unfold cellNeighborhood
  split
  · exact chainNeighborhood_nodup W k idx odd
  · split
    · exact chainNeighborhood_nodup W k (idx+1) odd
    · exact interiorNeighborhood_nodup W k idx odd p

theorem startNeighborhood_nodup (W k : Nat) (odd : Bool) (p : Nat) :
    (startNeighborhood W k odd p).Nodup := by
  unfold startNeighborhood
  split
  · simp
  · exact chainNeighborhood_nodup W k 0 odd

theorem endNeighborhood_nodup (W k : Nat) (odd : Bool) (p : Nat) :
    (endNeighborhood W k odd p).Nodup := by
  unfold endNeighborhood
  split
  · exact chainNeighborhood_nodup W k W odd
  · simp

theorem rainbowNeighborhood_nodup (W k v : Nat) (odd : Bool) (p : Nat) :
    (rainbowNeighborhood W k v odd p).Nodup := by
  unfold rainbowNeighborhood
  split <;> split <;> apply cellNeighborhood_nodup

def rainbowVariable (W k v : Nat) (odd : Bool) (p : Nat) : Nat :=
  if odd then
    if p = 0 then cellOff W (columnIndex (k+1) false) v+1
    else cellOff W (columnIndex k true) (W-1-v)+8
  else if p = 0 then cellOff W (columnIndex k false) v+8
    else cellOff W (columnIndex k true) (W-1-v)+1

theorem rainbowNeighborhood_cover {W m k v p : Nat} {odd : Bool}
    (bits : Nat → Nat → Bool×Bool) (hv : v<W) (_hp : p<2)
    (b : GridBlock) (hb : b.Valid W m) (l : Literal) (hl : l ∈ (b.formula W bits).flatten)
    (he : rainbowVariable W k v odd p = l.var) :
    b ∈ rainbowNeighborhood W k v odd p := by
  cases odd <;> by_cases hp0 : p=0 <;>
    simp only [rainbowVariable,rainbowNeighborhood,Bool.false_eq_true,ite_false,ite_true,hp0] at he ⊢
  · exact cellNeighborhood_complete bits hv (by decide) b hb l hl he
  · exact cellNeighborhood_complete bits (by omega) (by decide) b hb l hl he
  · exact cellNeighborhood_complete bits hv (by decide) b hb l hl he
  · exact cellNeighborhood_complete bits (by omega) (by decide) b hb l hl he

end STACS2027.PlanarSource.RotationTable

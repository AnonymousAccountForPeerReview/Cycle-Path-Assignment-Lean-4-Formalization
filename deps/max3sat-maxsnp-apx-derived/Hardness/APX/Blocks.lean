module

public import Hardness.MaxSNP.Main
public import PT.SAT
public import PT.List
import Mathlib.Tactic.Linarith

/-!
# Balanced disjoint unions of formulas

`blockUnion fs` is a formula made of one *block* for every formula `φ_i` of the list `fs`: the
variables of `φ_i` are shifted by `i * W`, where `W = maxVar fs` bounds the variables of all
formulas, so that the blocks have pairwise disjoint variables, and the shifted formula is
repeated `m / |φ_i|` times, where `m = maxLen fs` is the greatest number of clauses, so that
every (nonempty) block has more than `m / 2` and at most `m` clauses.

The main result is `blockUnion_gap`: if an assignment `y` of `blockUnion fs` is within the
factor `1 + 1 / (C + 1)` of the optimum and `C + 1 ≥ 2 * |fs| * den`, then the restriction
`y.drop (j * W)` of `y` to the block of a *satisfiable* formula `φ_j` leaves fewer than the
fraction `num / den` of the clauses of `φ_j` unsatisfied.
-/

@[expose] public section

set_option linter.dupNamespace false

namespace Complexity

open Complexity.PT

namespace SAT

/-- Shift the variables of a clause by `o`. -/
def shiftClause (o : Nat) (cl : Clause) : Clause := cl.map fun l => ⟨l.var + o, l.positive⟩

/-- Shift the variables of a formula by `o`. -/
def shiftCNF (o : Nat) (f : CNF) : CNF := f.map (shiftClause o)

theorem evalClause_shiftClause (a : Assignment) (o : Nat) (cl : Clause) :
    evalClause a (shiftClause o cl) = evalClause (fun v => a (v + o)) cl := by
  induction cl with
  | nil => rfl
  | cons l cl ih =>
    simp only [shiftClause, List.map_cons, evalClause_cons] at ih ⊢
    rw [ih]
    rfl

theorem satCount_shiftCNF (a : Assignment) (o : Nat) (f : CNF) :
    satCount a (shiftCNF o f) = satCount (fun v => a (v + o)) f := by
  simp only [satCount, shiftCNF, List.countP_map]
  congr 1
  funext cl
  exact evalClause_shiftClause a o cl

theorem assignmentOf_drop (y : Word) (o v : Nat) :
    assignmentOf (y.drop o) v = assignmentOf y (v + o) := by
  simp [assignmentOf, List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.add_comm]

theorem satCount_append (a : Assignment) (f g : CNF) :
    satCount a (f ++ g) = satCount a f + satCount a g := List.countP_append

theorem satCount_flatten_replicate (a : Assignment) (r : Nat) (f : CNF) :
    satCount a (List.replicate r f).flatten = r * satCount a f := by
  induction r with
  | zero => simp [satCount]
  | succ r ih =>
    rw [List.replicate_succ, List.flatten_cons, satCount_append, ih, Nat.succ_mul, Nat.add_comm]

end SAT

/-! ### Maxima of lists -/

theorem le_foldl_max_init (l : List Nat) (s : Nat) : s ≤ l.foldl max s := by
  induction l generalizing s with
  | nil => exact Nat.le_refl _
  | cons a l ih => exact Nat.le_trans (Nat.le_max_left s a) (ih _)

theorem le_foldl_max {l : List Nat} {x : Nat} (h : x ∈ l) (s : Nat) : x ≤ l.foldl max s := by
  induction l generalizing s with
  | nil => simp at h
  | cons a l ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_trans (Nat.le_max_right s x) (le_foldl_max_init l _)
    · exact ih h _

/-! ### Blocks -/

/-- The greatest number of clauses of a formula of the list. -/
def maxLen (fs : List SAT.CNF) : Nat := (fs.map List.length).foldl max 0

/-- A strict bound on the variables of the formulas of the list. -/
def maxVar (fs : List SAT.CNF) : Nat := (fs.map SAT.variableBound).foldl max 0

/-- The block of the formula `q.1` with index `q.2`: its variables are shifted by `q.2 * W`
and the result is repeated `m / |q.1|` times. -/
def block (m W : Nat) (q : SAT.CNF × Nat) : SAT.CNF :=
  (List.replicate (m / q.1.length) (SAT.shiftCNF (q.2 * W) q.1)).flatten

/-- The union of the blocks of the formulas of `fs`. -/
def blockUnion (fs : List SAT.CNF) : SAT.CNF :=
  fs.zipIdx.flatMap (block (maxLen fs) (maxVar fs))

theorem length_le_maxLen {fs : List SAT.CNF} {f : SAT.CNF} (h : f ∈ fs) :
    f.length ≤ maxLen fs :=
  le_foldl_max (List.mem_map.mpr ⟨f, h, rfl⟩) 0

theorem variableBound_le_maxVar {fs : List SAT.CNF} {f : SAT.CNF} (h : f ∈ fs) :
    SAT.variableBound f ≤ maxVar fs :=
  le_foldl_max (List.mem_map.mpr ⟨f, h, rfl⟩) 0

theorem satCount_block (a : SAT.Assignment) (m W : Nat) (f : SAT.CNF) (i : Nat) :
    SAT.satCount a (block m W (f, i)) =
      m / f.length * SAT.satCount (fun v => a (v + i * W)) f := by
  rw [block, SAT.satCount_flatten_replicate, SAT.satCount_shiftCNF]

theorem length_block_le (m W : Nat) (q : SAT.CNF × Nat) : (block m W q).length ≤ m := by
  have h : ∀ r (g : SAT.CNF), (List.replicate r g).flatten.length = r * g.length := by
    intro r g
    induction r with
    | zero => simp
    | succ r ih => rw [List.replicate_succ, List.flatten_cons, List.length_append, ih,
        Nat.succ_mul, Nat.add_comm]
  rw [block, h, SAT.shiftCNF, List.length_map]
  exact Nat.div_mul_le_self m _

/-- The clauses of a block are shifted clauses of its formula. -/
theorem mem_block {m W : Nat} {q : SAT.CNF × Nat} {cl : SAT.Clause} (h : cl ∈ block m W q) :
    ∃ cl' ∈ q.1, cl = SAT.shiftClause (q.2 * W) cl' := by
  simp only [block, List.mem_flatten, List.mem_replicate] at h
  obtain ⟨g, ⟨-, rfl⟩, hcl⟩ := h
  obtain ⟨cl', hcl', rfl⟩ := List.mem_map.mp hcl
  exact ⟨cl', hcl', rfl⟩

/-- The variables of the block with index `i` lie in `[i * W, (i + 1) * W)`. -/
theorem var_of_mem_block {m W : Nat} {q : SAT.CNF × Nat} {cl : SAT.Clause} {l : SAT.Literal}
    (hW : SAT.variableBound q.1 ≤ W) (h : cl ∈ block m W q) (hl : l ∈ cl) :
    q.2 * W ≤ l.var ∧ l.var < (q.2 + 1) * W := by
  obtain ⟨cl', hcl', rfl⟩ := mem_block h
  obtain ⟨l', hl', rfl⟩ := List.mem_map.mp hl
  have := SAT.literal_lt_variableBound hcl' hl'
  show q.2 * W ≤ l'.var + q.2 * W ∧ l'.var + q.2 * W < (q.2 + 1) * W
  rw [Nat.succ_mul]
  omega

theorem isThreeCNF_blockUnion {fs : List SAT.CNF} (h : ∀ f ∈ fs, SAT.IsThreeCNF f) :
    SAT.IsThreeCNF (blockUnion fs) := by
  intro cl hcl
  obtain ⟨q, hq, hcl⟩ := List.mem_flatMap.mp hcl
  obtain ⟨cl', hcl', rfl⟩ := mem_block hcl
  obtain ⟨f, i⟩ := q
  have hf : f ∈ fs := by
    obtain ⟨-, -, hf⟩ := List.mem_zipIdx hq
    rw [hf]
    exact List.getElem_mem _
  rw [SAT.shiftClause, List.length_map]
  exact h f hf cl' hcl'

theorem length_blockUnion_le (fs : List SAT.CNF) :
    (blockUnion fs).length ≤ fs.length * maxLen fs := by
  rw [blockUnion, List.length_flatMap]
  have := sum_map_le_mul (l := fs.zipIdx) (g := fun q => (block (maxLen fs) (maxVar fs) q).length)
    (K := maxLen fs) fun q _ => length_block_le _ _ q
  simpa using this

/-- Splitting the indexed list at the position `j`. -/
theorem zipIdx_split {α : Type} {fs : List α} {j : Nat} {φ : α} (h : fs[j]? = some φ) :
    fs.zipIdx = (fs.take j).zipIdx ++ (φ, j) :: (fs.drop (j + 1)).zipIdx (j + 1) := by
  obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.mp h
  conv_lhs => rw [← List.take_append_drop j fs, List.drop_eq_getElem_cons hj]
  rw [List.zipIdx_append, List.zipIdx_cons, List.length_take_of_le (Nat.le_of_lt hj),
    Nat.zero_add]

/-- **The gap lemma for balanced unions.** If `y` is within the factor `1 + 1 / (C + 1)` of
the optimum `opt'` of `blockUnion fs`, where `C + 1 ≥ 2 * |fs| * den`, and the formula `φ` at
position `j` is nonempty and satisfiable, then the restriction of `y` to the block of `φ`
satisfies more than the fraction `1 - num / den` of the clauses of `φ`. -/
theorem blockUnion_gap {fs : List SAT.CNF} {j : Nat} {φ : SAT.CNF} (hj : fs[j]? = some φ)
    (hne : φ ≠ []) (hsat : SAT.Satisfiable φ) (y : Word) {num den C opt' : Nat}
    (hnum : 0 < num) (hC : 2 * fs.length * den ≤ C + 1)
    (hopt : ∀ y' : Word, SAT.satCount (SAT.assignmentOf y') (blockUnion fs) ≤ opt')
    (hr : (C + 1) * opt' ≤ (C + 2) * SAT.satCount (SAT.assignmentOf y) (blockUnion fs)) :
    den * φ.length <
      den * SAT.satCount (SAT.assignmentOf (y.drop (j * maxVar fs))) φ + num * φ.length := by
  have hmem : φ ∈ fs := List.mem_of_getElem? hj
  have hL : 0 < fs.length := List.length_pos_of_mem hmem
  have hn : 0 < φ.length := List.length_pos_iff.mpr hne
  have hnm : φ.length ≤ maxLen fs := length_le_maxLen hmem
  have hlenU := Nat.le_trans (SAT.satCount_le_length (SAT.assignmentOf y) (blockUnion fs))
    (length_blockUnion_le fs)
  obtain ⟨a, ha⟩ := hsat
  -- the assignment that agrees with `a` on the block of `φ` and with `y` elsewhere
  let a' : SAT.Assignment := fun v =>
    if j * maxVar fs ≤ v ∧ v < (j + 1) * maxVar fs then a (v - j * maxVar fs)
    else SAT.assignmentOf y v
  obtain ⟨y', hy'⟩ := SAT.exists_word_assignment a' (blockUnion fs)
  have h1 := hopt y'
  rw [SAT.satCount_congr hy'] at h1
  have hsplit : blockUnion fs =
      (fs.take j).zipIdx.flatMap (block (maxLen fs) (maxVar fs)) ++
        (block (maxLen fs) (maxVar fs) (φ, j) ++
          ((fs.drop (j + 1)).zipIdx (j + 1)).flatMap (block (maxLen fs) (maxVar fs))) := by
    rw [blockUnion, zipIdx_split hj, List.flatMap_append, List.flatMap_cons]
  have hpre : SAT.satCount a' ((fs.take j).zipIdx.flatMap (block (maxLen fs) (maxVar fs))) =
      SAT.satCount (SAT.assignmentOf y)
        ((fs.take j).zipIdx.flatMap (block (maxLen fs) (maxVar fs))) := by
    refine SAT.satCount_congr fun cl hcl l hl => ?_
    obtain ⟨⟨f, i⟩, hq, hcl⟩ := List.mem_flatMap.mp hcl
    obtain ⟨-, hi, hf⟩ := List.mem_zipIdx hq
    have hf : f ∈ fs := by
      rw [hf]
      exact List.mem_of_mem_take (List.getElem_mem _)
    have hv : l.var < (i + 1) * maxVar fs :=
      (var_of_mem_block (variableBound_le_maxVar hf) hcl hl).2
    have hij : (i + 1) * maxVar fs ≤ j * maxVar fs := by
      refine Nat.mul_le_mul_right _ ?_
      have := List.length_take_le j fs
      omega
    show (if j * maxVar fs ≤ l.var ∧ l.var < (j + 1) * maxVar fs then _ else _) = _
    rw [ite_eq_right (by omega)]
  have hpost : SAT.satCount a'
      (((fs.drop (j + 1)).zipIdx (j + 1)).flatMap (block (maxLen fs) (maxVar fs))) =
      SAT.satCount (SAT.assignmentOf y)
        (((fs.drop (j + 1)).zipIdx (j + 1)).flatMap (block (maxLen fs) (maxVar fs))) := by
    refine SAT.satCount_congr fun cl hcl l hl => ?_
    obtain ⟨⟨f, i⟩, hq, hcl⟩ := List.mem_flatMap.mp hcl
    obtain ⟨hi, -, hf⟩ := List.mem_zipIdx hq
    have hf : f ∈ fs := by
      rw [hf]
      exact List.mem_of_mem_drop (List.getElem_mem _)
    have hv : i * maxVar fs ≤ l.var :=
      (var_of_mem_block (variableBound_le_maxVar hf) hcl hl).1
    have hij : (j + 1) * maxVar fs ≤ i * maxVar fs := Nat.mul_le_mul_right _ hi
    show (if j * maxVar fs ≤ l.var ∧ l.var < (j + 1) * maxVar fs then _ else _) = _
    rw [ite_eq_right (by omega)]
  have hB' : SAT.satCount a' (block (maxLen fs) (maxVar fs) (φ, j)) =
      maxLen fs / φ.length * φ.length := by
    rw [satCount_block, ← SAT.satCount_eq_length ha]
    congr 1
    refine SAT.satCount_congr fun cl hcl l hl => ?_
    have h2 := SAT.literal_lt_variableBound hcl hl
    have h3 := variableBound_le_maxVar hmem
    show (if j * maxVar fs ≤ l.var + j * maxVar fs ∧ l.var + j * maxVar fs < (j + 1) * maxVar fs
      then a (l.var + j * maxVar fs - j * maxVar fs) else _) = _
    rw [ite_eq_left (by rw [Nat.succ_mul]; omega), Nat.add_sub_cancel]
  have hB : SAT.satCount (SAT.assignmentOf y) (block (maxLen fs) (maxVar fs) (φ, j)) =
      maxLen fs / φ.length *
        SAT.satCount (SAT.assignmentOf (y.drop (j * maxVar fs))) φ := by
    rw [satCount_block]
    congr 1
    exact SAT.satCount_congr fun cl _ l _ => (SAT.assignmentOf_drop y _ _).symm
  rw [hsplit, SAT.satCount_append, SAT.satCount_append, hpre, hpost, hB'] at h1
  rw [hsplit, SAT.satCount_append, SAT.satCount_append, hB] at hr hlenU
  -- arithmetic
  have hs := SAT.satCount_le_length (SAT.assignmentOf (y.drop (j * maxVar fs))) φ
  have hr1 : 1 ≤ maxLen fs / φ.length := Nat.div_pos hnm hn
  have hm : maxLen fs < φ.length * (maxLen fs / φ.length + 1) := Nat.lt_mul_div_succ _ hn
  generalize SAT.satCount (SAT.assignmentOf (y.drop (j * maxVar fs))) φ = s at *
  generalize SAT.satCount (SAT.assignmentOf y)
    ((fs.take j).zipIdx.flatMap (block (maxLen fs) (maxVar fs))) = A1 at *
  generalize SAT.satCount (SAT.assignmentOf y)
    (((fs.drop (j + 1)).zipIdx (j + 1)).flatMap (block (maxLen fs) (maxVar fs))) = A2 at *
  generalize maxLen fs / φ.length = r at *
  generalize maxLen fs = m at *
  generalize φ.length = n at *
  generalize fs.length = L at *
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hs
  have e1 : (C + 1) * (r * d) ≤ L * m := by
    have := Nat.mul_le_mul_left (C + 1) h1
    nlinarith
  have e2 : L * m < L * (2 * (r * (s + d))) := by
    refine Nat.mul_lt_mul_of_pos_left ?_ hL
    nlinarith
  have e3 : (C + 1) * d < 2 * L * (s + d) := by
    have : r * ((C + 1) * d) < r * (2 * L * (s + d)) := by nlinarith
    exact Nat.lt_of_mul_lt_mul_left this
  have e4 : 2 * L * den * d ≤ (C + 1) * d := Nat.mul_le_mul_right d hC
  have e5 : s + d ≤ num * (s + d) := Nat.le_mul_of_pos_left _ hnum
  have e6 : 2 * L * (den * d) < 2 * L * (num * (s + d)) := by nlinarith
  have := Nat.lt_of_mul_lt_mul_left e6
  rw [Nat.mul_add]
  omega

/-! ### Polynomial time -/

@[fun_prop] protected theorem PT.shiftCNF {α : Type} [Code α] {o : α → Nat} {f : α → SAT.CNF}
    (ho : PT o) (hf : PT f) : PT (fun a => SAT.shiftCNF (o a) (f a)) := by
  unfold SAT.shiftCNF SAT.shiftClause
  fun_prop

@[fun_prop] protected theorem PT.maxLen {α : Type} [Code α] {fs : α → List SAT.CNF}
    (h : PT fs) : PT (fun a => maxLen (fs a)) := by
  unfold maxLen
  fun_prop

@[fun_prop] protected theorem PT.maxVar {α : Type} [Code α] {fs : α → List SAT.CNF}
    (h : PT fs) : PT (fun a => maxVar (fs a)) := by
  unfold maxVar
  fun_prop

@[fun_prop] protected theorem PT.blockUnion {α : Type} [Code α] {fs : α → List SAT.CNF}
    (h : PT fs) : PT (fun a => blockUnion (fs a)) := by
  unfold blockUnion block
  fun_prop

end Complexity

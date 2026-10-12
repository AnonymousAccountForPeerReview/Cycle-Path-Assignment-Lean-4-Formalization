module

public import PT.All

/-!
# Zero-delimited unary words and the list programs of the expander extraction

Plain-list side of `Hardness/Expander`: the serialisation of lists of numbers used by the
vendored machines (`unaryWords`), its polynomial-time parser (`parseWords`), the input table fed
to the vendored overlay machine (`inputWords`) and the program reading the neighbour lists off
its output table (`extract`). Nothing here depends on the vendored development.
-/

@[expose] public section

namespace Complexity.Expander

open Complexity Complexity.PT

/-- `n` ones followed by a zero. -/
def unaryWord (n : Nat) : Word := List.replicate n true ++ [false]

/-- Concatenation of the unary codes of a list of numbers. -/
def unaryWords (ws : List Nat) : Word := ws.flatMap unaryWord

/-- One step of the parser: state `(numbers read so far, reversed; current count)`. -/
def parseStep (s : List Nat × Nat) (b : Bool) : List Nat × Nat :=
  if b then (s.1, s.2 + 1) else (s.2 :: s.1, 0)

/-- Parser for `unaryWords`. -/
def parseWords (w : Word) : List Nat := (w.foldl parseStep ([], 0)).1.reverse

theorem foldl_parseStep_replicate (n : Nat) (acc : List Nat) (c : Nat) :
    (List.replicate n true).foldl parseStep (acc, c) = (acc, c + n) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, List.foldl_cons]
    have : parseStep (acc, c) true = (acc, c + 1) := rfl
    rw [this, ih]
    congr 1
    omega

theorem foldl_parseStep_unaryWords (ws acc : List Nat) :
    (unaryWords ws).foldl parseStep (acc, 0) = (ws.reverse ++ acc, 0) := by
  induction ws generalizing acc with
  | nil => rfl
  | cons n ws ih =>
    have h : unaryWords (n :: ws) = List.replicate n true ++ false :: unaryWords ws := by
      simp [unaryWords, unaryWord]
    rw [h, List.foldl_append, foldl_parseStep_replicate, List.foldl_cons]
    have : parseStep (acc, 0 + n) false = (n :: acc, 0) := by simp [parseStep]
    rw [this, ih]
    simp

@[simp] theorem parseWords_unaryWords (ws : List Nat) : parseWords (unaryWords ws) = ws := by
  simp [parseWords, foldl_parseStep_unaryWords]

theorem unaryWords_cons (n : Nat) (ws : List Nat) :
    unaryWords (n :: ws) = List.replicate n true ++ false :: unaryWords ws := by
  simp [unaryWords, unaryWord]

/-- The first number of a serialised list is its number of leading ones. -/
theorem takeWhile_unaryWords_cons (n : Nat) (ws : List Nat) :
    ((unaryWords (n :: ws)).takeWhile id).length = n := by
  rw [unaryWords_cons]
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ]

protected theorem PT.unaryWords : PT unaryWords := by
  unfold unaryWords unaryWord
  fun_prop

protected theorem PT.parseWords : PT parseWords := by
  unfold parseWords
  have h : PT (fun w : Word => w.foldl parseStep ([], 0)) := by
    refine PT.foldl_of_add_le (f := fun _ (s : List Nat × Nat) (b : Bool) => parseStep s b)
      (init := fun _ => (([] : List Nat), 0)) (l := fun w : Word => w)
      (by unfold parseStep; fun_prop) (by fun_prop) (by fun_prop)
      (fun _ => 2) (PolynomialBound.constant 2) ?_
    intro w s b _
    unfold parseStep
    split <;> simp only [size_prod, size_cons, size_nat] <;> omega
  fun_prop

/-! ### The input table and the extraction program -/

/-- The words of the port table on `k` vertices with one self-reversing port per vertex and
all-zero relations of length `r`: header `[k, k * 1]`, then one row `[v, v, 0, …, 0]` per
vertex. -/
def inputWords (r k : Nat) : List Nat :=
  [k, k * 1] ++ (List.range k).flatMap fun v => [v, v] ++ List.replicate r 0

/-- Read the neighbour lists off the words `[n, n * (d + q)] ++ rows` of a port table with
`d + q` ports, each row consisting of `r + 2` words whose second word is the index
`p' + (d + q) * v'` of the reverse dart: vertex `v` gets the tails `v'` of the reverses of its
ports `d, …, d + q - 1`. -/
def extract (r d q : Nat) (ws : List Nat) : List (List Nat) :=
  (List.range (ws.headD 0)).map fun v => (List.range q).map fun i =>
    ws.getD (2 + ((r + 2) * (d + i + (d + q) * v) + 1)) 0 / (d + q)

/-- Entry `c * r + j` of a concatenation of blocks of length `c` is entry `j` of block `r`. -/
theorem getD_flatMap_of_length {α β : Type} (f : α → List β) (c : Nat) (l : List α)
    (hc : ∀ x ∈ l, (f x).length = c) (r j : Nat) (hr : r < l.length) (hj : j < c) (d : β) :
    (l.flatMap f).getD (c * r + j) d = (f l[r]).getD j d := by
  induction l generalizing r with
  | nil => simp at hr
  | cons x l ih =>
    have hx : (f x).length = c := hc x (by simp)
    rw [List.flatMap_cons]
    cases r with
    | zero =>
      simp only [Nat.mul_zero, Nat.zero_add, List.getElem_cons_zero]
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
        List.getD_eq_getElem?_getD]
    | succ r =>
      have hidx : c * (r + 1) + j = (f x).length + (c * r + j) := by
        rw [hx, Nat.mul_succ]; omega
      rw [hidx, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
        Nat.add_sub_cancel_left, ← List.getD_eq_getElem?_getD]
      simp only [List.getElem_cons_succ]
      exact ih (fun y hy => hc y (by simp [hy])) r (by simpa using hr)

/-- `extract` on the words of a port table whose row `p + (d + q) * v` stores, as its second
word, the reverse index `p' + (d + q) * g v i` for the ports `p = d + i`. -/
theorem extract_flatMap {α : Type} (r d q n m : Nat) (l : List α) (f : α → List Nat)
    (hf : ∀ x ∈ l, (f x).length = r + 2) (g : Nat → Nat → Nat)
    (h : ∀ v, v < n → ∀ i, i < q → ∃ (hlt : d + i + (d + q) * v < l.length) (p : Nat),
      p < d + q ∧ (f l[d + i + (d + q) * v]).getD 1 0 = p + (d + q) * g v i) :
    extract r d q ([n, m] ++ l.flatMap f) =
      (List.range n).map fun v => (List.range q).map fun i => g v i := by
  unfold extract
  simp only [List.cons_append, List.nil_append, List.headD_cons]
  refine List.map_congr_left fun v hv => List.map_congr_left fun i hi => ?_
  obtain ⟨hlt, p, hp, hrow⟩ := h v (List.mem_range.mp hv) i (List.mem_range.mp hi)
  have h2 : (n :: m :: l.flatMap f).getD (2 + ((r + 2) * (d + i + (d + q) * v) + 1)) 0 =
      (l.flatMap f).getD ((r + 2) * (d + i + (d + q) * v) + 1) 0 := by
    rw [Nat.add_comm 2]
    simp [List.getD_eq_getElem?_getD]
  rw [h2, getD_flatMap_of_length f (r + 2) l hf _ 1 hlt (by omega), hrow,
    Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hp, Nat.zero_add]

protected theorem PT.inputWords (r : Nat) : PT (inputWords r) := by
  unfold inputWords
  fun_prop

protected theorem PT.extract (r d q : Nat) : PT (extract r d q) := by
  unfold extract
  fun_prop

end Complexity.Expander

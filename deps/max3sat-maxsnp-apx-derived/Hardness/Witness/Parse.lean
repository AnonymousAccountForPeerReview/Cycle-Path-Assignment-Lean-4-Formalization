module

public import PT.All

/-!
# Total parsers and iteration helpers for the witness decoder

Everything here is plain list programming in the `PT` framework (no vendored definitions):

* `unaryWords w`: the list of numbers of a zero-delimited unary code (`n` ones followed by a
  zero for every number `n`), computed by one left fold; `unaryWords_code` inverts the code
  `ns.flatMap fun n => replicate n true ++ [false]`, and `pt_unaryWords`.
* `column ws off r cnt`: the entries `ws[off + r * e]`, `e < cnt` (one column of a table stored
  row by row with rows of `r` words after a header of `off` words); `getD_flatMap_of_length`
  is the index computation for such tables.
* `iterList B k w`: the pair `(B^[k] w, [w, B w, …, B^[k-1] w])`, computed by iterating
  `iterStep B`; `pt_iterList` under a polynomial bound on the lengths of the iterates.
-/

@[expose] public section

set_option linter.dupNamespace false

namespace Complexity.WitnessDecode

open Complexity.PT Complexity.PT.Code

/-! ### Unary codes -/

/-- One step of the unary parser: a `true` increments the current number, a `false` closes it. -/
def unaryStep (s : Nat × List Nat) (b : Bool) : Nat × List Nat :=
  if b then (s.1 + 1, s.2) else (0, s.2 ++ [s.1])

/-- The zero-delimited unary code of a list of numbers. -/
def unaryCode (ns : List Nat) : Word := ns.flatMap fun n => List.replicate n true ++ [false]

/-- The numbers of a zero-delimited unary code (a trailing unfinished number is dropped). -/
def unaryWords (w : Word) : List Nat := (w.foldl unaryStep (0, [])).2

theorem foldl_unaryStep_replicate (n c : Nat) (acc : List Nat) :
    (List.replicate n true).foldl unaryStep (c, acc) = (c + n, acc) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, List.foldl_cons]
    simp only [unaryStep, ↓reduceIte]
    rw [ih]
    congr 1
    omega

theorem foldl_unaryStep_code (ns : List Nat) (acc : List Nat) :
    (unaryCode ns).foldl unaryStep (0, acc) = (0, acc ++ ns) := by
  induction ns generalizing acc with
  | nil => simp [unaryCode]
  | cons n ns ih =>
    have h : unaryCode (n :: ns) = (List.replicate n true ++ [false]) ++ unaryCode ns := by
      simp [unaryCode]
    rw [h, List.foldl_append, List.foldl_append, foldl_unaryStep_replicate]
    simp only [List.foldl_cons, List.foldl_nil, unaryStep, Bool.false_eq_true, ↓reduceIte,
      Nat.zero_add]
    rw [ih]
    simp

@[simp] theorem unaryWords_code (ns : List Nat) : unaryWords (unaryCode ns) = ns := by
  simp [unaryWords, foldl_unaryStep_code]

theorem unaryCode_append (ns ms : List Nat) :
    unaryCode (ns ++ ms) = unaryCode ns ++ unaryCode ms := by
  simp [unaryCode]

theorem sum_map_size_nat (l : List Nat) : (l.map size).sum = l.sum + l.length := by
  induction l with
  | nil => rfl
  | cons n l ih =>
    simp only [List.map_cons, List.sum_cons, size_nat, ih, List.length_cons]
    omega

/-- The potential `s.1 + Σ s.2 + |s.2|` grows by one per bit. -/
theorem foldl_unaryStep_potential (pre : Word) (s : Nat × List Nat) :
    (pre.foldl unaryStep s).1 + (pre.foldl unaryStep s).2.sum +
        (pre.foldl unaryStep s).2.length = s.1 + s.2.sum + s.2.length + pre.length := by
  induction pre generalizing s with
  | nil => simp
  | cons b pre ih =>
    rw [List.foldl_cons, ih]
    cases b <;> simp [unaryStep] <;> omega

theorem size_unaryState (s : Nat × List Nat) :
    size s ≤ 2 * (s.1 + s.2.sum + s.2.length) + 2 := by
  rw [size_prod, size_nat, size_list, sum_map_size_nat]
  omega

theorem pt_unaryWords : PT unaryWords := by
  have hstep : PT (fun p : Word × (Nat × List Nat) × Bool => unaryStep p.2.1 p.2.2) := by
    unfold unaryStep
    fun_prop
  have h := PT.foldl (f := fun _ s b => unaryStep s b) (init := fun _ => ((0 : Nat), ([] : List Nat)))
    (l := fun w : Word => w) hstep (PT.const _) PT.id (fun N => N + 1)
    (PolynomialBound.identity.add (PolynomialBound.constant 1)) ?_
  · exact (PT.snd h).of_eq fun w => rfl
  · intro w pre hpre
    show size (pre.foldl unaryStep (0, [])) ≤ size w + 1
    have h1 := foldl_unaryStep_potential pre (0, [])
    have h2 := size_unaryState (pre.foldl unaryStep (0, []))
    have h3 := hpre.length_le
    have h4 := size_word w
    simp only [List.sum_nil, List.length_nil] at h1
    omega

@[fun_prop] protected theorem PT.unaryWords {α : Type} [Code α] {w : α → Word} (hw : PT w) :
    PT (fun a => unaryWords (w a)) :=
  pt_unaryWords.comp hw

/-! ### Tables stored row by row -/

/-- Entry `off + r * e` of `ws` for `e < cnt`: one column of a table stored row by row, with
rows of `r` words after a header of `off` words. -/
def column (ws : List Nat) (off r cnt : Nat) : List Nat :=
  (List.range cnt).map fun e => ws.getD (off + r * e) 0

@[simp] theorem column_length (ws : List Nat) (off r cnt : Nat) :
    (column ws off r cnt).length = cnt := by
  simp [column]

theorem pt_column (r : Nat) :
    PT (fun p : List Nat × Nat × Nat => column p.1 p.2.1 r p.2.2) := by
  unfold column
  fun_prop

@[fun_prop] protected theorem PT.column {α : Type} [Code α] (r : Nat) {ws : α → List Nat}
    {off cnt : α → Nat} (hws : PT ws) (hoff : PT off) (hcnt : PT cnt) :
    PT (fun a => column (ws a) (off a) r (cnt a)) :=
  PT.comp₃ (h := fun ws off cnt => column ws off r cnt) (pt_column r) hws hoff hcnt

/-- Indexing into the concatenation of rows of a fixed length `r`. -/
theorem getD_flatMap_of_length {β : Type} (rows : List β) (f : β → List Nat) (r : Nat)
    (hr : ∀ b ∈ rows, (f b).length = r) (e j : Nat) (he : e < rows.length) (hj : j < r) :
    (rows.flatMap f).getD (r * e + j) 0 = (f (rows[e])).getD j 0 := by
  induction rows generalizing e with
  | nil => simp at he
  | cons b rows ih =>
    have hb : (f b).length = r := hr b (List.mem_cons_self ..)
    rw [List.flatMap_cons]
    cases e with
    | zero =>
      simp only [Nat.mul_zero, Nat.zero_add, List.getElem_cons_zero]
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
        ← List.getD_eq_getElem?_getD]
    | succ e =>
      have he' : e < rows.length := by simpa using he
      have := ih (fun b hb => hr b (List.mem_cons_of_mem _ hb)) e he'
      simp only [List.getElem_cons_succ]
      rw [← this, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_right (by rw [hb, Nat.mul_succ]; omega), hb]
      congr 2
      rw [Nat.mul_succ]
      omega

/-! ### Iteration with the list of intermediate values -/

/-- One step of `iterList`: apply `B` and remember the old value. -/
def iterStep (B : Word → Word) (s : Word × List Word) : Word × List Word := (B s.1, s.2 ++ [s.1])

/-- `(B^[k] w, [w, B w, …, B^[k-1] w])`. -/
def iterList (B : Word → Word) (k : Nat) (w : Word) : Word × List Word :=
  (iterStep B)^[k] (w, [])

theorem iterStep_iterate (B : Word → Word) (i : Nat) (w : Word) :
    (iterStep B)^[i] (w, []) = (B^[i] w, (List.range i).map fun j => B^[j] w) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [iterStep, List.range_succ, List.map_append, List.map_cons, List.map_nil]
    rw [Function.iterate_succ_apply']

theorem iterList_eq (B : Word → Word) (k : Nat) (w : Word) :
    iterList B k w = (B^[k] w, (List.range k).map fun j => B^[j] w) :=
  iterStep_iterate B k w

theorem size_map_words_le (ws : List Word) (K : Nat) (h : ∀ w ∈ ws, w.length ≤ K) :
    size ws ≤ ws.length * (2 * K + 2) + 1 := by
  have := size_map_le (l := ws) (g := fun w => w) (K := 2 * K + 1) (fun w hw => by
    rw [size_word]
    have := h w hw
    omega)
  simpa using this

/-- Iterating a polynomial-time word function a polynomial number of times, keeping all
intermediate values, is polynomial-time when all iterates have polynomially bounded length. -/
theorem pt_iterList {α : Type} [Code α] {B : Word → Word} (hB : PolyTime B) {w : α → Word}
    (hw : PT w) {k : α → Nat} (hk : PT k) (c e : Nat)
    (hsize : ∀ a i, i ≤ k a → (B^[i] (w a)).length ≤ powerBound c e (size a)) :
    PT (fun a => iterList B (k a) (w a)) := by
  obtain ⟨ck, ek, hke⟩ := hk.nat_le
  have hB' : PT B := PT.of_polyTime hB
  have hstep : PT (fun p : α × (Word × List Word) => iterStep B p.2) := by
    unfold iterStep
    fun_prop
  refine PT.iterate (step := fun _ s => iterStep B s) (init := fun a => (w a, [])) (n := k)
    hstep (by fun_prop) hk
    (fun N => (2 * powerBound c e N + 1) + (powerBound ck ek N * (2 * powerBound c e N + 2) + 1))
    (((PolynomialBound.constant 2).mul (PolynomialBound.power c e)).add
      (PolynomialBound.constant 1) |>.add
      (((PolynomialBound.power ck ek).mul (((PolynomialBound.constant 2).mul
        (PolynomialBound.power c e)).add (PolynomialBound.constant 2))).add
        (PolynomialBound.constant 1))) ?_
  intro a i hi
  show size ((iterStep B)^[i] (w a, [])) ≤ _
  rw [iterStep_iterate, size_pair, size_word]
  have h1 := hsize a i hi
  have h2 := size_map_words_le ((List.range i).map fun j => B^[j] (w a)) (powerBound c e (size a))
    (fun v hv => by
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hv
      exact hsize a j (by have := List.mem_range.mp hj; omega))
  have h3 := hke a
  simp only [List.length_map, List.length_range] at h2
  have h4 : i * (2 * powerBound c e (size a) + 2) ≤
      powerBound ck ek (size a) * (2 * powerBound c e (size a) + 2) :=
    Nat.mul_le_mul_right _ (by omega)
  omega

end Complexity.WitnessDecode

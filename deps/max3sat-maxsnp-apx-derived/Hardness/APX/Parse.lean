module

public import PT.SAT
public import PT.Raw
import Lean.Elab.Tactic.Omega

/-!
# A polynomial-time parser for formulas

`parseCNF : Word → SAT.CNF` is a total (lenient) parser with `parseCNF (SAT.encode f) = f`,
polynomial-time as a function of the raw word (`pt_parseCNF`). A word `x` is the code of a
formula exactly when `SAT.encode (parseCNF x) = x` (`encode_parseCNF_iff`), so instances of
problems on formulas can be recognized and decoded in polynomial time.

The parser iterates `clauseStep` (read one clause: its length in unary, then that many
literals by iterating `litStep`) as many times as the unary prefix of the word says.
-/

@[expose] public section

set_option linter.dupNamespace false

namespace Complexity

open Complexity.PT Complexity.Reg

/-! ### Unary prefixes -/

@[fun_prop] theorem pt_leadingOnes {α : Type} [Code α] {w : α → Word} (hw : PT w) :
    PT (fun a => leadingOnes (w a)) :=
  (PT.of_polyTime polyTime_leadingOnes).comp hw

@[fun_prop] theorem pt_afterOnes {α : Type} [Code α] {w : α → Word} (hw : PT w) :
    PT (fun a => afterOnes (w a)) :=
  (PT.of_polyTime polyTime_afterOnes).comp hw

theorem length_leadingOnes_le (w : Word) : (leadingOnes w).length ≤ w.length := by
  have := (stripOnes_length_le w 0).2
  simpa [leadingOnes] using this

theorem length_afterOnes_le (w : Word) : (afterOnes w).length ≤ w.length :=
  (stripOnes_length_le w 0).1

/-- Iterating a step that reads one item off the front of a word reads a sequence of items. -/
theorem iterate_writeValues {α : Type} (enc : α → Word)
    (step : List α × Word → List α × Word)
    (hstep : ∀ a acc r, step (acc, enc a ++ r) = (a :: acc, r)) (l acc : List α) (r : Word) :
    step^[l.length] (acc, SAT.writeValues enc l ++ r) = (l.reverse ++ acc, r) := by
  induction l generalizing acc with
  | nil => rfl
  | cons a l ih =>
    simp only [List.length_cons, Function.iterate_succ_apply, writeValues_cons,
      List.append_assoc, hstep, ih, List.reverse_cons, List.cons_append, List.nil_append]

/-! ### Literals -/

/-- Read one literal (a sign bit and a unary index) off the front of the word. -/
def litStep (s : List SAT.Literal × Word) : List SAT.Literal × Word :=
  (⟨(leadingOnes s.2.tail).length, s.2.headD false⟩ :: s.1, afterOnes s.2.tail)

theorem litStep_enc (l : SAT.Literal) (acc : List SAT.Literal) (r : Word) :
    litStep (acc, SAT.encodeLiteral l ++ r) = (l :: acc, r) := by
  obtain ⟨v, p⟩ := l
  simp [litStep, SAT.encodeLiteral, writeNat_append]

/-- Read `n` literals (in reverse order), returning the rest of the word. -/
def parseLits (n : Nat) (r : Word) : List SAT.Literal × Word := litStep^[n] ([], r)

theorem parseLits_bound (n : Nat) (r : Word) :
    (parseLits n r).2.length ≤ r.length ∧ size (parseLits n r).1 ≤ 1 + n * (r.length + 3) := by
  induction n with
  | zero => simp [parseLits]
  | succ n ih =>
    have e : parseLits (n + 1) r = litStep (parseLits n r) := by
      simp only [parseLits, Function.iterate_succ_apply']
    obtain ⟨h1, h2⟩ := ih
    have h3 := length_afterOnes_le (parseLits n r).2.tail
    have h4 := length_leadingOnes_le (parseLits n r).2.tail
    have h5 : (parseLits n r).2.tail.length ≤ (parseLits n r).2.length := by simp
    rw [e]
    simp only [litStep, size_cons, size_literal, Nat.succ_mul]
    omega

protected theorem PT.parseLits' : PT (fun p : Nat × Word => parseLits p.1 p.2) := by
  have hstep : PT litStep := by
    unfold litStep
    fun_prop
  refine PT.iterate_const (step := litStep)
    (init := fun p : Nat × Word => (([] : List SAT.Literal), p.2)) (n := fun p => p.1) hstep
    (by fun_prop) (by fun_prop) (fun N => N * (N + 3) + 2 * N + 2)
    (((PolynomialBound.identity.mul (PolynomialBound.identity.add (PolynomialBound.constant 3))).add
      ((PolynomialBound.constant 2).mul PolynomialBound.identity)).add
        (PolynomialBound.constant 2)) ?_
  intro p i hi
  obtain ⟨h1, h2⟩ := parseLits_bound i p.2
  have hN1 : i ≤ size p := by
    rw [size_prod, size_nat]
    omega
  have hN2 : p.2.length ≤ size p := by
    rw [size_prod, size_word]
    omega
  have hmul := Nat.mul_le_mul hN1 (Nat.add_le_add_right hN2 3)
  show size (parseLits i p.2) ≤ _
  rw [size_prod (parseLits i p.2), size_word]
  omega

@[fun_prop] protected theorem PT.parseLits {α : Type} [Code α] {n : α → Nat} {r : α → Word}
    (hn : PT n) (hr : PT r) : PT (fun a => parseLits (n a) (r a)) :=
  PT.parseLits'.comp (hn.pair hr)

/-! ### Clauses and formulas -/

/-- Read one clause (its length in unary, then its literals) off the front of the word. -/
def clauseStep (s : List SAT.Clause × Word) : List SAT.Clause × Word :=
  ((parseLits (leadingOnes s.2).length (afterOnes s.2)).1.reverse :: s.1,
    (parseLits (leadingOnes s.2).length (afterOnes s.2)).2)

theorem clauseStep_enc (cl : SAT.Clause) (acc : List SAT.Clause) (r : Word) :
    clauseStep (acc, SAT.encodeClause cl ++ r) = (cl :: acc, r) := by
  have h : SAT.encodeClause cl ++ r =
      List.replicate cl.length true ++ false :: (SAT.writeValues SAT.encodeLiteral cl ++ r) :=
    writeList_append _ _ _
  have h2 := iterate_writeValues SAT.encodeLiteral litStep litStep_enc cl [] r
  simp only [clauseStep, h, leadingOnes_ones, afterOnes_ones, List.length_replicate, parseLits,
    h2, List.append_nil, List.reverse_reverse]

theorem clauseStep_bound (s : List SAT.Clause × Word) :
    (clauseStep s).2.length ≤ s.2.length ∧
      size (clauseStep s).1 ≤ size s.1 + (s.2.length * (s.2.length + 3) + 2) := by
  obtain ⟨h1, h2⟩ := parseLits_bound (leadingOnes s.2).length (afterOnes s.2)
  have h3 := length_afterOnes_le s.2
  have h4 := length_leadingOnes_le s.2
  have hmul := Nat.mul_le_mul h4 (Nat.add_le_add_right h3 3)
  simp only [clauseStep, size_cons, size_reverse]
  omega

/-- The lenient parser for formulas. -/
def parseCNF (x : Word) : SAT.CNF :=
  (clauseStep^[(leadingOnes x).length] ([], afterOnes x)).1.reverse

/-- The parser inverts `SAT.encode`. -/
@[simp] theorem parseCNF_encode (f : SAT.CNF) : parseCNF (SAT.encode f) = f := by
  have h : SAT.encode f =
      List.replicate f.length true ++ false :: (SAT.writeValues SAT.encodeClause f ++ []) := by
    have := writeList_append SAT.encodeClause f []
    rw [List.append_nil] at this
    exact this
  have h2 := iterate_writeValues SAT.encodeClause clauseStep clauseStep_enc f [] []
  rw [parseCNF, h, leadingOnes_ones, afterOnes_ones, List.length_replicate, h2]
  simp

/-- A word is the code of a formula exactly when re-encoding the parsed formula gives the
word back. -/
theorem encode_parseCNF_iff (x : Word) :
    SAT.encode (parseCNF x) = x ↔ ∃ f, SAT.encode f = x :=
  ⟨fun h => ⟨_, h⟩, fun ⟨f, hf⟩ => by rw [← hf, parseCNF_encode]⟩

theorem clauseStep_iterate_bound (i : Nat) (r : Word) :
    (clauseStep^[i] ([], r)).2.length ≤ r.length ∧
      size (clauseStep^[i] ([], r)).1 ≤ 1 + i * (r.length * (r.length + 3) + 2) := by
  induction i with
  | zero => simp
  | succ i ih =>
    obtain ⟨h1, h2⟩ := ih
    obtain ⟨h3, h4⟩ := clauseStep_bound (clauseStep^[i] ([], r))
    have hmul := Nat.mul_le_mul h1 (Nat.add_le_add_right h1 3)
    rw [Function.iterate_succ_apply', Nat.succ_mul]
    omega

/-- The parser is polynomial-time. -/
theorem pt_parseCNF : PT parseCNF := by
  have hstep : PT clauseStep := by
    unfold clauseStep
    fun_prop
  have h := PT.iterate_const (step := clauseStep)
    (init := fun x : Word => (([] : List SAT.Clause), afterOnes x))
    (n := fun x : Word => (leadingOnes x).length) hstep (by fun_prop) (by fun_prop)
    (fun N => N * (N * (N + 3) + 2) + 2 * N + 2)
    (((PolynomialBound.identity.mul ((PolynomialBound.identity.mul
      (PolynomialBound.identity.add (PolynomialBound.constant 3))).add
        (PolynomialBound.constant 2))).add
      ((PolynomialBound.constant 2).mul PolynomialBound.identity)).add
        (PolynomialBound.constant 2)) ?_
  · exact PT.reverse (PT.fst h)
  · intro x i hi
    obtain ⟨h1, h2⟩ := clauseStep_iterate_bound i (afterOnes x)
    have h3 := length_afterOnes_le x
    have h4 := length_leadingOnes_le x
    have hN : x.length ≤ size x := by
      rw [size_word]
      omega
    have hR : (afterOnes x).length ≤ size x := Nat.le_trans h3 hN
    have hmul1 := Nat.mul_le_mul hR (Nat.add_le_add_right hR 3)
    have hmul2 := Nat.mul_le_mul (Nat.le_trans hi (Nat.le_trans h4 hN))
      (Nat.add_le_add_right hmul1 2)
    rw [size_prod (clauseStep^[i] ([], afterOnes x)), size_word]
    omega

@[fun_prop] protected theorem PT.parseCNF {α : Type} [Code α] {w : α → Word} (hw : PT w) :
    PT (fun a => parseCNF (w a)) :=
  pt_parseCNF.comp hw

end Complexity

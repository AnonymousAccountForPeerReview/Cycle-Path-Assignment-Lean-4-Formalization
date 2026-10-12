module

public import Hardness.MaxSNP.Hard.Defs
public import PT.Words
public import PT.SAT
public import PT.RawMore
public import PT.List
public import PT.ListMore

/-!
# MAX-3-SAT is MaxSNP-hard: the two maps are polynomial-time

The instance map `snpToSat k φ` and the solution map `satToSnp k φ`, followed by `fitRel sa`,
are polynomial-time, for every fixed `k`, `φ` and `sa`. The functions depending on the
constants `k`, `φ`, `sa` (the tuples, the evaluation of `φ`, the splitting of clauses of bounded
length, the relations of the signature) are handled by induction on these constants;
everything else is a list program for `fun_prop`.
-/

@[expose] public section

set_option linter.dupNamespace false

namespace Complexity

open Complexity.PT

variable {α : Type} [Code α]

/-- The `k`-tuples of the universe, for a fixed `k`. -/
theorem pt_tuples (k : Nat) : PT (fun n : Nat => tuples n k) := by
  induction k with
  | zero => exact PT.const _
  | succ k ih =>
    simp only [tuples_succ]
    fun_prop

@[fun_prop] protected theorem PT.tuples (k : Nat) {n : α → Nat} (hn : PT n) :
    PT (fun a => tuples (n a) k) :=
  (pt_tuples k).comp hn

/-- Evaluating a fixed formula. -/
theorem pt_evalB (A : List (Nat × List Nat)) (ψ : QF) :
    PT (fun p : Relations × List Bool × List Nat => ψ.evalB A p.1 p.2.1 p.2.2) := by
  induction ψ with
  | input rel args =>
    simp only [QF.evalB, Relations.holds]
    fun_prop
  | sol rel args =>
    simp only [QF.evalB]
    fun_prop
  | eq i j =>
    simp only [QF.evalB]
    fun_prop
  | not ψ ih =>
    simp only [QF.evalB]
    fun_prop
  | and ψ χ ih₁ ih₂ =>
    simp only [QF.evalB]
    fun_prop
  | or ψ χ ih₁ ih₂ =>
    simp only [QF.evalB]
    fun_prop

@[fun_prop] protected theorem PT.evalB (A : List (Nat × List Nat)) (ψ : QF)
    {G : α → Relations} {β : α → List Bool} {x : α → List Nat} (hG : PT G) (hβ : PT β)
    (hx : PT x) : PT (fun a => ψ.evalB A (G a) (β a) (x a)) :=
  (pt_evalB A ψ).comp (hG.pair (hβ.pair hx))

/-- Splitting a clause, with a fixed bound on the number of pieces. -/
theorem pt_splitN (m : Nat) : PT (fun p : Nat × SAT.Clause => splitN m p.1 p.2) := by
  induction m with
  | zero =>
    simp only [splitN]
    fun_prop
  | succ m ih =>
    simp only [splitN]
    fun_prop

@[fun_prop] protected theorem PT.splitN (m : Nat) {z : α → Nat} {ls : α → SAT.Clause}
    (hz : PT z) (hls : PT ls) : PT (fun a => splitN m (z a) (ls a)) :=
  (pt_splitN m).comp (hz.pair hls)

/-- The instance map is polynomial-time. -/
theorem pt_snpToSat (k : Nat) (φ : QF) : PT (snpToSat k φ) := by
  unfold snpToSat splitFrom longClauses keptTuples emitted negClause keptTuple normWord
    tupleVars groundAtoms groundAtom
  fun_prop

/-- The solution map is polynomial-time. -/
theorem pt_satToSnp (k : Nat) (φ : QF) :
    PT (fun p : (Nat × Relations) × Word => satToSnp k φ p.1 p.2) := by
  unfold satToSnp relOfWord groundAtoms groundAtom
  fun_prop

/-- Cutting a structure of a fixed signature out of relations. -/
theorem pt_fitFrom (sa : List Nat) (i : Nat) :
    PT (fun p : Nat × Relations => fitFrom sa i p.1 p.2) := by
  induction sa generalizing i with
  | nil =>
    simp only [fitFrom]
    fun_prop
  | cons a sa ih =>
    have h := ih (i + 1)
    simp only [fitFrom]
    unfold Relations.holds
    fun_prop

/-- The solution map followed by cutting out a structure of the signature `sa`. -/
theorem pt_fitRel_satToSnp (sa : List Nat) (k : Nat) (φ : QF) :
    PT (fun p : (Nat × Relations) × Word => fitRel sa p.1.1 (satToSnp k φ p.1 p.2)) :=
  (pt_fitFrom sa 0).comp (PT.pair (PT.fst (PT.fst PT.id)) (pt_satToSnp k φ))

end Complexity

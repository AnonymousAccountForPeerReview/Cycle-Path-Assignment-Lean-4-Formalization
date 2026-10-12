module

public import Hardness.Formula
public import PT.All

/-!
# The two encoding converters

`Hardness.GapPCP.pcp_gap_of_converters` needs polynomial-time word functions converting between
the project's code `SAT.encode` of 3-CNF formulas and the vendored serialisation `formulaBits`
(`ConvertsIn`, `ConvertsOut` of `Hardness.Formula`).  Both are obtained from the `PT` framework:

* the vendored serialisation `oaiCode N ψ` of a formula `ψ` whose clauses all have exactly three
  literals is the `Code`-encoding of the pair `(N, ψ.map clauseTriple)` of type
  `Nat × List ((Nat × Nat) × (Nat × Nat) × (Nat × Nat))`, a literal being the pair of its
  variable and its sign (`1` for positive, `0` for negative): `oaiCode_eq_enc`;
* `convInData : SAT.CNF → Nat × List OAITriple`, `φ ↦ (|encode φ|, (padCNF φ).map clauseTriple)`,
  and `convOutData : Nat × List OAITriple → SAT.CNF`, `(N, ts) ↦ ts.map tripleClause`, are
  polynomial-time on codes (`pt_convInData`, `pt_convOutData`).

Hence `exists_converterIn` and `exists_converterOut`.
-/

@[expose] public section

set_option linter.dupNamespace false

namespace Complexity

open Complexity.PT Complexity.PT.Code
open OAI.UniqueGamesTheorem
open Foundations.Complexity (formulaBits)

/-! ### The vendored serialisation as a `Code`-encoding -/

/-- A three-literal clause as plain numbers: for each literal its variable and its sign. -/
abbrev OAITriple : Type := (Nat × Nat) × (Nat × Nat) × (Nat × Nat)

/-- A literal as a pair of numbers: the variable, and `1` (positive) or `0` (negative). -/
def litPair (l : SAT.Literal) : Nat × Nat := (l.var, if l.positive then 1 else 0)

/-- The literal of a pair of numbers: positive iff the second number is `1`. -/
def pairLit (p : Nat × Nat) : SAT.Literal := ⟨p.1, decide (p.2 = 1)⟩

/-- The first three literals of a clause as a triple of pairs of numbers (missing literals are
replaced by `x₀`; this does not happen for clauses with exactly three literals). -/
def clauseTriple (d : SAT.Clause) : OAITriple :=
  (litPair (d.getD 0 ⟨0, true⟩), litPair (d.getD 1 ⟨0, true⟩), litPair (d.getD 2 ⟨0, true⟩))

/-- The three-literal clause of a triple of pairs of numbers. -/
def tripleClause (t : OAITriple) : SAT.Clause := [pairLit t.1, pairLit t.2.1, pairLit t.2.2]

@[simp] theorem pairLit_litPair (l : SAT.Literal) : pairLit (litPair l) = l := by
  obtain ⟨v, p⟩ := l
  cases p <;> simp [pairLit, litPair]

theorem tripleClause_clauseTriple {d : SAT.Clause} (hd : d.length = 3) :
    tripleClause (clauseTriple d) = d := by
  match d, hd with
  | [l₀, l₁, l₂], _ => simp [tripleClause, clauseTriple]

/-- The code of the pair of a literal is its vendored code. -/
theorem enc_litPair (l : SAT.Literal) : (enc (litPair l) : Word) = oaiLiteralCode l := by
  obtain ⟨v, p⟩ := l
  cases p <;> rfl

/-- The code of the triple of a three-literal clause is the concatenation of the vendored
codes of its literals. -/
theorem enc_clauseTriple {d : SAT.Clause} (hd : d.length = 3) :
    (enc (clauseTriple d) : Word) = d.flatMap oaiLiteralCode := by
  match d, hd with
  | [l₀, l₁, l₂], _ =>
    simp only [clauseTriple, List.getD_cons_zero, List.getD_cons_succ, enc_pair, enc_litPair,
      List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- **The vendored serialisation is a `Code`-encoding**: for clauses with exactly three
literals, `oaiCode N ψ` is the code of the pair `(N, ψ.map clauseTriple)`. -/
theorem oaiCode_eq_enc (N : Nat) (ψ : SAT.CNF) (h : ∀ d ∈ ψ, d.length = 3) :
    oaiCode N ψ = enc (N, ψ.map clauseTriple) := by
  rw [enc_pair, enc_list, SAT.writeList, writeValues_eq_flatMap, List.length_map,
    List.flatMap_map, oaiCode, enc_nat, List.append_assoc]
  congr 2
  apply List.flatMap_congr
  intro d hd
  exact (enc_clauseTriple (h d hd)).symm

/-! ### Padding, without pattern matching -/

/-- `padClause` in terms of `length` and `getD`. -/
theorem padClause_eq (cl : SAT.Clause) :
    padClause cl =
      if cl.length = 0 then
        [[⟨0, true⟩, ⟨0, true⟩, ⟨0, true⟩], [⟨0, false⟩, ⟨0, false⟩, ⟨0, false⟩]]
      else
        [[cl.getD 0 ⟨0, true⟩, cl.getD 1 (cl.getD 0 ⟨0, true⟩),
          cl.getD 2 (cl.getD 1 (cl.getD 0 ⟨0, true⟩))]] := by
  match cl with
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | _ :: _ :: _ :: _ => rfl

@[fun_prop] protected theorem PT.padClause {α : Type} [Code α] {f : α → SAT.Clause}
    (hf : PT f) : PT (fun a => padClause (f a)) := by
  have h : PT (fun cl : SAT.Clause =>
      if cl.length = 0 then
        ([[⟨0, true⟩, ⟨0, true⟩, ⟨0, true⟩], [⟨0, false⟩, ⟨0, false⟩, ⟨0, false⟩]] : SAT.CNF)
      else
        [[cl.getD 0 ⟨0, true⟩, cl.getD 1 (cl.getD 0 ⟨0, true⟩),
          cl.getD 2 (cl.getD 1 (cl.getD 0 ⟨0, true⟩))]]) := by
    fun_prop
  exact (h.of_eq fun cl => (padClause_eq cl).symm).comp hf

@[fun_prop] protected theorem PT.padCNF {α : Type} [Code α] {f : α → SAT.CNF}
    (hf : PT f) : PT (fun a => padCNF (f a)) := by
  unfold padCNF
  fun_prop

@[fun_prop] protected theorem PT.clauseTriple {α : Type} [Code α] {f : α → SAT.Clause}
    (hf : PT f) : PT (fun a => clauseTriple (f a)) := by
  unfold clauseTriple litPair
  fun_prop

@[fun_prop] protected theorem PT.tripleClause {α : Type} [Code α] {f : α → OAITriple}
    (hf : PT f) : PT (fun a => tripleClause (f a)) := by
  unfold tripleClause pairLit
  fun_prop

/-! ### The converters -/

/-- The data map of the converter into the vendored format: the length of the code of `φ`
(the number of variables) and the triples of the padded clauses. -/
def convInData (φ : SAT.CNF) : Nat × List OAITriple :=
  ((Code.enc φ : Word).length, (padCNF φ).map clauseTriple)

/-- The data map of the converter out of the vendored format: forget the number of variables
and turn every triple into a clause. -/
def convOutData (p : Nat × List OAITriple) : SAT.CNF := p.2.map tripleClause

theorem pt_convInData : PT convInData := by
  unfold convInData
  fun_prop

theorem pt_convOutData : PT convOutData := by
  unfold convOutData
  fun_prop

theorem enc_convInData (φ : SAT.CNF) :
    enc (convInData φ) = oaiCode (SAT.encode φ).length (padCNF φ) :=
  (oaiCode_eq_enc _ _ (padCNF_length_three φ)).symm

theorem convOutData_map_clauseTriple (N : Nat) (ψ : SAT.CNF) (h : ∀ d ∈ ψ, d.length = 3) :
    convOutData (N, ψ.map clauseTriple) = ψ := by
  unfold convOutData
  rw [List.map_map]
  conv_rhs => rw [← List.map_id ψ]
  apply List.map_congr_left
  intro d hd
  exact tripleClause_clauseTriple (h d hd)

/-- There is a polynomial-time converter from the project's code of 3-CNF formulas to the
vendored serialisation. -/
theorem exists_converterIn : ∃ c₁ : Word → Word, PolyTime c₁ ∧ ConvertsIn c₁ := by
  obtain ⟨F, hF, hF'⟩ := pt_convInData.exists_polyTime
  refine ⟨F, hF, (convertsIn_iff F).mpr fun φ _ => ?_⟩
  rw [← enc_convInData]
  exact hF' φ

/-- There is a polynomial-time converter from the vendored serialisation to the project's
code. -/
theorem exists_converterOut : ∃ c₂ : Word → Word, PolyTime c₂ ∧ ConvertsOut c₂ := by
  obtain ⟨F, hF, hF'⟩ := pt_convOutData.exists_polyTime
  refine ⟨F, hF, convertsOut_of_plain F fun N ψ h3 _ => ?_⟩
  rw [oaiCode_eq_enc N ψ h3, hF', convOutData_map_clauseTriple N ψ h3]
  rfl

end Complexity

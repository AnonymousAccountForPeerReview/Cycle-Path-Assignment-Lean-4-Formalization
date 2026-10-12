module

public import Complexity.SATBounds
public import ComplexityExt.PCP.Defs
public import OAI.Computability.UniqueGames.PCP.NameCompaction

/-!
# The two representations of 3-CNF formulas

The project's formulas are `SAT.CNF = List (List SAT.Literal)` with variables indexed by natural
numbers and the code `SAT.encode`. The vendored development uses
`OAI.UniqueGamesTheorem.Foundations.Target.Formula`: a number `variables` and a list of clauses
with exactly three literal slots over `Fin variables`, serialised by `formulaBits`.

* `toOAI : SAT.CNF → Formula` pads every clause to exactly three literals (`padCNF`) and uses
  `variables := (SAT.encode φ).length`, which is positive and exceeds every variable index.
  `ofOAI (toOAI φ) = padCNF φ`, and for 3-CNF `φ` satisfiability is preserved in both directions.
* `ofOAI : Formula → SAT.CNF` forgets the bound on the variables.
* Both serialisations are described by plain list functions: `formulaBits F =
  oaiCode F.variables (ofOAI F)` and `formulaBits (toOAI φ) = oaiCode (SAT.encode φ).length
  (padCNF φ)`; `SAT.encode` is spelled out in `encode_eq_flatMap`.
* `ConvertsIn`, `ConvertsOut` specify the two polynomial-time converters between the codes;
  `convertsIn_iff` and `convertsOut_of_plain` restate them without `Vector`/`Fin`.
-/

@[expose] public section

namespace Complexity

open OAI.UniqueGamesTheorem
open Foundations.Target (Formula)
open Foundations.Complexity (formulaBits formulaWords clauseWords literalWords encodeWords
  encodeWord)

/-! ### Padding to exactly three literals (plain lists) -/

/-- A clause of at most three literals as clauses of exactly three literals: the last literal
is repeated; the empty clause becomes the unsatisfiable pair `x₀ ∨ x₀ ∨ x₀`, `¬x₀ ∨ ¬x₀ ∨ ¬x₀`.
(Longer clauses are truncated to their first three literals; they do not occur in 3-CNF.) -/
def padClause : SAT.Clause → SAT.CNF
  | [] => [[⟨0, true⟩, ⟨0, true⟩, ⟨0, true⟩], [⟨0, false⟩, ⟨0, false⟩, ⟨0, false⟩]]
  | [l₀] => [[l₀, l₀, l₀]]
  | [l₀, l₁] => [[l₀, l₁, l₁]]
  | l₀ :: l₁ :: l₂ :: _ => [[l₀, l₁, l₂]]

/-- Pad every clause: the plain-data form of the clause list of `toOAI`. -/
def padCNF (φ : SAT.CNF) : SAT.CNF := φ.flatMap padClause

@[simp] theorem padCNF_nil : padCNF [] = [] := rfl

@[simp] theorem padCNF_cons (cl : SAT.Clause) (φ : SAT.CNF) :
    padCNF (cl :: φ) = padClause cl ++ padCNF φ := rfl

theorem padClause_length_three (cl : SAT.Clause) : ∀ d ∈ padClause cl, d.length = 3 := by
  match cl with
  | [] => simp [padClause]
  | [_] => simp [padClause]
  | [_, _] => simp [padClause]
  | _ :: _ :: _ :: _ => simp [padClause]

/-- Every clause of `padCNF φ` has exactly three literals. -/
theorem padCNF_length_three (φ : SAT.CNF) : ∀ d ∈ padCNF φ, d.length = 3 := by
  intro d hd
  obtain ⟨cl, -, hcl⟩ := List.mem_flatMap.mp hd
  exact padClause_length_three cl d hcl

theorem padClause_var (cl : SAT.Clause) :
    ∀ d ∈ padClause cl, ∀ l ∈ d, l.var = 0 ∨ l ∈ cl := by
  match cl with
  | [] =>
    intro d hd l hl
    simp only [padClause, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl <;> simp at hl <;> simp [hl]
  | [_] =>
    intro d hd l hl
    simp only [padClause, List.mem_cons, List.not_mem_nil, or_false] at hd
    subst hd
    right
    simpa using hl
  | [_, _] =>
    intro d hd l hl
    simp only [padClause, List.mem_cons, List.not_mem_nil, or_false] at hd
    subst hd
    right
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl ⊢
    tauto
  | _ :: _ :: _ :: _ =>
    intro d hd l hl
    simp only [padClause, List.mem_cons, List.not_mem_nil, or_false] at hd
    subst hd
    right
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl ⊢
    tauto

theorem encode_length_pos (φ : SAT.CNF) : 0 < (SAT.encode φ).length := by
  cases φ with
  | nil => simp
  | cons cl φ => rw [SATBounds.encode_cons_length]; omega

/-- Every variable of `padCNF φ` is below the length of the code of `φ`. -/
theorem padCNF_var_lt (φ : SAT.CNF) :
    ∀ d ∈ padCNF φ, ∀ l ∈ d, l.var < (SAT.encode φ).length := by
  intro d hd l hl
  obtain ⟨cl, hcl, hd⟩ := List.mem_flatMap.mp hd
  rcases padClause_var cl d hd l hl with h | h
  · rw [h]
    exact encode_length_pos φ
  · exact Nat.lt_of_lt_of_le (SAT.literal_lt_variableBound hcl h)
      (SATBounds.variableBound_le_encode_length φ)

theorem evalCNF_padClause (a : SAT.Assignment) (cl : SAT.Clause) (h : cl.length ≤ 3) :
    SAT.evalCNF a (padClause cl) = SAT.evalClause a cl := by
  match cl, h with
  | [], _ => simp [padClause]
  | [l₀], _ => simp [padClause]
  | [l₀, l₁], _ => simp [padClause]
  | [l₀, l₁, l₂], _ => simp [padClause]
  | _ :: _ :: _ :: _ :: _, h => exact absurd h (by simp)

/-- Padding does not change the truth value of a 3-CNF formula under any assignment. -/
theorem evalCNF_padCNF (a : SAT.Assignment) (φ : SAT.CNF) (h : SAT.IsThreeCNF φ) :
    SAT.evalCNF a (padCNF φ) = SAT.evalCNF a φ := by
  induction φ with
  | nil => rfl
  | cons cl φ ih =>
    rw [padCNF_cons, SAT.evalCNF_append, SAT.evalCNF_cons,
      evalCNF_padClause a cl (h cl (by simp)), ih (fun d hd => h d (by simp [hd]))]

theorem satisfiable_padCNF_iff (φ : SAT.CNF) (h : SAT.IsThreeCNF φ) :
    SAT.Satisfiable (padCNF φ) ↔ SAT.Satisfiable φ := by
  constructor <;> rintro ⟨a, ha⟩ <;> refine ⟨a, ?_⟩
  · rwa [evalCNF_padCNF a φ h] at ha
  · rwa [evalCNF_padCNF a φ h]

/-! ### From the vendored representation to lists -/

/-- Forget the bound on the variable of a literal. -/
def ofLiteral {n : Nat} (l : Foundations.Target.Literal n) : SAT.Literal :=
  ⟨l.variableIndex.val, l.positive⟩

/-- The list of the three literals of a clause. -/
def ofClause {n : Nat} (cl : Foundations.Target.Clause n) : SAT.Clause :=
  [ofLiteral cl[0], ofLiteral cl[1], ofLiteral cl[2]]

/-- The formula as a list of three-literal clauses over natural-number variables. -/
def ofOAI (F : Formula) : SAT.CNF := F.clauses.map ofClause

@[simp] theorem ofOAI_length (F : Formula) : (ofOAI F).length = F.clauses.length := by
  simp [ofOAI]

/-- Every clause of `ofOAI F` has exactly three literals. -/
theorem ofOAI_length_three (F : Formula) : ∀ d ∈ ofOAI F, d.length = 3 := by
  intro d hd
  obtain ⟨cl, -, rfl⟩ := List.mem_map.mp hd
  rfl

theorem ofOAI_isThreeCNF (F : Formula) : SAT.IsThreeCNF (ofOAI F) :=
  fun d hd => (ofOAI_length_three F d hd).le

/-- Every variable of `ofOAI F` is below `F.variables`. -/
theorem ofOAI_var_lt (F : Formula) : ∀ d ∈ ofOAI F, ∀ l ∈ d, l.var < F.variables := by
  intro d hd l hl
  obtain ⟨cl, -, rfl⟩ := List.mem_map.mp hd
  simp only [ofClause, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl <;> exact Fin.isLt _

theorem evalLiteral_ofLiteral {n : Nat} (a : SAT.Assignment) (l : Foundations.Target.Literal n) :
    SAT.evalLiteral a (ofLiteral l) = l.eval (fun i => a i.val) := rfl

theorem evalClause_ofClause {n : Nat} (a : SAT.Assignment) (cl : Foundations.Target.Clause n) :
    SAT.evalClause a (ofClause cl) = cl.eval (fun i => a i.val) := by
  simp [ofClause, Foundations.Target.Clause.eval, evalLiteral_ofLiteral, Bool.or_assoc]

/-- The natural-number assignment that extends `A` by `false`. -/
def extendAssignment {n : Nat} (A : Fin n → Bool) : SAT.Assignment :=
  fun i => if h : i < n then A ⟨i, h⟩ else false

theorem extendAssignment_restrict {n : Nat} (A : Fin n → Bool) :
    (fun i : Fin n => extendAssignment A i.val) = A := by
  funext i
  simp [extendAssignment]

theorem satisfiable_ofOAI_iff (F : Formula) : SAT.Satisfiable (ofOAI F) ↔ F.Satisfiable := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨fun i => a i.val, fun cl hcl => ?_⟩
    rw [← evalClause_ofClause]
    exact List.all_eq_true.mp ha _ (List.mem_map_of_mem hcl)
  · rintro ⟨A, hA⟩
    refine ⟨extendAssignment A, List.all_eq_true.mpr ?_⟩
    intro d hd
    obtain ⟨cl, hcl, rfl⟩ := List.mem_map.mp hd
    rw [evalClause_ofClause, extendAssignment_restrict]
    exact hA cl hcl

theorem satisfiable_ofOAI (F : Formula) (h : F.Satisfiable) : SAT.Satisfiable (ofOAI F) :=
  (satisfiable_ofOAI_iff F).mpr h

/-- Under any assignment, the satisfied clauses of `ofOAI F` and the failed clauses of `F`
together are all clauses. -/
theorem satCount_ofOAI_add_failedCount (F : Formula) (a : SAT.Assignment) :
    SAT.satCount a (ofOAI F) +
      Foundations.PCP.NameCompaction.failedCount F (fun i => a i.val) = F.clauses.length := by
  unfold SAT.satCount Foundations.PCP.NameCompaction.failedCount
    Foundations.PCP.NameCompaction.evaluationList ofOAI
  generalize F.clauses = cs
  induction cs with
  | nil => rfl
  | cons cl cs ih =>
    simp only [List.map_cons, List.countP_cons, List.count_cons, List.length_cons,
      evalClause_ofClause]
    cases h : cl.eval (fun i => a i.val) <;> simp at ih ⊢ <;> omega

/-! ### From lists to the vendored representation -/

/-- `v` as an element of `Fin N` (`0` when `v` is out of range). -/
def clampFin (N : Nat) (h : 0 < N) (v : Nat) : Fin N :=
  if hv : v < N then ⟨v, hv⟩ else ⟨0, h⟩

theorem clampFin_val {N : Nat} (h : 0 < N) {v : Nat} (hv : v < N) : (clampFin N h v).val = v := by
  simp [clampFin, hv]

/-- A literal over `Fin N`. -/
def toLiteral (N : Nat) (h : 0 < N) (l : SAT.Literal) : Foundations.Target.Literal N :=
  ⟨clampFin N h l.var, l.positive⟩

/-- The first three literals of a list as a clause (missing slots are filled with `x₀`; this
does not happen for the clauses of `padCNF`). -/
def toClause (N : Nat) (h : 0 < N) (d : SAT.Clause) : Foundations.Target.Clause N :=
  #v[toLiteral N h (d.getD 0 ⟨0, true⟩), toLiteral N h (d.getD 1 ⟨0, true⟩),
    toLiteral N h (d.getD 2 ⟨0, true⟩)]

theorem ofLiteral_toLiteral {N : Nat} (h : 0 < N) {l : SAT.Literal} (hl : l.var < N) :
    ofLiteral (toLiteral N h l) = l := by
  cases l
  simp [ofLiteral, toLiteral, clampFin_val h hl]

theorem ofClause_toClause {N : Nat} (h : 0 < N) {d : SAT.Clause} (hd : d.length = 3)
    (hvar : ∀ l ∈ d, l.var < N) : ofClause (toClause N h d) = d := by
  match d, hd with
  | [l₀, l₁, l₂], _ =>
    have h₀ := ofLiteral_toLiteral h (hvar l₀ (by simp))
    have h₁ := ofLiteral_toLiteral h (hvar l₁ (by simp))
    have h₂ := ofLiteral_toLiteral h (hvar l₂ (by simp))
    simp only [ofClause, toClause, List.getD_cons_zero, List.getD_cons_succ]
    change [ofLiteral (toLiteral N h l₀), ofLiteral (toLiteral N h l₁),
      ofLiteral (toLiteral N h l₂)] = _
    rw [h₀, h₁, h₂]

/-- The vendored formula of a CNF formula `φ` (intended: a 3-CNF formula).
`variables := (SAT.encode φ).length`, which is at least `1` and exceeds every variable index of
`φ`; the clauses are those of `padCNF φ`: clauses of one or two literals are padded by
repeating the last literal, and an empty clause becomes the two clauses `x₀ ∨ x₀ ∨ x₀` and
`¬x₀ ∨ ¬x₀ ∨ ¬x₀`. -/
def toOAI (φ : SAT.CNF) : Formula where
  «variables» := (SAT.encode φ).length
  clauses := (padCNF φ).map (toClause (SAT.encode φ).length (encode_length_pos φ))

@[simp] theorem toOAI_variables (φ : SAT.CNF) : (toOAI φ).variables = (SAT.encode φ).length := rfl

/-- The plain-data form of `toOAI`: its clauses are the padded clauses of `φ`. -/
theorem ofOAI_toOAI (φ : SAT.CNF) : ofOAI (toOAI φ) = padCNF φ := by
  unfold ofOAI toOAI
  rw [List.map_map]
  conv_rhs => rw [← List.map_id (padCNF φ)]
  apply List.map_congr_left
  intro d hd
  exact ofClause_toClause _ (padCNF_length_three φ d hd) (padCNF_var_lt φ d hd)

/-- `toOAI` preserves satisfiability of 3-CNF formulas, in both directions. -/
theorem toOAI_satisfiable_iff (φ : SAT.CNF) (h : SAT.IsThreeCNF φ) :
    (toOAI φ).Satisfiable ↔ SAT.Satisfiable φ := by
  rw [← satisfiable_ofOAI_iff, ofOAI_toOAI, satisfiable_padCNF_iff φ h]

/-! ### The two serialisations as list functions -/

/-- The vendored code of a literal: variable index in unary, then `1` or `0` in unary for the
sign. -/
def oaiLiteralCode (l : SAT.Literal) : Word :=
  SAT.writeNat l.var ++ (if l.positive then [true, false] else [false])

/-- The vendored serialisation, on plain data: the number of variables `N` and a list `ψ` of
clauses (lists of literals; three each for an actual formula). All numbers are in unary
(`SAT.writeNat n` is `n` ones and a zero): `N`, the number of clauses, then literal by literal
the variable index and the sign (`1` for positive). -/
def oaiCode (N : Nat) (ψ : SAT.CNF) : Word :=
  SAT.writeNat N ++ SAT.writeNat ψ.length ++ ψ.flatMap fun d => d.flatMap oaiLiteralCode

theorem encodeWord_eq_writeNat (n : Nat) : encodeWord n = SAT.writeNat n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [SAT.writeNat, ← ih]
    simp [encodeWord, List.replicate_succ]

theorem encodeWords_cons (n : Nat) (ns : List Nat) :
    encodeWords (n :: ns) = SAT.writeNat n ++ encodeWords ns := by
  rw [encodeWords, encodeWord_eq_writeNat]

theorem encodeWords_literalWords {n : Nat} (l : Foundations.Target.Literal n) :
    encodeWords (literalWords l) = oaiLiteralCode (ofLiteral l) := by
  obtain ⟨v, p⟩ := l
  cases p <;>
    simp [literalWords, encodeWords_cons, oaiLiteralCode, ofLiteral, encodeWords, encodeWord]

theorem encodeWords_clauseWords {n : Nat} (cl : Foundations.Target.Clause n) :
    encodeWords (clauseWords cl) = (ofClause cl).flatMap oaiLiteralCode := by
  simp [clauseWords, ofClause, encodeWords_literalWords]

theorem encodeWords_flatMap_clauseWords {n : Nat} (cs : List (Foundations.Target.Clause n)) :
    encodeWords (cs.flatMap clauseWords) =
      (cs.map ofClause).flatMap fun d => d.flatMap oaiLiteralCode := by
  induction cs with
  | nil => rfl
  | cons cl cs ih =>
    rw [List.flatMap_cons, Foundations.Complexity.encodeWords_append, ih,
      encodeWords_clauseWords, List.map_cons, List.flatMap_cons]

/-- The vendored serialisation of `F` only depends on `F.variables` and the plain clause list
`ofOAI F`. -/
theorem formulaBits_eq_oaiCode (F : Formula) : formulaBits F = oaiCode F.variables (ofOAI F) := by
  unfold formulaBits formulaWords oaiCode ofOAI
  rw [Foundations.Complexity.encodeWords_append, encodeWords_cons, encodeWords_cons,
    encodeWords_flatMap_clauseWords]
  simp [encodeWords]

/-- The vendored serialisation spelled out: `variables`, the number of clauses, then for each
clause its three literals, each as variable index and sign, all in unary. -/
theorem formulaBits_eq (F : Formula) :
    formulaBits F = SAT.writeNat F.variables ++ SAT.writeNat F.clauses.length ++
      F.clauses.flatMap fun cl =>
        SAT.writeNat cl[0].variableIndex.val ++ SAT.writeNat (if cl[0].positive then 1 else 0) ++
        (SAT.writeNat cl[1].variableIndex.val ++ SAT.writeNat (if cl[1].positive then 1 else 0)) ++
        (SAT.writeNat cl[2].variableIndex.val ++ SAT.writeNat (if cl[2].positive then 1 else 0)) := by
  rw [formulaBits_eq_oaiCode, oaiCode, ofOAI, List.length_map, List.flatMap_map]
  congr 1
  apply List.flatMap_congr
  intro cl _
  have hsign : ∀ b : Bool, (if b then [true, false] else [false]) =
      SAT.writeNat (if b then 1 else 0) := by
    intro b
    cases b <;> rfl
  simp [ofClause, oaiLiteralCode, ofLiteral, hsign]

/-- The serialisation of `toOAI φ` in terms of the code of `φ` and the padded clause list. -/
theorem formulaBits_toOAI (φ : SAT.CNF) :
    formulaBits (toOAI φ) = oaiCode (SAT.encode φ).length (padCNF φ) := by
  rw [formulaBits_eq_oaiCode, ofOAI_toOAI, toOAI_variables]

theorem writeValues_eq_flatMap {α : Type} (enc : α → Word) (xs : List α) :
    SAT.writeValues enc xs = xs.flatMap enc := by
  induction xs with
  | nil => rfl
  | cons x xs ih => rw [SAT.writeValues, ih, List.flatMap_cons]

/-- The project's code spelled out: the number of clauses, then for each clause its number of
literals and its literals, each as sign bit followed by the variable index in unary. -/
theorem encode_eq_flatMap (ψ : SAT.CNF) :
    SAT.encode ψ = SAT.writeNat ψ.length ++ ψ.flatMap fun d =>
      SAT.writeNat d.length ++ d.flatMap fun l => l.positive :: SAT.writeNat l.var := by
  rw [SAT.encode, SAT.writeList, writeValues_eq_flatMap]
  congr 1
  apply List.flatMap_congr
  intro d _
  rw [SAT.encodeClause, SAT.writeList, writeValues_eq_flatMap]
  rfl

/-- The project's code of `ofOAI F` spelled out. -/
theorem encode_ofOAI (F : Formula) :
    SAT.encode (ofOAI F) = SAT.writeNat F.clauses.length ++ F.clauses.flatMap fun cl =>
      [true, true, true, false] ++ (cl[0].positive :: SAT.writeNat cl[0].variableIndex.val) ++
        (cl[1].positive :: SAT.writeNat cl[1].variableIndex.val) ++
        (cl[2].positive :: SAT.writeNat cl[2].variableIndex.val) := by
  rw [encode_eq_flatMap, ofOAI, List.length_map, List.flatMap_map]
  congr 1
  apply List.flatMap_congr
  intro cl _
  simp [ofClause, ofLiteral, SAT.writeNat]

/-! ### The converter specifications -/

/-- `c₁` converts the project's code of a 3-CNF formula into the vendored serialisation. -/
def ConvertsIn (c₁ : Word → Word) : Prop :=
  ∀ φ : SAT.CNF, SAT.IsThreeCNF φ → c₁ (SAT.encode φ) = formulaBits (toOAI φ)

/-- `c₂` converts the vendored serialisation back. -/
def ConvertsOut (c₂ : Word → Word) : Prop :=
  ∀ F : Formula, c₂ (formulaBits F) = SAT.encode (ofOAI F)

/-- `ConvertsIn` on plain data: on the code `w` of a 3-CNF formula `φ`, write `|w|` in unary
(the number of variables), then the padded clauses `padCNF φ` in the format `oaiCode`. -/
theorem convertsIn_iff (c₁ : Word → Word) :
    ConvertsIn c₁ ↔ ∀ φ : SAT.CNF, SAT.IsThreeCNF φ →
      c₁ (SAT.encode φ) = oaiCode (SAT.encode φ).length (padCNF φ) := by
  simp only [ConvertsIn, formulaBits_toOAI]

/-- `ConvertsOut` on plain data: it suffices to map `oaiCode N ψ` to `SAT.encode ψ` whenever
every clause of `ψ` has exactly three literals, all with variables below `N`. -/
theorem convertsOut_of_plain (c₂ : Word → Word)
    (h : ∀ (N : Nat) (ψ : SAT.CNF), (∀ d ∈ ψ, d.length = 3) → (∀ d ∈ ψ, ∀ l ∈ d, l.var < N) →
      c₂ (oaiCode N ψ) = SAT.encode ψ) : ConvertsOut c₂ := by
  intro F
  rw [formulaBits_eq_oaiCode]
  exact h F.variables (ofOAI F) (ofOAI_length_three F) (ofOAI_var_lt F)

end Complexity

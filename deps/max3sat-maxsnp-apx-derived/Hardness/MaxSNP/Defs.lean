module

public import ComplexityExt.Approx.Defs
public import PT.Raw

/-!
# MAX-3-SAT as a MaxSNP₀ problem: the formula and the two maps

The quantifier-free formula `φ₃` in four variables, the instance map `sat2snp` and the
solution map `snp2sat` of the L-reduction from MAX-3-SAT to `maxSNP0 ga₃ sa₃ 4 φ₃`, the
signatures `ga₃` and `sa₃`, and the list of polynomial-time obligations about these explicit
list programs (`Obligations`).

The structure built from a formula `f` has the universe `{0, …, n - 1}` with
`n = (SAT.encode f).length` (which exceeds the number of clauses and every variable index),
and eight input relations `G_s` of arity 4, one for each sign pattern `s < 8`. A nonempty
clause number `i` is padded to three literals `l₁ l₂ l₃` (by repeating its first literal) and
contributes the tuple `[i, l₁.var, l₂.var, l₃.var]` to the relation whose index codes the
signs of `l₁ l₂ l₃`. Empty clauses contribute nothing. The solution is one unary relation `S`,
the set of true variables.
-/

@[expose] public section

namespace Complexity

open Complexity.PT

/-! ### Padding clauses to three literals -/

/-- The first literal of a clause (a default for the empty clause). -/
def lit1 (cl : SAT.Clause) : SAT.Literal := cl.headD ⟨0, true⟩

/-- The second literal of a clause, or the first one again if there is none. -/
def lit2 (cl : SAT.Clause) : SAT.Literal := cl.tail.headD (lit1 cl)

/-- The third literal of a clause, or the first one again if there is none. -/
def lit3 (cl : SAT.Clause) : SAT.Literal := cl.tail.tail.headD (lit1 cl)

/-- The index of the sign pattern `(b₁, b₂, b₃)`. -/
def signCode (b₁ b₂ b₃ : Bool) : Nat :=
  (if b₁ then 1 else 0) + (if b₂ then 2 else 0) + (if b₃ then 4 else 0)

/-- The index of the sign pattern of the three padded literals of a clause. -/
def clauseSign (cl : SAT.Clause) : Nat :=
  signCode (lit1 cl).positive (lit2 cl).positive (lit3 cl).positive

/-- The tuple contributed by the clause `q.1` with number `q.2`. -/
def clauseTuple (q : SAT.Clause × Nat) : List Nat :=
  [q.2, (lit1 q.1).var, (lit2 q.1).var, (lit3 q.1).var]

/-- The input relation with index `s`: the tuples of the nonempty clauses with sign pattern
`s`. -/
def snpRel (f : SAT.CNF) (s : Nat) : List (List Nat) :=
  (f.zipIdx.filter fun q => !q.1.isEmpty && clauseSign q.1 == s).map clauseTuple

/-- The instance map: the universe size and the eight input relations. -/
def sat2snp (f : SAT.CNF) : Nat × Relations :=
  ((SAT.encode f).length, [0, 1, 2, 3, 4, 5, 6, 7].map (snpRel f))

/-- The solution map: bit `v` of the assignment says whether `S₀(v)` holds, for `v` below the
universe size. -/
def snp2sat (f : SAT.CNF) (S : Relations) : Word :=
  (List.range (SAT.encode f).length).map fun v => S.holds 0 [v]

/-! ### The formula -/

/-- The literal `S₀(xᵢ)` or its negation. -/
def litQF (pos : Bool) (i : Nat) : QF :=
  if pos then .sol 0 [i] else .not (.sol 0 [i])

/-- `G_s(x₀, x₁, x₂, x₃) ∧ (±S₀(x₁) ∨ ±S₀(x₂) ∨ ±S₀(x₃))` for the sign pattern
`s = (b₁, b₂, b₃)`. -/
def branchQF (b₁ b₂ b₃ : Bool) : QF :=
  .and (.input (signCode b₁ b₂ b₃) [0, 1, 2, 3])
    (.or (litQF b₁ 1) (.or (litQF b₂ 2) (litQF b₃ 3)))

/-- The MaxSNP₀ formula of MAX-3-SAT: `⋁_s (G_s(x₀, x₁, x₂, x₃) ∧ (±S₀(x₁) ∨ ±S₀(x₂) ∨
±S₀(x₃)))`, over the eight sign patterns `s`. -/
def φ₃ : QF :=
  .or (branchQF false false false) (.or (branchQF true false false)
    (.or (branchQF false true false) (.or (branchQF true true false)
      (.or (branchQF false false true) (.or (branchQF true false true)
        (.or (branchQF false true true) (branchQF true true true)))))))

/-- The input signature of `φ₃`: eight relations of arity 4. -/
def ga₃ : List Nat := List.replicate 8 4

/-- The solution signature of `φ₃`: one unary relation. -/
def sa₃ : List Nat := [1]

/-! ### Polynomial-time obligations -/

/-- The polynomial-time facts about explicit list programs used by the MaxSNP theorems. -/
structure Obligations : Prop where
  /-- Counting the clauses satisfied by an assignment written as a word. -/
  satCount : PT (fun p : Word × SAT.CNF => SAT.satCount (SAT.assignmentOf p.1) p.2)
  /-- The instance map of the L-reduction from MAX-3-SAT to `maxSNP0 ga₃ sa₃ 4 φ₃`. -/
  sat2snp : PT sat2snp
  /-- The solution map of the L-reduction from MAX-3-SAT to `maxSNP0 ga₃ sa₃ 4 φ₃`. -/
  snp2sat : PT (fun p : SAT.CNF × Relations => snp2sat p.1 p.2)

end Complexity

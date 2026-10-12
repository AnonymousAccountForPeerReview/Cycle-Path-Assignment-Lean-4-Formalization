module

public import ComplexityExt.Approx.Defs

/-!
# MAX-3-SAT is MaxSNP-hard: the two maps of the L-reduction

For a quantifier-free formula `φ` in `k` variables, the instance map `snpToSat k φ` sends a
structure `(n, G)` to a 3-CNF formula, and the solution map `satToSnp k φ` sends an
assignment (written as a word) back to solution relations. Everything is an explicit
first-order list program.

* `QF.atoms φ` lists the occurrences of solution atoms `S_r(x_{i₁}, …)` of `φ`; its length
  `a` is a constant of the reduction.
* A *ground atom* is a pair `(r, u)` of a relation index and a tuple of elements; the ground
  atoms that can occur are listed in `groundAtoms`, and the Boolean variable of a ground atom
  is its first position in that list (`List.idxOf`).
* `QF.evalB A G β t ψ` evaluates `ψ` at the tuple `t` with the solution atom `q` replaced by
  the bit of `β` at the position of `q` in `A`.
* A tuple is *kept* if some consistent choice of bits makes `φ` true. For a kept tuple and
  every word `β` of length `a` falsifying `φ`, the *long clause* `negClause vs β` says that
  the variables `vs` of the atoms of the tuple do not have the values `β`.
* `splitN` splits a long clause into clauses with at most three literals, using fresh
  variables, such that exactly one piece is lost when the long clause is false.
* `fitRel sa n S` cuts a structure of the solution signature `sa` over the universe out of the
  relations `S` written by an assignment; for a well-formed formula this does not change the
  value (`Hardness.MaxSNP.Hard.Fit`).
-/

@[expose] public section

namespace Complexity

/-- The occurrences of solution atoms of a formula, in order. -/
def QF.atoms : QF → List (Nat × List Nat)
  | .input _ _ => []
  | .sol rel args => [(rel, args)]
  | .eq _ _ => []
  | .not φ => φ.atoms
  | .and φ ψ => φ.atoms ++ ψ.atoms
  | .or φ ψ => φ.atoms ++ ψ.atoms

/-- The truth value of a formula at the tuple `x` when the solution atom `q` has the truth
value written in `β` at the first position of `q` in the list `A`. -/
def QF.evalB (A : List (Nat × List Nat)) (G : Relations) (β : List Bool) (x : List Nat) :
    QF → Bool
  | .input rel args => G.holds rel (args.map fun i => x.getD i 0)
  | .sol rel args => β.getD (A.idxOf (rel, args)) false
  | .eq i j => decide (x.getD i 0 = x.getD j 0)
  | .not φ => !(φ.evalB A G β x)
  | .and φ ψ => φ.evalB A G β x && ψ.evalB A G β x
  | .or φ ψ => φ.evalB A G β x || ψ.evalB A G β x

/-- The ground atom obtained from the atom `q` at the tuple `t`. -/
def groundAtom (t : List Nat) (q : Nat × List Nat) : Nat × List Nat :=
  (q.1, q.2.map fun i => t.getD i 0)

/-- All ground atoms of the atoms `A` at the `k`-tuples of the universe `{0, …, n - 1}`. -/
def groundAtoms (A : List (Nat × List Nat)) (k n : Nat) : List (Nat × List Nat) :=
  (tuples n k).flatMap fun t => A.map (groundAtom t)

/-- The Boolean variables of the atoms `A` at the tuple `t`: positions in the list `gl` of
ground atoms. -/
def tupleVars (A gl : List (Nat × List Nat)) (t : List Nat) : List Nat :=
  A.map fun q => gl.idxOf (groundAtom t q)

/-- Make the values `β` of the variables `vs` consistent: every variable gets the value of
its first occurrence. -/
def normWord (vs : List Nat) (β : List Bool) : List Bool :=
  vs.map fun v => ((vs.zip β).lookup v).getD false

/-- The tuple `t` is kept: some consistent truth values of its atoms make `φ` true. -/
def keptTuple (φ : QF) (G : Relations) (gl : List (Nat × List Nat)) (t : List Nat) : Bool :=
  (allWords φ.atoms.length).any fun β =>
    φ.evalB φ.atoms G (normWord (tupleVars φ.atoms gl t) β) t

/-- The clause saying that the variables `vs` do not have the values `β`. -/
def negClause (vs : List Nat) (β : List Bool) : SAT.Clause :=
  List.zipWith (fun v b => (⟨v, !b⟩ : SAT.Literal)) vs β

/-- The long clauses of the tuple `t`: one for each word of truth values falsifying `φ`. -/
def emitted (φ : QF) (G : Relations) (gl : List (Nat × List Nat)) (t : List Nat) :
    List SAT.Clause :=
  ((allWords φ.atoms.length).filter fun β => !φ.evalB φ.atoms G β t).map
    (negClause (tupleVars φ.atoms gl t))

/-- The kept tuples of the structure `(n, G)`. -/
def keptTuples (k : Nat) (φ : QF) (n : Nat) (G : Relations) : List (List Nat) :=
  (tuples n k).filter fun t => keptTuple φ G (groundAtoms φ.atoms k n) t

/-- The long clauses of the structure `(n, G)`. -/
def longClauses (k : Nat) (φ : QF) (n : Nat) (G : Relations) : List SAT.Clause :=
  (keptTuples k φ n G).flatMap fun t => emitted φ G (groundAtoms φ.atoms k n) t

/-- Split a clause into clauses with at most three literals, with the fresh variables
`z, z + 1, …` (at most `m` of them): `l₁ ∨ l₂ ∨ rest` becomes `l₁ ∨ l₂ ∨ z` and the pieces of
`¬z ∨ rest`. -/
def splitN : Nat → Nat → SAT.Clause → List SAT.Clause
  | 0, _, ls => [ls]
  | m + 1, z, ls =>
    if ls.length ≤ 3 then [ls]
    else [ls.getD 0 ⟨0, true⟩, ls.getD 1 ⟨0, true⟩, ⟨z, true⟩] ::
      splitN m (z + 1) (⟨z, false⟩ :: ls.drop 2)

/-- Split the clauses of the list `Ls`, numbered from `s`; clause number `i` uses the fresh
variables `base + i * m, …, base + i * m + m - 1`. -/
def splitFrom (m base s : Nat) (Ls : List SAT.Clause) : SAT.CNF :=
  (Ls.zipIdx s).flatMap fun q => splitN m (base + q.2 * m) q.1

/-- The instance map: the pieces of the long clauses of the structure. -/
def snpToSat (k : Nat) (φ : QF) (p : Nat × Relations) : SAT.CNF :=
  splitFrom φ.atoms.length (groundAtoms φ.atoms k p.1).length 0 (longClauses k φ p.1 p.2)

/-- The relations with indices below `R` in which the ground atom `g` of the list `gl` holds
when its variable is true in `y`. -/
def relOfWord (gl : List (Nat × List Nat)) (R : Nat) (y : Word) : Relations :=
  (List.range R).map fun r =>
    (gl.filter fun g => g.1 == r && y.getD (gl.idxOf g) false).map Prod.snd

/-- A strict upper bound of the relation indices of the atoms `A`. -/
def relBound (A : List (Nat × List Nat)) : Nat := (A.map Prod.fst).sum + 1

/-- The solution map: the solution relations written by an assignment. -/
def satToSnp (k : Nat) (φ : QF) (p : Nat × Relations) (y : Word) : Relations :=
  relOfWord (groundAtoms φ.atoms k p.1) (relBound φ.atoms) y

/-- The relations, with indices `i, i + 1, …`, of a structure of signature `sa` over the
universe `{0, …, n - 1}` cut out of the relations `S`: the relation of arity `a` keeps the
`a`-tuples of the universe at which the corresponding relation of `S` holds. -/
def fitFrom : List Nat → Nat → Nat → Relations → Relations
  | [], _, _, _ => []
  | a :: sa, i, n, S => ((tuples n a).filter fun u => S.holds i u) :: fitFrom sa (i + 1) n S

/-- The structure of signature `sa` over the universe `{0, …, n - 1}` cut out of the relations
`S`. -/
def fitRel (sa : List Nat) (n : Nat) (S : Relations) : Relations := fitFrom sa 0 n S

end Complexity

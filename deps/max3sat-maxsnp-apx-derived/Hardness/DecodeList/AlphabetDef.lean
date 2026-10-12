module

public import Hardness.DecodeList.Common

/-!
# List form of the alphabet-reduction decoder: definition and polynomial time

`alphaList q V W L` is the list program for `Decode.alphabetDecode` (Step A of
`Hardness/Decode/NOTES.md` §2): for every `v < V` it scans the block
`L[E0 + v * 2 ^ q + r]`, `r < 2 ^ q`, `E0 = W * alphaLocalCount q`, and returns the least `a < q`
minimising the number of `r` at which bit `0` of the block entry differs from bit `a` of `r`.

Everything that depends only on `q` is a constant of the program: the block length `2 ^ q`,
the offset factor `alphaLocalCount q` and the table `tapeTable q` of all tapes in rank order
together with their bits.  Only the dependence on `(V, W, L)` is polynomial-time reasoning.

The equality with `alphabetDecode` is proved in `Hardness/DecodeList/Alphabet.lean`.
-/

@[expose] public section

set_option linter.dupNamespace false

namespace Complexity.DecodeList

open Complexity.PT
open OAI.UniqueGamesTheorem.Foundations.PCP.Decode

/-- Number of local events per dart of the alphabet-reduced table
(`AlphabetTable.Enumeration.localCount`), as a plain arithmetic expression. -/
def alphaLocalCount (q : Nat) : Nat := 4 * (2 * 2 ^ q) * (2 ^ (q * q)) ^ 5

/-- The constant dictator table: for every rank `r < 2 ^ q`, in increasing order, the pair of
`r` and the list of the bits `r / 2 ^ a % 2`, `a < q`, of the tape of rank `r`. -/
def tapeTable (q : Nat) : List (Nat × List Nat) :=
  (List.range (2 ^ q)).map fun r => (r, (List.range q).map fun a => r / 2 ^ a % 2)

/-- Number of table entries `(r, bits)` at which bit `0` of `L[base + r]` differs from
`bits[a]`. -/
def alphaCount (tbl : List (Nat × List Nat)) (L : List Nat) (base a : Nat) : Nat :=
  tbl.countP fun e => decide (L.getD (base + e.1) 0 % 2 ≠ e.2.getD a 0)

/-- List form of `alphabetDecode`: `V`, `W` are the numbers of vertices and darts of the powered
table, `L` the labeling of the alphabet-reduced table as a list. -/
def alphaList (q V W : Nat) (L : List Nat) : List Nat :=
  (List.range V).map fun v =>
    argMinUpTo (alphaCount (tapeTable q) L (W * alphaLocalCount q + v * 2 ^ q)) (q - 1)

@[simp] theorem alphaList_length (q V W : Nat) (L : List Nat) :
    (alphaList q V W L).length = V := by
  simp [alphaList]

theorem alphaList_getElem (q V W : Nat) (L : List Nat) (v : Nat)
    (hv : v < (alphaList q V W L).length) :
    (alphaList q V W L)[v] =
      argMinUpTo (alphaCount (tapeTable q) L (W * alphaLocalCount q + v * 2 ^ q)) (q - 1) := by
  simp [alphaList]

/-- The count against a constant table is polynomial-time in the labeling list, the block
offset and the candidate letter. -/
theorem pt_alphaCount (tbl : List (Nat × List Nat)) :
    PT (fun p : (List Nat × Nat) × Nat => alphaCount tbl p.1.1 p.1.2 p.2) := by
  unfold alphaCount
  fun_prop

/-- The alphabet-reduction decoder is polynomial-time (for every fixed `q`). -/
theorem pt_alphaList (q : Nat) :
    PT (fun p : (Nat × Nat) × List Nat => alphaList q p.1.1 p.1.2 p.2) := by
  unfold alphaList
  have hcount : PT (fun x : (((Nat × Nat) × List Nat) × Nat) × Nat =>
      alphaCount (tapeTable q) x.1.1.2
        (x.1.1.1.2 * alphaLocalCount q + x.1.2 * 2 ^ q) x.2) :=
    (pt_alphaCount (tapeTable q)).comp
      (f := fun y : (List Nat × Nat) × Nat => alphaCount (tapeTable q) y.1.1 y.1.2 y.2)
      (g := fun x : (((Nat × Nat) × List Nat) × Nat) × Nat =>
        ((x.1.1.2, x.1.1.1.2 * alphaLocalCount q + x.1.2 * 2 ^ q), x.2))
      (by fun_prop)
  have hbody : PT (fun x : ((Nat × Nat) × List Nat) × Nat =>
      argMinUpTo (alphaCount (tapeTable q) x.1.2
        (x.1.1.2 * alphaLocalCount q + x.2 * 2 ^ q)) (q - 1)) :=
    PT.argMinUpTo (count := fun (x : ((Nat × Nat) × List Nat) × Nat) (a : Nat) =>
        alphaCount (tapeTable q) x.1.2 (x.1.1.2 * alphaLocalCount q + x.2 * 2 ^ q) a)
      (k := fun _ => q - 1) hcount (PT.const _)
  exact PT.map (f := fun (p : (Nat × Nat) × List Nat) (v : Nat) =>
      argMinUpTo (alphaCount (tapeTable q) p.2
        (p.1.2 * alphaLocalCount q + v * 2 ^ q)) (q - 1))
    (l := fun p : (Nat × Nat) × List Nat => List.range p.1.1) hbody (by fun_prop)

end Complexity.DecodeList

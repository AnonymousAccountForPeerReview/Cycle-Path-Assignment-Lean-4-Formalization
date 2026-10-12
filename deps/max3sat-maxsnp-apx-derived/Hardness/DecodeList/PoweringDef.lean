module

public import Hardness.DecodeList.Common

/-!
# List form of the powering decoder: definition and polynomial time

`powerList d n N V rot ell` is the list program for `Decode.powerDecode` (Step B of
`Hardness/Decode/NOTES.md` §2).  Its inputs are the number `V` of vertices, the rotation of the
port table as a list (`rot[p + d * v] = p' + d * v'` when the dart `(v, p)` is reversed to
`(v', p')`) and the labeling `ell` of the powered table as a list of numbers `< 64 ^ C`.

* `stepList d rot x p = rot[p + d * x] / d` is the vertex reached from `x` through the port `p`;
  `walkList d rot w ports` applies the ports of a list in order.
* `opinionList d n rot ell w u` is the base-64 digit of `ell[w]` belonging to the first address
  (in the order of the constant table `addressTable d n`) whose walk from `w` ends in `u`, and
  `0` if there is none.
* `countList d n N rot ell u a` is the number of port words `p` of length `N` (constant table
  `wordsList d N`) such that `opinionList … (walkList d rot u p) u = a`.
* `powerList d n N V rot ell` lists, for `u < V`, the least `a ≤ 63` maximising that count.

Everything that depends only on `d`, `n`, `N` is a constant of the program: the list
`wordsList d N` of all port words of length `N`, and the table `addressTable d n` of all port
words of length `≤ n + 1` with the weights `64 ^ (C - 1 - rank)` of their digits.  Only the
dependence on `(V, rot, ell)` is polynomial-time reasoning: walking is a fold of list lookups
and one division by the constant `d`, a digit is a division and a remainder by constants.

The equality with `powerDecode` is proved in `Hardness/DecodeList/Powering.lean`.
-/

@[expose] public section

set_option linter.dupNamespace false

namespace Complexity.DecodeList

open Complexity.PT
open OAI.UniqueGamesTheorem.Foundations.PCP.Decode

/-! ### Constant tables -/

/-- All port words of length `k` over `{0, …, d - 1}` as lists, in lexicographic order with the
first port most significant (the order of `PoweringAddresses.allWords`). -/
def wordsList (d : Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | k + 1 => (List.range d).flatMap fun a => (wordsList d k).map fun p => a :: p

/-- `Σ_{i < k} d ^ i`: the number of port words of length `< k`. -/
def geomSum (d k : Nat) : Nat := ((List.range k).map fun i => d ^ i).sum

/-- The value of a port word read as a base-`d` numeral, first port most significant. -/
def wordValue (d : Nat) (ports : List Nat) : Nat := ports.foldl (fun acc x => acc * d + x) 0

/-- The rank of an address (`PoweringEnumeration.addressEquiv`): the number of shorter words plus
the value of the word. -/
def addressRank (d : Nat) (ports : List Nat) : Nat := geomSum d ports.length + wordValue d ports

/-- The weight `64 ^ (C - 1 - rank)` of the base-64 digit belonging to an address, where
`C = geomSum d (n + 2)` is the number of addresses (port words of length `≤ n + 1`). -/
def addressWeight (d n : Nat) (ports : List Nat) : Nat :=
  64 ^ (geomSum d (n + 2) - (addressRank d ports + 1))

/-- The constant address table: all port words of length `≤ n + 1`, by increasing length and
lexicographically for equal length (the order of `PoweringAddresses.allAddresses d (n + 1)`),
each with the weight of its base-64 digit. -/
def addressTable (d n : Nat) : List (List Nat × Nat) :=
  (List.range (n + 2)).flatMap fun len =>
    (wordsList d len).map fun ports => (ports, addressWeight d n ports)

/-! ### The program -/

/-- One step of a walk: the vertex `rot[p + d * x] / d` reached from `x` through the port `p`. -/
def stepList (d : Nat) (rot : List Nat) (x p : Nat) : Nat := rot.getD (p + d * x) 0 / d

/-- The end point of the walk from `w` along a list of ports. -/
def walkList (d : Nat) (rot : List Nat) (w : Nat) (ports : List Nat) : Nat :=
  ports.foldl (stepList d rot) w

/-- The opinion of `w` about `u` read from an address table: the digit `ell[w] / weight % 64` of
the first table entry whose walk from `w` ends in `u`, and `0` if there is none. -/
def opinionWith (tbl : List (List Nat × Nat)) (d : Nat) (rot ell : List Nat) (w u : Nat) : Nat :=
  (tbl.find? fun e => walkList d rot w e.1 == u).elim 0 fun e => ell.getD w 0 / e.2 % 64

/-- Number of the port words `p` of a list such that the opinion about `u` of the end point of
the walk `p` from `u` is `a`. -/
def countWith (tbl : List (List Nat × Nat)) (words : List (List Nat)) (d : Nat)
    (rot ell : List Nat) (u a : Nat) : Nat :=
  words.countP fun p => opinionWith tbl d rot ell (walkList d rot u p) u == a

/-- The opinion of `w` about `u` (`opinion(w, u)` of NOTES.md). -/
def opinionList (d n : Nat) (rot ell : List Nat) (w u : Nat) : Nat :=
  opinionWith (addressTable d n) d rot ell w u

/-- `count_u(a)` of NOTES.md. -/
def countList (d n N : Nat) (rot ell : List Nat) (u a : Nat) : Nat :=
  countWith (addressTable d n) (wordsList d N) d rot ell u a

/-- List form of `powerDecode`: `V` is the number of vertices, `rot` the rotation of the port
table as a list (`rotList`), `ell` the labeling of the powered table as a list. -/
def powerList (d n N : Nat) (V : Nat) (rot : List Nat) (ell : List Nat) : List Nat :=
  (List.range V).map fun u => argMaxUpTo (countList d n N rot ell u) 63

@[simp] theorem powerList_length (d n N V : Nat) (rot ell : List Nat) :
    (powerList d n N V rot ell).length = V := by
  simp [powerList]

theorem powerList_getElem (d n N V : Nat) (rot ell : List Nat) (u : Nat)
    (hu : u < (powerList d n N V rot ell).length) :
    (powerList d n N V rot ell)[u] = argMaxUpTo (countList d n N rot ell u) 63 := by
  simp [powerList]

/-! ### Polynomial time -/

theorem stepList_le_size (d : Nat) (rot : List Nat) (x p : Nat) :
    stepList d rot x p + 1 ≤ size rot := by
  unfold stepList
  have h1 : rot.getD (p + d * x) 0 / d ≤ rot.getD (p + d * x) 0 := Nat.div_le_self _ _
  have h2 : rot.getD (p + d * x) 0 + 1 ≤ size rot := by
    rw [List.getD_eq_getElem?_getD]
    cases h : rot[p + d * x]? with
    | none =>
      have := size_pos_list rot
      simp only [Option.getD_none]
      omega
    | some y =>
      have hy : y ∈ rot := List.mem_of_getElem? h
      have := size_le_of_mem hy
      simp only [size_nat, Option.getD_some] at this ⊢
      exact this
  omega

/-- Walking is polynomial-time in the rotation list, the start vertex and the port list: the
current vertex is always (after the first step) an entry of the rotation list divided by `d`. -/
theorem pt_walkList (d : Nat) :
    PT (fun p : List Nat × Nat × List Nat => walkList d p.1 p.2.1 p.2.2) := by
  unfold walkList
  refine PT.foldl_of_size_le (f := fun (a : List Nat × Nat × List Nat) s b => stepList d a.1 s b)
    (init := fun a => a.2.1) (l := fun a => a.2.2) ?_ (by fun_prop) (by fun_prop)
    (fun N => N) PolynomialBound.identity ?_
  · unfold stepList
    fun_prop
  · intro a s b _
    have := stepList_le_size d a.1 s b
    simp only [size_prod, size_nat]
    omega

@[fun_prop] protected theorem PT.walkList {α : Type} [Code α] (d : Nat) {rot : α → List Nat}
    {w : α → Nat} {ports : α → List Nat} (hrot : PT rot) (hw : PT w) (hports : PT ports) :
    PT (fun a => walkList d (rot a) (w a) (ports a)) :=
  PT.comp₃ (pt_walkList d) hrot hw hports

/-- The opinion against a constant address table is polynomial-time. -/
theorem pt_opinionWith (tbl : List (List Nat × Nat)) (d : Nat) :
    PT (fun p : (List Nat × List Nat) × Nat × Nat => opinionWith tbl d p.1.1 p.1.2 p.2.1 p.2.2) := by
  unfold opinionWith
  fun_prop

@[fun_prop] protected theorem PT.opinionWith {α : Type} [Code α] (tbl : List (List Nat × Nat))
    (d : Nat) {rot ell : α → List Nat} {w u : α → Nat} (hrot : PT rot) (hell : PT ell)
    (hw : PT w) (hu : PT u) :
    PT (fun a => opinionWith tbl d (rot a) (ell a) (w a) (u a)) :=
  (pt_opinionWith tbl d).comp
    (g := fun a => ((rot a, ell a), w a, u a)) (by fun_prop)

/-- The count against constant tables is polynomial-time. -/
theorem pt_countWith (tbl : List (List Nat × Nat)) (words : List (List Nat)) (d : Nat) :
    PT (fun p : (List Nat × List Nat) × Nat × Nat => countWith tbl words d p.1.1 p.1.2 p.2.1 p.2.2) := by
  unfold countWith
  fun_prop

/-- The powering decoder is polynomial-time (for all fixed `d`, `n`, `N`). -/
theorem pt_powerList (d n N : Nat) :
    PT (fun p : Nat × List Nat × List Nat => powerList d n N p.1 p.2.1 p.2.2) := by
  unfold powerList
  have hcount : PT (fun x : ((Nat × List Nat × List Nat) × Nat) × Nat =>
      countList d n N x.1.1.2.1 x.1.1.2.2 x.1.2 x.2) :=
    (pt_countWith (addressTable d n) (wordsList d N) d).comp
      (g := fun x : ((Nat × List Nat × List Nat) × Nat) × Nat =>
        ((x.1.1.2.1, x.1.1.2.2), x.1.2, x.2)) (by fun_prop)
  have hbody : PT (fun x : (Nat × List Nat × List Nat) × Nat =>
      argMaxUpTo (countList d n N x.1.2.1 x.1.2.2 x.2) 63) :=
    PT.argMaxUpTo (count := fun x : (Nat × List Nat × List Nat) × Nat =>
      countList d n N x.1.2.1 x.1.2.2 x.2) hcount (PT.const 63)
  exact PT.map (f := fun (p : Nat × List Nat × List Nat) u =>
    argMaxUpTo (countList d n N p.2.1 p.2.2 u) 63) hbody (by fun_prop)

end Complexity.DecodeList

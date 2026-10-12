module

public import Hardness.DecodeList.PoweringDef
public import Hardness.Decode.PoweringTable

/-!
# List form of the powering decoder: specification

`powerList_spec`: on the rotation list `rotList P` of a port table and the list of an encoded
labeling, the list program `powerList` of `Hardness/DecodeList/PoweringDef.lean` returns the list
of `Decode.powerDecode P n N labels`.

The proof identifies, in this order,

* one step and whole walks of the list program with `PoweringWalks.next`/`wordEnd` in
  `PortTables.portGraph P` (`stepList_eq`, `walkList_portsOf`);
* the constant tables with the vendored enumerations: `wordsList d k` is
  `PoweringAddresses.allWords d k` (`wordsList_eq`), `addressTable d n` is
  `PoweringAddresses.allAddresses d (n + 1)` with the digit weights given by
  `PoweringEnumeration.addressEquiv` (`addressTable_eq`, through `addressEquiv_val`,
  `wordEquiv_val`);
* the digit `ell[w] / weight % 64` with `PoweringTableSemantics.decodeLabeling`
  (`decodeLabeling_val`);
* the first-match scan with `sampledOpinion` (`Decode.sampledOpinion_eq_find`) and the count over
  the list `allWords d N` with the cardinality in `opinionCount` (`countList_eq`).
-/

@[expose] public section

set_option linter.dupNamespace false

namespace Complexity.DecodeList

open OAI OAI.UniqueGamesTheorem.Foundations.PCP
open OAI.UniqueGamesTheorem.Foundations.PCP.Decode
open PoweringWalks PoweringLabels PoweringAddresses PoweringEnumeration PoweringTableSemantics

/-- The rotation of a port table as a list: entry `p + d * v` is the stored reverse index
`p' + d * v'` of the dart `(v, p)`. -/
def rotList {V d : Nat} (P : PortTables.Table V d) : List Nat :=
  List.ofFn fun i : Fin (V * d) => (P.reverseIndex[i]).val

/-- A port word as the list of its ports. -/
def portsOf {d len : Nat} (p : Fin len → Fin d) : List Nat :=
  List.ofFn fun i => (p i).val

@[simp] theorem portsOf_length {d len : Nat} (p : Fin len → Fin d) : (portsOf p).length = len := by
  simp [portsOf]

theorem portsOf_succ {d len : Nat} (p : Fin (len + 1) → Fin d) :
    portsOf p = (p 0).val :: portsOf (fun j => p j.succ) := by
  simp only [portsOf, List.ofFn_succ]

theorem portsOf_cases {d len : Nat} (a : Fin d) (p : Fin len → Fin d) :
    portsOf (Fin.cases a p : Fin (len + 1) → Fin d) = a.val :: portsOf p := by
  rw [portsOf_succ]
  rfl

section Walks

variable {V d : Nat}

theorem rotList_getD (P : PortTables.Table V d) (i : Fin (V * d)) :
    (rotList P).getD i.val 0 = (P.reverseIndex[i]).val := by
  simp [rotList, List.getD_eq_getElem?_getD]

/-- One step of the list walk is `PoweringWalks.next` in the port graph of the table. -/
theorem stepList_eq (P : PortTables.Table V d) (v : Fin V) (p : Fin d) :
    stepList d (rotList P) v.val p.val = (next (PortTables.portGraph P) v p).val := by
  have h := rotList_getD P (PortTables.rowIndex V d (v, p))
  rw [PortTables.rowIndex_val] at h
  unfold stepList
  rw [h]
  rfl

/-- The list walk along the ports of a word is `PoweringWalks.wordEnd`. -/
theorem walkList_portsOf (P : PortTables.Table V d) :
    ∀ (len : Nat) (v : Fin V) (p : Fin len → Fin d),
      walkList d (rotList P) v.val (portsOf p) =
        (wordEnd (PortTables.portGraph P) len v p).val
  | 0, v, p => by simp [walkList, portsOf, wordEnd]
  | len + 1, v, p => by
    have ih := walkList_portsOf P len (next (PortTables.portGraph P) v (p 0)) (fun j => p j.succ)
    rw [portsOf_succ]
    unfold walkList at ih ⊢
    rw [List.foldl_cons, stepList_eq, ih]
    rfl

end Walks

section Tables

/-- The constant word list enumerates `PoweringAddresses.allWords` in the same order. -/
theorem wordsList_eq (d : Nat) : ∀ k, wordsList d k = (PoweringAddresses.allWords d k).map portsOf
  | 0 => by simp [wordsList, PoweringAddresses.allWords, portsOf]
  | k + 1 => by
    rw [wordsList, PoweringAddresses.allWords, wordsList_eq d k, List.map_flatMap, ← List.map_coe_finRange_eq_range,
      List.flatMap_map]
    congr 1
    funext a
    rw [List.map_map, List.map_map]
    congr 1
    funext p
    exact (portsOf_cases a p).symm

theorem geomSum_succ (d k : Nat) : geomSum d (k + 1) = geomSum d k + d ^ k := by
  simp [geomSum, List.range_succ]

theorem sum_pow_eq_geomSum (d : Nat) : ∀ k, (∑ i : Fin k, d ^ i.val) = geomSum d k
  | 0 => by simp [geomSum]
  | k + 1 => by
    rw [Fin.sum_univ_castSucc, geomSum_succ, ← sum_pow_eq_geomSum d k]
    rfl

theorem addressCount_eq_geomSum (d t : Nat) : addressCount d t = geomSum d (t + 1) :=
  sum_pow_eq_geomSum d (t + 1)

theorem foldl_wordValue (d : Nat) (l : List Nat) (acc : Nat) :
    l.foldl (fun acc x => acc * d + x) acc = acc * d ^ l.length + wordValue d l := by
  unfold wordValue
  induction l generalizing acc with
  | nil => simp
  | cons x t ih =>
    rw [List.foldl_cons, List.foldl_cons, ih, ih (0 * d + x), List.length_cons, Nat.pow_succ]
    simp only [Nat.zero_mul, Nat.zero_add, Nat.add_mul, Nat.mul_assoc, Nat.add_assoc,
      Nat.mul_comm d]

theorem wordValue_cons (d x : Nat) (l : List Nat) :
    wordValue d (x :: l) = x * d ^ l.length + wordValue d l := by
  have h := foldl_wordValue d l (0 * d + x)
  rw [Nat.zero_mul, Nat.zero_add] at h
  rw [← h]
  unfold wordValue
  rw [List.foldl_cons, Nat.zero_mul, Nat.zero_add]

/-- The rank of a word among the words of its length is its base-`d` value. -/
theorem wordEquiv_val_eq (d : Nat) :
    ∀ (len : Nat) (p : Fin len → Fin d), (wordEquiv d len p).val = wordValue d (portsOf p)
  | 0, p => by simp [wordValue, portsOf]
  | len + 1, p => by
    have ih := wordEquiv_val_eq d len (fun j => p j.succ)
    rw [wordEquiv_val] at ih ⊢
    rw [portsOf_succ, wordValue_cons, portsOf_length, Fin.sum_univ_castSucc, ← ih, Fin.rev_last,
      Nat.add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [Fin.rev_castSucc]
    rfl

theorem addressRank_eq (d t : Nat) (a : PortWords (Fin d) t) :
    (addressEquiv d t a).val = addressRank d (portsOf a.2) := by
  rw [addressEquiv_val, sum_pow_eq_geomSum, wordEquiv_val_eq]
  unfold addressRank
  rw [portsOf_length]

theorem addressWeight_eq (d n : Nat) (a : PortWords (Fin d) (n + 1)) :
    addressWeight d n (portsOf a.2) = 64 ^ (addressEquiv d (n + 1) a).rev.val := by
  unfold addressWeight
  rw [Fin.val_rev, addressRank_eq, addressCount_eq_geomSum]

/-- The constant address table enumerates `PoweringAddresses.allAddresses d (n + 1)` in the same
order, with the weight of the digit of each address. -/
theorem addressTable_eq (d n : Nat) :
    addressTable d n = (allAddresses d (n + 1)).map fun a =>
      (portsOf a.2, 64 ^ (addressEquiv d (n + 1) a).rev.val) := by
  unfold addressTable allAddresses
  rw [List.map_flatMap, ← List.map_coe_finRange_eq_range, List.flatMap_map]
  congr 1
  funext len
  rw [wordsList_eq, List.map_map, List.map_map]
  congr 1
  funext p
  exact Prod.ext rfl (addressWeight_eq d n ⟨len, p⟩)

end Tables

section Digits

/-- The digit of an encoded label at an address: division by the weight of the address and
remainder modulo `64`. -/
theorem decodeLabeling_val {V : Nat} (d n : Nat) (labels : EncodedLabeling V d n) (w : Fin V)
    (a : PortWords (Fin d) (n + 1)) :
    (decodeLabeling d n labels w a).val =
      (labels w).val / 64 ^ (addressEquiv d (n + 1) a).rev.val % 64 := rfl

end Digits

section Counting

/-- Counting over a duplicate-free list of all elements of a finite type. -/
theorem countP_eq_card_filter {α : Type*} [Fintype α] [DecidableEq α] (l : List α)
    (hnodup : l.Nodup) (hmem : ∀ x, x ∈ l) (q : α → Prop) [DecidablePred q] :
    l.countP (fun x => decide (q x)) = (Finset.univ.filter q).card := by
  rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup (hnodup.filter _)]
  congr 1
  ext x
  simp [hmem]

theorem nodup_allWords (d N : Nat) : (PoweringAddresses.allWords d N).Nodup := by
  rw [← Multiset.coe_nodup, ← Multiset.toFinset_card_eq_card_iff_nodup]
  have h : (↑(PoweringAddresses.allWords d N) : Multiset (Fin N → Fin d)).toFinset = Finset.univ := by
    ext p
    simp [mem_allWords]
  rw [h, Multiset.coe_card, length_allWords]
  simp

theorem argMaxUpTo_congr {f g : Nat → Nat} (k : Nat) (h : ∀ i, i ≤ k → f i = g i) :
    argMaxUpTo f k = argMaxUpTo g k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have ih' := ih fun i hi => h i (Nat.le_succ_of_le hi)
    simp only [argMaxUpTo]
    rw [← ih', h (k + 1) (Nat.le_refl _),
      h (argMaxUpTo f k) (Nat.le_succ_of_le (argMaxUpTo_le f k))]

end Counting

section Spec

variable {V d : Nat}

/-- The list opinion of `w` about `u` is the first-match opinion of `sampledOpinion_eq_find`. -/
theorem opinionList_eq (P : PortTables.Table V d) (n : Nat) (labels : EncodedLabeling V d n)
    (w u : Fin V) :
    opinionList d n (rotList P) (labelList labels) w.val u.val =
      (((allAddresses d (n + 1)).find? (fun a => decide
        (wordEnd (PortTables.portGraph P) a.1.val w a.2 = u))).elim (0 : Fin 64)
        (decodeLabeling d n labels w)).val := by
  unfold opinionList opinionWith
  rw [addressTable_eq, List.find?_map]
  have hpred : ((fun e : List Nat × Nat => walkList d (rotList P) w.val e.1 == u.val) ∘
      fun a : PortWords (Fin d) (n + 1) =>
        (portsOf a.2, 64 ^ (addressEquiv d (n + 1) a).rev.val)) =
      fun a => decide (wordEnd (PortTables.portGraph P) a.1.val w a.2 = u) := by
    funext a
    rw [Function.comp_apply, walkList_portsOf, Bool.eq_iff_iff]
    simp [Fin.ext_iff]
  rw [hpred]
  cases (allAddresses d (n + 1)).find? (fun a => decide
      (wordEnd (PortTables.portGraph P) a.1.val w a.2 = u)) with
  | none => rfl
  | some a =>
    simp only [Option.map_some, Option.elim_some]
    rw [labelList_getD, decodeLabeling_val]

theorem countList_eq (P : PortTables.Table V d) (n N : Nat) (labels : EncodedLabeling V d n)
    (u : Fin V) (a : Fin 64) :
    countList d n N (rotList P) (labelList labels) u.val a.val =
      opinionCount P n N labels u a := by
  unfold countList countWith opinionCount
  rw [wordsList_eq, List.countP_map,
    ← countP_eq_card_filter (PoweringAddresses.allWords d N) (nodup_allWords d N) (mem_allWords d N)]
  congr 1
  funext p
  rw [Function.comp_apply, walkList_portsOf, sampledOpinion_eq_find, Bool.eq_iff_iff]
  have h := opinionList_eq P n labels (wordEnd (PortTables.portGraph P) N u p) u
  unfold opinionList at h
  rw [h]
  simp [Fin.ext_iff]

/-- **Specification of the powering list program.** -/
theorem powerList_spec (P : PortTables.Table V d) (n N : Nat)
    (labels : EncodedLabeling V d n) :
    powerList d n N V (rotList P) (labelList labels) = labelList (powerDecode P n N labels) := by
  apply List.ext_getElem
  · simp
  · intro u h1 h2
    have hu : u < V := by simpa using h1
    have hr : (labelList (powerDecode P n N labels))[u] =
        (powerDecode P n N labels ⟨u, hu⟩).val := by
      simp [labelList]
    rw [powerList_getElem, hr]
    unfold powerDecode leastArgMax
    apply argMaxUpTo_congr
    intro a ha
    have ha' : a < 64 := Nat.lt_succ_of_le ha
    rw [countList_eq P n N labels ⟨u, hu⟩ ⟨a, ha'⟩]
    simp [extendCount, ha']

end Spec

end Complexity.DecodeList

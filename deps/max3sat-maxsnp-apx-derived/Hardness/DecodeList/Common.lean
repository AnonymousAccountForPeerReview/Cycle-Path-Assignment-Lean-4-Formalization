module

public import Hardness.Decode.Selectors
public import PT.All

/-!
# Shared conventions for the list-level decoders

Labelings `Fin n → Fin m` are represented by the list of their values, and the deterministic
selectors of `Hardness/Decode/Selectors.lean` are polynomial-time in the `PT` framework.
-/

@[expose] public section

set_option linter.dupNamespace false

namespace Complexity.DecodeList

open Complexity.PT
open OAI.UniqueGamesTheorem.Foundations.PCP.Decode

/-- A labeling as the list of its values. -/
def labelList {n m : Nat} (L : Fin n → Fin m) : List Nat :=
  List.ofFn fun i => (L i).val

@[simp] theorem labelList_length {n m : Nat} (L : Fin n → Fin m) : (labelList L).length = n := by
  simp [labelList]

theorem labelList_getD {n m : Nat} (L : Fin n → Fin m) (i : Fin n) (d : Nat) :
    (labelList L).getD i.val d = (L i).val := by
  simp [labelList, List.getD_eq_getElem?_getD]

theorem labelList_getD_of_lt {n m : Nat} (L : Fin n → Fin m) {i : Nat} (hi : i < n) (d : Nat) :
    (labelList L).getD i d = (L ⟨i, hi⟩).val :=
  labelList_getD L ⟨i, hi⟩ d

theorem labelList_injective {n m : Nat} {L L' : Fin n → Fin m} (h : labelList L = labelList L') :
    L = L' := by
  funext i
  apply Fin.ext
  have := congrArg (fun l => l.getD i.val 0) h
  simp only [labelList_getD] at this
  exact this

variable {α : Type} [Code α]

/-- The least arg-max scan is polynomial-time when the counting function is. -/
protected theorem PT.argMaxUpTo {count : α → Nat → Nat} {k : α → Nat}
    (hcount : PT (fun p : α × Nat => count p.1 p.2)) (hk : PT k) :
    PT (fun a => argMaxUpTo (count a) (k a)) := by
  obtain ⟨c, e, hke⟩ := hk.nat_le
  refine PT.of_natRec (g := fun a i => argMaxUpTo (count a) i) (base := fun _ => 0)
    (step := fun a i s => if count a s < count a (i + 1) then i + 1 else s)
    (PT.const 0) ?_ hk (fun _ => rfl) (fun _ _ => rfl)
    (fun N => powerBound c e N + 1) ((PolynomialBound.power c e).add (PolynomialBound.constant 1)) ?_
  · have h1 : PT (fun p : α × Nat × Nat => count p.1 p.2.2) :=
      hcount.comp (PT.pair PT.fst' (PT.snd (PT.snd' )))
    have h2 : PT (fun p : α × Nat × Nat => count p.1 (p.2.1 + 1)) :=
      hcount.comp (PT.pair PT.fst' (PT.succ (PT.fst (PT.snd'))))
    fun_prop
  · intro a i hi
    have h1 := argMaxUpTo_le (count a) i
    have h2 := hke a
    simp only [size_nat]
    omega

/-- The least arg-min scan is polynomial-time when the counting function is. -/
protected theorem PT.argMinUpTo {count : α → Nat → Nat} {k : α → Nat}
    (hcount : PT (fun p : α × Nat => count p.1 p.2)) (hk : PT k) :
    PT (fun a => argMinUpTo (count a) (k a)) := by
  obtain ⟨c, e, hke⟩ := hk.nat_le
  refine PT.of_natRec (g := fun a i => argMinUpTo (count a) i) (base := fun _ => 0)
    (step := fun a i s => if count a (i + 1) < count a s then i + 1 else s)
    (PT.const 0) ?_ hk (fun _ => rfl) (fun _ _ => rfl)
    (fun N => powerBound c e N + 1) ((PolynomialBound.power c e).add (PolynomialBound.constant 1)) ?_
  · have h1 : PT (fun p : α × Nat × Nat => count p.1 p.2.2) :=
      hcount.comp (PT.pair PT.fst' (PT.snd (PT.snd' )))
    have h2 : PT (fun p : α × Nat × Nat => count p.1 (p.2.1 + 1)) :=
      hcount.comp (PT.pair PT.fst' (PT.succ (PT.fst (PT.snd'))))
    fun_prop
  · intro a i hi
    have h1 := argMinUpTo_le (count a) i
    have h2 := hke a
    simp only [size_nat]
    omega

end Complexity.DecodeList

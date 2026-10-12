module

public import ComplexityExt.Witness.Extract
public import Complexity.CookLevin
import Lean.Elab.Tactic.Omega

/-!
# Soundness of the ANONYMIZED–ANONYMIZED tableau with an explicit certificate

Every satisfying assignment of the tableau formula `CookLevin.formula` (not
merely its satisfiability) determines an accepting run: the certificate is the
word `Witness.readCells` reads from the one-hot variables of the initial row.
-/

@[expose] public section

namespace Complexity.Witness

open Complexity.SAT Complexity.CSPSAT Complexity.FiniteRows

theorem getD_map_bit_eq_blank_iff (word : List Bool) (i : Nat) :
    (word.map Symbol.bit).getD i .blank = .blank ↔ word.length ≤ i := by
  simp only [List.getD, List.getElem?_map]
  by_cases hi : i < word.length
  · simp [List.getElem?_eq_getElem hi]
    omega
  · simp [List.getElem?_eq_none (by omega : word.length ≤ i)]
    omega

theorem getD_map_bit_of_lt (word : List Bool) (i : Nat) (hi : i < word.length) :
    (word.map Symbol.bit).getD i .blank = .bit word[i] := by
  simp [List.getD, List.getElem?_eq_getElem hi]

/-- A satisfying assignment of the tableau formula encodes an accepting run on
the fixed prefix followed by the certificate read from the initial row. -/
theorem formula_sound (M : Machine) (width steps : Nat) (hwidth : 0 < width)
    (pfx : List Bool) (bound : Nat) (fit : pfx.length + bound ≤ width)
    (hsize : pfx.length + bound + 2 * steps ≤ width)
    (a : Assignment)
    (ha : evalCNF a (CookLevin.formula M width steps hwidth pfx bound fit) = true) :
    ∃ tape, runInput M steps
      (pfx ++ readCells M.states width pfx.length bound a) = some (true, tape) := by
  unfold CookLevin.formula at ha
  obtain ⟨hrows, htuples⟩ := (CSPSAT.encode_correct a _).mp ha
  have hsat : Satisfied (valuationOf a hrows)
      (Tableau.problem (CookLevin.transitionSystem M width hwidth) steps
        (InitialWord.problem M width pfx bound fit) (CookLevin.accepting M width)) := by
    intro t ht
    obtain ⟨atom, hatom, hafalse⟩ := htuples t ht
    refine ⟨atom, hatom, ?_⟩
    intro heq
    have hatrue := (valuationOf_atom a hrows atom).mpr heq
    simp [hafalse] at hatrue
  obtain ⟨hi, ht, hf⟩ := (Tableau.problem_correct _ steps _ _ _).mp hsat
  have hlast := Tableau.rowAt_iterate_of_transitions _ steps _ ht (Fin.last steps)
  rw [hlast, Fin.val_last] at hf
  obtain ⟨witness, hw, hrow⟩ := (InitialWord.problem_iff M width pfx bound fit _).mp hi
  have hcell : ∀ i, i < bound → ∀ j : Value M,
      (a (cellVar M.states width pfx.length i j.val) = true ↔
        symbolValue M ((witness.map Symbol.bit).getD i .blank) = j) := by
    intro i hib j
    have hslot : pfx.length + i < width := by omega
    have key := valuationOf_atom a hrows
      (Tableau.cell (0 : Fin (steps + 1)) (rightSlot width ⟨pfx.length + i, hslot⟩), j)
    have hidx : atomIndex (m := (steps + 1) * (2 * width + 1)) (d := M.states + 3)
        (Tableau.cell (0 : Fin (steps + 1)) (rightSlot width ⟨pfx.length + i, hslot⟩), j) =
        cellVar M.states width pfx.length i j.val := by
      simp [atomIndex, Tableau.cell, rightSlot, cellVar]
    have hval : valuationOf a hrows
        (Tableau.cell (0 : Fin (steps + 1)) (rightSlot width ⟨pfx.length + i, hslot⟩)) =
        symbolValue M ((witness.map Symbol.bit).getD i .blank) := by
      have h := congrFun hrow (rightSlot width ⟨pfx.length + i, hslot⟩)
      rw [InitialWord.encode_window, encode_right] at h
      simp only [Status.tape, initial, Tape.ofInput, List.map_append] at h
      rw [InitialWord.getD_append_right (by simp)] at h
      simpa [Tableau.rowAt] using h
    rw [hidx] at key
    rw [key]
    change valuationOf a hrows _ = j ↔ _
    rw [hval]
  have hread : readCells M.states width pfx.length bound a = witness := by
    apply readCells_eq _ _ _ _ _ _ hw
    · intro i hib
      rw [← getD_map_bit_eq_blank_iff]
      have h := hcell i hib (symbolValue M .blank)
      exact h.trans ⟨fun h => symbolValue_injective M h, fun h => congrArg _ h⟩
    · intro i hi
      have h := hcell i (by omega) (symbolValue M (.bit true))
      rw [getD_map_bit_of_lt witness i hi] at h
      apply Bool.eq_iff_iff.mpr
      refine h.trans ⟨fun h => ?_, fun h => by rw [h]⟩
      have hs := symbolValue_injective M h
      simpa using hs
  rw [hread]
  have hinput : (pfx ++ witness).length + 2 * steps ≤ width := by
    simp only [List.length_append]
    omega
  rw [hrow] at hf
  exact (CookLevin.iterate_initialRow_accepted_iff M width hwidth steps _ hinput).mp hf

/-- The same statement for the total generator `CookLevin.compile`. -/
theorem compile_sound (M : Machine) (steps : Nat) (pfx : List Bool) (bound : Nat)
    (a : Assignment) (ha : evalCNF a (CookLevin.compile M steps pfx bound) = true) :
    ∃ tape, runInput M steps
      (pfx ++ readCells M.states (CookLevin.windowWidth steps pfx bound) pfx.length bound a) =
        some (true, tape) := by
  apply formula_sound M _ steps _ pfx bound _ _ a ha
  unfold CookLevin.windowWidth
  omega

end Complexity.Witness

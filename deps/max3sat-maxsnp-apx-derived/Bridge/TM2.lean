module

public import Mathlib.Computability.TuringMachine.Computable
public import Complexity.StackCompile
public import Bridge.TM2.Sim
public import Mathlib.SetTheory.Cardinal.NatCard

/-!
# From Mathlib's TM2 polynomial-time computability to Boolean-stack machines

A polynomial-time `Turing.FinTM2` computation whose stack alphabets are all finite is
simulated, with polynomial overhead, by a `Complexity.StackMachine.Machine`.
-/

@[expose] public section

namespace Bridge

open Turing

attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.σFin

/-- The simulation data attached to a polynomial-time TM2 computation with finite alphabets. -/
noncomputable def setupOf {α β : Type} {ea : α → List Bool} {eb : β → List Bool} {f : α → β}
    (h : Turing.TM2ComputableInPolyTime ea eb f) (hfin : ∀ k, Finite (h.tm.Γ k)) : Setup where
  tm := h.tm
  inp := h.inputAlphabet.invFun
  out := h.outputAlphabet.toFun
  N := Finset.univ.sup fun k => Nat.card (h.tm.Γ k)
  idx k g := haveI := hfin k; (Finite.equivFin (h.tm.Γ k) g).val
  idx_lt k g := by
    have := hfin k
    exact lt_of_lt_of_le (Finite.equivFin (h.tm.Γ k) g).isLt
      (Finset.le_sup (f := fun k => Nat.card (h.tm.Γ k)) (Finset.mem_univ k))
  idx_inj k := by
    have := hfin k
    intro a b hab
    exact (Finite.equivFin (h.tm.Γ k)).injective (Fin.ext hab)

/-- A polynomial-time TM2 computation with finite stack alphabets is simulated by a
Boolean-stack machine in polynomial time, on every encoded input. -/
theorem stack_of_tm2 {α β : Type} {ea : α → List Bool} {eb : β → List Bool} {f : α → β}
    (h : Turing.TM2ComputableInPolyTime ea eb f) (hfin : ∀ k, Finite (h.tm.Γ k)) :
    ∃ S : Complexity.StackMachine.Machine, ∃ bound : Nat → Nat,
      Complexity.PolynomialBound bound ∧
      ∀ a, ∃ time registers, time ≤ bound (ea a).length ∧
        Complexity.StackMachine.runInput S time (ea a) = some (true, registers) ∧
        registers 0 = eb (f a) := by
  let s : Setup := setupOf h hfin
  refine ⟨Complexity.StackProgram.compile s.prog (encodingOfFintype (Setup.Label s) .done),
    fun n => s.total n (h.time.eval n), s.total_poly _ (polynomialBound_eval h.time), ?_⟩
  intro a
  obtain ⟨⟨t, ht⟩, htle⟩ := h.outputsFun a
  have ht' : (flip bind (TM2.step s.tm.m))^[t]
      (some (initList s.tm ((ea a).map s.inp))) =
      some (haltList s.tm (List.map h.outputAlphabet.invFun (eb (f a)))) := ht
  obtain ⟨time, r', h1, h2, h3⟩ := s.simulate (ea a) t _ ht'
  have hout : List.map h.outputAlphabet.toFun (List.map h.outputAlphabet.invFun (eb (f a))) =
      eb (f a) := by
    have hid : h.outputAlphabet.toFun ∘ h.outputAlphabet.invFun = id := by
      funext b
      exact h.outputAlphabet.right_inv b
    rw [List.map_map, hid, List.map_id]
  refine ⟨time, r', Nat.le_trans h1 (s.total_mono _ htle), ?_, h3.trans hout⟩
  rw [runInput_compile]
  exact h2

end Bridge

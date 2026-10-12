module

public import Bridge.TM2
public import ComplexityExt.Reg.Clocked

/-!
# Total polynomial-time functions from Mathlib's TM2 polynomial-time computability

`Bridge.stack_of_tm2` simulates a polynomial-time `Turing.FinTM2` computation by a
Boolean-stack machine, but only on encoded inputs `ea a`.  The clocked simulation of
`Complexity/Reg/Clocked.lean` turns this into a function that is polynomial-time computable
on *all* binary words (`Complexity.PolyTime`) and agrees with the TM2 computation on every
encoded input.
-/

@[expose] public section

namespace Bridge

/-- A polynomial-time TM2 computation with finite alphabets yields a total polynomial-time
function on words that agrees with it on all encoded inputs. -/
theorem exists_polyTime_of_tm2 {α β : Type} {ea : α → List Bool} {eb : β → List Bool}
    {f : α → β} (h : Turing.TM2ComputableInPolyTime ea eb f) (hfin : ∀ k, Finite (h.tm.Γ k)) :
    ∃ F : Complexity.Word → Complexity.Word, Complexity.PolyTime F ∧
      ∀ a, F (ea a) = eb (f a) := by
  obtain ⟨S, bound, hb, hS⟩ := stack_of_tm2 h hfin
  obtain ⟨F, hF, hagree⟩ := Complexity.Reg.exists_polyTime_of_stack_run S bound hb
  refine ⟨F, hF, fun a => ?_⟩
  obtain ⟨time, registers, ht, hrun, hout⟩ := hS a
  exact (hagree (ea a) time registers ht hrun).trans hout

end Bridge

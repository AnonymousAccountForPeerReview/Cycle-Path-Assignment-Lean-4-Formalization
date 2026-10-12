module
public import NPHardness.PlanarBoundedMembershipSemantic
import Lean.Elab.Tactic.Omega
@[expose] public section
namespace STACS2027.PlanarBoundedMembership
open Complexity Complexity.SAT Complexity.Planar Complexity.Planar.Vf Complexity.Planar.Chk
open Complexity.StackTableauEmitter

/-- The registered certificate-length wrapper, parameterized by a finite check.
The compiler and its polynomial-time proof are the unchanged registered implementation. -/
def checkedProgram (check : C) : ClauseProgram 1 :=
  .forDown (.var 0) (.ifLe lenExpr (.var 1)
    (.ifLe (.var 1) lenExpr (.seq (.clause []) (check.compile σv)) .skip) .skip)

theorem checkedProgram_emit (check : C) (u : List Bool) :
    (checkedProgram check).emit u (fun _ => u.length) = [[]] ↔
      ∃ L, totalLen L = u.length ∧
        Holds u check (fun t => if t = sL then L else u.length) := by
  let E := fun L => (check.compile σv).emit u (extend L (fun _ => u.length))
  let G := fun L => if totalLen L = u.length then [] :: E L else []
  have hstep : ∀ L, (ClauseProgram.ifLe lenExpr (.var 1)
      (.ifLe (.var 1) lenExpr (.seq (.clause []) (check.compile σv)) .skip)
      .skip).emit u (extend L (fun _ => u.length)) = G L := by
    intro L
    have h1 : (NumExpr.var 1 : NumExpr 2).eval (extend L (fun _ => u.length)) = u.length := rfl
    simp only [ClauseProgram.emit, eval_lenExpr, h1, extend_zero, G]
    by_cases hL : totalLen L = u.length
    · simp [hL, E]
    · by_cases h2 : totalLen L ≤ u.length
      · simp [hL, h2, show ¬ u.length ≤ totalLen L by omega]
      · simp [hL, h2]
  have hE : ∀ L, E L = [] ↔ Holds u check (fun t => if t = sL then L else u.length) := by
    intro L
    apply compile_holds
    intro t
    by_cases ht : t = sL
    · subst ht; rfl
    · simp only [σv, ht, ite_false]; rfl
  simp only [checkedProgram, ClauseProgram.emit_forDown, hstep]
  have hb : (NumExpr.var 0 : NumExpr 1).eval (fun _ => u.length) = u.length := rfl
  rw [hb]
  by_cases hex : ∃ L, totalLen L = u.length
  · obtain ⟨L0, hL0⟩ := hex
    have hlt : L0 < u.length := hL0 ▸ lt_totalLen L0
    rw [flatMap_single G L0 _ (by simp [hlt])
      (List.pairwise_reverse.mpr (List.nodup_range.imp fun h => Ne.symm h))
      (by
        intro a _ hne
        simp only [G]
        have : totalLen a ≠ u.length := fun h => hne (totalLen_inj (h.trans hL0.symm))
        simp [this])]
    simp only [G, hL0, ite_true, List.cons.injEq, true_and]
    constructor
    · intro h; exact ⟨L0, hL0, (hE L0).mp h⟩
    · rintro ⟨L, hL, hh⟩
      have := totalLen_inj (hL.trans hL0.symm)
      subst this
      exact (hE L).mpr hh
  · have hz : (List.range u.length).reverse.flatMap G = [] := by
      rw [flatMap_eq_nil_iff]
      intro a _
      have : totalLen a ≠ u.length := fun h => hex ⟨a, h⟩
      simp [G, this]
    rw [hz]
    constructor
    · intro h; cases h
    · rintro ⟨L, hL, _⟩; exact absurd ⟨L, hL⟩ hex

end STACS2027.PlanarBoundedMembership

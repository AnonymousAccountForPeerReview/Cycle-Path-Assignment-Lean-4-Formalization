module
public import NPHardness.PlanarBoundedMembershipFacts
import Lean.Elab.Tactic.Omega
@[expose] public section
namespace STACS2027.PlanarBoundedMembership
open Complexity Complexity.SAT Complexity.Planar Complexity.Planar.Vf Complexity.Planar.Chk

/-- Local finite checks for the additional Definition 7 restrictions. -/
structure TableCaps (t : ParseTables) : Prop where
  two : ∀ j, j < t.m → 2 ≤ t.kk j
  positive : ∀ i j, i < t.M → j < t.M → t.S i = 1 → t.S j = 1 → t.V i = t.V j → i = j
  negative : ∀ i j k, i < t.M → j < t.M → k < t.M →
    t.S i ≠ 1 → t.S j ≠ 1 → t.S k ≠ 1 → t.V i = t.V j → t.V i = t.V k →
      i = j ∨ i = k ∨ j = k

def cTwo : C := .all tj (E sm) (rd 1 (E tj) tc (reqLe (k 2) (E tc)))

def cPositive : C :=
  .all ti (E sM) (.all tj (E sM)
    (rd 8 (E ti) ta (rd 8 (E tj) tb
      (whenEq (E ta) (k 1) (whenEq (E tb) (k 1)
        (rd 7 (E ti) tc (rd 7 (E tj) td
          (whenEq (E tc) (E td) (reqEq (E ti) (E tj))))))))))

def cNegative : C :=
  .all ti (E sM) (.all tj (E sM) (.all tk (E sM)
    (rd 8 (E ti) ta (rd 8 (E tj) tb (rd 8 (E tk) tc
      (whenNe (E ta) (k 1) (whenNe (E tb) (k 1) (whenNe (E tc) (k 1)
        (rd 7 (E ti) td (rd 7 (E tj) te (rd 7 (E tk) tg
          (whenEq (E td) (E te) (whenEq (E td) (E tg)
            (whenNe (E ti) (E tj) (whenNe (E ti) (E tk) (reqEq (E tj) (E tk)))))))))))))))))

def extraCheck : C := .both cTwo (.both cPositive cNegative)

section
variable {u : List Bool} {L : Nat} {ρ : Sl → Nat} (hg : GlobalWF u L) (he : EnvOK u L ρ)
include hg he

theorem s_two : Holds u cTwo ρ ↔ ∀ j, j < (decodeCert u L).pt.m → 2 ≤ (decodeCert u L).pt.kk j := by
  unfold cTwo
  vsimp

theorem s_positive : Holds u cPositive ρ ↔
    ∀ i j, i < (decodeCert u L).pt.M → j < (decodeCert u L).pt.M →
      (decodeCert u L).pt.S i = 1 → (decodeCert u L).pt.S j = 1 →
      (decodeCert u L).pt.V i = (decodeCert u L).pt.V j → i = j := by
  unfold cPositive
  vsimp
  constructor
  · intro h i j hi hj; exact h i hi j hj
  · intro h i hi j hj; exact h i j hi hj

theorem s_negative : Holds u cNegative ρ ↔
    ∀ i j k, i < (decodeCert u L).pt.M → j < (decodeCert u L).pt.M → k < (decodeCert u L).pt.M →
      (decodeCert u L).pt.S i ≠ 1 → (decodeCert u L).pt.S j ≠ 1 → (decodeCert u L).pt.S k ≠ 1 →
      (decodeCert u L).pt.V i = (decodeCert u L).pt.V j →
      (decodeCert u L).pt.V i = (decodeCert u L).pt.V k → i = j ∨ i = k ∨ j = k := by
  unfold cNegative
  vsimp
  constructor
  · intro h i j k hi hj hk hsi hsj hsk hvj hvk
    by_cases hij : i = j
    · exact Or.inl hij
    by_cases hik : i = k
    · exact Or.inr (Or.inl hik)
    exact Or.inr (Or.inr (h i hi j hj k hk hsi hsj hsk hvj hvk hij hik))
  · intro h i hi j hj k hk hsi hsj hsk hvj hvk hij hik
    rcases h i j k hi hj hk hsi hsj hsk hvj hvk with hh | hh | hh
    · exact False.elim (hij hh)
    · exact False.elim (hik hh)
    · exact hh

theorem s_extra : Holds u extraCheck ρ ↔ TableCaps (decodeCert u L).pt := by
  simp only [extraCheck, holds_both, s_two hg he, s_positive hg he, s_negative hg he]
  exact ⟨fun h => ⟨h.1,h.2.1,h.2.2⟩, fun h => ⟨h.two,h.positive,h.negative⟩⟩
end

end STACS2027.PlanarBoundedMembership

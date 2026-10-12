module

public import ApproximationHardness.Embed.IncGraph
import Lean.Elab.Tactic.Omega

/-! # The first-occurrence dictionary used by incidence preprocessing -/

@[expose] public section

namespace STACS2027.Embed

open Complexity.SAT

/-- The first variable dart plus one, or zero for an unseen variable. -/
def firstCode (past : List Literal) (v : Nat) : Nat :=
  let i := past.findIdx (fun l => l.var == v)
  if i < past.length then 2 * i + 1 else 0

theorem firstCode_snoc (past : List Literal) (l : Literal) (v : Nat) :
    firstCode (past ++ [l]) v =
      if firstCode past v = 0 ∧ l.var = v then 2 * past.length + 1 else firstCode past v := by
  unfold firstCode
  dsimp only
  by_cases hp : past.findIdx (fun l => l.var == v) < past.length
  · have hp' : past.findIdx (fun l => l.var == v) < past.length + 1 := by omega
    simp [List.findIdx_append, hp, hp']
  · have he : past.findIdx (fun l => l.var == v) = past.length :=
      Nat.le_antisymm List.findIdx_le_length (by omega)
    by_cases hl : l.var = v
    · simp [List.findIdx_append, he, hl, List.findIdx_cons]
    · simp [List.findIdx_append, he, hl, List.findIdx_cons] <;> omega

theorem firstCode_positive (past : List Literal) (l : Literal) :
    0 < firstCode (past ++ [l]) l.var := by
  have hp : (past ++ [l]).findIdx (fun x => x.var == l.var) < (past ++ [l]).length :=
    List.findIdx_lt_length.mpr ⟨l, by simp, by simp⟩
  have hp' : (past ++ [l]).findIdx (fun x => x.var == l.var) < past.length + 1 := by
    simpa using hp
  simp [firstCode, hp']

theorem firstCode_prefix {past full : List Literal} (hpre : past <+: full) {v : Nat}
    (hp : 0 < firstCode past v) : firstCode full v = firstCode past v := by
  have hi : past.findIdx (fun l => l.var == v) < past.length := by
    by_cases hi : past.findIdx (fun l => l.var == v) < past.length
    · exact hi
    · simp [firstCode, hi] at hp
  have he := hpre.findIdx_eq_of_findIdx_lt_length hi
  have hb : past.length ≤ full.length := hpre.length_le
  have hi' : full.findIdx (fun l => l.var == v) < full.length := by rw [he]; omega
  unfold firstCode
  dsimp only
  rw [ite_eq_left hi', ite_eq_left hi, he]

theorem firstCode_firstOcc (f : CNF) {i : Nat} (hi : i < f.flatten.length) :
    firstCode f.flatten (varAt f i) = 2 * firstOcc f (varAt f i) + 1 := by
  have hp := (firstOcc_spec f hi).2.1
  unfold firstOcc at hp
  unfold firstCode
  dsimp only
  rw [ite_eq_left hp]
  rfl

end STACS2027.Embed

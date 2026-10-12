module

public import NPHardness.GlobalCompleteness

/-! Orientation-aware port identification. The orientation is data, not an
assumption: every occurrence may reverse the two endpoints of its shared edge.
The following files transport the existing local and global correctness proof
through this generalized construction. -/

@[expose] public section
namespace STACS2027.Oriented

class Orientation where
  flip : PlacedLiteral → Bool

variable [Orientation]

set_option linter.unusedSectionVars false

def orientSide (p : PlacedLiteral) (side : Bool) : Bool :=
  if Orientation.flip p then !side else side

@[simp] theorem orientSide_involutive (p : PlacedLiteral) (s : Bool) :
    orientSide p (orientSide p s) = s := by
  unfold orientSide
  cases Orientation.flip p <;> cases s <;> rfl

theorem orientSide_injective (p : PlacedLiteral) {s t : Bool}
    (h : orientSide p s = orientSide p t) : s = t := by
  simpa using congrArg (orientSide p) h

def clauseVertex (width n j : Nat) (c : List PlacedLiteral) (v : Nat) : Nat :=
  match attachmentAt c v with
  | some (p, side) => blockVertex width p.literal.var (variableEndpoint p.port (orientSide p side))
  | none => blockVertex width (n + j) v

theorem clauseVertex_attachment {width n j : Nat} {c : List PlacedLiteral}
    {i : Nat} (hi : i < 3) {p : PlacedLiteral} (hp : c[i]? = some p) (side : Bool) :
    clauseVertex width n j c (clauseEndpoint i side) =
      blockVertex width p.literal.var (variableEndpoint p.port (orientSide p side)) := by
  have h : attachmentAt c (clauseEndpoint i side) = some (p,side) :=
    attachmentAt_spec.mpr ⟨i, hi, hp, rfl⟩
  simp only [clauseVertex, h]

theorem clauseVertex_injective {width n j : Nat} {c : List PlacedLiteral}
    (hw : 7 ≤ width) (hc : (c.map PlacedLiteral.key).Nodup)
    (hb : ∀ p ∈ c, p.literal.var < n ∧ p.port < 3)
    {u v : Nat} (hu : u < width) (hv : v < width)
    (he : clauseVertex width n j c u = clauseVertex width n j c v) : u = v := by
  cases hau : attachmentAt c u with
  | none =>
    cases hav : attachmentAt c v with
    | none => exact (blockVertex_injective hu hv (by simpa [clauseVertex, hau, hav] using he)).2
    | some ps =>
      obtain ⟨p, side⟩ := ps
      obtain ⟨i, _, hip, _⟩ := attachmentAt_spec.mp hav
      have hpm : p ∈ c := List.mem_of_getElem? hip
      have hpv := (hb p hpm).1
      have hep : variableEndpoint p.port (orientSide p side) < width := Nat.lt_of_lt_of_le (variableEndpoint_bound _ _) hw
      have htag := (blockVertex_injective hu hep (by simpa [clauseVertex, hau, hav] using he)).1
      omega
  | some ps =>
    obtain ⟨p, side⟩ := ps
    obtain ⟨i, _, hip, hui⟩ := attachmentAt_spec.mp hau
    have hpm : p ∈ c := List.mem_of_getElem? hip
    have hpv := (hb p hpm).1
    have hep : variableEndpoint p.port (orientSide p side) < width := Nat.lt_of_lt_of_le (variableEndpoint_bound _ _) hw
    cases hav : attachmentAt c v with
    | none =>
      have htag := (blockVertex_injective hep hv (by simpa [clauseVertex, hau, hav] using he)).1
      omega
    | some qs =>
      obtain ⟨q, side'⟩ := qs
      obtain ⟨i', _, hiq, hvi⟩ := attachmentAt_spec.mp hav
      have hqm : q ∈ c := List.mem_of_getElem? hiq
      have heq : variableEndpoint q.port (orientSide q side') < width := Nat.lt_of_lt_of_le (variableEndpoint_bound _ _) hw
      obtain ⟨hvar, hend⟩ := blockVertex_injective hep heq (by simpa [clauseVertex, hau, hav] using he)
      obtain ⟨hport, hside⟩ := variableEndpoint_injective (hb p hpm).2 (hb q hqm).2 _ _ hend
      have hkey : p.key = q.key := Prod.ext hvar hport
      have hlen : i < (c.map PlacedLiteral.key).length := by
        have h := (List.getElem?_eq_some_iff.mp hip).1
        simpa using h
      have hidx : i = i' := hc.eq_of_getElem?_eq hlen (by simp [List.getElem?_map, hip, hiq, hkey])
      have hpq : p = q := by
        rw [hidx] at hip
        exact Option.some.inj (hip.symm.trans hiq)
      subst q
      have hs := orientSide_injective p hside
      rw [hui, hvi, hidx, hs]

end STACS2027.Oriented

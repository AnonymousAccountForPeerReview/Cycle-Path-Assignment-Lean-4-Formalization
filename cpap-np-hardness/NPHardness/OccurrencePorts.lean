module

public import NPHardness.BoundedSAT

/-!
Computable allocation of the three variable-gadget attachment ports. Every
literal occurrence receives its number among earlier equal signed literals.
Positive occurrences use port 0; negative occurrences use ports 1 and 2.
The proofs count occurrences with multiplicity and do not assume a clean CNF.
-/

@[expose] public section
namespace STACS2027
open Complexity.SAT

structure PlacedLiteral where
  literal : Literal
  earlier : Nat
deriving DecidableEq, Repr

def placeLiterals (past : List Literal) : List Literal → List PlacedLiteral
  | [] => []
  | l :: ls => ⟨l, past.count l⟩ :: placeLiterals (past ++ [l]) ls

def placeFormula (past : List Literal) : CNF → List (List PlacedLiteral)
  | [] => []
  | c :: f => placeLiterals past c :: placeFormula (past ++ c) f

def PlacedLiteral.port (l : PlacedLiteral) : Nat :=
  if l.literal.positive then 0 else l.earlier + 1

def PlacedLiteral.key (l : PlacedLiteral) : Nat × Nat := (l.literal.var, l.port)

theorem placeLiterals_forget (past ls : List Literal) :
    (placeLiterals past ls).map PlacedLiteral.literal = ls := by
  induction ls generalizing past with
  | nil => rfl
  | cons l ls ih => simp [placeLiterals, ih]

theorem placeLiterals_append (past as bs : List Literal) :
    placeLiterals past (as ++ bs) = placeLiterals past as ++ placeLiterals (past ++ as) bs := by
  induction as generalizing past with
  | nil => simp [placeLiterals]
  | cons l ls ih =>
    simp only [List.cons_append, placeLiterals, ih]
    simp [List.append_assoc]

theorem placeFormula_flatten (past : List Literal) (f : CNF) :
    (placeFormula past f).flatten = placeLiterals past f.flatten := by
  induction f generalizing past with
  | nil => rfl
  | cons c f ih => simp [placeFormula, ih, placeLiterals_append]

theorem placeFormula_forget (past : List Literal) (f : CNF) :
    (placeFormula past f).map (List.map PlacedLiteral.literal) = f := by
  induction f generalizing past with
  | nil => rfl
  | cons c f ih => simp [placeFormula, placeLiterals_forget, ih]

theorem placeLiterals_bounds (past ls : List Literal) : ∀ p ∈ placeLiterals past ls,
    past.count p.literal ≤ p.earlier ∧ p.earlier < (past ++ ls).count p.literal := by
  induction ls generalizing past with
  | nil => simp [placeLiterals]
  | cons l ls ih =>
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · simp [List.count_append]
    · obtain ⟨hlo, hhi⟩ := ih (past ++ [l]) p hp
      constructor
      · have hm : past.count p.literal ≤ (past ++ [l]).count p.literal := by
          simp only [List.count_append]
          omega
        exact Nat.le_trans hm hlo
      · simpa only [List.append_assoc, List.singleton_append] using hhi

theorem placeLiterals_nodup (past ls : List Literal) : (placeLiterals past ls).Nodup := by
  induction ls generalizing past with
  | nil => simp [placeLiterals]
  | cons l ls ih =>
    apply List.nodup_cons.mpr
    refine ⟨?_, ih _⟩
    intro hm
    have h := (placeLiterals_bounds (past ++ [l]) ls _ hm).1
    simp only [List.count_append, List.count_singleton, beq_self_eq_true, ↓reduceIte] at h
    omega

theorem occurrences_eq_count (f : CNF) (v : Nat) (p : Bool) :
    occurrences f v p = f.flatten.count ⟨v,p⟩ := by
  unfold occurrences
  have h : ∀ xs : List Literal,
      (xs.filter fun l => l.var == v && l.positive == p).length = xs.count ⟨v,p⟩ := by
    intro xs
    induction xs with
    | nil => rfl
    | cons l xs ih =>
      have he : (l.var == v && l.positive == p) = (l == ⟨v,p⟩) := by
        apply Bool.eq_iff_iff.mpr
        simp only [Bool.and_eq_true, beq_iff_eq]
        cases l
        simp only [Literal.mk.injEq]
      rw [List.filter_cons]
      rw [he]
      by_cases hl : l = ⟨v,p⟩ <;> simp [hl, ih, Nat.add_comm]
  exact h f.flatten

theorem BoundedOccurrence.placement_bounds {f : CNF} (hf : BoundedOccurrence f)
    {p : PlacedLiteral} (hp : p ∈ (placeFormula [] f).flatten) :
    (p.literal.positive = true → p.earlier = 0) ∧
    (p.literal.positive = false → p.earlier < 2) := by
  rw [placeFormula_flatten] at hp
  have h := (placeLiterals_bounds [] f.flatten p hp).2
  simp only [List.nil_append] at h
  constructor
  · intro hs
    have hb := hf.2.1 p.literal.var
    rw [occurrences_eq_count] at hb
    have he : p.literal = ⟨p.literal.var, true⟩ := by cases p with | mk l n => cases l; simp_all
    rw [he] at h
    omega
  · intro hs
    have hb := hf.2.2 p.literal.var
    rw [occurrences_eq_count] at hb
    have he : p.literal = ⟨p.literal.var, false⟩ := by cases p with | mk l n => cases l; simp_all
    rw [he] at h
    omega

theorem BoundedOccurrence.placement_port_lt {f : CNF} (hf : BoundedOccurrence f)
    {p : PlacedLiteral} (hp : p ∈ (placeFormula [] f).flatten) : p.port < 3 := by
  obtain ⟨hpos, hneg⟩ := hf.placement_bounds hp
  cases hs : p.literal.positive
  · have := hneg hs
    simp [PlacedLiteral.port, hs]
    omega
  · simp [PlacedLiteral.port, hs]

theorem BoundedOccurrence.placement_key_injective {f : CNF} (hf : BoundedOccurrence f)
    {p q : PlacedLiteral} (hp : p ∈ (placeFormula [] f).flatten)
    (hq : q ∈ (placeFormula [] f).flatten) (he : p.key = q.key) : p = q := by
  obtain ⟨hpp, hpn⟩ := hf.placement_bounds hp
  obtain ⟨hqp, hqn⟩ := hf.placement_bounds hq
  simp only [PlacedLiteral.key, Prod.mk.injEq] at he
  cases p with | mk p pr =>
    cases q with | mk q qr =>
      cases p with | mk pv pp =>
        cases q with | mk qv qp =>
          simp only at *
          cases pp <;> cases qp <;> simp_all [PlacedLiteral.port]

/-- No two occurrence positions are glued to the same variable port. -/
theorem BoundedOccurrence.placement_keys_nodup {f : CNF} (hf : BoundedOccurrence f) :
    ((placeFormula [] f).flatten.map PlacedLiteral.key).Nodup := by
  rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
  have hn : (placeFormula [] f).flatten.Nodup := by
    rw [placeFormula_flatten]
    exact placeLiterals_nodup [] f.flatten
  exact hn.imp_of_mem (fun {p q} hp hq hne he => hne (hf.placement_key_injective hp hq he))

end STACS2027

module

public import Hardness.MaxSNP.Hard.Defs
public import Hardness.MaxSNP.Max3SAT

/-!
# Cutting a structure of the solution signature out of arbitrary relations

The relations `satToSnp k φ (n, G) y` written by an assignment need not form a structure of
the solution signature `sa` over the universe `{0, …, n - 1}` (they may repeat tuples, have
other relation indices, or contain tuples of other lengths). `fitRel sa n S` keeps, for each
relation of the signature, exactly the tuples of the universe of the right arity at which `S`
holds:

* `fits_fitRel`: `fitRel sa n S` is a structure of signature `sa` over the universe;
* `eval_fitRel`, `countP_fitRel`: a formula that is well formed for the solution signature
  `sa` has the same value at every tuple of the universe for `S` and for `fitRel sa n S`.
-/

@[expose] public section

namespace Complexity

theorem length_fitFrom (sa : List Nat) (i n : Nat) (S : Relations) :
    (fitFrom sa i n S).length = sa.length := by
  induction sa generalizing i with
  | nil => rfl
  | cons a sa ih => simp [fitFrom, ih]

/-- The relation with index `r` of `fitFrom sa i n S`. -/
theorem getD_fitFrom {sa : List Nat} {i n : Nat} {S : Relations} {r a : Nat}
    (h : sa[r]? = some a) :
    (fitFrom sa i n S).getD r [] = (tuples n a).filter fun u => S.holds (i + r) u := by
  induction sa generalizing i r with
  | nil => simp at h
  | cons b sa ih =>
    cases r with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      simp [fitFrom]
    | succ r =>
      simp only [List.getElem?_cons_succ] at h
      simp only [fitFrom, List.getD_cons_succ]
      rw [ih h, Nat.add_assoc, Nat.add_comm 1 r]

/-- `fitRel sa n S` is a structure of signature `sa` over the universe `{0, …, n - 1}`. -/
theorem fits_fitRel (sa : List Nat) (n : Nat) (S : Relations) : (fitRel sa n S).Fits n sa := by
  refine ⟨length_fitFrom sa 0 n S, ?_⟩
  suffices h : ∀ i, ∀ p ∈ (fitFrom sa i n S).zip sa,
      p.1.Nodup ∧ ∀ t ∈ p.1, t.length = p.2 ∧ ∀ a ∈ t, a < n from h 0
  induction sa with
  | nil => simp [fitFrom]
  | cons a sa ih =>
    intro i p hp
    simp only [fitFrom, List.zip_cons_cons, List.mem_cons] at hp
    rcases hp with rfl | hp
    · refine ⟨(nodup_tuples n a).filter _, fun t ht => ?_⟩
      exact mem_tuples.mp (List.mem_filter.mp ht).1
    · exact ih (i + 1) p hp

/-- On a tuple of the universe whose length is the arity of the relation `r` of the signature,
`fitRel sa n S` holds exactly where `S` holds. -/
theorem holds_fitRel {sa : List Nat} {n : Nat} {S : Relations} {r : Nat} {u : List Nat}
    (hr : sa[r]? = some u.length) (hu : ∀ a ∈ u, a < n) :
    (fitRel sa n S).holds r u = S.holds r u := by
  rw [Relations.holds_eq, fitRel, getD_fitFrom hr, Nat.zero_add, Bool.eq_iff_iff,
    decide_eq_true_eq, List.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨mem_tuples.mpr ⟨rfl, hu⟩, h⟩⟩

/-- A formula that is well formed for the solution signature `sa` has the same value for `S`
and for `fitRel sa n S` at every `k`-tuple of the universe. -/
theorem eval_fitRel {ga sa : List Nat} {k n : Nat} {φ : QF} (hφ : φ.WellFormed ga sa k)
    (G S : Relations) {t : List Nat} (ht : t ∈ tuples n k) :
    φ.eval G (fitRel sa n S) t = φ.eval G S t := by
  obtain ⟨htk, htn⟩ := mem_tuples.mp ht
  induction φ with
  | input rel args => rfl
  | sol rel args =>
    obtain ⟨hr, hargs⟩ := hφ
    simp only [QF.eval]
    refine holds_fitRel (by rw [List.length_map]; exact hr) fun a ha => ?_
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
    have hik : i < t.length := htk ▸ hargs i hi
    rw [← List.getElem_eq_getD (h := hik) 0]
    exact htn _ (List.getElem_mem hik)
  | eq i j => rfl
  | not φ ih => simp only [QF.eval, ih hφ]
  | and φ ψ ih₁ ih₂ => simp only [QF.eval, ih₁ hφ.1, ih₂ hφ.2]
  | or φ ψ ih₁ ih₂ => simp only [QF.eval, ih₁ hφ.1, ih₂ hφ.2]

/-- The value of `fitRel sa n S` is the value of `S`, for a well-formed formula. -/
theorem countP_fitRel {ga sa : List Nat} {k n : Nat} {φ : QF} (hφ : φ.WellFormed ga sa k)
    (G S : Relations) :
    (tuples n k).countP (fun t => φ.eval G (fitRel sa n S) t) =
      (tuples n k).countP (fun t => φ.eval G S t) :=
  List.countP_congr fun t ht => by rw [eval_fitRel hφ G S ht]

end Complexity

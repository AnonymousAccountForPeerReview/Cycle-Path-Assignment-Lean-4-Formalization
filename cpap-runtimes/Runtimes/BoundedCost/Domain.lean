module

public import Runtimes.BoundedCost.NormalizedAnswer
public import Runtimes.BoundedCost.SearchPaths
import Mathlib.Tactic

/-!
# Dense-domain invariants for compression

Clause deletion and added literal requirements retain the original input's
variable bound.  The least-deviation minimum-cut assignment is unique, so
different sufficient finite node bounds produce the same assignment.
-/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 Complexity.SAT

def LiteralDomain (n : ℕ) (L : List Literal) : Prop := ∀ l ∈ L, l.var < n

theorem isLeastCut_unique {τ δ ρ : Assignment} {f : CNF} {L : List Literal}
    (hδ : IsLeastCut τ f L δ) (hρ : IsLeastCut τ f L ρ) : δ = ρ := by
  have he : cutCost τ δ f = cutCost τ ρ f :=
    Nat.le_antisymm (hδ.optimal ρ hρ.required) (hρ.optimal δ hδ.required)
  funext x
  have hd := hδ.least ρ hρ.required he.symm x
  have hr := hρ.least δ hδ.required he x
  cases ht : τ x <;> cases ha : δ x <;> cases hb : ρ x <;> simp_all

theorem twoCNF_sublist {n : ℕ} {f g : CNF} (hf : TwoSat.IsTwoCNF n f)
    (hg : g.Sublist f) : TwoSat.IsTwoCNF n g := fun c hc => hf c (hg.subset hc)

theorem twoCNF_erase {n : ℕ} {f : CNF} (hf : TwoSat.IsTwoCNF n f) (c : Clause) :
    TwoSat.IsTwoCNF n (f.erase c) := twoCNF_sublist hf List.erase_sublist

theorem literalDomain_cons {n : ℕ} {L : List Literal} {a : Literal}
    (hL : LiteralDomain n L) (ha : a.var < n) : LiteralDomain n (a :: L) := by
  intro l hl
  rcases List.mem_cons.mp hl with rfl | hl
  · exact ha
  · exact hL l hl

theorem compressionBranches_domain {n : ℕ} {f : CNF} (hf : TwoSat.IsTwoCNF n f)
    {r : CompressionBranch} (hr : r ∈ compressionBranches f) : LiteralDomain n r.2 := by
  induction f generalizing r with
  | nil => simp [compressionBranches] at hr; subst r; simp [LiteralDomain]
  | cons c f ih =>
    obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp (hf c (by simp)).1
    have ht : TwoSat.IsTwoCNF n f := fun c hc => hf c (by simp [hc])
    have ha := (hf [a, b] (by simp)).2 a (by simp)
    have hb := (hf [a, b] (by simp)).2 b (by simp)
    simp only [compressionBranches, List.mem_append, List.mem_map] at hr
    rcases hr with (⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩) | ⟨s, hs, rfl⟩
    · exact ih (r := s) ht hs
    · exact literalDomain_cons (ih ht hs) ha
    · exact literalDomain_cons (ih ht hs) hb

theorem compressionBase_twoCNF {n : ℕ} {f : CNF} (hf : TwoSat.IsTwoCNF n f)
    (σ : Assignment) : TwoSat.IsTwoCNF n (compressionBase σ f) :=
  twoCNF_sublist hf List.filter_sublist

theorem compressionSpecial_twoCNF {n : ℕ} {f : CNF} {c : Clause}
    (hf : TwoSat.IsTwoCNF n (f ++ [c])) (σ : Assignment) :
    TwoSat.IsTwoCNF n (compressionSpecial σ f c) :=
  twoCNF_sublist hf (List.filter_sublist.append_right [c])

end STACS2027.Runtimes.BoundedCost

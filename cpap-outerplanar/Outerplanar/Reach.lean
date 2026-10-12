module

public import Outerplanar.Minors
import Mathlib.Tactic

/-!
# Reachability by walks within a vertex set

`Reach g S u v`: a walk of `g` from `u` to `v` all of whose vertices satisfy `S`, as an
inductive relation. It is reflexive on `S`, symmetric, transitive, and contains the edges
between vertices of `S`; it is equivalent to the explicit walks of `ConnectedWithin`
(`reach_of_walk`, `walk_of_reach`, `connectedWithin_iff`).
-/

@[expose] public section

namespace STACS2027

/-- A walk of `g` within `S` from `u` to `v`. -/
inductive Reach (g : Graph) (S : ℕ → Prop) : ℕ → ℕ → Prop
  | refl {u : ℕ} : S u → Reach g S u u
  | step {u v w : ℕ} : S u → Adj g u v → Reach g S v w → Reach g S u w

theorem WalkWithin.mem {g : Graph} {S : ℕ → Prop} :
    ∀ {w : List ℕ}, WalkWithin g S w → ∀ x ∈ w, S x
  | [], _, x, hx => by simp at hx
  | [_], h, x, hx => by simp at hx; subst hx; exact h
  | _ :: _ :: _, ⟨ha, _, hw⟩, x, hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ha
    · exact WalkWithin.mem hw x hx

theorem WalkWithin.snoc {g : Graph} {S : ℕ → Prop} :
    ∀ {w : List ℕ} {x y : ℕ}, WalkWithin g S (w ++ [x]) → Adj g x y → S y →
      WalkWithin g S (w ++ [x, y])
  | [], _, _, hx, hxy, hy => ⟨hx, hxy, hy⟩
  | [_], _, _, ⟨ha, hax, hx⟩, hxy, hy => ⟨ha, hax, hx, hxy, hy⟩
  | _ :: b :: rest, _, _, ⟨ha, hab, h1⟩, hxy, hy => by
    refine ⟨ha, hab, ?_⟩
    have := WalkWithin.snoc (w := b :: rest) h1 hxy hy
    simpa using this

theorem WalkWithin.reverse {g : Graph} {S : ℕ → Prop} :
    ∀ {w : List ℕ}, WalkWithin g S w → WalkWithin g S w.reverse
  | [], _ => trivial
  | [_], h => h
  | a :: b :: rest, ⟨ha, hab, hw⟩ => by
    have ih := WalkWithin.reverse hw
    have e1 : (a :: b :: rest).reverse = rest.reverse ++ [b, a] := by simp
    have e2 : (b :: rest).reverse = rest.reverse ++ [b] := by simp
    rw [e1]
    rw [e2] at ih
    exact WalkWithin.snoc ih hab.symm ha

namespace Reach

variable {g : Graph} {S : ℕ → Prop}

theorem left {u v : ℕ} (h : Reach g S u v) : S u := by
  cases h with
  | refl hu => exact hu
  | step hu _ _ => exact hu

theorem right {u v : ℕ} (h : Reach g S u v) : S v := by
  induction h with
  | refl hu => exact hu
  | step _ _ _ ih => exact ih

theorem edge {u v : ℕ} (hu : S u) (hv : S v) (h : Adj g u v) : Reach g S u v :=
  .step hu h (.refl hv)

theorem trans {u v x : ℕ} (h1 : Reach g S u v) (h2 : Reach g S v x) : Reach g S u x := by
  induction h1 with
  | refl _ => exact h2
  | step hu hadj _ ih => exact .step hu hadj (ih h2)

theorem symm {u v : ℕ} (h : Reach g S u v) : Reach g S v u := by
  induction h with
  | refl hu => exact .refl hu
  | step hu hadj hr ih => exact ih.trans (.edge hr.left hu hadj.symm)

theorem mono {T : ℕ → Prop} (hST : ∀ v, S v → T v) {u v : ℕ} (h : Reach g S u v) :
    Reach g T u v := by
  induction h with
  | refl hu => exact .refl (hST _ hu)
  | step hu hadj _ ih => exact .step (hST _ hu) hadj ih

theorem graph_mono {h : Graph} (hg : ∀ u v, Adj g u v → Adj h u v) {u v : ℕ}
    (hr : Reach g S u v) : Reach h S u v := by
  induction hr with
  | refl hu => exact .refl hu
  | step hu hadj _ ih => exact .step hu (hg _ _ hadj) ih

end Reach

theorem reach_of_walk {g : Graph} {S : ℕ → Prop} :
    ∀ {w : List ℕ} {u v : ℕ}, w.head? = some u → w.getLast? = some v → WalkWithin g S w →
      Reach g S u v
  | [], _, _, h, _, _ => by simp at h
  | [a], u, v, h1, h2, hw => by
    simp at h1 h2; subst h1; subst h2; exact .refl hw
  | a :: b :: rest, u, v, h1, h2, ⟨ha, hab, hw⟩ => by
    simp only [List.head?_cons, Option.some.injEq] at h1
    subst h1
    have h2' : (b :: rest).getLast? = some v := by simpa [List.getLast?_cons_cons] using h2
    exact .step ha hab (reach_of_walk rfl h2' hw)

theorem walk_of_reach {g : Graph} {S : ℕ → Prop} {u v : ℕ} (h : Reach g S u v) :
    ∃ w : List ℕ, w.head? = some u ∧ w.getLast? = some v ∧ WalkWithin g S w := by
  induction h with
  | @refl u hu => exact ⟨[u], rfl, rfl, hu⟩
  | @step u v' x hu hadj _ ih =>
    obtain ⟨w, h1, h2, hw⟩ := ih
    obtain ⟨w', rfl⟩ : ∃ w', w = v' :: w' := by
      cases w with
      | nil => simp at h1
      | cons z w' => simp at h1; subst h1; exact ⟨w', rfl⟩
    exact ⟨u :: v' :: w', rfl, by simpa [List.getLast?_cons_cons] using h2, ⟨hu, hadj, hw⟩⟩

theorem connectedWithin_iff {g : Graph} {S : ℕ → Prop} :
    ConnectedWithin g S ↔ ∀ u v, S u → S v → Reach g S u v := by
  constructor
  · intro h u v hu hv
    obtain ⟨w, h1, h2, hw⟩ := h u v hu hv
    exact reach_of_walk h1 h2 hw
  · intro h u v hu hv
    exact walk_of_reach (h u v hu hv)

/-- Connectivity through a hub: every vertex of `S` reaches `c`. -/
theorem connectedWithin_of_hub {g : Graph} {S : ℕ → Prop} {c : ℕ}
    (h : ∀ v, S v → Reach g S v c) : ConnectedWithin g S := by
  rw [connectedWithin_iff]
  intro u v hu hv
  exact (h u hu).trans (h v hv).symm

end STACS2027

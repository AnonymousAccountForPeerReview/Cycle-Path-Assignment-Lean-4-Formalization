module

public import Outerplanar.Minors
import Mathlib.Tactic

/-!
# Palm trees and heads

A *palm tree* of a graph `g` (a depth-first forest): a parent function `par` (roots are
their own parents) with tree edges `par v — v`, preorder numbers decreasing to the parent,
and every edge of `g` joining an ancestor to a descendant (`palm`).

A non-root vertex `c` is a *head* when every edge leaving the subtree of `c` ends at the
parent of `c` (`IsHead`): the tree edge `par c — c` starts a block (ANONYMIZED and ANONYMIZED:
`low(c) ≥ pre(par c)`). Every child of a root is a head. `head x` is the first head on the
path from `x` to its root: no head lies strictly between `head x` and `x`.
-/

@[expose] public section

namespace STACS2027

/-- A palm tree (depth-first forest) of `g`. -/
structure Palm (g : Graph) where
  par : ℕ → ℕ
  pre : ℕ → ℕ
  par_adj : ∀ v, IsVertex g v → par v ≠ v → Adj g (par v) v
  par_pre : ∀ v, IsVertex g v → par v ≠ v → pre (par v) < pre v
  palm : ∀ u v, Adj g u v → (∃ k, par^[k] v = u) ∨ (∃ k, par^[k] u = v)

namespace Palm

variable {g : Graph} (P : Palm g)

/-- `a` is an ancestor of `v` (or `v` itself). -/
def Anc (a v : ℕ) : Prop := ∃ k, P.par^[k] v = a

theorem anc_refl (v : ℕ) : P.Anc v v := ⟨0, rfl⟩

theorem anc_par (v : ℕ) : P.Anc (P.par v) v := ⟨1, rfl⟩

theorem anc_trans {a b c : ℕ} (h1 : P.Anc a b) (h2 : P.Anc b c) : P.Anc a c := by
  obtain ⟨i, rfl⟩ := h1
  obtain ⟨j, rfl⟩ := h2
  exact ⟨i + j, by rw [Function.iterate_add_apply]⟩

theorem anc_of_anc_par {a v : ℕ} (h : P.Anc a (P.par v)) : P.Anc a v :=
  P.anc_trans h (P.anc_par v)

theorem anc_par_of_ne {a v : ℕ} (h : P.Anc a v) (hne : a ≠ v) : P.Anc a (P.par v) := by
  obtain ⟨k, rfl⟩ := h
  cases k with
  | zero => exact absurd rfl hne
  | succ k => exact ⟨k, by rw [Function.iterate_succ_apply]⟩

theorem isVertex_par {v : ℕ} (hv : IsVertex g v) : IsVertex g (P.par v) := by
  by_cases h : P.par v = v
  · rw [h]; exact hv
  · exact ⟨v, (P.par_adj v hv h).symm⟩

theorem isVertex_iterate {v : ℕ} (hv : IsVertex g v) : ∀ k, IsVertex g (P.par^[k] v) := by
  intro k
  induction k generalizing v with
  | zero => exact hv
  | succ k ih => rw [Function.iterate_succ_apply]; exact ih (P.isVertex_par hv)

theorem isVertex_anc {a v : ℕ} (hv : IsVertex g v) (h : P.Anc a v) : IsVertex g a := by
  obtain ⟨k, rfl⟩ := h
  exact P.isVertex_iterate hv k

theorem pre_anc {a v : ℕ} (hv : IsVertex g v) (h : P.Anc a v) : a = v ∨ P.pre a < P.pre v := by
  obtain ⟨k, rfl⟩ := h
  induction k generalizing v with
  | zero => exact Or.inl rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    by_cases hr : P.par v = v
    · rw [hr]; exact ih hv
    · have hp := P.par_pre v hv hr
      rcases ih (P.isVertex_par hv) with h | h
      · right; rw [h]; exact hp
      · right; omega

theorem anc_antisymm {a v : ℕ} (hv : IsVertex g v) (h1 : P.Anc a v) (h2 : P.Anc v a) : a = v := by
  have ha := P.isVertex_anc hv h1
  rcases P.pre_anc hv h1 with h | h
  · exact h
  · rcases P.pre_anc ha h2 with h' | h'
    · exact h'.symm
    · omega

/-- The ancestors of a vertex form a chain. -/
theorem anc_chain {a b v : ℕ} (ha : P.Anc a v) (hb : P.Anc b v) : P.Anc a b ∨ P.Anc b a := by
  obtain ⟨i, rfl⟩ := ha
  obtain ⟨j, rfl⟩ := hb
  rcases Nat.le_total i j with h | h
  · right; exact ⟨j - i, by rw [← Function.iterate_add_apply]; congr 1; omega⟩
  · left; exact ⟨i - j, by rw [← Function.iterate_add_apply]; congr 1; omega⟩

/-- A root has no proper ancestor. -/
theorem anc_root {a r : ℕ} (hr : P.par r = r) (h : P.Anc a r) : a = r := by
  obtain ⟨k, rfl⟩ := h
  exact Function.iterate_fixed hr k

theorem par_ne_of_anc {a v : ℕ} (h : P.Anc a v) (hne : a ≠ v) :
    P.par v ≠ v := by
  intro hr
  exact hne (P.anc_root hr h)

/-! ### Heads -/

/-- `c` is a head: a non-root vertex every edge leaving whose subtree ends at its parent. -/
def IsHead (c : ℕ) : Prop :=
  IsVertex g c ∧ P.par c ≠ c ∧ ∀ u w, P.Anc c u → Adj g u w → ¬ P.Anc c w → w = P.par c

/-- Every child of a root is a head. -/
theorem isHead_of_root_child {c : ℕ} (hc : IsVertex g c) (hne : P.par c ≠ c)
    (hr : P.par (P.par c) = P.par c) : P.IsHead c := by
  refine ⟨hc, hne, ?_⟩
  intro u w hcu huw hcw
  rcases P.palm u w huw with ⟨k, hk⟩ | ⟨k, hk⟩
  · exact absurd (P.anc_trans hcu ⟨k, hk⟩) hcw
  · -- `w` is an ancestor of `u`
    have hwu : P.Anc w u := ⟨k, hk⟩
    rcases P.anc_chain hcu hwu with h | h
    · exact absurd h hcw
    · have h' := P.anc_par_of_ne h (fun e => hcw (e ▸ P.anc_refl c))
      exact P.anc_root hr h'

open Classical in
/-- The first head on the path from `x` to its root, with fuel. -/
noncomputable def headAux : ℕ → ℕ → ℕ
  | 0, x => x
  | f + 1, x => if P.par x = x then x else if P.IsHead x then x else headAux f (P.par x)

/-- The first head on the path from `x` to its root. -/
noncomputable def head (x : ℕ) : ℕ := P.headAux (P.pre x + 1) x

/-- No head lies strictly between `h` and `x`. -/
def NoHeadBetween (h x : ℕ) : Prop := ∀ y, P.Anc y x → P.Anc h y → y ≠ h → ¬ P.IsHead y

theorem headAux_spec : ∀ (f x : ℕ), IsVertex g x → P.par x ≠ x → P.pre x < f →
    P.IsHead (P.headAux f x) ∧ P.Anc (P.headAux f x) x ∧ P.NoHeadBetween (P.headAux f x) x
  | 0, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | f + 1, x, hx, hr, hf => by
    by_cases hh : P.IsHead x
    · have he : P.headAux (f + 1) x = x := by rw [headAux, ite_eq_right hr, ite_eq_left hh]
      rw [he]
      refine ⟨hh, P.anc_refl x, fun y hyx hxy hne => ?_⟩
      exact absurd (P.anc_antisymm hx hyx hxy) hne
    · have he : P.headAux (f + 1) x = P.headAux f (P.par x) := by
        rw [headAux, ite_eq_right hr, ite_eq_right hh]
      rw [he]
      have hpr : P.par (P.par x) ≠ P.par x := fun h => hh (P.isHead_of_root_child hx hr h)
      have hpre := P.par_pre x hx hr
      obtain ⟨h1, h2, h3⟩ := headAux_spec f (P.par x) (P.isVertex_par hx) hpr (by omega)
      refine ⟨h1, P.anc_of_anc_par h2, fun y hyx hhy hne => ?_⟩
      by_cases hyx' : y = x
      · rw [hyx']; exact hh
      · exact h3 y (P.anc_par_of_ne hyx hyx') hhy hne

theorem head_spec {x : ℕ} (hx : IsVertex g x) (hr : P.par x ≠ x) :
    P.IsHead (P.head x) ∧ P.Anc (P.head x) x ∧ P.NoHeadBetween (P.head x) x :=
  P.headAux_spec _ x hx hr (Nat.lt_succ_self _)

/-- A head is not a root, nor is anything below it. -/
theorem par_ne_of_head_anc {h x : ℕ} (hh : P.IsHead h) (hhx : P.Anc h x) : P.par x ≠ x := by
  intro hr
  have := P.anc_root hr hhx
  subst this
  exact hh.2.1 hr

/-- A head above `x` is above `head x`. -/
theorem anc_head {h x : ℕ} (hx : IsVertex g x) (hh : P.IsHead h) (hhx : P.Anc h x) :
    P.Anc h (P.head x) := by
  obtain ⟨h1, h2, h3⟩ := P.head_spec hx (P.par_ne_of_head_anc hh hhx)
  rcases P.anc_chain hhx h2 with h' | h'
  · exact h'
  · by_cases he : h = P.head x
    · rw [he]; exact P.anc_refl _
    · exact absurd hh (h3 h hhx h' he)

/-- Between `head x` and `x`, every vertex has the same head. -/
theorem head_eq_of_between {x a : ℕ} (hx : IsVertex g x) (hr : P.par x ≠ x) (hax : P.Anc a x)
    (hha : P.Anc (P.head x) a) : P.head a = P.head x := by
  obtain ⟨h1, h2, h3⟩ := P.head_spec hx hr
  have ha : IsVertex g a := P.isVertex_anc hx hax
  have har : P.par a ≠ a := P.par_ne_of_head_anc h1 hha
  obtain ⟨k1, k2, k3⟩ := P.head_spec ha har
  have hk : P.Anc (P.head a) x := P.anc_trans k2 hax
  rcases P.anc_chain hk h2 with h' | h'
  · -- `head x` lies between `head a` and `a`
    by_contra hne
    exact k3 _ hha h' (Ne.symm hne) h1
  · by_contra hne
    exact h3 _ hk h' hne k1

end Palm

end STACS2027

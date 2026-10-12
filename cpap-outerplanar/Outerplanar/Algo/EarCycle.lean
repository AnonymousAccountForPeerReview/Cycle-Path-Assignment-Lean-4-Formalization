module

public import Outerplanar.Algo.Ear
public import Outerplanar.OuterplanarSym
import Mathlib.Data.List.GetD
import Mathlib.Tactic

/-!
# Ear elimination: successor functions of cyclic orders

The reconstruction phase of the ear elimination (`Outerplanar/Algo/Ear.lean`) builds a
successor function. Here:

* `Fwd succ K`: `succ` maps every entry of `K` to the cyclically next one;
  `Rep succ K`: `succ` follows `K` in one of the two directions. Both are invariant under
  rotation (`Fwd.isRotated`, `Rep.isRotated`).
* `rep_reinsert`: if `succ` follows the cycle `C` (in some direction) and `v` is a new vertex
  whose logged neighbours are the two ends of `C`, then `reinsert succ (v, u, w)` follows
  `v :: C`.
* `walk_fwd`: following the successors from the first entry of `K` reads off `K`.
* `rep_three`: the initial successor function `x → y → z → x` follows any list of the three
  vertices.
-/

@[expose] public section

namespace STACS2027.Ear

/-- `succ` maps every entry of `K` to the cyclically next one. -/
def Fwd (succ : ℕ → ℕ) (K : List ℕ) : Prop := CycAdj (fun a b => succ a = b) K

/-- `succ` follows the cyclic order of `K` in one of the two directions. -/
def Rep (succ : ℕ → ℕ) (K : List ℕ) : Prop := Fwd succ K ∨ Fwd succ K.reverse

theorem Fwd.isRotated {succ : ℕ → ℕ} {K K' : List ℕ} (h : Fwd succ K) (hr : K ~r K') :
    Fwd succ K' :=
  CycAdj.isRotated h hr

theorem Rep.isRotated {succ : ℕ → ℕ} {K K' : List ℕ} (h : Rep succ K) (hr : K ~r K') :
    Rep succ K' := by
  rcases h with h | h
  · exact Or.inl (h.isRotated hr)
  · exact Or.inr (h.isRotated hr.reverse)

/-- Reinserting `v` between the two ends of `C`, as the reconstruction does. -/
theorem reinsert_eq {succ : ℕ → ℕ} {v u w : ℕ} {C : List ℕ} (hC : C.Nodup) (h3 : 3 ≤ C.length)
    (huw : (u = C.getD 0 0 ∧ w = C.getD (C.length - 1) 0) ∨
      (u = C.getD (C.length - 1) 0 ∧ w = C.getD 0 0))
    (h : Fwd succ C) :
    reinsert succ (v, u, w) =
      Function.update (Function.update succ (C.getD (C.length - 1) 0) v) v (C.getD 0 0) := by
  have h1 : succ (C.getD 0 0) = C.getD 1 0 := h.1 0 (by omega)
  have h2 : succ (C.getD (C.length - 1) 0) = C.getD 0 0 := h.2
  have hne : C.getD 1 0 ≠ C.getD (C.length - 1) 0 := getD_ne_of_ne hC (by omega) (by omega)
    (by omega)
  rcases huw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp only [reinsert, h1, hne, ite_false]
  · simp only [reinsert, h2, ite_true]

theorem fwd_reinsert {succ : ℕ → ℕ} {v u w : ℕ} {C : List ℕ} (hC : C.Nodup) (h3 : 3 ≤ C.length)
    (hv : v ∉ C)
    (huw : (u = C.getD 0 0 ∧ w = C.getD (C.length - 1) 0) ∨
      (u = C.getD (C.length - 1) 0 ∧ w = C.getD 0 0))
    (h : Fwd succ C) : Fwd (reinsert succ (v, u, w)) (v :: C) := by
  rw [reinsert_eq hC h3 huw h]
  have hw0 : C.getD (C.length - 1) 0 ≠ v := fun e =>
    hv (e ▸ getD_mem_of_lt (by omega))
  refine ⟨fun j hj => ?_, ?_⟩
  · cases j with
    | zero => simp
    | succ i =>
      simp only [List.length_cons] at hj
      simp only [List.getD_cons_succ]
      have hiv : C.getD i 0 ≠ v := fun e => hv (e ▸ getD_mem_of_lt (by omega))
      have hiw : C.getD i 0 ≠ C.getD (C.length - 1) 0 :=
        getD_ne_of_ne hC (by omega) (by omega) (by omega)
      rw [Function.update_of_ne hiv, Function.update_of_ne hiw]
      exact h.1 i (by omega)
  · have hc : (v :: C).getD C.length 0 = C.getD (C.length - 1) 0 := by
      cases C with
      | nil => simp at h3
      | cons a t => simp
    simp only [List.length_cons, Nat.add_sub_cancel, List.getD_cons_zero, hc]
    rw [Function.update_of_ne hw0, Function.update_self]

/-- **Reinsertion** of an eliminated vertex between its two logged neighbours. -/
theorem rep_reinsert {succ : ℕ → ℕ} {v u w : ℕ} {C : List ℕ} (hC : C.Nodup) (h3 : 3 ≤ C.length)
    (hv : v ∉ C)
    (huw : (u = C.getD 0 0 ∧ w = C.getD (C.length - 1) 0) ∨
      (u = C.getD (C.length - 1) 0 ∧ w = C.getD 0 0))
    (h : Rep succ C) : Rep (reinsert succ (v, u, w)) (v :: C) := by
  rcases h with h | h
  · exact Or.inl (fwd_reinsert hC h3 hv huw h)
  · right
    have hr0 : C.reverse.getD 0 0 = C.getD (C.length - 1) 0 := by
      rw [List.getD_reverse _ (by omega)]
      simp
    have hr1 : C.reverse.getD (C.reverse.length - 1) 0 = C.getD 0 0 := by
      rw [List.getD_reverse _ (by simp; omega)]
      simp only [List.length_reverse]
      congr 1
      omega
    have hf := fwd_reinsert (List.nodup_reverse.mpr hC) (by simpa using h3)
      (by simpa using hv) (by rw [hr0, hr1]; tauto) h
    rw [List.reverse_cons]
    exact hf.isRotated (List.isRotated_concat v C.reverse).symm

/-- Following the successors reads off the cycle. -/
theorem walk_fwd {succ : ℕ → ℕ} {K : List ℕ} (h : Fwd succ K) :
    ∀ m j, j + m = K.length → walk succ m (K.getD j 0) = K.drop j := by
  intro m
  induction m with
  | zero =>
    intro j hj
    simp only [Nat.add_zero] at hj
    subst hj
    simp [walk]
  | succ m ih =>
    intro j hj
    rw [List.drop_eq_getElem_cons (by omega), ← List.getD_eq_getElem _ 0 (by omega)]
    simp only [walk, List.cons.injEq, true_and]
    rcases Nat.lt_or_ge (j + 1) K.length with hlt | hge
    · rw [h.1 j hlt]
      exact ih (j + 1) (by omega)
    · have hm : m = 0 := by omega
      subst hm
      simp only [walk]
      rw [List.drop_eq_nil_of_le (by omega)]

theorem walk_fwd_length {succ : ℕ → ℕ} {K : List ℕ} (h : Fwd succ K) :
    walk succ K.length (K.getD 0 0) = K := by
  simpa using walk_fwd h K.length 0 (by omega)

theorem fwd_three {f : ℕ → ℕ} {a b c : ℕ} (h : f a = b ∧ f b = c ∧ f c = a) :
    Fwd f [a, b, c] := by
  refine ⟨fun j hj => ?_, by simpa using h.2.2⟩
  have hj2 : j < 2 := by simp at hj; omega
  interval_cases j
  · simpa using h.1
  · simpa using h.2.1

/-- The successor function `x → y → z → x` follows every arrangement of `x`, `y`, `z`. -/
theorem rep_three {x y z : ℕ} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) {K : List ℕ}
    (hK : K.Nodup) (hl : K.length = 3) (hm : ∀ a, a ∈ K ↔ a = x ∨ a = y ∨ a = z) :
    Rep (Function.update (Function.update (Function.update (fun _ => 0) x y) y z) z x) K := by
  set f := Function.update (Function.update (Function.update (fun _ => 0) x y) y z) z x
    with hf
  have fx : f x = y := by
    simp only [hf, Function.update_of_ne hxz, Function.update_of_ne hxy, Function.update_self]
  have fy : f y = z := by
    simp only [hf, Function.update_of_ne hyz, Function.update_self]
  have fz : f z = x := by simp only [hf, Function.update_self]
  match K, hl with
  | [a, b, c], _ =>
    have ha := (hm a).mp (by simp)
    have hb := (hm b).mp (by simp)
    have hc := (hm c).mp (by simp)
    have hab : a ≠ b := by rintro rfl; simp at hK
    have hac : a ≠ c := by rintro rfl; simp at hK
    have hbc : b ≠ c := by rintro rfl; simp at hK
    unfold Rep
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
      rcases hc with rfl | rfl | rfl <;>
      first
        | exact absurd rfl hab | exact absurd rfl hac | exact absurd rfl hbc
        | exact Or.inl (fwd_three ⟨by assumption, by assumption, by assumption⟩)
        | exact Or.inr (fwd_three ⟨by assumption, by assumption, by assumption⟩)

end STACS2027.Ear

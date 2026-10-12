module

public import Outerplanar.TreeDP
import Mathlib.Tactic

/-!
# Backtracking in the tree dynamic program

Complements to `Outerplanar.TreeDP` for reading an optimal assignment off the tables:

* `Tree.induction_sub`: induction from a node down its subtree, along the children;
* `Problem.tot_eq_dp_of_local`: if, at every node `v` of the subtree of `r`, the values `γ`
  attain the minimum of the dynamic program at `v` with their own values on the variables
  with top `v` (`loc v γ + ∑ w, dp w γ = dp v γ`; note `upd v γ γ = γ`), then the cost of
  the subtree of `r` under `γ` is `dp r γ`;
* `Problem.total_eq_dp_of_local`: at a root, such values are optimal: their total cost is
  `dp r γ`, the optimum (`dp_root`).
-/

@[expose] public section

namespace STACS2027.TreeDP

open Finset

namespace Tree

variable {N : Type*} [DecidableEq N] (T : Tree N)

/-- **Induction down a subtree**: a property of `r` passed from every node to its
children holds on the subtree of `r`. -/
theorem induction_sub {Q : N → Prop} (hstep : ∀ v w, w ∈ T.children v → Q v → Q w) :
    ∀ r, Q r → ∀ v ∈ T.sub r, Q v := by
  intro r
  induction hr : T.size r using Nat.strong_induction_on generalizing r with
  | _ m ih =>
  intro hQ v hv
  by_cases h : v = r
  · exact h ▸ hQ
  · obtain ⟨w, hw, hvw⟩ := T.mem_child_of_mem_sub hv h
    exact ih _ (hr ▸ T.size_lt hw) w rfl (hstep r w hw hQ) v hvw

end Tree

namespace Problem

variable {N X F D : Type*} [DecidableEq N] [DecidableEq F] {T : Tree N} (P : Problem N X F D T)

omit [DecidableEq F] in
theorem upd_self (v : N) (γ : X → D) : P.upd v γ γ = γ := by
  funext x; simp [upd]

section DP

variable [DecidableEq X] [Fintype X] [Fintype D] [Nonempty D]

/-- **Backtracking**: values `γ` that attain, at every node of the subtree of `r`, the
minimum of the dynamic program with their own values cost `dp r γ` on the subtree. -/
theorem tot_eq_dp_of_local {r : N} {γ : X → D}
    (h : ∀ v ∈ T.sub r, P.loc v γ + ∑ w ∈ T.children v, P.dp w γ = P.dp v γ) :
    P.tot r γ = P.dp r γ := by
  induction hr : T.size r using Nat.strong_induction_on generalizing r with
  | _ m ih =>
  rw [P.tot_split, ← h r (T.mem_sub r)]
  congr 1
  apply Finset.sum_congr rfl
  intro w hw
  exact ih _ (hr ▸ T.size_lt hw)
    (fun v hv => h v (T.sub_trans (T.child_mem hw) hv)) rfl

/-- **Backtracking at the root**: values attaining the minimum of the dynamic program at
every node cost `dp r γ` in all, the optimum. -/
theorem total_eq_dp_of_local {r : N} (htop : ∀ x, P.top x ∈ T.sub r)
    (hown : ∀ f ∈ P.factors, P.own f ∈ T.sub r) {γ : X → D}
    (h : ∀ v ∈ T.sub r, P.loc v γ + ∑ w ∈ T.children v, P.dp w γ = P.dp v γ) :
    P.total γ = P.dp r γ ∧ P.total γ = (univ : Finset (X → D)).inf' univ_nonempty P.total := by
  have h1 : P.total γ = P.dp r γ := by
    rw [← P.tot_eq_dp_of_local h]
    unfold tot total
    congr 1
    ext f
    simp only [mem_filter, iff_self_and]
    exact hown f
  exact ⟨h1, h1.trans (P.dp_root htop hown γ)⟩

end DP

end Problem

end STACS2027.TreeDP

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic

/-!
# Dynamic programming over a rooted tree

The abstract form of the dynamic program of Appendix F. A rooted tree is given by the
subtree `sub v` and the children of each node; variables `x` take values in a finite set
`D` and have a *top* node; every cost term (factor) `f` has an owner node and depends only
on the variables of its scope, and every variable in the scope of `f` has its top at an
ancestor of the owner (or at the owner).

`dp v α` minimizes, over the values `β` of the variables whose top is `v`, the cost of the
factors owned by `v` plus the `dp` values of the children; the variables whose top lies
above `v` keep their values from `α`. `dp_eq_min`: `dp v α` is the minimum of the total
cost of the factors owned in the subtree of `v` over all values of the variables whose
top lies in the subtree, the others taken from `α`. At the root it is the optimum
(`dp_root`). `dp v α` depends on `α` only through the *boundary variables* of `v`: those
with top outside the subtree of `v` in the scope of a factor owned in it (`dp_congr`).
-/

@[expose] public section

namespace STACS2027.TreeDP

open Finset

/-- A rooted tree on the nodes `N`: subtrees, children and a size decreasing to the
children. -/
structure Tree (N : Type*) [DecidableEq N] where
  sub : N → Finset N
  children : N → Finset N
  size : N → ℕ
  mem_sub : ∀ v, v ∈ sub v
  sub_trans : ∀ {v w}, w ∈ sub v → sub w ⊆ sub v
  child_mem : ∀ {v w}, w ∈ children v → w ∈ sub v
  not_mem_child : ∀ {v w}, w ∈ children v → v ∉ sub w
  sub_eq : ∀ v, sub v = insert v ((children v).biUnion sub)
  disj : ∀ {v w w'}, w ∈ children v → w' ∈ children v → w ≠ w' → Disjoint (sub w) (sub w')
  size_lt : ∀ {v w}, w ∈ children v → size w < size v

namespace Tree

variable {N : Type*} [DecidableEq N] (T : Tree N)

theorem eq_of_mem_sub {u v : N} (h1 : u ∈ T.sub v) (h2 : v ∈ T.sub u) : u = v := by
  by_contra hne
  rw [T.sub_eq v] at h1
  rcases Finset.mem_insert.mp h1 with h | h
  · exact hne h
  · obtain ⟨w, hw, hu⟩ := Finset.mem_biUnion.mp h
    exact T.not_mem_child hw (T.sub_trans hu h2)

/-- A node of the subtree of `v` other than `v` lies in the subtree of a child. -/
theorem mem_child_of_mem_sub {u v : N} (h : u ∈ T.sub v) (hne : u ≠ v) :
    ∃ w ∈ T.children v, u ∈ T.sub w := by
  rw [T.sub_eq v] at h
  rcases Finset.mem_insert.mp h with h | h
  · exact absurd h hne
  · exact Finset.mem_biUnion.mp h

theorem child_unique {v w w' u : N} (hw : w ∈ T.children v) (hw' : w' ∈ T.children v)
    (hu : u ∈ T.sub w) (hu' : u ∈ T.sub w') : w = w' := by
  by_contra hne
  exact Finset.disjoint_left.mp (T.disj hw hw' hne) hu hu'

end Tree

/-- A minimization problem over the variables `X` with values in `D`, structured by the
tree: variables with tops, factors with owners, costs and scopes. -/
structure Problem (N X F D : Type*) [DecidableEq N] (T : Tree N) where
  top : X → N
  factors : Finset F
  own : F → N
  cost : F → (X → D) → ℕ
  scope : F → Finset X
  cost_congr : ∀ f γ γ', (∀ x ∈ scope f, γ x = γ' x) → cost f γ = cost f γ'
  scope_top : ∀ f ∈ factors, ∀ x ∈ scope f, own f ∈ T.sub (top x)

namespace Problem

variable {N X F D : Type*} [DecidableEq N] [DecidableEq F] {T : Tree N} (P : Problem N X F D T)

/-- The cost of the factors owned by `v`. -/
def loc (v : N) (γ : X → D) : ℕ := ∑ f ∈ P.factors.filter (fun f => P.own f = v), P.cost f γ

/-- The cost of the factors owned in the subtree of `v`. -/
def tot (v : N) (γ : X → D) : ℕ := ∑ f ∈ P.factors.filter (fun f => P.own f ∈ T.sub v), P.cost f γ

/-- The total cost. -/
def total (γ : X → D) : ℕ := ∑ f ∈ P.factors, P.cost f γ

/-- The values `β` on the variables with top `v`, `α` elsewhere. -/
def upd (v : N) (α β : X → D) : X → D := fun x => if P.top x = v then β x else α x

/-- The values `γ` on the variables with top in the subtree of `v`, `α` elsewhere. -/
def ext (v : N) (α γ : X → D) : X → D := fun x => if P.top x ∈ T.sub v then γ x else α x

/-- The cost of a subtree splits into the node's own factors and the children's subtrees. -/
theorem tot_split (v : N) (γ : X → D) :
    P.tot v γ = P.loc v γ + ∑ w ∈ T.children v, P.tot w γ := by
  unfold tot loc
  have hfil : P.factors.filter (fun f => P.own f ∈ T.sub v) =
      P.factors.filter (fun f => P.own f = v) ∪
        (T.children v).biUnion (fun w => P.factors.filter (fun f => P.own f ∈ T.sub w)) := by
    ext f
    simp only [mem_filter, mem_union, mem_biUnion]
    constructor
    · rintro ⟨hf, ho⟩
      by_cases h : P.own f = v
      · exact Or.inl ⟨hf, h⟩
      · obtain ⟨w, hw, hu⟩ := T.mem_child_of_mem_sub ho h
        exact Or.inr ⟨w, hw, hf, hu⟩
    · rintro (⟨hf, h⟩ | ⟨w, hw, hf, hu⟩)
      · exact ⟨hf, h ▸ T.mem_sub _⟩
      · exact ⟨hf, T.sub_trans (T.child_mem hw) hu⟩
  rw [hfil, sum_union, sum_biUnion]
  · intro w hw w' hw' hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro f h1 h2
    simp only [mem_filter] at h1 h2
    exact Finset.disjoint_left.mp (T.disj hw hw' hne) h1.2 h2.2
  · rw [Finset.disjoint_left]
    intro f h1 h2
    simp only [mem_filter, mem_biUnion] at h1 h2
    obtain ⟨w, hw, -, hu⟩ := h2
    rw [h1.2] at hu
    exact T.not_mem_child hw hu

omit [DecidableEq F] in
theorem loc_ext (v : N) (α γ : X → D) : P.loc v (P.ext v α γ) = P.loc v (P.upd v α γ) := by
  unfold loc
  apply Finset.sum_congr rfl
  intro f hf
  simp only [mem_filter] at hf
  apply P.cost_congr
  intro x hx
  have hst := P.scope_top f hf.1 x hx
  rw [hf.2] at hst
  simp only [ext, upd]
  by_cases h : P.top x ∈ T.sub v
  · rw [ite_eq_left h, ite_eq_left (T.eq_of_mem_sub h hst)]
  · have : P.top x ≠ v := fun he => h (he ▸ T.mem_sub _)
    rw [ite_eq_right h, ite_eq_right this]

omit [DecidableEq F] in
theorem tot_ext_child {v w : N} (hw : w ∈ T.children v) (α γ : X → D) :
    P.tot w (P.ext v α γ) = P.tot w (P.ext w (P.upd v α γ) γ) := by
  unfold tot
  apply Finset.sum_congr rfl
  intro f hf
  simp only [mem_filter] at hf
  apply P.cost_congr
  intro x hx
  have hst := P.scope_top f hf.1 x hx
  simp only [ext, upd]
  by_cases hxw : P.top x ∈ T.sub w
  · rw [ite_eq_left (T.sub_trans (T.child_mem hw) hxw), ite_eq_left hxw]
  · rw [ite_eq_right hxw]
    by_cases hxv : P.top x ∈ T.sub v
    · rw [ite_eq_left hxv]
      by_cases hv : P.top x = v
      · rw [ite_eq_left hv]
      · exfalso
        obtain ⟨w', hw', hu⟩ := T.mem_child_of_mem_sub hxv hv
        have h1 : P.own f ∈ T.sub w' := T.sub_trans hu hst
        have := T.child_unique hw hw' hf.2 h1
        subst this
        exact hxw hu
    · have : P.top x ≠ v := fun he => hxv (he ▸ T.mem_sub _)
      rw [ite_eq_right hxv, ite_eq_right this]

section DP

variable [DecidableEq X] [Fintype X] [Fintype D] [Nonempty D]

/-- **The dynamic program**: `dp v α` is the least cost of the factors owned by `v` plus the
values of the children, over the values of the variables with top `v`. -/
def dp (v : N) (α : X → D) : ℕ :=
  (univ : Finset (X → D)).inf' univ_nonempty fun β =>
    P.loc v (P.upd v α β) + ∑ w ∈ (T.children v).attach, dp w.1 (P.upd v α β)
termination_by T.size v
decreasing_by exact T.size_lt w.2

omit [DecidableEq F] in
theorem dp_eq (v : N) (α : X → D) :
    P.dp v α = (univ : Finset (X → D)).inf' univ_nonempty fun β =>
      P.loc v (P.upd v α β) + ∑ w ∈ T.children v, P.dp w (P.upd v α β) := by
  rw [dp]
  congr 1
  funext β
  congr 1
  exact Finset.sum_attach (T.children v) (fun w => P.dp w (P.upd v α β))

/-- **Correctness of the dynamic program**: `dp v α` is the least cost of the factors owned
in the subtree of `v`, over all values of the variables whose top is in the subtree, the
other variables taking their values from `α`. -/
theorem dp_eq_min (v : N) (α : X → D) :
    P.dp v α = (univ : Finset (X → D)).inf' univ_nonempty fun γ => P.tot v (P.ext v α γ) := by
  induction hv : T.size v using Nat.strong_induction_on generalizing v α with
  | _ s ih =>
  subst hv
  have IH : ∀ w ∈ T.children v, ∀ α', P.dp w α' =
      (univ : Finset (X → D)).inf' univ_nonempty fun γ => P.tot w (P.ext w α' γ) :=
    fun w hw α' => ih _ (T.size_lt hw) w α' rfl
  rw [P.dp_eq]
  apply le_antisymm
  · -- the dynamic program is at most every total
    rw [Finset.le_inf'_iff]
    intro γ _
    rw [P.tot_split, P.loc_ext]
    refine le_trans (Finset.inf'_le _ (mem_univ γ)) ?_
    apply Nat.add_le_add_left
    apply Finset.sum_le_sum
    intro w hw
    rw [IH w hw, P.tot_ext_child hw]
    exact Finset.inf'_le _ (mem_univ γ)
  · -- some total attains the dynamic program
    obtain ⟨β, -, hβ⟩ := Finset.exists_mem_eq_inf' (s := (univ : Finset (X → D)))
      univ_nonempty (fun β => P.loc v (P.upd v α β) + ∑ w ∈ T.children v, P.dp w (P.upd v α β))
    rw [hβ]
    have hopt : ∀ w ∈ T.children v, ∃ γw : X → D,
        P.dp w (P.upd v α β) = P.tot w (P.ext w (P.upd v α β) γw) := by
      intro w hw
      rw [IH w hw]
      obtain ⟨γw, -, h⟩ := Finset.exists_mem_eq_inf' (s := (univ : Finset (X → D)))
        univ_nonempty (fun γ => P.tot w (P.ext w (P.upd v α β) γ))
      exact ⟨γw, h⟩
    classical
    choose! γs hγs using hopt
    let γ : X → D := fun x =>
      if P.top x = v then β x
      else if h : ∃ w ∈ T.children v, P.top x ∈ T.sub w then γs h.choose x else β x
    have hupd : P.upd v α γ = P.upd v α β := by
      funext x
      simp only [upd, γ]
      split_ifs <;> rfl
    have hext : ∀ w ∈ T.children v,
        P.ext w (P.upd v α γ) γ = P.ext w (P.upd v α β) (γs w) := by
      intro w hw
      funext x
      rw [hupd]
      simp only [ext]
      by_cases hx : P.top x ∈ T.sub w
      · rw [ite_eq_left hx, ite_eq_left hx]
        have hnv : P.top x ≠ v := fun he => T.not_mem_child hw (he ▸ hx)
        have hex : ∃ w ∈ T.children v, P.top x ∈ T.sub w := ⟨w, hw, hx⟩
        simp only [γ, ite_eq_right hnv, dite_eq_left hex]
        have := T.child_unique hex.choose_spec.1 hw hex.choose_spec.2 hx
        rw [this]
      · rw [ite_eq_right hx, ite_eq_right hx]
    refine le_trans (Finset.inf'_le _ (mem_univ γ)) ?_
    rw [P.tot_split, P.loc_ext, hupd]
    apply le_of_eq
    congr 1
    apply Finset.sum_congr rfl
    intro w hw
    rw [P.tot_ext_child hw, hupd, hγs w hw]
    congr 1
    have h := hext w hw
    simp only [hupd] at h ⊢
    exact h

/-- At a root whose subtree contains every top and every owner, the dynamic program is the
optimum. -/
theorem dp_root {r : N} (htop : ∀ x, P.top x ∈ T.sub r) (hown : ∀ f ∈ P.factors, P.own f ∈ T.sub r)
    (α : X → D) :
    P.dp r α = (univ : Finset (X → D)).inf' univ_nonempty P.total := by
  rw [P.dp_eq_min]
  congr 1
  funext γ
  have h1 : P.ext r α γ = γ := by
    funext x; simp [ext, htop x]
  have h2 : P.factors.filter (fun f => P.own f ∈ T.sub r) = P.factors := by
    ext f; simp only [mem_filter, and_iff_left_iff_imp]; exact hown f
  simp only [tot, h1, h2, total]

/-- The boundary variables of `v`: top outside the subtree, in the scope of a factor owned
in the subtree. -/
def boundary (v : N) : Finset X :=
  univ.filter fun x => P.top x ∉ T.sub v ∧
    ∃ f ∈ P.factors, P.own f ∈ T.sub v ∧ x ∈ P.scope f

/-- `dp v α` depends on `α` only through the boundary variables of `v`. -/
theorem dp_congr (v : N) (α α' : X → D)
    (h : ∀ x ∈ P.boundary v, α x = α' x) : P.dp v α = P.dp v α' := by
  rw [P.dp_eq_min, P.dp_eq_min]
  congr 1
  funext γ
  unfold tot
  apply Finset.sum_congr rfl
  intro f hf
  simp only [mem_filter] at hf
  apply P.cost_congr
  intro x hx
  simp only [ext]
  split_ifs with hx'
  · rfl
  · exact h x (by simp only [boundary, mem_filter, mem_univ, true_and]; exact ⟨hx', f, hf.1, hf.2, hx⟩)

end DP

omit [DecidableEq F] in
/-- **Lemma 32** (abstract form): a variable in the scope of a factor owned by `v` has its
top at `v` or is a boundary variable of `v`. -/
theorem top_eq_or_mem_boundary [DecidableEq X] [Fintype X] {f : F} (hf : f ∈ P.factors) {x : X}
    (hx : x ∈ P.scope f) : P.top x = P.own f ∨ x ∈ P.boundary (P.own f) := by
  by_cases h : P.top x = P.own f
  · exact Or.inl h
  · right
    simp only [boundary, mem_filter, mem_univ, true_and]
    refine ⟨fun h' => h (T.eq_of_mem_sub h' (P.scope_top f hf x hx)), f, hf, T.mem_sub _, hx⟩

omit [DecidableEq F] in
/-- **Lemma 33** (abstract form): a boundary variable of a child of `v` has its top at `v`
or is a boundary variable of `v`. -/
theorem boundary_child [DecidableEq X] [Fintype X] {v w : N} (hw : w ∈ T.children v) {x : X}
    (hx : x ∈ P.boundary w) : P.top x = v ∨ x ∈ P.boundary v := by
  simp only [boundary, mem_filter, mem_univ, true_and] at hx ⊢
  obtain ⟨hxw, f, hf, hfw, hxf⟩ := hx
  by_cases hv : P.top x = v
  · exact Or.inl hv
  · right
    refine ⟨?_, f, hf, T.sub_trans (T.child_mem hw) hfw, hxf⟩
    intro hxv
    obtain ⟨w', hw', hu⟩ := T.mem_child_of_mem_sub hxv hv
    have := T.child_unique hw hw' hfw (T.sub_trans hu (P.scope_top f hf x hxf))
    subst this
    exact hxw hu

end Problem

end STACS2027.TreeDP

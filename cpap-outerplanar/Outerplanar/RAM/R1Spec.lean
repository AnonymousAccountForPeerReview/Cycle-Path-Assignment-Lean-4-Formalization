module

public import Outerplanar.RAM.Iface
import Mathlib.Tactic

/-!
# Phase R1 (neighbour lists and depth-first search), abstract side

The machine builds the CSR neighbour lists of `E = idEdges g` edge by edge and then runs the
depth-first search `DFS.step` step by step. This file supplies the abstract facts:

* neighbour lists of prefixes: `nbOf (E.take (j + 1))` is `nbOf (E.take j)` with the second end
  of the edge `E[j]` appended to the list of the first end and vice versa (`nbOf_take_succ_eq`,
  with `app L u w`: `w` appended to the list of `u`), so the degree counts `cnt E j v` grow by
  `bmp` (`cnt_succ`);
* the prefix sums `ps E v` of the degrees (the CSR offsets, `csrOff E N = (range (N+1)).map (ps E)`),
  `ps_succ`, monotonicity, `ps_total` (`ps E N = 2 |E|`), and `arr_csrAdj` (the CSR array from
  the per-vertex segments);
* the depth-first search: the steps as `visitS`/`bumpS` updates (`step_push`, `step_exam`,
  `step_pop`, `step_root`, `step_skip`), `drun_add`, `drun_eq_final` (a halted state reached from
  `init` is `final`), `mu_init`, `mu_congr`, and size bounds on the stack and the preorder list
  (`length_stk_lt`, `length_ord_lt`, `length_ord_le`).
-/

@[expose] public section

namespace STACS2027.RAM.R1

open STACS2027.Algo

/-! ### Neighbour lists of prefixes -/

theorem nbOf_append (E₁ E₂ : List Edge) (v : ℕ) : nbOf (E₁ ++ E₂) v = nbOf E₁ v ++ nbOf E₂ v := by
  simp [nbOf, List.flatMap_append]

theorem nbOf_singleton (e : Edge) (v : ℕ) :
    nbOf [e] v = if e.1 = v then [e.2] else if e.2 = v then [e.1] else [] := by
  simp [nbOf]

@[simp] theorem nbOf_nil (v : ℕ) : nbOf [] v = [] := rfl

theorem nbOf_take_succ {E : List Edge} {j : ℕ} (hj : j < E.length) (v : ℕ) :
    nbOf (E.take (j + 1)) v = nbOf (E.take j) v ++
      (if E[j].1 = v then [E[j].2] else if E[j].2 = v then [E[j].1] else []) := by
  rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, nbOf_append,
    nbOf_singleton]

/-- `w` appended to the list of `u`. -/
def app (L : ℕ → List ℕ) (u w : ℕ) : ℕ → List ℕ := Function.update L u (L u ++ [w])

/-- The cell `u` incremented. -/
def bmp (f : ℕ → ℕ) (u : ℕ) : ℕ → ℕ := Function.update f u (f u + 1)

/-- The neighbour lists after one more edge `(a, b)`, `a ≠ b`. -/
theorem nbOf_take_succ_eq {E : List Edge} {j : ℕ} (hj : j < E.length) (hne : E[j].1 ≠ E[j].2) :
    nbOf (E.take (j + 1)) = app (app (nbOf (E.take j)) E[j].1 E[j].2) E[j].2 E[j].1 := by
  funext v
  rw [nbOf_take_succ hj]
  simp only [app]
  by_cases h2 : v = E[j].2
  · subst h2
    simp [hne, Function.update_of_ne (Ne.symm hne)]
  · rw [Function.update_of_ne h2]
    by_cases h1 : v = E[j].1
    · subst h1; simp
    · rw [Function.update_of_ne h1]; simp [Ne.symm h1, Ne.symm h2]

/-- The degree of `v` among the first `j` edges. -/
def cnt (E : List Edge) (j v : ℕ) : ℕ := (nbOf (E.take j) v).length

theorem cnt_zero (E : List Edge) : cnt E 0 = fun _ => 0 := by
  funext v; simp [cnt]

theorem cnt_full (E : List Edge) : cnt E E.length = fun v => (nbOf E v).length := by
  funext v; simp [cnt]

theorem length_nbOf_take_le (E : List Edge) (j v : ℕ) :
    (nbOf (E.take j) v).length ≤ (nbOf E v).length := by
  have h := congrArg List.length (congrFun (congrArg nbOf (List.take_append_drop j E)) v)
  rw [nbOf_append, List.length_append] at h
  omega

theorem cnt_le (E : List Edge) (j v : ℕ) : cnt E j v ≤ (nbOf E v).length :=
  length_nbOf_take_le E j v

theorem length_app (L : ℕ → List ℕ) (u w v : ℕ) :
    (app L u w v).length = bmp (fun x => (L x).length) u v := by
  simp only [app, bmp]
  by_cases h : v = u
  · subst h; simp
  · simp [Function.update_of_ne h]

/-- The degree counts after one more edge `(a, b)`, `a ≠ b`. -/
theorem cnt_succ {E : List Edge} {j : ℕ} (hj : j < E.length) (hne : E[j].1 ≠ E[j].2) :
    cnt E (j + 1) = bmp (bmp (cnt E j) E[j].1) E[j].2 := by
  funext v
  have h := congrFun (nbOf_take_succ_eq hj hne) v
  simp only [cnt, h, length_app]
  rfl

/-! ### Prefix sums of the degrees -/

/-- The start of the neighbour list of `v` in the CSR array: the sum of the degrees below `v`. -/
def ps (E : List Edge) (v : ℕ) : ℕ := ((List.range v).map fun u => (nbOf E u).length).sum

@[simp] theorem ps_zero (E : List Edge) : ps E 0 = 0 := rfl

theorem ps_succ (E : List Edge) (v : ℕ) : ps E (v + 1) = ps E v + (nbOf E v).length := by
  simp [ps, List.range_succ]

theorem ps_mono (E : List Edge) {v w : ℕ} (h : v ≤ w) : ps E v ≤ ps E w := by
  induction w, h using Nat.le_induction with
  | base => exact le_rfl
  | succ w _ ih => rw [ps_succ]; omega

theorem ps_add_le (E : List Edge) {v w : ℕ} (h : v < w) : ps E v + (nbOf E v).length ≤ ps E w := by
  rw [← ps_succ]; exact ps_mono E h

theorem csrOff_eq (E : List Edge) (N : ℕ) : csrOff E N = (List.range (N + 1)).map (ps E) := rfl

theorem length_csrAdj (E : List Edge) (N : ℕ) : (csrAdj E N).length = ps E N := by
  simp [csrAdj, List.length_flatMap, ps]

theorem csrAdj_succ (E : List Edge) (N : ℕ) : csrAdj E (N + 1) = csrAdj E N ++ nbOf E N := by
  simp [csrAdj, List.range_succ, List.flatMap_append]

/-- The CSR array from the segments of the vertices. -/
theorem arr_csrAdj {m : ℕ → ℕ} {b : ℕ} {E : List Edge} {N : ℕ}
    (h : ∀ v, v < N → Arr m (b + ps E v) (nbOf E v)) : Arr m b (csrAdj E N) := by
  induction N with
  | zero => simp [csrAdj]
  | succ N ih =>
    rw [csrAdj_succ, arr_append, length_csrAdj]
    exact ⟨ih fun v hv => h v (by omega), h N (by omega)⟩

theorem sum_indicator (a N : ℕ) :
    ((List.range N).map fun u => if a = u then 1 else 0).sum = if a < N then 1 else 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    split_ifs <;> omega

theorem length_nbOf_cons (e : Edge) (E : List Edge) (v : ℕ) :
    (nbOf (e :: E) v).length =
      ((if e.1 = v then 1 else 0) + if e.1 ≠ v ∧ e.2 = v then 1 else 0) + (nbOf E v).length := by
  rw [show e :: E = [e] ++ E from rfl, nbOf_append, nbOf_singleton, List.length_append]
  by_cases h1 : e.1 = v
  · simp [h1]
  · by_cases h2 : e.2 = v <;> simp [h1, h2]

/-- The sum of the degrees is twice the number of edges. -/
theorem ps_total {E : List Edge} {N : ℕ} (h : ∀ e ∈ E, e.1 < e.2 ∧ e.2 < N) :
    ps E N = 2 * E.length := by
  induction E with
  | nil => simp [ps]
  | cons e E ih =>
    have he := h e (by simp)
    have ih' := ih fun e' he' => h e' (by simp [he'])
    have hsplit : ∀ u, (nbOf (e :: E) u).length =
        ((if e.1 = u then 1 else 0) + (if e.2 = u then 1 else 0)) + (nbOf E u).length := by
      intro u
      rw [length_nbOf_cons]
      by_cases h1 : e.1 = u
      · have : e.2 ≠ u := by omega
        simp [h1, this]
      · simp [h1]
    unfold ps at ih' ⊢
    simp only [hsplit, List.sum_map_add, sum_indicator] at ih' ⊢
    rw [ih']
    simp only [List.length_cons]
    split_ifs <;> omega

/-! ### The depth-first search -/

open DFS

/-- Visiting `w` with parent `p`: preorder number `cnt + 1`, parent `p`, pushed, recorded. -/
def visitS (s : State) (w p : ℕ) : State :=
  { s with
    pre := Function.update s.pre w (s.cnt + 1)
    par := Function.update s.par w p
    stk := w :: s.stk
    cnt := s.cnt + 1
    ord := s.ord ++ [w] }

/-- Advancing the neighbour pointer of `v`. -/
def bumpS (s : State) (v : ℕ) : State := { s with ptr := Function.update s.ptr v (s.ptr v + 1) }

section steps

variable {nb : ℕ → List ℕ} {s : State} {v : ℕ} {rest : List ℕ}

theorem step_push (hst : s.stk = v :: rest) (hlt : s.ptr v < (nb v).length)
    (hw : s.pre ((nb v).getD (s.ptr v) 0) = 0) :
    step nb s = visitS (bumpS s v) ((nb v).getD (s.ptr v) 0) v := by
  simp only [step, hst, hlt, hw, ↓reduceIte, visitS, bumpS]

theorem step_exam (hst : s.stk = v :: rest) (hlt : s.ptr v < (nb v).length)
    (hw : s.pre ((nb v).getD (s.ptr v) 0) ≠ 0) : step nb s = bumpS s v := by
  simp only [step, hst, hlt, hw, ↓reduceIte, bumpS]

theorem step_pop (hst : s.stk = v :: rest) (hlt : ¬ s.ptr v < (nb v).length) :
    step nb s = { s with stk := rest } := by
  simp [step, hst, hlt]

theorem step_root {r : ℕ} {rs' : List ℕ} (hst : s.stk = []) (hrs : s.rs = r :: rs')
    (hr : s.pre r = 0) : step nb s = { visitS s r r with rs := rs' } := by
  simp [step, hst, hrs, hr, visitS]

theorem step_skip {r : ℕ} {rs' : List ℕ} (hst : s.stk = []) (hrs : s.rs = r :: rs')
    (hr : s.pre r ≠ 0) : step nb s = { s with rs := rs' } := by
  simp [step, hst, hrs, hr]

end steps

theorem drun_add (nb : ℕ → List ℕ) :
    ∀ (a b : ℕ) (s : State), DFS.run nb (a + b) s = DFS.run nb b (DFS.run nb a s)
  | 0, b, s => by simp [DFS.run]
  | a + 1, b, s => by
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [DFS.run]
    exact drun_add nb a b (step nb s)

theorem drun_succ (nb : ℕ → List ℕ) (k : ℕ) (s : State) :
    DFS.run nb (k + 1) s = step nb (DFS.run nb k s) := by
  rw [drun_add]; rfl

/-- A halted state reached from the initial state is the final state. -/
theorem drun_eq_final {vs : List ℕ} {nb : ℕ → List ℕ} (hok : Ok vs nb) {k : ℕ}
    (hh : Halted (DFS.run nb k (init vs))) : DFS.run nb k (init vs) = final vs nb := by
  have h1 : DFS.run nb (k + mu vs nb (init vs)) (init vs) = DFS.run nb k (init vs) := by
    rw [drun_add, run_halted hh]
  have h2 : DFS.run nb (mu vs nb (init vs) + k) (init vs) = final vs nb := by
    rw [drun_add]; exact run_halted (final_halted hok) k
  rw [← h1, Nat.add_comm, h2]

theorem mu_init (vs : List ℕ) (nb : ℕ → List ℕ) :
    mu vs nb (init vs) = 3 * vs.length + (vs.map fun v => (nb v).length).sum := by
  simp [mu, init]; omega

/-- The measure depends only on `pre` and `ptr` on the candidates and the lengths of the stack
and of the candidate list. -/
theorem mu_congr {vs : List ℕ} {nb : ℕ → List ℕ} {s s' : State}
    (hpre : ∀ v ∈ vs, s.pre v = s'.pre v) (hptr : ∀ v ∈ vs, s.ptr v = s'.ptr v)
    (hstk : s.stk.length = s'.stk.length) (hrs : s.rs.length = s'.rs.length) :
    mu vs nb s = mu vs nb s' := by
  unfold mu
  rw [List.filter_congr (fun v hv => by rw [hpre v hv]),
    List.map_congr_left (fun v hv => by rw [hptr v hv]), hstk, hrs]

section bounds

variable {N : ℕ} {nb : ℕ → List ℕ} {s : State}

theorem lt_of_pre_ne (hI : Inv (List.range N) nb s) {v : ℕ} (h : s.pre v ≠ 0) : v < N :=
  List.mem_range.mp (hI.vis_vs v h)

theorem lt_of_mem_stk (hI : Inv (List.range N) nb s) {v : ℕ} (h : v ∈ s.stk) : v < N :=
  lt_of_pre_ne hI (hI.stk_vis v h)

/-- Room on the stack for an unvisited vertex. -/
theorem length_stk_lt (hI : Inv (List.range N) nb s) {w : ℕ} (hw : w < N) (hw0 : s.pre w = 0) :
    s.stk.length < N := by
  have hnd : (w :: s.stk).Nodup :=
    List.nodup_cons.mpr ⟨fun h => hI.stk_vis w h hw0, hI.stk_nodup⟩
  have hsub : w :: s.stk ⊆ List.range N := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact List.mem_range.mpr hw
    · exact List.mem_range.mpr (lt_of_mem_stk hI hx)
  have := (hnd.subperm hsub).length_le
  simp only [List.length_cons, List.length_range] at this
  omega

theorem length_ord_le (hI : Inv (List.range N) nb s) (hO : OrdInv s) : s.ord.length ≤ N := by
  have hsub : s.ord ⊆ List.range N := fun x hx =>
    List.mem_range.mpr (lt_of_pre_ne hI ((hO.mem x).mpr hx))
  simpa using (hO.nodup.subperm hsub).length_le

/-- Room in the preorder list for an unvisited vertex. -/
theorem length_ord_lt (hI : Inv (List.range N) nb s) (hO : OrdInv s) {w : ℕ} (hw : w < N)
    (hw0 : s.pre w = 0) : s.ord.length < N := by
  have hnd : (w :: s.ord).Nodup :=
    List.nodup_cons.mpr ⟨fun h => (hO.mem w).mpr h hw0, hO.nodup⟩
  have hsub : w :: s.ord ⊆ List.range N := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact List.mem_range.mpr hw
    · exact List.mem_range.mpr (lt_of_pre_ne hI ((hO.mem x).mpr hx))
  have := (hnd.subperm hsub).length_le
  simp only [List.length_cons, List.length_range] at this
  omega

end bounds

/-! ### The id graph -/

theorem idEdges_ps (g : Graph) : ps (idEdges g) (numV g) = 2 * (idEdges g).length :=
  ps_total fun _ he => idEdges_lt he

theorem idEdges_ne {g : Graph} {j : ℕ} (hj : j < (idEdges g).length) :
    (idEdges g)[j].1 ≠ (idEdges g)[j].2 :=
  Nat.ne_of_lt (idEdges_lt (List.getElem_mem hj)).1

theorem idEdges_lt_get {g : Graph} {j : ℕ} (hj : j < (idEdges g).length) :
    (idEdges g)[j].1 < numV g ∧ (idEdges g)[j].2 < numV g := by
  have := idEdges_lt (List.getElem_mem hj)
  constructor <;> omega

theorem lt_of_mem_nbOf {g : Graph} {v w : ℕ} (h : w ∈ nbOf (idEdges g) v) : w < numV g :=
  List.mem_range.mp ((ok_idEdges g).closed w v ((ok_idEdges g).symm v w h))

end STACS2027.RAM.R1

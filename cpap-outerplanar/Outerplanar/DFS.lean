module

public import Outerplanar.Palm
import Mathlib.Tactic

/-!
# Depth-first search

An iterative depth-first search (`dfsStep`), in the form a random-access machine runs it:
neighbour lists `nb v`, a list `rs` of root candidates, a stack `stk` of the open vertices,
a pointer `ptr v` to the next neighbour of `v` to examine, the preorder numbers `pre`
(`0` for unvisited vertices, else one more than the preorder index) and the parents `par`.

`Inv`: the stack is a tree path from a root; parents of visited vertices are visited
neighbours with smaller preorder numbers; and every examined neighbour of an open vertex,
and every neighbour of a finished vertex, is visited and is an ancestor or a descendant
of it. The measure `μ` decreases at every step; after `μ` of the initial state steps the
search has halted (`halted_run`, `final_halted`), and then every edge joins an ancestor and a
descendant: the parents form a palm tree (`palm_of_final`).
-/

@[expose] public section

namespace STACS2027.DFS

/-- The state of the search. -/
structure State where
  pre : ℕ → ℕ
  par : ℕ → ℕ
  ptr : ℕ → ℕ
  stk : List ℕ
  rs : List ℕ
  cnt : ℕ
  ord : List ℕ

/-- One step of the search. -/
def step (nb : ℕ → List ℕ) (s : State) : State :=
  match s.stk with
  | v :: rest =>
    if s.ptr v < (nb v).length then
      if s.pre ((nb v).getD (s.ptr v) 0) = 0 then
        { s with
          ptr := Function.update s.ptr v (s.ptr v + 1)
          pre := Function.update s.pre ((nb v).getD (s.ptr v) 0) (s.cnt + 1)
          par := Function.update s.par ((nb v).getD (s.ptr v) 0) v
          stk := (nb v).getD (s.ptr v) 0 :: v :: rest
          cnt := s.cnt + 1
          ord := s.ord ++ [(nb v).getD (s.ptr v) 0] }
      else { s with ptr := Function.update s.ptr v (s.ptr v + 1) }
    else { s with stk := rest }
  | [] =>
    match s.rs with
    | r :: rs' =>
      if s.pre r = 0 then
        { s with
          pre := Function.update s.pre r (s.cnt + 1)
          par := Function.update s.par r r
          stk := [r]
          rs := rs'
          cnt := s.cnt + 1
          ord := s.ord ++ [r] }
      else { s with rs := rs' }
    | [] => s

/-- The initial state, with root candidates `vs`. -/
def init (vs : List ℕ) : State := ⟨fun _ => 0, fun _ => 0, fun _ => 0, [], vs, 0, []⟩

/-- The search has halted. -/
def Halted (s : State) : Prop := s.stk = [] ∧ s.rs = []

/-- `n` steps of the search. -/
def run (nb : ℕ → List ℕ) : ℕ → State → State
  | 0, s => s
  | n + 1, s => run nb n (step nb s)

/-- `a` is an ancestor of `v` (or `v`) for the parents `par`. -/
def Anc (par : ℕ → ℕ) (a v : ℕ) : Prop := ∃ k, par^[k] v = a

/-- `v` and `w` are related: one is an ancestor of the other. -/
def Rel (par : ℕ → ℕ) (v w : ℕ) : Prop := Anc par v w ∨ Anc par w v

/-- The stack is a tree path: each entry is the parent of the one before it, the last
is a root. -/
def StackPath (par : ℕ → ℕ) : List ℕ → Prop
  | [] => True
  | [r] => par r = r
  | v :: u :: rest => par v = u ∧ StackPath par (u :: rest)

variable (vs : List ℕ) (nb : ℕ → List ℕ)

/-- The hypotheses on the neighbour lists: symmetric, without loops, and with every vertex
having a neighbour among the root candidates. -/
structure Ok : Prop where
  symm : ∀ v w, w ∈ nb v → v ∈ nb w
  noloop : ∀ v, v ∉ nb v
  closed : ∀ v w, w ∈ nb v → v ∈ vs

/-- The invariant. -/
structure Inv (s : State) : Prop where
  stk_vis : ∀ v ∈ s.stk, s.pre v ≠ 0
  stk_path : StackPath s.par s.stk
  stk_nodup : s.stk.Nodup
  par_vis : ∀ v, s.pre v ≠ 0 → s.par v ≠ v → s.pre (s.par v) ≠ 0
  par_nb : ∀ v, s.pre v ≠ 0 → s.par v ≠ v → v ∈ nb (s.par v)
  par_pre : ∀ v, s.pre v ≠ 0 → s.par v ≠ v → s.pre (s.par v) < s.pre v
  pre_le : ∀ v, s.pre v ≤ s.cnt
  ptr_le : ∀ v ∈ s.stk, s.ptr v ≤ (nb v).length
  open_rel : ∀ v ∈ s.stk, ∀ i < s.ptr v, s.pre ((nb v).getD i 0) ≠ 0 ∧ Rel s.par v ((nb v).getD i 0)
  fin_rel : ∀ v, s.pre v ≠ 0 → v ∉ s.stk → ∀ w ∈ nb v, s.pre w ≠ 0 ∧ Rel s.par v w
  roots : ∀ v ∈ vs, v ∈ s.rs ∨ s.pre v ≠ 0
  rs_sub : ∀ v ∈ s.rs, v ∈ vs
  vis_vs : ∀ v, s.pre v ≠ 0 → v ∈ vs
  ptr_zero : ∀ v, s.pre v = 0 → s.ptr v = 0

/-! ### Ancestors and updates of the parents -/

theorem rel_symm {par : ℕ → ℕ} {v w : ℕ} (h : Rel par v w) : Rel par w v := h.symm

theorem stack_anc {par : ℕ → ℕ} : ∀ {v : ℕ} {rest : List ℕ}, StackPath par (v :: rest) →
    ∀ u ∈ v :: rest, Anc par u v
  | v, [], _, u, hu => by simp at hu; subst hu; exact ⟨0, rfl⟩
  | v, w :: rest, ⟨hv, hp⟩, u, hu => by
    rcases List.mem_cons.mp hu with rfl | hu
    · exact ⟨0, rfl⟩
    · obtain ⟨k, hk⟩ := stack_anc hp u hu
      exact ⟨k + 1, by rw [Function.iterate_succ_apply, hv, hk]⟩

/-- The ancestors of visited vertices are visited. -/
theorem iterate_vis {pre par : ℕ → ℕ} (hpv : ∀ v, pre v ≠ 0 → par v ≠ v → pre (par v) ≠ 0)
    {x : ℕ} (hx : pre x ≠ 0) : ∀ k, pre (par^[k] x) ≠ 0 := by
  intro k
  induction k generalizing x with
  | zero => exact hx
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    by_cases hr : par x = x
    · rw [hr]; exact ih hx
    · exact ih (hpv x hx hr)

/-- Changing the parent of an unvisited vertex does not change the ancestors of visited
vertices. -/
theorem iterate_update {pre par : ℕ → ℕ} (hpv : ∀ v, pre v ≠ 0 → par v ≠ v → pre (par v) ≠ 0)
    {w y x : ℕ} (hw : pre w = 0) (hx : pre x ≠ 0) :
    ∀ k, (Function.update par w y)^[k] x = par^[k] x := by
  intro k
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    have hxw : x ≠ w := fun h => hx (h ▸ hw)
    rw [Function.update_of_ne hxw]
    by_cases hr : par x = x
    · rw [hr]; exact ih hx
    · exact ih (hpv x hx hr)

theorem anc_update_iff {pre par : ℕ → ℕ} (hpv : ∀ v, pre v ≠ 0 → par v ≠ v → pre (par v) ≠ 0)
    {w y a x : ℕ} (hw : pre w = 0) (hx : pre x ≠ 0) :
    Anc (Function.update par w y) a x ↔ Anc par a x := by
  simp only [Anc, iterate_update hpv hw hx]

theorem rel_update {pre par : ℕ → ℕ} (hpv : ∀ v, pre v ≠ 0 → par v ≠ v → pre (par v) ≠ 0)
    {w y a x : ℕ} (hw : pre w = 0) (ha : pre a ≠ 0) (hx : pre x ≠ 0) :
    Rel (Function.update par w y) a x ↔ Rel par a x := by
  simp only [Rel, anc_update_iff hpv hw hx, anc_update_iff hpv hw ha]

theorem stackPath_update {pre par : ℕ → ℕ} {w y : ℕ} (hw : pre w = 0) :
    ∀ {l : List ℕ}, (∀ v ∈ l, pre v ≠ 0) → StackPath par l → StackPath (Function.update par w y) l
  | [], _, _ => trivial
  | [r], hl, h => by
    have : r ≠ w := fun e => hl r (by simp) (e ▸ hw)
    simp only [StackPath, Function.update_of_ne this]; exact h
  | v :: u :: rest, hl, ⟨h1, h2⟩ => by
    have : v ≠ w := fun e => hl v (by simp) (e ▸ hw)
    refine ⟨by rw [Function.update_of_ne this]; exact h1, ?_⟩
    exact stackPath_update hw (fun x hx => hl x (List.mem_cons_of_mem _ hx)) h2

theorem getD_mem_nb {l : List ℕ} {i : ℕ} (h : i < l.length) : l.getD i 0 ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
  exact List.getElem_mem h

/-! ### The invariant is preserved -/

theorem inv_init : Inv vs nb (init vs) := by
  refine ⟨by simp [init], trivial, by simp [init], by simp [init], by simp [init], by simp [init],
    by simp [init], by simp [init], by simp [init], by simp [init], fun v hv => Or.inl hv,
    fun v hv => hv, by simp [init], by simp [init]⟩

variable {vs nb}

/-- Starting a new tree at an unvisited root candidate. -/
theorem inv_root {s : State} (hI : Inv vs nb s) (hst : s.stk = [])
    {r : ℕ} {rs' : List ℕ} (hrs' : s.rs = r :: rs') (hr0 : s.pre r = 0) :
    Inv vs nb { s with
      pre := Function.update s.pre r (s.cnt + 1)
      par := Function.update s.par r r
      stk := [r]
      rs := rs'
      cnt := s.cnt + 1
      ord := s.ord ++ [r] } := by
  obtain ⟨hsv, hsp, hsn, hpv, hpn, hpp, hpl, hptr, hor, hfr, hro, hrs, hvv, hpz⟩ := hI
  have hrvs : r ∈ vs := hrs r (by simp [hrs'])
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only
  · simp
  · simp [StackPath]
  · simp
  · intro x hx hxr
    by_cases hxr' : x = r
    · subst hxr'; simp at hxr
    · rw [Function.update_of_ne hxr'] at hx hxr
      rw [Function.update_of_ne hxr']
      have := hpv x hx hxr
      by_cases h : s.par x = r
      · rw [h]; simp
      · rw [Function.update_of_ne h]; exact this
  · intro x hx hxr
    by_cases hxr' : x = r
    · subst hxr'; simp at hxr
    · rw [Function.update_of_ne hxr'] at hx hxr ⊢
      exact hpn x hx hxr
  · intro x hx hxr
    by_cases hxr' : x = r
    · subst hxr'; simp at hxr
    · rw [Function.update_of_ne hxr'] at hx hxr ⊢
      have h1 := hpp x hx hxr
      have h2 := hpv x hx hxr
      have hne : s.par x ≠ r := fun e => h2 (e ▸ hr0)
      rw [Function.update_of_ne hne, Function.update_of_ne hxr']
      exact h1
  · intro x
    by_cases hx : x = r
    · subst hx; simp
    · rw [Function.update_of_ne hx]; have := hpl x; omega
  · intro x hx
    simp at hx; subst hx; simp [hpz x hr0]
  · intro x hx i hi
    simp at hx; subst hx; rw [hpz x hr0] at hi; omega
  · intro x hx hxs w hw
    have hxr : x ≠ r := by intro e; subst e; simp at hxs
    rw [Function.update_of_ne hxr] at hx
    have hxs' : x ∉ s.stk := by rw [hst]; simp
    obtain ⟨h1, h2⟩ := hfr x hx hxs' w hw
    have hwr : w ≠ r := fun e => h1 (e ▸ hr0)
    refine ⟨by rw [Function.update_of_ne hwr]; exact h1, ?_⟩
    exact (rel_update hpv hr0 hx h1).mpr h2
  · intro x hx
    rcases hro x hx with h | h
    · rw [hrs'] at h
      rcases List.mem_cons.mp h with rfl | h
      · right; simp
      · left; exact h
    · right
      by_cases hxr : x = r
      · subst hxr; simp
      · rw [Function.update_of_ne hxr]; exact h
  · intro x hx; exact hrs x (by simp [hrs', hx])
  · intro x hx
    by_cases hxr : x = r
    · subst hxr; exact hrvs
    · rw [Function.update_of_ne hxr] at hx; exact hvv x hx
  · intro x hx
    by_cases hxr : x = r
    · subst hxr; simp at hx
    · rw [Function.update_of_ne hxr] at hx; exact hpz x hx

/-- Skipping a visited root candidate. -/
theorem inv_skip {s : State} (hI : Inv vs nb s) (_hst : s.stk = [])
    {r : ℕ} {rs' : List ℕ} (hrs' : s.rs = r :: rs') (hr0 : s.pre r ≠ 0) :
    Inv vs nb { s with rs := rs' } := by
  obtain ⟨hsv, hsp, hsn, hpv, hpn, hpp, hpl, hptr, hor, hfr, hro, hrs, hvv, hpz⟩ := hI
  refine ⟨hsv, hsp, hsn, hpv, hpn, hpp, hpl, hptr, hor, hfr, ?_, ?_, hvv, hpz⟩ <;> dsimp only
  · intro x hx
    rcases hro x hx with h | h
    · rw [hrs'] at h
      rcases List.mem_cons.mp h with rfl | h
      · exact Or.inr hr0
      · exact Or.inl h
    · exact Or.inr h
  · intro x hx; exact hrs x (by simp [hrs', hx])

/-- Descending to an unvisited neighbour `w` of the top `v`. -/
theorem inv_push (hok : Ok vs nb) {s : State} (hI : Inv vs nb s) {v : ℕ} {rest : List ℕ}
    (hst : s.stk = v :: rest) (hlt : s.ptr v < (nb v).length)
    (hw0 : s.pre ((nb v).getD (s.ptr v) 0) = 0) :
    Inv vs nb { s with
      ptr := Function.update s.ptr v (s.ptr v + 1)
      pre := Function.update s.pre ((nb v).getD (s.ptr v) 0) (s.cnt + 1)
      par := Function.update s.par ((nb v).getD (s.ptr v) 0) v
      stk := (nb v).getD (s.ptr v) 0 :: v :: rest
      cnt := s.cnt + 1
      ord := s.ord ++ [(nb v).getD (s.ptr v) 0] } := by
  obtain ⟨hsv, hsp, hsn, hpv, hpn, hpp, hpl, hptr, hor, hfr, hro, hrs, hvv, hpz⟩ := hI
  have hvs : v ∈ s.stk := by rw [hst]; simp
  have hvv0 := hsv v hvs
  set w := (nb v).getD (s.ptr v) 0 with hw_def
  have hwnb : w ∈ nb v := getD_mem_nb hlt
  have hwv : w ≠ v := fun e => hok.noloop v (e ▸ hwnb)
  have hwstk : w ∉ s.stk := fun h => hsv w h hw0
  have hwvs : w ∈ vs := hok.closed w v (hok.symm v w hwnb)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · simp
    · have : x ≠ w := fun e => hwstk (e ▸ (hst ▸ hx))
      rw [Function.update_of_ne this]; exact hsv x (hst ▸ hx)
  · refine ⟨by simp, ?_⟩
    exact stackPath_update hw0 (fun x hx => hsv x (hst ▸ hx)) (hst ▸ hsp)
  · exact List.nodup_cons.mpr ⟨fun h => hwstk (hst ▸ h), hst ▸ hsn⟩
  · intro x hx hxr
    by_cases hxw : x = w
    · subst hxw; simp only [Function.update_self]; rw [Function.update_of_ne hwv.symm]
      exact hvv0
    · rw [Function.update_of_ne hxw] at hx hxr ⊢
      have h1 := hpv x hx hxr
      have hne : s.par x ≠ w := fun e => h1 (e ▸ hw0)
      rw [Function.update_of_ne hne]; exact h1
  · intro x hx hxr
    by_cases hxw : x = w
    · subst hxw; simp only [Function.update_self]; exact hwnb
    · rw [Function.update_of_ne hxw] at hx hxr ⊢
      exact hpn x hx hxr
  · intro x hx hxr
    by_cases hxw : x = w
    · subst hxw
      simp only [Function.update_self]
      rw [Function.update_of_ne hwv.symm]
      have := hpl v; omega
    · simp only [Function.update_of_ne hxw] at hx hxr ⊢
      have h1 := hpv x hx hxr
      have hne : s.par x ≠ w := fun e => h1 (e ▸ hw0)
      rw [Function.update_of_ne hne]; exact hpp x hx hxr
  · intro x
    by_cases hxw : x = w
    · subst hxw; simp
    · rw [Function.update_of_ne hxw]; have := hpl x; omega
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · rw [Function.update_of_ne hwv, hpz _ hw0]; omega
    · by_cases hxv : x = v
      · subst hxv; simp; omega
      · rw [Function.update_of_ne hxv]; exact hptr x (hst ▸ hx)
  · intro x hx i hi
    rcases List.mem_cons.mp hx with rfl | hx
    · rw [Function.update_of_ne hwv, hpz _ hw0] at hi; omega
    · by_cases hxv : x = v
      · subst hxv
        simp only [Function.update_self] at hi
        by_cases hi' : i = s.ptr x
        · subst hi'
          refine ⟨by rw [← hw_def]; simp, ?_⟩
          rw [← hw_def]
          exact Or.inl ⟨1, by simp⟩
        · have hi'' : i < s.ptr x := by omega
          obtain ⟨h1, h2⟩ := hor x hvs i hi''
          have hne : (nb x).getD i 0 ≠ w := fun e => h1 (e ▸ hw0)
          refine ⟨by rw [Function.update_of_ne hne]; exact h1, ?_⟩
          exact (rel_update hpv hw0 hvv0 h1).mpr h2
      · rw [Function.update_of_ne hxv] at hi
        have hxs : x ∈ s.stk := hst ▸ hx
        obtain ⟨h1, h2⟩ := hor x hxs i hi
        have hne : (nb x).getD i 0 ≠ w := fun e => h1 (e ▸ hw0)
        refine ⟨by rw [Function.update_of_ne hne]; exact h1, ?_⟩
        exact (rel_update hpv hw0 (hsv x hxs) h1).mpr h2
  · intro x hx hxs u hu
    have hxw : x ≠ w := fun e => hxs (by simp [e])
    rw [Function.update_of_ne hxw] at hx
    have hxs' : x ∉ s.stk := by rw [hst]; intro h; exact hxs (List.mem_cons_of_mem _ h)
    obtain ⟨h1, h2⟩ := hfr x hx hxs' u hu
    have hne : u ≠ w := fun e => h1 (e ▸ hw0)
    refine ⟨by rw [Function.update_of_ne hne]; exact h1, ?_⟩
    exact (rel_update hpv hw0 hx h1).mpr h2
  · intro x hx
    rcases hro x hx with h | h
    · exact Or.inl h
    · right
      by_cases hxw : x = w
      · subst hxw; simp
      · rw [Function.update_of_ne hxw]; exact h
  · exact hrs
  · intro x hx
    by_cases hxw : x = w
    · subst hxw; exact hwvs
    · rw [Function.update_of_ne hxw] at hx; exact hvv x hx
  · intro x hx
    by_cases hxw : x = w
    · subst hxw; simp at hx
    · rw [Function.update_of_ne hxw] at hx
      by_cases hxv : x = v
      · subst hxv; exact absurd hx hvv0
      · rw [Function.update_of_ne hxv]; exact hpz x hx

/-- Examining a visited neighbour of the top `v`. -/
theorem inv_exam (hok : Ok vs nb) {s : State} (hI : Inv vs nb s) {v : ℕ} {rest : List ℕ}
    (hst : s.stk = v :: rest) (hlt : s.ptr v < (nb v).length)
    (hw0 : s.pre ((nb v).getD (s.ptr v) 0) ≠ 0) :
    Inv vs nb { s with ptr := Function.update s.ptr v (s.ptr v + 1) } := by
  obtain ⟨hsv, hsp, hsn, hpv, hpn, hpp, hpl, hptr, hor, hfr, hro, hrs, hvv, hpz⟩ := hI
  have hvs : v ∈ s.stk := by rw [hst]; simp
  have hvv0 := hsv v hvs
  have hanc := stack_anc (by rw [← hst]; exact hsp)
  set w := (nb v).getD (s.ptr v) 0 with hw_def
  have hwnb : w ∈ nb v := getD_mem_nb hlt
  have hrel : Rel s.par v w := by
    by_cases hws : w ∈ s.stk
    · right; exact hanc w (hst ▸ hws)
    · exact (hfr w hw0 hws v (hok.symm v w hwnb)).2.symm
  refine ⟨hsv, hsp, hsn, hpv, hpn, hpp, hpl, ?_, ?_, hfr, hro, hrs, hvv, ?_⟩ <;> dsimp only
  · intro x hx
    by_cases hxv : x = v
    · subst hxv; simp; omega
    · rw [Function.update_of_ne hxv]; exact hptr x hx
  · intro x hx i hi
    by_cases hxv : x = v
    · subst hxv
      simp only [Function.update_self] at hi
      by_cases hi' : i = s.ptr x
      · subst hi'; exact ⟨hw0, hrel⟩
      · exact hor x hvs i (by omega)
    · rw [Function.update_of_ne hxv] at hi
      exact hor x hx i hi
  · intro x hx
    by_cases hxv : x = v
    · subst hxv; exact absurd hx hvv0
    · rw [Function.update_of_ne hxv]; exact hpz x hx

/-- Finishing the top `v`. -/
theorem inv_pop {s : State} (hI : Inv vs nb s) {v : ℕ} {rest : List ℕ}
    (hst : s.stk = v :: rest) (hlt : ¬ s.ptr v < (nb v).length) :
    Inv vs nb { s with stk := rest } := by
  obtain ⟨hsv, hsp, hsn, hpv, hpn, hpp, hpl, hptr, hor, hfr, hro, hrs, hvv, hpz⟩ := hI
  have hvs : v ∈ s.stk := by rw [hst]; simp
  have hle := hptr v hvs
  have hnd := hst ▸ hsn
  refine ⟨fun x hx => hsv x (by rw [hst]; exact List.mem_cons_of_mem _ hx), ?_,
    (List.nodup_cons.mp hnd).2, hpv, hpn, hpp, hpl,
    fun x hx => hptr x (by rw [hst]; exact List.mem_cons_of_mem _ hx),
    fun x hx => hor x (by rw [hst]; exact List.mem_cons_of_mem _ hx), ?_, hro, hrs, hvv, hpz⟩ <;>
    dsimp only
  · have := hst ▸ hsp
    rcases rest with _ | ⟨u, rest'⟩
    · trivial
    · exact this.2
  · intro x hx hxs u hu
    by_cases hxv : x = v
    · subst hxv
      obtain ⟨i, hi, rfl⟩ : ∃ i, i < (nb x).length ∧ (nb x).getD i 0 = u := by
        obtain ⟨i, hi, he⟩ := List.getElem_of_mem hu
        exact ⟨i, hi, by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; simp [he]⟩
      exact hor x hvs i (by omega)
    · exact hfr x hx (by rw [hst]; simp [hxv, hxs]) u hu

theorem inv_step (hok : Ok vs nb) {s : State} (hI : Inv vs nb s) : Inv vs nb (step nb s) := by
  unfold step
  split
  · rename_i v rest hst
    split
    · rename_i hlt
      split
      · exact inv_push hok hI hst hlt (by assumption)
      · exact inv_exam hok hI hst hlt (by assumption)
    · exact inv_pop hI hst (by assumption)
  · rename_i hst
    split
    · rename_i r rs' hrs'
      split
      · exact inv_root hI hst hrs' (by assumption)
      · exact inv_skip hI hst hrs' (by assumption)
    · exact hI

/-! ### The preorder list -/

/-- The preorder list records the visited vertices in the order of their preorder numbers. -/
structure OrdInv (s : State) : Prop where
  mem : ∀ v, s.pre v ≠ 0 ↔ v ∈ s.ord
  nodup : s.ord.Nodup
  pre_eq : ∀ v ∈ s.ord, s.pre v = s.ord.idxOf v + 1
  cnt_eq : s.cnt = s.ord.length

theorem ordInv_init (vs : List ℕ) : OrdInv (init vs) :=
  ⟨by simp [init], List.nodup_nil, by simp [init], rfl⟩

theorem ordInv_visit {s : State} (h : OrdInv s) {w : ℕ} (hw : s.pre w = 0) :
    OrdInv { s with
      pre := Function.update s.pre w (s.cnt + 1)
      ord := s.ord ++ [w]
      cnt := s.cnt + 1 } := by
  obtain ⟨hm, hn, hp, hc⟩ := h
  have hwo : w ∉ s.ord := fun h' => (hm w).mpr h' hw
  refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp only
  · intro v
    by_cases hv : v = w
    · subst hv; simp
    · rw [Function.update_of_ne hv, hm v]; simp [hv]
  · exact hn.append (List.nodup_singleton w) (by simpa using hwo)
  · intro v hv
    by_cases hvw : v = w
    · subst hvw
      rw [Function.update_self, List.idxOf_append_of_notMem hwo, hc]; simp
    · rw [Function.update_of_ne hvw]
      have hv' : v ∈ s.ord := by simpa [hvw] using hv
      rw [List.idxOf_append_of_mem hv', hp v hv']
  · simp [hc]

theorem ordInv_step {s : State} (h : OrdInv s) : OrdInv (step nb s) := by
  unfold step
  split
  · split
    · split
      · rename_i hw0
        have := ordInv_visit h hw0
        exact ⟨this.mem, this.nodup, this.pre_eq, this.cnt_eq⟩
      · exact ⟨h.mem, h.nodup, h.pre_eq, h.cnt_eq⟩
    · exact ⟨h.mem, h.nodup, h.pre_eq, h.cnt_eq⟩
  · split
    · split
      · rename_i hr0
        have := ordInv_visit h hr0
        exact ⟨this.mem, this.nodup, this.pre_eq, this.cnt_eq⟩
      · exact ⟨h.mem, h.nodup, h.pre_eq, h.cnt_eq⟩
    · exact ⟨h.mem, h.nodup, h.pre_eq, h.cnt_eq⟩

theorem ordInv_run : ∀ n {s : State}, OrdInv s → OrdInv (run nb n s)
  | 0, _, h => h
  | n + 1, _, h => ordInv_run n (ordInv_step h)

/-! ### Termination -/

/-- The measure: twice the unvisited candidates, the unexamined neighbours, the stack and
the remaining candidates. -/
def mu (vs : List ℕ) (nb : ℕ → List ℕ) (s : State) : ℕ :=
  2 * (vs.filter fun v => s.pre v = 0).length + (vs.map fun v => (nb v).length - s.ptr v).sum +
    s.stk.length + s.rs.length

theorem sum_map_le_aux {l : List ℕ} {f g : ℕ → ℕ} (hle : ∀ x ∈ l, f x ≤ g x) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    have := hle a (by simp)
    have := ih (fun x hx => hle x (List.mem_cons_of_mem _ hx))
    omega

theorem sum_map_lt_aux {l : List ℕ} {f g : ℕ → ℕ} (hle : ∀ x ∈ l, f x ≤ g x) {y : ℕ}
    (hy : y ∈ l) (hlt : f y < g y) : (l.map f).sum < (l.map g).sum := by
  induction l with
  | nil => simp at hy
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    have ha := hle a (by simp)
    have hle' : ∀ x ∈ l, f x ≤ g x := fun x hx => hle x (List.mem_cons_of_mem _ hx)
    rcases List.mem_cons.mp hy with rfl | hy
    · have := sum_map_le_aux hle'; omega
    · have := ih hle' hy; omega

theorem length_filter_eq_sum (l : List ℕ) (p : ℕ → Prop) [DecidablePred p] :
    (l.filter fun x => p x).length = (l.map fun x => if p x then 1 else 0).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases h : p a
    · simp [h, ih, Nat.add_comm]
    · simp [h, ih]

/-- Visiting a candidate lowers the number of unvisited candidates. -/
theorem unvisited_lt {l : List ℕ} {pre : ℕ → ℕ} {w x : ℕ} (hw : pre w = 0) (hx : x ≠ 0)
    (hwl : w ∈ l) :
    (l.filter fun v => Function.update pre w x v = 0).length < (l.filter fun v => pre v = 0).length := by
  rw [length_filter_eq_sum, length_filter_eq_sum]
  apply sum_map_lt_aux (y := w) _ hwl (by simp [hw, hx])
  intro y _
  by_cases hyw : y = w
  · subst hyw; simp [hx]
  · simp [Function.update_of_ne hyw]

theorem unvisited_le {l : List ℕ} {pre : ℕ → ℕ} {w x : ℕ} (hx : x ≠ 0) :
    (l.filter fun v => Function.update pre w x v = 0).length ≤ (l.filter fun v => pre v = 0).length := by
  rw [length_filter_eq_sum, length_filter_eq_sum]
  apply sum_map_le_aux
  intro y _
  by_cases hyw : y = w
  · subst hyw; simp [hx]
  · simp [Function.update_of_ne hyw]

theorem ptrsum_lt {l : List ℕ} {nb : ℕ → List ℕ} {ptr : ℕ → ℕ} {v : ℕ} (hv : v ∈ l)
    (hlt : ptr v < (nb v).length) :
    (l.map fun x => (nb x).length - Function.update ptr v (ptr v + 1) x).sum <
      (l.map fun x => (nb x).length - ptr x).sum := by
  apply sum_map_lt_aux (y := v) _ hv (by simp; omega)
  intro y _
  by_cases hyv : y = v
  · subst hyv; simp; omega
  · simp [Function.update_of_ne hyv]

theorem mu_step (hok : Ok vs nb) {s : State} (hI : Inv vs nb s) (hh : ¬ Halted s) :
    mu vs nb (step nb s) < mu vs nb s := by
  unfold step
  split
  · rename_i v rest hst
    have hvs : v ∈ s.stk := by rw [hst]; simp
    have hvl : v ∈ vs := hI.vis_vs v (hI.stk_vis v hvs)
    split
    · rename_i hlt
      split
      · rename_i hw0
        set w := (nb v).getD (s.ptr v) 0
        have hwnb : w ∈ nb v := getD_mem_nb hlt
        have hwl : w ∈ vs := hok.closed w v (hok.symm v w hwnb)
        unfold mu; dsimp only
        have h1 := unvisited_lt (l := vs) hw0 (by omega : s.cnt + 1 ≠ 0) hwl
        have h2 := ptrsum_lt (l := vs) (nb := nb) hvl hlt
        rw [hst]; simp only [List.length_cons]
        omega
      · unfold mu; dsimp only
        have h2 := ptrsum_lt (l := vs) (nb := nb) hvl hlt
        omega
    · unfold mu; dsimp only
      rw [hst]; simp only [List.length_cons]
      omega
  · rename_i hst
    split
    · rename_i r rs' hrs'
      have hrl : r ∈ vs := hI.rs_sub r (by rw [hrs']; simp)
      split
      · rename_i hr0
        unfold mu; dsimp only
        have h1 := unvisited_lt (l := vs) hr0 (by omega : s.cnt + 1 ≠ 0) hrl
        rw [hst, hrs']; simp only [List.length_cons, List.length_nil]
        omega
      · unfold mu; dsimp only
        rw [hrs']; simp only [List.length_cons]
        omega
    · rename_i hrs'
      exact absurd ⟨hst, hrs'⟩ hh

theorem step_halted {s : State} (h : Halted s) : step nb s = s := by
  unfold step; rw [h.1]; simp only; rw [h.2]

theorem run_halted {s : State} (h : Halted s) : ∀ n, run nb n s = s := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simp only [run, step_halted h, ih]

theorem inv_run (hok : Ok vs nb) : ∀ n {s : State}, Inv vs nb s → Inv vs nb (run nb n s)
  | 0, _, h => h
  | n + 1, _, h => inv_run hok n (inv_step hok h)

theorem halted_run (hok : Ok vs nb) : ∀ n {s : State}, Inv vs nb s → mu vs nb s ≤ n →
    Halted (run nb n s)
  | 0, s, h, hm => by
    by_contra hh
    have := mu_step hok h hh
    omega
  | n + 1, s, h, hm => by
    by_cases hh : Halted s
    · simp only [run, step_halted hh, run_halted hh]; exact hh
    · have := mu_step hok h hh
      exact halted_run hok n (inv_step hok h) (by omega)

/-- The final state of the search. -/
def final (vs : List ℕ) (nb : ℕ → List ℕ) : State := run nb (mu vs nb (init vs)) (init vs)

theorem final_inv (hok : Ok vs nb) : Inv vs nb (final vs nb) := inv_run hok _ (inv_init vs nb)

theorem final_halted (hok : Ok vs nb) : Halted (final vs nb) :=
  halted_run hok _ (inv_init vs nb) le_rfl

theorem final_ordInv : OrdInv (final vs nb) := ordInv_run _ (ordInv_init vs)

/-- **The search yields a palm tree** of every graph whose neighbour lists it searches. -/
theorem palm_of_final (hok : Ok vs nb) {g : Graph} (hnb : ∀ v w, w ∈ nb v ↔ Adj g v w)
    (hvs : ∀ v, IsVertex g v → v ∈ vs) :
    ∃ P : Palm g, P.par = (final vs nb).par ∧ P.pre = (final vs nb).pre := by
  have hI := final_inv hok
  have hH := final_halted hok
  set s := final vs nb
  have hvis : ∀ v, IsVertex g v → s.pre v ≠ 0 := by
    intro v hv
    rcases hI.roots v (hvs v hv) with h | h
    · rw [hH.2] at h; simp at h
    · exact h
  refine ⟨⟨s.par, s.pre, ?_, ?_, ?_⟩, rfl, rfl⟩
  · intro v hv hr
    exact (hnb _ _).mp (hI.par_nb v (hvis v hv) hr)
  · intro v hv hr
    exact hI.par_pre v (hvis v hv) hr
  · intro u v huv
    have hu : IsVertex g u := ⟨v, huv.symm⟩
    have h := (hI.fin_rel u (hvis u hu) (by rw [hH.1]; simp) v ((hnb u v).mpr huv)).2
    exact h

end STACS2027.DFS

namespace STACS2027

/-- Every graph has a palm tree. -/
theorem exists_palm (g : Graph) : Nonempty (Palm g) := by
  let vs := vertices g
  let nb : ℕ → List ℕ := fun v => vs.filter fun w => decide (Adj g v w)
  have hnb : ∀ v w, w ∈ nb v ↔ Adj g v w := by
    intro v w
    simp only [nb, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    intro h
    exact (endpoints_mem_vertices h.2).2
  have hok : DFS.Ok vs nb := by
    refine ⟨fun v w h => (hnb w v).mpr ((hnb v w).mp h).symm,
      fun v h => ((hnb v v).mp h).1 rfl, fun v w h => (endpoints_mem_vertices ((hnb v w).mp h).2).1⟩
  obtain ⟨P, -, -⟩ := DFS.palm_of_final hok hnb (fun v ⟨u, huv⟩ => (endpoints_mem_vertices huv.2).2)
  exact ⟨P⟩

end STACS2027

module

public import Mathlib.Logic.Relation
public import Mathlib.Logic.Function.Basic
import Mathlib.Tactic

/-!
# Strongly connected components by the path-based algorithm (abstract side)

A linear-time algorithm computing the strongly connected components of a directed graph in a
topological order, in the iterative form a random-access machine runs it. It is the
path-based algorithm (Purdom 1970, Munro 1971, Cheriyan–Mehlhorn 1996, Gabow 2000): a variant
of ANONYMIZED's algorithm in which the low links are replaced by a stack `B` of group boundaries.

The graph has the vertices `0, …, N - 1` and the out-neighbour lists `nb v` (`Closed N nb`).
The state (`State`) holds

* `lab v`: `0` if `v` is unvisited, `i + 1` if `v` is at position `i` of the stack `S` of
  visited vertices whose component is not yet known, and a value `> N` once `v` is assigned
  to a component (all vertices of a component get the same value; the `k`-th component found
  gets `N + 1 + k`);
* `ptr v`: the number of examined out-arcs of `v`; `stk`: the depth-first search stack (top
  first); `S` (bottom first); `B` (top first): the values `lab r` of the roots of the
  *groups*, the segments of `S` that are already known to be strongly connected; `nxt`: the
  next root candidate; `nc`: the number of components found.

One step (`step`): examine the next arc `v → w` of the top `v` of the search stack: an
unvisited `w` is visited (pushed on `stk`, `S`, and as a new group on `B`); if `w` is in a
lower group of `S`, the two top groups are merged (one boundary is popped; the arc is examined
again in the next step); otherwise the arc is done. When all arcs of `v` are done, `v` is
popped from `stk`; if it is the root of the top group, that group is popped from `S` and
becomes a component (all its vertices get the label `N + 1 + nc`). With an empty search stack,
the next root candidate is visited if new.

`Inv` is the invariant (`inv_step`); the groups are strongly connected (`grp_sc`), and so are
the components (`asg_sc`); every arc out of a component ends in the same or an earlier
component (`asg_mono`). The measure `mu` decreases by more than the number of vertices a step
pops from `S` (`mu_step`), and at most `mu (init) = 5 N + ∑ |nb v|` steps lead to the halted
state `final N nb` (`halted_run`). **Main theorem** (`final_spec`): in the final state every
vertex `v < N` has a label `> N`; for every arc `v → w`, `lab w ≤ lab v` (a topological order
of the components, sinks first); and vertices with the same label are mutually reachable.
-/

@[expose] public section

namespace STACS2027.Runtimes.TwoSat.Scc

/-- Reachability along the arcs `u → w`, `w ∈ nb u`. -/
def Reach (nb : ℕ → List ℕ) : ℕ → ℕ → Prop := Relation.ReflTransGen fun u w => w ∈ nb u

theorem Reach.refl' (nb : ℕ → List ℕ) (u : ℕ) : Reach nb u u := Relation.ReflTransGen.refl

theorem Reach.trans' {nb : ℕ → List ℕ} {u v w : ℕ} (h₁ : Reach nb u v) (h₂ : Reach nb v w) :
    Reach nb u w := Relation.ReflTransGen.trans h₁ h₂

theorem Reach.arc {nb : ℕ → List ℕ} {u v w : ℕ} (h₁ : Reach nb u v) (h₂ : w ∈ nb v) :
    Reach nb u w := Relation.ReflTransGen.tail h₁ h₂

/-- The out-neighbours of the vertices below `N` are below `N`. -/
def Closed (N : ℕ) (nb : ℕ → List ℕ) : Prop := ∀ u, u < N → ∀ w ∈ nb u, w < N

/-- The state of the search. -/
structure State where
  lab : ℕ → ℕ
  ptr : ℕ → ℕ
  stk : List ℕ
  S : List ℕ
  B : List ℕ
  nxt : ℕ
  nc : ℕ

/-- `a` and `b` (labels of vertices of `S`) are in the same group: no boundary separates them. -/
def SameGrp (B : List ℕ) (a b : ℕ) : Prop := ∀ t ∈ B, (t ≤ a ↔ t ≤ b)

/-- The labels `lab` with the vertices of `L` relabelled `v`. -/
def relab (lab : ℕ → ℕ) (L : List ℕ) (v : ℕ) : ℕ → ℕ := fun x => if x ∈ L then v else lab x

/-- Advancing the arc pointer of `v`. -/
def bump (s : State) (v : ℕ) : State := { s with ptr := Function.update s.ptr v (s.ptr v + 1) }

/-- Visiting `w`: pushed on `S` (label `|S| + 1`), as a new group on `B`, and on `stk`. -/
def push (s : State) (w : ℕ) : State :=
  { s with
    lab := Function.update s.lab w (s.S.length + 1)
    S := s.S ++ [w]
    B := (s.S.length + 1) :: s.B
    stk := w :: s.stk }

/-- Popping the top group (whose root `v`, the top of `stk`, is finished) as a component. -/
def popc (N : ℕ) (s : State) (v : ℕ) (rest : List ℕ) : State :=
  { s with
    lab := relab s.lab (s.S.drop (s.lab v - 1)) (N + 1 + s.nc)
    S := s.S.take (s.lab v - 1)
    B := s.B.tail
    stk := rest
    nc := s.nc + 1 }

/-- One step of the search. -/
def step (N : ℕ) (nb : ℕ → List ℕ) (s : State) : State :=
  match s.stk with
  | v :: rest =>
    if s.ptr v < (nb v).length then
      if s.lab ((nb v).getD (s.ptr v) 0) = 0 then push (bump s v) ((nb v).getD (s.ptr v) 0)
      else if s.lab ((nb v).getD (s.ptr v) 0) < s.B.headD 0 then { s with B := s.B.tail }
      else bump s v
    else if s.lab v = s.B.headD 0 then popc N s v rest
    else { s with stk := rest }
  | [] =>
    if s.nxt < N then
      if s.lab s.nxt = 0 then { push s s.nxt with nxt := s.nxt + 1 }
      else { s with nxt := s.nxt + 1 }
    else s

/-- The initial state. -/
def init : State := ⟨fun _ => 0, fun _ => 0, [], [], [], 0, 0⟩

/-- The search has halted. -/
def Halted (N : ℕ) (s : State) : Prop := s.stk = [] ∧ N ≤ s.nxt

/-- `k` steps of the search. -/
def run (N : ℕ) (nb : ℕ → List ℕ) : ℕ → State → State
  | 0, s => s
  | k + 1, s => run N nb k (step N nb s)

/-- The invariant. -/
structure Inv (N : ℕ) (nb : ℕ → List ℕ) (s : State) : Prop where
  S_lab : ∀ i (h : i < s.S.length), s.lab s.S[i] = i + 1
  onS : ∀ x, s.lab x ≠ 0 → s.lab x ≤ N → x ∈ s.S
  S_len : s.S.length ≤ N
  vis_lt : ∀ x, s.lab x ≠ 0 → x < N
  asg_lt : ∀ x, N < s.lab x → s.lab x ≤ N + s.nc
  B_pw : s.B.Pairwise (· > ·)
  B_le : ∀ b ∈ s.B, 1 ≤ b ∧ b ≤ s.S.length
  B_bot : s.S ≠ [] → 1 ∈ s.B
  B_root : ∀ b ∈ s.B, ∃ r ∈ s.stk, s.lab r = b
  stk_S : ∀ v ∈ s.stk, v ∈ s.S
  stk_pw : s.stk.Pairwise fun v u => Reach nb u v ∧ s.lab u < s.lab v
  ptr_le : ∀ v, s.ptr v ≤ (nb v).length
  fin : ∀ x ∈ s.S, x ∉ s.stk → (nb x).length ≤ s.ptr x
  ptr_zero : ∀ x, s.lab x = 0 → s.ptr x = 0
  grp_sc : ∀ x ∈ s.S, ∀ y ∈ s.S, SameGrp s.B (s.lab x) (s.lab y) → Reach nb x y
  asg_sc : ∀ x y, N < s.lab x → s.lab x = s.lab y → Reach nb x y
  asg_mono : ∀ x, N < s.lab x → ∀ w ∈ nb x, N < s.lab w ∧ s.lab w ≤ s.lab x
  S_mono : ∀ x ∈ s.S, ∀ i < s.ptr x, N < s.lab ((nb x).getD i 0) ∨
    ((nb x).getD i 0 ∈ s.S ∧ ∀ b ∈ s.B, b ≤ s.lab x → b ≤ s.lab ((nb x).getD i 0))
  nxt_le : s.nxt ≤ N
  below_nxt : ∀ x, x < s.nxt → s.lab x ≠ 0

/-! ### Lists -/

theorem getD_mem {l : List ℕ} {i : ℕ} (h : i < l.length) : l.getD i 0 ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
  exact List.getElem_mem h

theorem getD_mem_or {l : List ℕ} (i : ℕ) : l.getD i 0 ∈ l ∨ l.getD i 0 = 0 := by
  by_cases h : i < l.length
  · exact Or.inl (getD_mem h)
  · right; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl

section labS

variable {S : List ℕ} {lab : ℕ → ℕ} (h : ∀ i (hi : i < S.length), lab S[i] = i + 1)
include h

theorem lab_mem {x : ℕ} (hx : x ∈ S) : 1 ≤ lab x ∧ lab x ≤ S.length := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
  rw [h i hi]; omega

theorem nodup_of_lab : S.Nodup := by
  rw [List.nodup_iff_injective_get]
  intro i j hij
  have h1 := h i i.2
  have h2 := h j j.2
  simp only [List.get_eq_getElem] at hij
  rw [hij] at h1
  exact Fin.ext (by omega)

theorem eq_of_lab_eq {x y : ℕ} (hx : x ∈ S) (hy : y ∈ S) (hxy : lab x = lab y) : x = y := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hy
  rw [h i hi, h j hj] at hxy
  have : i = j := by omega
  subst this; rfl

theorem mem_drop_iff {k x : ℕ} : x ∈ S.drop k ↔ x ∈ S ∧ k < lab x := by
  constructor
  · intro hx
    obtain ⟨j, hj, rfl⟩ := List.mem_drop_iff_getElem.mp hx
    exact ⟨List.getElem_mem _, by rw [h _ (by omega)]; omega⟩
  · rintro ⟨hx, hk⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
    rw [h i hi] at hk
    refine List.mem_drop_iff_getElem.mpr ⟨i - k, by omega, ?_⟩
    simp only [show k + (i - k) = i by omega]

theorem mem_take_iff {k x : ℕ} : x ∈ S.take k ↔ x ∈ S ∧ lab x ≤ k := by
  constructor
  · intro hx
    obtain ⟨j, hj, rfl⟩ := List.mem_take_iff_getElem.mp hx
    exact ⟨List.getElem_mem _, by rw [h _ (by omega)]; omega⟩
  · rintro ⟨hx, hk⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
    rw [h i hi] at hk
    exact List.mem_take_iff_getElem.mpr ⟨i, by omega, rfl⟩

end labS

/-- A strictly decreasing list of values in `[1, K]` has at most `K` entries. -/
theorem length_le_of_pw {l : List ℕ} {K : ℕ} (hpw : l.Pairwise (· > ·))
    (hle : ∀ b ∈ l, 1 ≤ b ∧ b ≤ K) : l.length ≤ K := by
  have hnd : l.Nodup := hpw.imp fun h => Nat.ne_of_gt h
  have hsub : l ⊆ List.range' 1 K := fun b hb => by
    have := hle b hb
    exact List.mem_range'_1.mpr ⟨this.1, by omega⟩
  simpa using (hnd.subperm hsub).length_le

theorem nodup_range_length {l : List ℕ} {N : ℕ} (hnd : l.Nodup) (hl : ∀ x ∈ l, x < N) :
    l.length ≤ N := by
  have hsub : l ⊆ List.range N := fun x hx => List.mem_range.mpr (hl x hx)
  simpa using (hnd.subperm hsub).length_le

theorem pw_mem_cases {R : ℕ → ℕ → Prop} {l : List ℕ} (h : l.Pairwise R) {a b : ℕ} (ha : a ∈ l)
    (hb : b ∈ l) : a = b ∨ R a b ∨ R b a := by
  induction l with
  | nil => simp at ha
  | cons x l ih =>
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.mp ha with ha | ha <;> rcases List.mem_cons.mp hb with hb | hb
    · left; rw [ha, hb]
    · right; left; rw [ha]; exact h.1 _ hb
    · right; right; rw [hb]; exact h.1 _ ha
    · exact ih h.2 ha hb

/-! ### Consequences of the invariant -/

section consequences

variable {N : ℕ} {nb : ℕ → List ℕ} {s : State} (hI : Inv N nb s)
include hI

theorem Inv.lab_S {x : ℕ} (hx : x ∈ s.S) : 1 ≤ s.lab x ∧ s.lab x ≤ s.S.length :=
  lab_mem hI.S_lab hx

theorem Inv.nodup : s.S.Nodup := nodup_of_lab hI.S_lab

theorem Inv.S_lt {x : ℕ} (hx : x ∈ s.S) : x < N :=
  hI.vis_lt x (by have := hI.lab_S hx; omega)

theorem Inv.lab_le_N {x : ℕ} (hx : x ∈ s.S) : s.lab x ≤ N := by
  have := hI.lab_S hx; have := hI.S_len; omega

theorem Inv.mem_S_iff {x : ℕ} : x ∈ s.S ↔ s.lab x ≠ 0 ∧ s.lab x ≤ N :=
  ⟨fun hx => ⟨by have := hI.lab_S hx; omega, hI.lab_le_N hx⟩, fun ⟨h1, h2⟩ => hI.onS x h1 h2⟩

theorem Inv.stk_S_lab {v : ℕ} (hv : v ∈ s.stk) : 1 ≤ s.lab v ∧ s.lab v ≤ s.S.length :=
  hI.lab_S (hI.stk_S v hv)

/-- The top of the stack has the largest label of the stack. -/
theorem Inv.top_max {v : ℕ} {rest : List ℕ} (hst : s.stk = v :: rest) {u : ℕ} (hu : u ∈ rest) :
    s.lab u < s.lab v := by
  have h := hI.stk_pw
  rw [hst, List.pairwise_cons] at h
  exact (h.1 u hu).2

theorem Inv.not_mem_rest {v : ℕ} {rest : List ℕ} (hst : s.stk = v :: rest) : v ∉ rest :=
  fun h => absurd (hI.top_max hst h) (lt_irrefl _)

/-- Two vertices of the stack: the one with the smaller label reaches the other. -/
theorem Inv.stk_reach {u v : ℕ} (hu : u ∈ s.stk) (hv : v ∈ s.stk) (hle : s.lab u ≤ s.lab v) :
    Reach nb u v := by
  rcases pw_mem_cases hI.stk_pw hu hv with rfl | h | h
  · exact Reach.refl' _ _
  · omega
  · exact h.1

/-- A nonempty `S` has a nonempty `B` whose head is its largest entry. -/
theorem Inv.head_ge {b : ℕ} (hb : b ∈ s.B) : b ≤ s.B.headD 0 := by
  have hpw := hI.B_pw
  cases hB : s.B with
  | nil => rw [hB] at hb; simp at hb
  | cons h t =>
    rw [hB] at hb hpw
    simp only [List.headD_cons]
    rcases List.mem_cons.mp hb with rfl | hb
    · exact le_rfl
    · exact le_of_lt ((List.pairwise_cons.mp hpw).1 b hb)

end consequences

/-! ### Groups -/

theorem sameGrp_cons {t : ℕ} {B : List ℕ} {a b : ℕ} :
    SameGrp (t :: B) a b ↔ (t ≤ a ↔ t ≤ b) ∧ SameGrp B a b := List.forall_mem_cons

theorem sameGrp_refl (B : List ℕ) (a : ℕ) : SameGrp B a a := fun _ _ => Iff.rfl

theorem SameGrp.symm {B : List ℕ} {a b : ℕ} (h : SameGrp B a b) : SameGrp B b a :=
  fun t ht => (h t ht).symm

theorem SameGrp.of_cons {t : ℕ} {B : List ℕ} {a b : ℕ} (h : SameGrp (t :: B) a b) :
    SameGrp B a b := (sameGrp_cons.mp h).2

/-- The largest entry of `l` at most `a`. -/
theorem exists_max_le (l : List ℕ) (a : ℕ) (h : ∃ b ∈ l, b ≤ a) :
    ∃ b ∈ l, b ≤ a ∧ ∀ b' ∈ l, b' ≤ a → b' ≤ b := by
  induction l with
  | nil => obtain ⟨b, hb, _⟩ := h; simp at hb
  | cons x t ih =>
    by_cases ht : ∃ b ∈ t, b ≤ a
    · obtain ⟨b, hb, hba, hmax⟩ := ih ht
      by_cases hx : x ≤ a
      · refine ⟨max x b, ?_, max_le hx hba, fun b' hb' hb'a => ?_⟩
        · rcases le_total x b with hxb | hxb
          · rw [max_eq_right hxb]; exact List.mem_cons_of_mem _ hb
          · rw [max_eq_left hxb]; exact List.mem_cons_self
        · rcases List.mem_cons.mp hb' with rfl | hb'
          · exact le_max_left _ _
          · exact le_trans (hmax b' hb' hb'a) (le_max_right _ _)
      · refine ⟨b, List.mem_cons_of_mem _ hb, hba, fun b' hb' hb'a => ?_⟩
        rcases List.mem_cons.mp hb' with rfl | hb'
        · exact absurd hb'a hx
        · exact hmax b' hb' hb'a
    · obtain ⟨b, hb, hba⟩ := h
      rcases List.mem_cons.mp hb with rfl | hb
      · refine ⟨b, List.mem_cons_self, hba, fun b' hb' hb'a => ?_⟩
        rcases List.mem_cons.mp hb' with rfl | hb'
        · exact le_rfl
        · exact absurd ⟨b', hb', hb'a⟩ ht
      · exact absurd ⟨b, hb, hba⟩ ht

theorem pw_le_head {l : List ℕ} (hpw : l.Pairwise (· > ·)) {b : ℕ} (hb : b ∈ l) : b ≤ l.headD 0 := by
  cases l with
  | nil => simp at hb
  | cons h t =>
    simp only [List.headD_cons]
    rcases List.mem_cons.mp hb with rfl | hb
    · exact le_rfl
    · exact le_of_lt ((List.pairwise_cons.mp hpw).1 b hb)

theorem headD_mem {l : List ℕ} (hl : l ≠ []) : l.headD 0 ∈ l := by
  cases l with
  | nil => exact absurd rfl hl
  | cons h t => exact List.mem_cons_self

section groups

variable {N : ℕ} {nb : ℕ → List ℕ} {s : State} (hI : Inv N nb s)
include hI

/-- The root of the group of a vertex of `S`: a vertex of the search stack in the same group,
with the largest boundary at most the label. -/
theorem Inv.root {x : ℕ} (hx : x ∈ s.S) :
    ∃ r ∈ s.stk, r ∈ s.S ∧ s.lab r ≤ s.lab x ∧ s.lab r ∈ s.B ∧ SameGrp s.B (s.lab x) (s.lab r) := by
  have h1 : 1 ∈ s.B := hI.B_bot (List.ne_nil_of_mem hx)
  obtain ⟨b, hb, hbx, hmax⟩ := exists_max_le s.B (s.lab x) ⟨1, h1, (hI.lab_S hx).1⟩
  obtain ⟨r, hr, rfl⟩ := hI.B_root b hb
  exact ⟨r, hr, hI.stk_S r hr, hbx, hb, fun t ht =>
    ⟨fun h => hmax t ht h, fun h => le_trans h hbx⟩⟩

/-- The head of `B` is at most the label of the top of the stack. -/
theorem Inv.head_le_top {v : ℕ} {rest : List ℕ} (hst : s.stk = v :: rest) :
    s.B.headD 0 ≤ s.lab v := by
  by_cases hB : s.B = []
  · rw [hB]; simp
  · obtain ⟨r, hr, hrl⟩ := hI.B_root _ (headD_mem hB)
    rw [← hrl]
    rw [hst] at hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact le_rfl
    · exact le_of_lt (hI.top_max hst hr)

theorem Inv.S_ne_of_stk {v : ℕ} (hv : v ∈ s.stk) : s.S ≠ [] :=
  List.ne_nil_of_mem (hI.stk_S v hv)

theorem Inv.B_ne_of_stk {v : ℕ} (hv : v ∈ s.stk) : s.B ≠ [] :=
  List.ne_nil_of_mem (hI.B_bot (hI.S_ne_of_stk hv))

theorem Inv.S_nil_of_stk (hst : s.stk = []) : s.S = [] := by
  by_contra h
  obtain ⟨r, hr, _⟩ := hI.B_root 1 (hI.B_bot h)
  rw [hst] at hr; simp at hr

theorem Inv.B_nil_of_S (hS : s.S = []) : s.B = [] := by
  cases hB : s.B with
  | nil => rfl
  | cons b t =>
    have := hI.B_le b (by rw [hB]; exact List.mem_cons_self)
    rw [hS] at this; simp at this; omega

end groups

/-! ### The invariant is preserved -/

section pres

variable {N : ℕ} {nb : ℕ → List ℕ}

theorem inv_init : Inv N nb init := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [init]

/-- Visiting an unvisited vertex `w` reachable from every vertex of the search stack. -/
theorem inv_push {s : State} (hI : Inv N nb s) {w : ℕ} (hw0 : s.lab w = 0) (hwN : w < N)
    (hreach : ∀ u ∈ s.stk, Reach nb u w) : Inv N nb (push s w) := by
  have hwS : w ∉ s.S := fun h => by have := hI.lab_S h; omega
  have hlen : s.S.length < N := by
    have hnd : (w :: s.S).Nodup := List.nodup_cons.mpr ⟨hwS, hI.nodup⟩
    have := nodup_range_length hnd (fun x hx => by
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hwN
      · exact hI.S_lt hx)
    simp only [List.length_cons] at this; omega
  have hne : ∀ x ∈ s.S, x ≠ w := fun x hx h => hwS (h ▸ hx)
  have hl : ∀ x, x ≠ w → Function.update s.lab w (s.S.length + 1) x = s.lab x :=
    fun x hx => Function.update_of_ne hx _ _
  have hlw : Function.update s.lab w (s.S.length + 1) w = s.S.length + 1 := by simp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [push]
  · intro i hi
    simp only [List.length_append, List.length_singleton] at hi
    by_cases hi' : i < s.S.length
    · rw [List.getElem_append_left hi', hl _ (hne _ (List.getElem_mem _))]
      exact hI.S_lab i hi'
    · obtain rfl : i = s.S.length := by omega
      rw [List.getElem_append_right le_rfl]
      simp
  · intro x h1 h2
    by_cases hx : x = w
    · subst hx; simp
    · rw [hl x hx] at h1 h2
      exact List.mem_append_left _ (hI.onS x h1 h2)
  · simp only [List.length_append, List.length_singleton]; omega
  · intro x h1
    by_cases hx : x = w
    · subst hx; exact hwN
    · rw [hl x hx] at h1; exact hI.vis_lt x h1
  · intro x h1
    by_cases hx : x = w
    · subst hx; rw [hlw] at h1; omega
    · rw [hl x hx] at h1 ⊢; exact hI.asg_lt x h1
  · refine List.Pairwise.cons (fun b hb => ?_) hI.B_pw
    have := (hI.B_le b hb).2; omega
  · intro b hb
    simp only [List.length_append, List.length_singleton]
    rcases List.mem_cons.mp hb with rfl | hb
    · omega
    · have := hI.B_le b hb; omega
  · intro _
    by_cases hS : s.S = []
    · simp [hS]
    · exact List.mem_cons_of_mem _ (hI.B_bot hS)
  · intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨w, List.mem_cons_self, hlw⟩
    · obtain ⟨r, hr, hrb⟩ := hI.B_root b hb
      exact ⟨r, List.mem_cons_of_mem _ hr, by rw [hl r (hne r (hI.stk_S r hr))]; exact hrb⟩
  · intro u hu
    rcases List.mem_cons.mp hu with rfl | hu
    · exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
    · exact List.mem_append_left _ (hI.stk_S u hu)
  · refine List.Pairwise.cons (fun u hu => ⟨hreach u hu, ?_⟩) ?_
    · rw [hl u (hne u (hI.stk_S u hu)), hlw]
      have := hI.stk_S_lab hu; omega
    · refine hI.stk_pw.imp_of_mem fun ha hb h => ?_
      rw [hl _ (hne _ (hI.stk_S _ ha)), hl _ (hne _ (hI.stk_S _ hb))]
      exact h
  · exact hI.ptr_le
  · intro x hx hxs
    rcases List.mem_append.mp hx with hx | hx
    · exact hI.fin x hx (fun h => hxs (List.mem_cons_of_mem _ h))
    · rw [List.mem_singleton] at hx; subst hx; exact absurd List.mem_cons_self hxs
  · intro x hx
    by_cases hxw : x = w
    · subst hxw; rw [hlw] at hx; omega
    · rw [hl x hxw] at hx; exact hI.ptr_zero x hx
  · intro x hx y hy hxy
    rcases List.mem_append.mp hx with hx' | hx' <;> rcases List.mem_append.mp hy with hy' | hy'
    · rw [hl x (hne x hx'), hl y (hne y hy')] at hxy
      exact hI.grp_sc x hx' y hy' hxy.of_cons
    · rw [List.mem_singleton] at hy'
      rw [hy', hl x (hne x hx'), hlw] at hxy
      have := (sameGrp_cons.mp hxy).1
      have := hI.lab_S hx'; omega
    · rw [List.mem_singleton] at hx'
      rw [hx', hl y (hne y hy'), hlw] at hxy
      have := (sameGrp_cons.mp hxy).1
      have := hI.lab_S hy'; omega
    · rw [List.mem_singleton] at hx' hy'; rw [hx', hy']; exact Reach.refl' _ _
  · intro x y hx hxy
    have hxw : x ≠ w := fun h => by subst h; rw [hlw] at hx; omega
    have hyw : y ≠ w := fun h => by subst h; rw [hlw, hl x hxw] at hxy; rw [hl x hxw] at hx; omega
    rw [hl x hxw] at hx hxy; rw [hl y hyw] at hxy
    exact hI.asg_sc x y hx hxy
  · intro x hx w' hw'
    have hxw : x ≠ w := fun h => by subst h; rw [hlw] at hx; omega
    rw [hl x hxw] at hx ⊢
    obtain ⟨h1, h2⟩ := hI.asg_mono x hx w' hw'
    have hw'w : w' ≠ w := fun h => by subst h; omega
    rw [hl w' hw'w]; exact ⟨h1, h2⟩
  · intro x hx i hi
    rcases List.mem_append.mp hx with hx | hx
    · rw [hl x (hne x hx)]
      rcases hI.S_mono x hx i hi with h | ⟨h1, h2⟩
      · left
        have : (nb x).getD i 0 ≠ w := fun h' => by rw [h'] at h; omega
        rw [hl _ this]; exact h
      · right
        rw [hl _ (hne _ h1)]
        refine ⟨List.mem_append_left _ h1, fun b hb hbx => ?_⟩
        rcases List.mem_cons.mp hb with rfl | hb
        · have := hI.lab_S hx; omega
        · exact h2 b hb hbx
    · rw [List.mem_singleton] at hx; subst hx
      rw [hI.ptr_zero _ hw0] at hi; omega
  · exact hI.nxt_le
  · intro x hx
    by_cases hxw : x = w
    · subst hxw; rw [hlw]; omega
    · rw [hl x hxw]; exact hI.below_nxt x hx

/-- Advancing the pointer of a vertex `v` of the stack past an arc whose end is assigned or in
the same or a higher group. -/
theorem inv_bump {s : State} (hI : Inv N nb s) {v : ℕ} (hv : v ∈ s.stk)
    (hlt : s.ptr v < (nb v).length)
    (hw : N < s.lab ((nb v).getD (s.ptr v) 0) ∨ ((nb v).getD (s.ptr v) 0 ∈ s.S ∧
      ∀ b ∈ s.B, b ≤ s.lab v → b ≤ s.lab ((nb v).getD (s.ptr v) 0))) :
    Inv N nb (bump s v) := by
  have hvS := hI.stk_S v hv
  have hp : ∀ x, x ≠ v → Function.update s.ptr v (s.ptr v + 1) x = s.ptr x :=
    fun x hx => Function.update_of_ne hx _ _
  refine ⟨hI.S_lab, hI.onS, hI.S_len, hI.vis_lt, hI.asg_lt, hI.B_pw, hI.B_le, hI.B_bot, hI.B_root,
    hI.stk_S, hI.stk_pw, ?_, ?_, ?_, hI.grp_sc, hI.asg_sc, hI.asg_mono, ?_, hI.nxt_le,
    hI.below_nxt⟩ <;> simp only [bump]
  · intro x
    by_cases hx : x = v
    · subst hx; simp; omega
    · rw [hp x hx]; exact hI.ptr_le x
  · intro x hx hxs
    have hxv : x ≠ v := fun h => hxs (h ▸ hv)
    rw [hp x hxv]; exact hI.fin x hx hxs
  · intro x hx
    have hxv : x ≠ v := fun h => by subst h; have := hI.lab_S hvS; omega
    rw [hp x hxv]; exact hI.ptr_zero x hx
  · intro x hx i hi
    by_cases hxv : x = v
    · subst hxv
      simp only [Function.update_self] at hi
      by_cases hi' : i < s.ptr x
      · exact hI.S_mono x hx i hi'
      · obtain rfl : i = s.ptr x := by omega
        exact hw
    · rw [hp x hxv] at hi; exact hI.S_mono x hx i hi

/-- Merging the two top groups, when the next arc of the top `v` ends in a lower group. -/
theorem inv_merge {s : State} (hI : Inv N nb s) {v : ℕ} {rest : List ℕ} (hst : s.stk = v :: rest)
    (hlt : s.ptr v < (nb v).length) (hw0 : s.lab ((nb v).getD (s.ptr v) 0) ≠ 0)
    (hwl : s.lab ((nb v).getD (s.ptr v) 0) < s.B.headD 0) :
    Inv N nb { s with B := s.B.tail } := by
  set w := (nb v).getD (s.ptr v) 0 with hw_def
  have hv : v ∈ s.stk := by rw [hst]; exact List.mem_cons_self
  have hvS := hI.stk_S v hv
  have hBne := hI.B_ne_of_stk hv
  obtain ⟨h, t, hB⟩ : ∃ h t, s.B = h :: t := by
    cases hB : s.B with
    | nil => exact absurd hB hBne
    | cons h t => exact ⟨h, t, rfl⟩
  rw [hB, List.headD_cons] at hwl
  have hpw := hI.B_pw
  rw [hB, List.pairwise_cons] at hpw
  have hhS : h ≤ s.S.length := (hI.B_le h (by rw [hB]; exact List.mem_cons_self)).2
  have hwS : w ∈ s.S := hI.onS w hw0 (by have := hI.S_len; omega)
  have h1t : 1 ∈ t := by
    have h1 := hI.B_bot (List.ne_nil_of_mem hvS)
    rw [hB] at h1
    rcases List.mem_cons.mp h1 with h1 | h1
    · omega
    · exact h1
  have htne : t ≠ [] := List.ne_nil_of_mem h1t
  have hhv : h ≤ s.lab v := by have := hI.head_le_top hst; rwa [hB] at this
  simp only [hB, List.tail_cons]
  -- the root `r1` of the top group and `r2` of the second group
  obtain ⟨r1, hr1, hr1l⟩ := hI.B_root h (by rw [hB]; exact List.mem_cons_self)
  obtain ⟨r2, hr2, hr2l⟩ := hI.B_root (t.headD 0) (by rw [hB]; exact List.mem_cons_of_mem _ (headD_mem htne))
  have ht2 : ∀ b ∈ t, b ≤ t.headD 0 := fun b hb => pw_le_head hpw.2 hb
  have ht2h : t.headD 0 < h := hpw.1 _ (headD_mem htne)
  have hr1S := hI.stk_S r1 hr1
  have hr2S := hI.stk_S r2 hr2
  -- every vertex of the top group reaches every vertex of the second group and back
  have cross : ∀ x ∈ s.S, ∀ y ∈ s.S, h ≤ s.lab x → s.lab y < h → SameGrp t (s.lab x) (s.lab y) →
      Reach nb x y ∧ Reach nb y x := by
    intro x hx y hy hxh hyh hxy
    have hty : ∀ b ∈ t, b ≤ s.lab y := fun b hb =>
      (hxy b hb).mp (le_trans (le_of_lt (hpw.1 b hb)) hxh)
    have hgy : SameGrp s.B (s.lab r2) (s.lab y) := by
      rw [hB, hr2l]
      refine sameGrp_cons.mpr ⟨⟨fun h' => by omega, fun h' => by omega⟩, fun b hb =>
        ⟨fun _ => hty b hb, fun _ => ht2 b hb⟩⟩
    have hgx : SameGrp s.B (s.lab r1) (s.lab x) := by
      rw [hB, hr1l]
      refine sameGrp_cons.mpr ⟨⟨fun _ => hxh, fun _ => le_rfl⟩, fun b hb =>
        ⟨fun _ => by have := hpw.1 b hb; omega, fun _ => by have := hpw.1 b hb; omega⟩⟩
    have hgv : SameGrp s.B (s.lab x) (s.lab v) := by
      rw [hB]
      refine sameGrp_cons.mpr ⟨⟨fun _ => hhv, fun _ => hxh⟩, fun b hb =>
        ⟨fun _ => by have := hpw.1 b hb; omega, fun _ => by have := hpw.1 b hb; omega⟩⟩
    have hr21 : Reach nb r2 r1 := hI.stk_reach hr2 hr1 (by rw [hr1l, hr2l]; omega)
    -- the root of the group of `w`
    obtain ⟨rw', hrw, hrwS, hrwl, hrwB, hgw⟩ := hI.root hwS
    have hrwt : s.lab rw' ∈ t := by
      rw [hB] at hrwB
      rcases List.mem_cons.mp hrwB with h' | h'
      · omega
      · exact h'
    have hrw2 : Reach nb rw' r2 := hI.stk_reach hrw hr2 (by rw [hr2l]; exact ht2 _ hrwt)
    refine ⟨?_, ?_⟩
    · have hxv : Reach nb x v := hI.grp_sc x hx v hvS hgv
      have hvw : Reach nb x w := hxv.arc (getD_mem hlt)
      have hwr : Reach nb w rw' := hI.grp_sc w hwS rw' hrwS hgw
      exact ((hvw.trans' hwr).trans' hrw2).trans' (hI.grp_sc r2 hr2S y hy hgy)
    · exact ((hI.grp_sc y hy r2 hr2S hgy.symm).trans' hr21).trans' (hI.grp_sc r1 hr1S x hx hgx)
  refine ⟨hI.S_lab, hI.onS, hI.S_len, hI.vis_lt, hI.asg_lt, hpw.2, ?_, ?_, ?_, hI.stk_S,
    hI.stk_pw, hI.ptr_le, hI.fin, hI.ptr_zero, ?_, hI.asg_sc, hI.asg_mono, ?_, hI.nxt_le,
    hI.below_nxt⟩
  · intro b hb; exact hI.B_le b (by rw [hB]; exact List.mem_cons_of_mem _ hb)
  · intro _; exact h1t
  · intro b hb; exact hI.B_root b (by rw [hB]; exact List.mem_cons_of_mem _ hb)
  · intro x hx y hy hxy
    by_cases hsep : (h ≤ s.lab x ↔ h ≤ s.lab y)
    · exact hI.grp_sc x hx y hy (by rw [hB]; exact sameGrp_cons.mpr ⟨hsep, hxy⟩)
    · by_cases hxh : h ≤ s.lab x
      · exact (cross x hx y hy hxh (by by_contra h'; exact hsep ⟨fun _ => by omega, fun _ => hxh⟩)
          hxy).1
      · exact (cross y hy x hx (by by_contra h'; exact hsep ⟨fun h'' => absurd h'' hxh,
          fun _ => by omega⟩) (by omega) hxy.symm).2
  · intro x hx i hi
    rcases hI.S_mono x hx i hi with h' | ⟨h1, h2⟩
    · exact Or.inl h'
    · exact Or.inr ⟨h1, fun b hb hbx => h2 b (by rw [hB]; exact List.mem_cons_of_mem _ hb) hbx⟩

/-- Popping a finished vertex that is not the root of the top group. -/
theorem inv_pop {s : State} (hI : Inv N nb s) {v : ℕ} {rest : List ℕ} (hst : s.stk = v :: rest)
    (hlt : ¬ s.ptr v < (nb v).length) (hroot : s.lab v ≠ s.B.headD 0) :
    Inv N nb { s with stk := rest } := by
  have hv : v ∈ s.stk := by rw [hst]; exact List.mem_cons_self
  have hpw := hI.stk_pw
  rw [hst, List.pairwise_cons] at hpw
  refine ⟨hI.S_lab, hI.onS, hI.S_len, hI.vis_lt, hI.asg_lt, hI.B_pw, hI.B_le, hI.B_bot, ?_,
    fun u hu => hI.stk_S u (by rw [hst]; exact List.mem_cons_of_mem _ hu), hpw.2, hI.ptr_le, ?_,
    hI.ptr_zero, hI.grp_sc, hI.asg_sc, hI.asg_mono, hI.S_mono, hI.nxt_le, hI.below_nxt⟩
  · intro b hb
    obtain ⟨r, hr, hrb⟩ := hI.B_root b hb
    rw [hst] at hr
    rcases List.mem_cons.mp hr with rfl | hr
    · have h1 := hI.head_ge hb
      have h2 := hI.head_le_top hst
      omega
    · exact ⟨r, hr, hrb⟩
  · intro x hx hxs
    by_cases hxv : x = v
    · subst hxv; dsimp only; omega
    · exact hI.fin x hx (by rw [hst]; exact fun h => (List.mem_cons.mp h).elim hxv hxs)

/-- Moving to the next root candidate. -/
theorem inv_nxt {s : State} (hI : Inv N nb s) (hlt : s.nxt < N) (h0 : s.lab s.nxt ≠ 0) :
    Inv N nb { s with nxt := s.nxt + 1 } := by
  refine ⟨hI.S_lab, hI.onS, hI.S_len, hI.vis_lt, hI.asg_lt, hI.B_pw, hI.B_le, hI.B_bot, hI.B_root,
    hI.stk_S, hI.stk_pw, hI.ptr_le, hI.fin, hI.ptr_zero, hI.grp_sc, hI.asg_sc, hI.asg_mono,
    hI.S_mono, hlt, ?_⟩
  intro x hx
  by_cases hxn : x = s.nxt
  · rw [hxn]; exact h0
  · exact hI.below_nxt x (by simp only at hx; omega)

/-- Popping the top group as a component, when its root `v` is finished. -/
theorem inv_popc {s : State} (hI : Inv N nb s) {v : ℕ} {rest : List ℕ} (hst : s.stk = v :: rest)
    (hlt : ¬ s.ptr v < (nb v).length) (hroot : s.lab v = s.B.headD 0) :
    Inv N nb (popc N s v rest) := by
  have hv : v ∈ s.stk := by rw [hst]; exact List.mem_cons_self
  have hvS := hI.stk_S v hv
  have hvl := hI.lab_S hvS
  have hBne := hI.B_ne_of_stk hv
  obtain ⟨h, t, hB⟩ : ∃ h t, s.B = h :: t := by
    cases hB : s.B with
    | nil => exact absurd hB hBne
    | cons h t => exact ⟨h, t, rfl⟩
  rw [hB, List.headD_cons] at hroot
  have hpw := hI.B_pw
  rw [hB, List.pairwise_cons] at hpw
  have hspw := hI.stk_pw
  rw [hst, List.pairwise_cons] at hspw
  set X := s.S.drop (s.lab v - 1) with hX_def
  set val := N + 1 + s.nc with hval
  have hX : ∀ x, x ∈ X ↔ x ∈ s.S ∧ s.lab v ≤ s.lab x := fun x => by
    rw [hX_def, mem_drop_iff hI.S_lab]; constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩
  have hS' : ∀ x, x ∈ s.S.take (s.lab v - 1) ↔ x ∈ s.S ∧ s.lab x < s.lab v := fun x => by
    rw [mem_take_iff hI.S_lab]; constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩
  have hlenS' : (s.S.take (s.lab v - 1)).length = s.lab v - 1 := by
    rw [List.length_take]; omega
  have hlX : ∀ x, x ∈ X → relab s.lab X val x = val := fun x hx => by simp [relab, hx]
  have hl : ∀ x, x ∉ X → relab s.lab X val x = s.lab x := fun x hx => by simp [relab, hx]
  have hXN : ∀ x ∈ X, s.lab x ≤ N := fun x hx => hI.lab_le_N ((hX x).mp hx).1
  have hnX : ∀ x, s.lab x < s.lab v → x ∉ X := fun x hx h' => by have := ((hX x).mp h').2; omega
  have hrest : ∀ u ∈ rest, s.lab u < s.lab v := fun u hu => hI.top_max hst hu
  have htlt : ∀ b ∈ t, b < h := fun b hb => hpw.1 b hb
  have hgX : ∀ x ∈ X, ∀ y ∈ X, SameGrp s.B (s.lab x) (s.lab y) := by
    intro x hx y hy
    have := ((hX x).mp hx).2; have := ((hX y).mp hy).2
    rw [hB]
    refine sameGrp_cons.mpr ⟨⟨fun _ => by omega, fun _ => by omega⟩, fun b hb =>
      ⟨fun _ => by have := htlt b hb; omega, fun _ => by have := htlt b hb; omega⟩⟩
  show Inv N nb ⟨relab s.lab X val, s.ptr, rest, s.S.take (s.lab v - 1), s.B.tail, s.nxt, s.nc + 1⟩
  rw [hB, List.tail_cons]
  refine ⟨?_, ?_, ?_, ?_, ?_, hpw.2, ?_, ?_, ?_, ?_, ?_, hI.ptr_le, ?_, ?_, ?_, ?_, ?_, ?_,
    hI.nxt_le, ?_⟩ <;> (try dsimp only)
  · intro i hi
    rw [List.getElem_take]
    have hi' : i < s.S.length := by rw [hlenS'] at hi; omega
    have := hI.S_lab i hi'
    rw [hl (s.S[i]) (hnX _ (by rw [this]; rw [hlenS'] at hi; omega))]
    exact this
  · intro x h1 h2
    by_cases hx : x ∈ X
    · rw [hlX x hx] at h2; omega
    · rw [hl x hx] at h1 h2
      have hxS := hI.onS x h1 h2
      exact (hS' x).mpr ⟨hxS, by by_contra h'; exact hx ((hX x).mpr ⟨hxS, by omega⟩)⟩
  · rw [hlenS']; have := hI.S_len; omega
  · intro x h1
    by_cases hx : x ∈ X
    · exact hI.S_lt ((hX x).mp hx).1
    · rw [hl x hx] at h1; exact hI.vis_lt x h1
  · intro x h1
    by_cases hx : x ∈ X
    · rw [hlX x hx]; omega
    · rw [hl x hx] at h1 ⊢; have := hI.asg_lt x h1; omega
  · intro b hb
    have := htlt b hb
    have := hI.B_le b (by rw [hB]; exact List.mem_cons_of_mem _ hb)
    rw [hlenS']; omega
  · intro hne
    have h1 := hI.B_bot (List.ne_nil_of_mem hvS)
    rw [hB] at h1
    rcases List.mem_cons.mp h1 with h1 | h1
    · exfalso; apply hne; rw [List.take_eq_nil_iff]; left; omega
    · exact h1
  · intro b hb
    obtain ⟨r, hr, hrb⟩ := hI.B_root b (by rw [hB]; exact List.mem_cons_of_mem _ hb)
    have hbh := htlt b hb
    rw [hst] at hr
    rcases List.mem_cons.mp hr with rfl | hr
    · omega
    · exact ⟨r, hr, by rw [hl r (hnX r (by omega))]; exact hrb⟩
  · intro u hu
    exact (hS' u).mpr ⟨hI.stk_S u (by rw [hst]; exact List.mem_cons_of_mem _ hu), hrest u hu⟩
  · refine hspw.2.imp_of_mem fun ha hb hab => ?_
    rw [hl _ (hnX _ (hrest _ ha)), hl _ (hnX _ (hrest _ hb))]
    exact hab
  · intro x hx hxs
    have hxS := ((hS' x).mp hx)
    have hxv : x ≠ v := fun h' => by subst h'; omega
    exact hI.fin x hxS.1 (by rw [hst]; exact fun h' => (List.mem_cons.mp h').elim hxv hxs)
  · intro x hx
    by_cases hxX : x ∈ X
    · rw [hlX x hxX] at hx; omega
    · rw [hl x hxX] at hx; exact hI.ptr_zero x hx
  · intro x hx y hy hxy
    have hx' := (hS' x).mp hx
    have hy' := (hS' y).mp hy
    rw [hl x (hnX x hx'.2), hl y (hnX y hy'.2)] at hxy
    refine hI.grp_sc x hx'.1 y hy'.1 ?_
    rw [hB]
    exact sameGrp_cons.mpr ⟨⟨fun _ => by omega, fun _ => by omega⟩, hxy⟩
  · intro x y hx hxy
    by_cases hxX : x ∈ X
    · rw [hlX x hxX] at hxy
      have hyX : y ∈ X := by
        by_contra hyX
        rw [hl y hyX] at hxy
        have := hI.asg_lt y (by omega); omega
      exact hI.grp_sc x ((hX x).mp hxX).1 y ((hX y).mp hyX).1 (hgX x hxX y hyX)
    · rw [hl x hxX] at hx hxy
      have hyX : y ∉ X := by
        intro hyX
        rw [hlX y hyX] at hxy
        have := hI.asg_lt x hx; omega
      rw [hl y hyX] at hxy
      exact hI.asg_sc x y hx hxy
  · intro x hx w hw
    by_cases hxX : x ∈ X
    · rw [hlX x hxX]
      have hxS := ((hX x).mp hxX)
      have hfin : (nb x).length ≤ s.ptr x := by
        by_cases hxv : x = v
        · subst hxv; omega
        · refine hI.fin x hxS.1 (fun h' => ?_)
          rw [hst] at h'
          rcases List.mem_cons.mp h' with h' | h'
          · exact hxv h'
          · have := hrest x h'; omega
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hw
      have hget : (nb x).getD i 0 = (nb x)[i] := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
      rcases hI.S_mono x hxS.1 i (by omega) with h' | ⟨h1, h2⟩
      · rw [hget] at h'
        have hwX : (nb x)[i] ∉ X := fun h'' => by have := hXN _ h''; omega
        rw [hl _ hwX]
        have := hI.asg_lt _ h'
        omega
      · rw [hget] at h1 h2
        have := h2 h (by rw [hB]; exact List.mem_cons_self) (by rw [← hroot]; exact hxS.2)
        have hwX : (nb x)[i] ∈ X := (hX _).mpr ⟨h1, by omega⟩
        rw [hlX _ hwX]
        omega
    · rw [hl x hxX] at hx ⊢
      obtain ⟨h1, h2⟩ := hI.asg_mono x hx w hw
      have hwX : w ∉ X := fun h'' => by have := hXN _ h''; omega
      rw [hl w hwX]
      exact ⟨h1, h2⟩
  · intro x hx i hi
    have hx' := (hS' x).mp hx
    rw [hl x (hnX x hx'.2)]
    rcases hI.S_mono x hx'.1 i hi with h' | ⟨h1, h2⟩
    · left
      have hwX : (nb x).getD i 0 ∉ X := fun h'' => by have := hXN _ h''; omega
      rw [hl _ hwX]; exact h'
    · by_cases hwX : (nb x).getD i 0 ∈ X
      · left; rw [hlX _ hwX]; omega
      · right
        rw [hl _ hwX]
        refine ⟨(hS' _).mpr ⟨h1, ?_⟩, fun b hb hbx =>
          h2 b (by rw [hB]; exact List.mem_cons_of_mem _ hb) hbx⟩
        by_contra h''
        exact hwX ((hX _).mpr ⟨h1, by omega⟩)
  · intro x hx
    by_cases hxX : x ∈ X
    · rw [hlX x hxX]; omega
    · rw [hl x hxX]; exact hI.below_nxt x hx

theorem push_bump (s : State) (v w : ℕ) : push (bump s v) w = bump (push s w) v := rfl

/-- **The invariant is preserved by a step.** -/
theorem inv_step (hcl : Closed N nb) {s : State} (hI : Inv N nb s) : Inv N nb (step N nb s) := by
  unfold step
  split
  · rename_i v rest hst
    have hv : v ∈ s.stk := by rw [hst]; exact List.mem_cons_self
    have hvS := hI.stk_S v hv
    have hvN := hI.S_lt hvS
    split
    · rename_i hlt
      have hwnb := getD_mem hlt
      split
      · rename_i hw0
        rw [push_bump]
        have hP := inv_push hI hw0 (hcl v hvN _ hwnb) (fun u hu => by
          refine (hI.stk_reach hu hv ?_).arc hwnb
          rw [hst] at hu
          rcases List.mem_cons.mp hu with rfl | hu
          · exact le_rfl
          · exact le_of_lt (hI.top_max hst hu))
        refine inv_bump hP (List.mem_cons_of_mem _ hv) hlt (Or.inr ⟨?_, fun b hb _ => ?_⟩) <;>
          simp only [push]
        · exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
        · simp only [Function.update_self]
          rcases List.mem_cons.mp hb with rfl | hb
          · exact le_rfl
          · have := (hI.B_le b hb).2; omega
      · rename_i hw0
        split
        · rename_i hwl
          exact inv_merge hI hst hlt hw0 hwl
        · rename_i hwl
          refine inv_bump hI hv hlt ?_
          by_cases hN : N < s.lab ((nb v).getD (s.ptr v) 0)
          · exact Or.inl hN
          · exact Or.inr ⟨hI.onS _ hw0 (by omega), fun b hb _ => le_trans (hI.head_ge hb)
              (by omega)⟩
    · rename_i hlt
      split
      · rename_i hroot
        exact inv_popc hI hst hlt hroot
      · rename_i hroot
        exact inv_pop hI hst hlt hroot
  · rename_i hst
    split
    · rename_i hlt
      split
      · rename_i h0
        exact inv_nxt (inv_push hI h0 hlt (by rw [hst]; simp)) hlt (by simp [push])
      · rename_i h0
        exact inv_nxt hI hlt h0
    · exact hI

/-! ### Termination -/

/-- The measure: four times the unvisited vertices, the unexamined arcs, the sizes of the
stacks, and the remaining root candidates. -/
def mu (N : ℕ) (nb : ℕ → List ℕ) (s : State) : ℕ :=
  4 * ((List.range N).filter fun v => s.lab v = 0).length +
    ((List.range N).map fun v => (nb v).length - s.ptr v).sum +
    s.stk.length + s.S.length + s.B.length + (N - s.nxt)

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

theorem unvisited_lt {l : List ℕ} {lab : ℕ → ℕ} {w x : ℕ} (hw : lab w = 0) (hx : x ≠ 0)
    (hwl : w ∈ l) :
    (l.filter fun v => Function.update lab w x v = 0).length < (l.filter fun v => lab v = 0).length := by
  rw [length_filter_eq_sum, length_filter_eq_sum]
  apply sum_map_lt_aux (y := w) _ hwl (by simp [hw, hx])
  intro y _
  by_cases hyw : y = w
  · subst hyw; simp [hx]
  · simp [Function.update_of_ne hyw]

theorem ptrsum_lt {l : List ℕ} {ptr : ℕ → ℕ} {v : ℕ} (hv : v ∈ l) (hlt : ptr v < (nb v).length) :
    (l.map fun x => (nb x).length - Function.update ptr v (ptr v + 1) x).sum <
      (l.map fun x => (nb x).length - ptr x).sum := by
  apply sum_map_lt_aux (y := v) _ hv (by simp; omega)
  intro y _
  by_cases hyv : y = v
  · subst hyv; simp; omega
  · simp [Function.update_of_ne hyv]

/-- The number of unvisited vertices below `N`. -/
def unv (N : ℕ) (s : State) : ℕ := ((List.range N).filter fun v => s.lab v = 0).length

/-- The number of unexamined arcs out of the vertices below `N`. -/
def rem (N : ℕ) (nb : ℕ → List ℕ) (s : State) : ℕ :=
  ((List.range N).map fun v => (nb v).length - s.ptr v).sum

theorem mu_eq (s : State) : mu N nb s =
    4 * unv N s + rem N nb s + s.stk.length + s.S.length + s.B.length + (N - s.nxt) := rfl

/-- **The measure decreases** at every step by more than the number of vertices popped from
`S`. -/
theorem mu_step (hcl : Closed N nb) {s : State} (hI : Inv N nb s) (hh : ¬ Halted N s) :
    mu N nb (step N nb s) + (s.S.length - (step N nb s).S.length) + 1 ≤ mu N nb s := by
  unfold step
  split
  · rename_i v rest hst
    have hv : v ∈ s.stk := by rw [hst]; exact List.mem_cons_self
    have hvS := hI.stk_S v hv
    have hvN := hI.S_lt hvS
    have hvr : v ∈ List.range N := List.mem_range.mpr hvN
    have hsl : s.stk.length = rest.length + 1 := by rw [hst]; rfl
    split
    · rename_i hlt
      have hwnb := getD_mem hlt
      have h2 : rem N nb (bump s v) < rem N nb s := ptrsum_lt (nb := nb) hvr hlt
      split
      · rename_i hw0
        have hwr := List.mem_range.mpr (hcl v hvN _ hwnb)
        have h1 : unv N (push (bump s v) ((nb v).getD (s.ptr v) 0)) < unv N s :=
          unvisited_lt (l := List.range N) hw0 (show s.S.length + 1 ≠ 0 by omega) hwr
        have h3 : rem N nb (push (bump s v) ((nb v).getD (s.ptr v) 0)) = rem N nb (bump s v) := rfl
        have h4 : (push (bump s v) ((nb v).getD (s.ptr v) 0)).S.length = s.S.length + 1 := by
          simp [push, bump]
        have h5 : (push (bump s v) ((nb v).getD (s.ptr v) 0)).stk.length = s.stk.length + 1 := rfl
        have h6 : (push (bump s v) ((nb v).getD (s.ptr v) 0)).B.length = s.B.length + 1 := rfl
        have h7 : (push (bump s v) ((nb v).getD (s.ptr v) 0)).nxt = s.nxt := rfl
        rw [mu_eq, mu_eq]
        omega
      · split
        · rename_i hw0 hwl
          have hB := hI.B_ne_of_stk hv
          have : s.B.length ≠ 0 := fun h => hB (List.length_eq_zero_iff.mp h)
          have h1 : unv N { s with B := s.B.tail } = unv N s := rfl
          have h3 : rem N nb { s with B := s.B.tail } = rem N nb s := rfl
          rw [mu_eq, mu_eq, h1, h3]
          simp only [List.length_tail]
          omega
        · have h1 : unv N (bump s v) = unv N s := rfl
          have h5 : (bump s v).stk.length = s.stk.length := rfl
          have h4 : (bump s v).S.length = s.S.length := rfl
          have h6 : (bump s v).B.length = s.B.length := rfl
          have h7 : (bump s v).nxt = s.nxt := rfl
          rw [mu_eq, mu_eq, h1]
          omega
    · rename_i hlt
      split
      · rename_i hroot
        have hvl := hI.lab_S hvS
        have hB := hI.B_ne_of_stk hv
        have : s.B.length ≠ 0 := fun h => hB (List.length_eq_zero_iff.mp h)
        have hU : unv N (popc N s v rest) = unv N s := by
          unfold unv popc
          congr 1
          apply List.filter_congr
          intro x _
          by_cases hx : x ∈ s.S.drop (s.lab v - 1)
          · have hxS := ((mem_drop_iff hI.S_lab).mp hx).1
            have := hI.lab_S hxS
            simp [relab, hx]; omega
          · simp [relab, hx]
        have h3 : rem N nb (popc N s v rest) = rem N nb s := rfl
        rw [mu_eq, mu_eq, hU, h3]
        simp only [popc, List.length_take, List.length_tail]
        omega
      · have h1 : unv N { s with stk := rest } = unv N s := rfl
        have h3 : rem N nb { s with stk := rest } = rem N nb s := rfl
        rw [mu_eq, mu_eq, h1, h3]
        dsimp only
        omega
  · rename_i hst
    split
    · rename_i hlt
      split
      · rename_i h0
        have hS := hI.S_nil_of_stk hst
        have hBn := hI.B_nil_of_S hS
        have h1 : unv N { push s s.nxt with nxt := s.nxt + 1 } < unv N s :=
          unvisited_lt (l := List.range N) h0 (show s.S.length + 1 ≠ 0 by omega)
            (List.mem_range.mpr hlt)
        have h3 : rem N nb { push s s.nxt with nxt := s.nxt + 1 } = rem N nb s := rfl
        have h4 : ({ push s s.nxt with nxt := s.nxt + 1 } : State).S.length = s.S.length + 1 := by
          simp [push]
        have h5 : ({ push s s.nxt with nxt := s.nxt + 1 } : State).stk.length = s.stk.length + 1 :=
          rfl
        have h6 : ({ push s s.nxt with nxt := s.nxt + 1 } : State).B.length = s.B.length + 1 := rfl
        have h7 : ({ push s s.nxt with nxt := s.nxt + 1 } : State).nxt = s.nxt + 1 := rfl
        rw [mu_eq, mu_eq]
        omega
      · have h1 : unv N { s with nxt := s.nxt + 1 } = unv N s := rfl
        have h3 : rem N nb { s with nxt := s.nxt + 1 } = rem N nb s := rfl
        rw [mu_eq, mu_eq, h1, h3]
        dsimp only
        omega
    · exact absurd ⟨hst, by omega⟩ hh

theorem step_halted {s : State} (h : Halted N s) : step N nb s = s := by
  unfold step; rw [h.1]; simp only
  have : ¬ s.nxt < N := by have := h.2; omega
  simp only [this, ↓reduceIte]

theorem run_halted {s : State} (h : Halted N s) : ∀ k, run N nb k s = s := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih => simp only [run, step_halted h, ih]

theorem inv_run (hcl : Closed N nb) : ∀ k {s : State}, Inv N nb s → Inv N nb (run N nb k s)
  | 0, _, h => h
  | k + 1, _, h => inv_run hcl k (inv_step hcl h)

theorem halted_run (hcl : Closed N nb) : ∀ k {s : State}, Inv N nb s → mu N nb s ≤ k →
    Halted N (run N nb k s)
  | 0, s, h, hm => by
    by_contra hh
    have := mu_step hcl h hh
    omega
  | k + 1, s, h, hm => by
    by_cases hh : Halted N s
    · simp only [run, step_halted hh, run_halted hh]; exact hh
    · have := mu_step hcl h hh
      exact halted_run hcl k (inv_step hcl h) (by omega)

theorem run_add : ∀ (a b : ℕ) (s : State), run N nb (a + b) s = run N nb b (run N nb a s)
  | 0, b, s => by simp [run]
  | a + 1, b, s => by
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [run]
    exact run_add a b (step N nb s)

theorem run_succ (k : ℕ) (s : State) : run N nb (k + 1) s = step N nb (run N nb k s) := by
  rw [run_add]; rfl

/-- The final state of the search. -/
def final (N : ℕ) (nb : ℕ → List ℕ) : State := run N nb (mu N nb init) init

theorem final_inv (hcl : Closed N nb) : Inv N nb (final N nb) := inv_run hcl _ inv_init

theorem final_halted (hcl : Closed N nb) : Halted N (final N nb) :=
  halted_run hcl _ inv_init le_rfl

/-- A halted state reached from the initial state is the final state. -/
theorem run_eq_final (hcl : Closed N nb) {k : ℕ} (hh : Halted N (run N nb k init)) :
    run N nb k init = final N nb := by
  have h1 : run N nb (k + mu N nb init) init = run N nb k init := by
    rw [run_add, run_halted hh]
  have h2 : run N nb (mu N nb init + k) init = final N nb := by
    rw [run_add]; exact run_halted (final_halted hcl) k
  rw [← h1, Nat.add_comm, h2]

theorem mu_init : mu N nb init = 5 * N + ((List.range N).map fun v => (nb v).length).sum := by
  simp [mu, init]; omega

/-- The measure depends only on `lab` and `ptr` below `N`, the lengths of the stacks and `nxt`. -/
theorem mu_congr {s s' : State} (hlab : ∀ v < N, s.lab v = s'.lab v)
    (hptr : ∀ v < N, s.ptr v = s'.ptr v) (hstk : s.stk.length = s'.stk.length)
    (hS : s.S.length = s'.S.length) (hB : s.B.length = s'.B.length) (hn : s.nxt = s'.nxt) :
    mu N nb s = mu N nb s' := by
  unfold mu
  rw [List.filter_congr (fun v hv => by rw [hlab v (List.mem_range.mp hv)]),
    List.map_congr_left (fun v hv => by rw [hptr v (List.mem_range.mp hv)]), hstk, hS, hB, hn]

/-- **Correctness of the search**: in the final state every vertex below `N` is assigned to a
component; along every arc the label does not increase (the components are found in a
topological order, sinks first); vertices with the same label reach each other. -/
theorem final_spec (hcl : Closed N nb) :
    (∀ x, x < N → N < (final N nb).lab x) ∧
    (∀ x, x < N → ∀ w ∈ nb x, (final N nb).lab w ≤ (final N nb).lab x) ∧
    (∀ x y, x < N → (final N nb).lab x = (final N nb).lab y → Reach nb x y) := by
  have hI := final_inv hcl
  have hH := final_halted hcl
  have hS := hI.S_nil_of_stk hH.1
  have hasg : ∀ x, x < N → N < (final N nb).lab x := by
    intro x hx
    have h0 := hI.below_nxt x (by have := hH.2; omega)
    by_contra hle
    have := hI.onS x h0 (by omega)
    rw [hS] at this; simp at this
  refine ⟨hasg, fun x hx w hw => (hI.asg_mono x (hasg x hx) w hw).2,
    fun x y hx hxy => hI.asg_sc x y (hasg x hx) hxy⟩

/-! ### Sizes (for the machine) -/

theorem Inv.stk_len {s : State} (hI : Inv N nb s) : s.stk.length ≤ s.S.length := by
  have hnd : s.stk.Nodup := hI.stk_pw.imp_of_mem fun _ _ h => by
    intro he; subst he; exact absurd h.2 (lt_irrefl _)
  exact (hnd.subperm fun x hx => hI.stk_S x hx).length_le

theorem Inv.B_len {s : State} (hI : Inv N nb s) : s.B.length ≤ s.S.length :=
  length_le_of_pw hI.B_pw hI.B_le

end pres

end STACS2027.Runtimes.TwoSat.Scc

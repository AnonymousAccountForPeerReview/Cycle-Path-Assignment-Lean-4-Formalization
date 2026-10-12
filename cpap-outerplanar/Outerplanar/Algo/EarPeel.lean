module

public import Outerplanar.Algo.Ear
import Outerplanar.Algo.EarInv
import Outerplanar.Algo.EarCorrect
import Outerplanar.Degenerate
import Mathlib.Tactic

/-!
# Peeling a 2-degenerate graph: an orientation with out-degree at most two

The ear-elimination machine (`RAM/EarProg.lean`) answers its adjacency queries from the
original graph `L` (`Outerplanar/Algo/EarStatic.lean`). To answer them in `O(1)` without an
`N × N` matrix, a *peeling pass* orients the edges of `L` so that every vertex has at most two
out-neighbours, stored in two arrays: `u w` is an edge iff `w` is an out-neighbour of `u` or `u`
one of `w`.

**The peeling** (on adjacency lists `adj` of the vertices `0, …, N - 1`): the vertices with at
most two neighbours are stacked; repeatedly pop `x`, remove it, record its alive neighbours as
its out-neighbours (`o1 x`, `o2 x`: the first two, `x` itself when missing), lower their
degrees and stack a vertex whose degree drops to two (`premove`, `pstep`). It stops when the
stack is empty.

Results (`PInv`, the invariant, for adjacency lists with `AdjOK`, those of an edge list):
* **for every input** (`PInv.step`, `pinv_init`): the stack holds distinct alive vertices below
  `N` (so at most `N`: `PInv.length_le`), the recorded degree of an alive vertex is its number
  of alive neighbours, and every popped vertex has at most two of them; every round removes a
  vertex, which lowers the potential `ppot` by its degree plus one (`ppot_step`): the pass takes
  linear time on every input;
* **under the hypothesis** that every nonempty set `U` of vertices has a vertex with at most two
  neighbours in `U` (`PInv.all_removed`): when the stack is empty every vertex is removed, and
  then the orientation is complete and sound (`PInv.orientation`). The hypothesis holds when `L`
  has an outerplanar Hamiltonian cycle (`Degenerate.outerplanarHam_degenerate`); for the lists
  `initAdj L` of an edge list: `peel_orient`.
-/

@[expose] public section

namespace STACS2027.Ear

/-! ### The peeling -/

/-- The state of the peeling. -/
structure PState where
  /-- Removed vertices. -/
  rm : ℕ → Bool
  /-- Current degrees (numbers of alive neighbours of the alive vertices). -/
  pd : ℕ → ℕ
  /-- The stack (top first). -/
  stack : List ℕ
  /-- First out-neighbour of a removed vertex (itself if none). -/
  o1 : ℕ → ℕ
  /-- Second out-neighbour of a removed vertex (itself if none). -/
  o2 : ℕ → ℕ

/-- The alive entries of the list of `x`. -/
def palive (adj : ℕ → List ℕ) (rm : ℕ → Bool) (x : ℕ) : List ℕ :=
  (adj x).filter fun y => rm y = false

/-- An alive neighbour `y` of the removed vertex loses one degree; it is stacked when its degree
becomes two. -/
def pdec (p : PState) (y : ℕ) : PState :=
  { p with pd := Function.update p.pd y (p.pd y - 1),
           stack := if p.pd y - 1 = 2 then y :: p.stack else p.stack }

/-- Remove `x` (already popped): mark it, lower the degrees of its alive neighbours in the order
of its list, record the first two of them. -/
def premove (adj : ℕ → List ℕ) (p : PState) (x : ℕ) : PState :=
  let rm' := Function.update p.rm x true
  let nb := palive adj rm' x
  let p2 := nb.foldl pdec { p with rm := rm' }
  { p2 with o1 := Function.update p.o1 x (nb.getD 0 x),
            o2 := Function.update p.o2 x (nb.getD 1 x) }

/-- One round: pop `x` and remove it. -/
def pstep (adj : ℕ → List ℕ) (p : PState) : PState :=
  match p.stack with
  | [] => p
  | x :: rest => premove adj { p with stack := rest } x

/-- The vertices below `j` with at most two neighbours, in increasing order. -/
def pstackPre (adj : ℕ → List ℕ) (j : ℕ) : List ℕ :=
  (List.range j).filter fun x => (adj x).length ≤ 2

/-- The initial state: nothing removed, the degrees, the vertices of degree at most two stacked
in increasing order. -/
def pinit (N : ℕ) (adj : ℕ → List ℕ) : PState where
  rm := fun _ => false
  pd := fun x => (adj x).length
  stack := (pstackPre adj N).reverse
  o1 := fun _ => 0
  o2 := fun _ => 0

/-! ### The fold over the alive neighbours -/

theorem foldl_pdec_rm (l : List ℕ) (p : PState) : (l.foldl pdec p).rm = p.rm := by
  induction l generalizing p with
  | nil => rfl
  | cons y l ih => rw [List.foldl_cons, ih]; rfl

theorem foldl_pdec_o1 (l : List ℕ) (p : PState) : (l.foldl pdec p).o1 = p.o1 := by
  induction l generalizing p with
  | nil => rfl
  | cons y l ih => rw [List.foldl_cons, ih]; rfl

theorem foldl_pdec_o2 (l : List ℕ) (p : PState) : (l.foldl pdec p).o2 = p.o2 := by
  induction l generalizing p with
  | nil => rfl
  | cons y l ih => rw [List.foldl_cons, ih]; rfl

theorem foldl_pdec_pd {l : List ℕ} (hl : l.Nodup) (p : PState) (y : ℕ) :
    (l.foldl pdec p).pd y = if y ∈ l then p.pd y - 1 else p.pd y := by
  induction l generalizing p with
  | nil => simp
  | cons z l ih =>
    rw [List.foldl_cons, ih (List.nodup_cons.mp hl).2]
    have hz := (List.nodup_cons.mp hl).1
    simp only [pdec, List.mem_cons, Function.update_apply]
    by_cases hyz : y = z
    · subst hyz; simp [hz]
    · simp [hyz]

theorem foldl_pdec_stack {l : List ℕ} (hl : l.Nodup) (p : PState) :
    (l.foldl pdec p).stack = (l.filter fun y => p.pd y - 1 = 2).reverse ++ p.stack := by
  induction l generalizing p with
  | nil => simp
  | cons z l ih =>
    rw [List.foldl_cons, ih (List.nodup_cons.mp hl).2]
    have hz := (List.nodup_cons.mp hl).1
    have hf : (l.filter fun y => (pdec p z).pd y - 1 = 2) = l.filter fun y => p.pd y - 1 = 2 :=
      List.filter_congr fun y hy => by
        have : y ≠ z := fun e => hz (e ▸ hy)
        simp [pdec, Function.update_of_ne this]
    rw [hf, List.filter_cons]
    by_cases h2 : p.pd z - 1 = 2 <;> simp [pdec, h2]

/-! ### The invariant -/

/-- The adjacency lists of a simple graph on `0, …, N - 1`. -/
structure AdjOK (N : ℕ) (adj : ℕ → List ℕ) : Prop where
  nodup : ∀ a, (adj a).Nodup
  symm : ∀ a b, b ∈ adj a → a ∈ adj b
  lt : ∀ a, ∀ b ∈ adj a, b < N
  irrefl : ∀ a, a ∉ adj a

/-- **The invariant of the peeling.** -/
structure PInv (N : ℕ) (adj : ℕ → List ℕ) (p : PState) : Prop where
  lt : ∀ x ∈ p.stack, x < N
  nodup : p.stack.Nodup
  alive : ∀ x ∈ p.stack, p.rm x = false
  pd : ∀ x, x < N → p.rm x = false → p.pd x = (palive adj p.rm x).length
  spd : ∀ x ∈ p.stack, p.pd x ≤ 2
  push : ∀ x, x < N → p.rm x = false → p.pd x ≤ 2 → x ∈ p.stack
  orient : ∀ a, p.rm a = true → ∀ b ∈ adj a,
    (p.o1 a = b ∨ p.o2 a = b) ∨ (p.rm b = true ∧ (p.o1 b = a ∨ p.o2 b = a))
  sound : ∀ a, p.rm a = true → (p.o1 a = a ∨ p.o1 a ∈ adj a) ∧ (p.o2 a = a ∨ p.o2 a ∈ adj a)

theorem pinv_init {N : ℕ} {adj : ℕ → List ℕ} : PInv N adj (pinit N adj) where
  lt := fun x hx => by
    simp only [pinit, pstackPre, List.mem_reverse, List.mem_filter, List.mem_range] at hx
    exact hx.1
  nodup := List.nodup_reverse.mpr (List.nodup_range.filter _)
  alive := fun _ _ => rfl
  pd := fun x _ _ => by simp [pinit, palive]
  spd := fun x hx => by
    simp only [pinit, pstackPre, List.mem_reverse, List.mem_filter, List.mem_range,
      decide_eq_true_eq] at hx
    exact hx.2
  push := fun x hx _ h2 => by
    simp only [pinit, pstackPre, List.mem_reverse, List.mem_filter, List.mem_range,
      decide_eq_true_eq]
    exact ⟨hx, h2⟩
  orient := fun _ h => by simp [pinit] at h
  sound := fun _ h => by simp [pinit] at h

theorem PInv.length_le {N : ℕ} {adj : ℕ → List ℕ} {p : PState} (h : PInv N adj p) :
    p.stack.length ≤ N := by
  simpa using h.nodup.length_le_of_subset (l₂ := List.range N) fun x hx =>
    List.mem_range.mpr (h.lt x hx)

theorem mem_getD_of_le_two {l : List ℕ} (hl : l.length ≤ 2) {b : ℕ} (hb : b ∈ l) (d : ℕ) :
    l.getD 0 d = b ∨ l.getD 1 d = b := by
  match l, hl with
  | [x], _ => simp at hb; simp [hb]
  | [x, y], _ =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl <;> simp

theorem getD_mem_or {l : List ℕ} (i d : ℕ) : l.getD i d = d ∨ l.getD i d ∈ l := by
  rw [List.getD_eq_getElem?_getD]
  cases h : l[i]? with
  | none => exact Or.inl rfl
  | some x => exact Or.inr (List.mem_of_getElem? h)

section Step

variable {N : ℕ} {adj : ℕ → List ℕ} {p : PState}

/-- **One round keeps the invariant** (for every input). -/
theorem PInv.step (hA : AdjOK N adj) (hP : PInv N adj p) {x : ℕ} {rest : List ℕ}
    (hs : p.stack = x :: rest) : PInv N adj (premove adj { p with stack := rest } x) := by
  have hxs : x ∈ p.stack := by rw [hs]; exact List.mem_cons_self ..
  have hxN := hP.lt x hxs
  have hxa := hP.alive x hxs
  have hx2 := hP.spd x hxs
  have hxr : x ∉ rest := by
    have := hP.nodup; rw [hs] at this; exact (List.nodup_cons.mp this).1
  have hrest : ∀ z ∈ rest, z ∈ p.stack := fun z hz => by rw [hs]; exact List.mem_cons_of_mem _ hz
  set rm' := Function.update p.rm x true with hrm'
  -- the alive neighbours of `x`
  have hnb : palive adj rm' x = palive adj p.rm x := by
    refine List.filter_congr fun y hy => ?_
    have : y ≠ x := fun e => hA.irrefl x (e ▸ hy)
    simp [hrm', Function.update_of_ne this]
  set nb := palive adj rm' x with hnbdef
  have hnbnd : nb.Nodup := (hA.nodup x).filter _
  have hmemnb : ∀ y, y ∈ nb ↔ y ∈ adj x ∧ p.rm y = false := by
    intro y
    rw [hnb, palive, List.mem_filter, decide_eq_true_eq]
  have hnblen : nb.length ≤ 2 := by rw [hnb, ← hP.pd x hxN hxa]; exact hx2
  -- the fields of the new state
  set q : PState := { p with stack := rest, rm := rm' }
  have hrm : (premove adj { p with stack := rest } x).rm = rm' := foldl_pdec_rm _ _
  have hpd : ∀ y, (premove adj { p with stack := rest } x).pd y =
      if y ∈ nb then p.pd y - 1 else p.pd y := foldl_pdec_pd hnbnd q
  have hst : (premove adj { p with stack := rest } x).stack =
      (nb.filter fun y => p.pd y - 1 = 2).reverse ++ rest := foldl_pdec_stack hnbnd q
  have ho1 : (premove adj { p with stack := rest } x).o1 = Function.update p.o1 x (nb.getD 0 x) :=
    rfl
  have ho2 : (premove adj { p with stack := rest } x).o2 = Function.update p.o2 x (nb.getD 1 x) :=
    rfl
  have hmemst : ∀ z, z ∈ (premove adj { p with stack := rest } x).stack ↔
      (z ∈ nb ∧ p.pd z - 1 = 2) ∨ z ∈ rest := by
    intro z
    rw [hst, List.mem_append, List.mem_reverse, List.mem_filter, decide_eq_true_eq]
  have hrm'x : ∀ z, rm' z = false ↔ z ≠ x ∧ p.rm z = false := by
    intro z
    by_cases hz : z = x
    · subst hz; simp [hrm']
    · simp [hrm', hz]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- lt
    intro z hz
    rcases (hmemst z).mp hz with ⟨hz, -⟩ | hz
    · exact hA.lt x z ((hmemnb z).mp hz).1
    · exact hP.lt z (hrest z hz)
  · -- nodup
    rw [hst]
    refine List.nodup_append.mpr ⟨List.nodup_reverse.mpr (hnbnd.filter _), ?_, ?_⟩
    · have := hP.nodup; rw [hs] at this; exact (List.nodup_cons.mp this).2
    · intro a ha b hb hab
      subst hab
      rw [List.mem_reverse, List.mem_filter, decide_eq_true_eq] at ha
      have := hP.spd a (hrest a hb)
      omega
  · -- alive
    intro z hz
    rw [hrm]
    rcases (hmemst z).mp hz with ⟨hz, -⟩ | hz
    · exact (decide_eq_true_eq.mp (List.mem_filter.mp hz).2)
    · exact (hrm'x z).mpr ⟨fun e => hxr (e ▸ hz), hP.alive z (hrest z hz)⟩
  · -- pd
    intro y hy hya
    rw [hrm] at hya ⊢
    obtain ⟨hyx, hyp⟩ := (hrm'x y).mp hya
    rw [hpd]
    have hkill : palive adj rm' y = (palive adj p.rm y).filter fun z => z ≠ x := by
      rw [hrm', palive, palive]
      exact filter_kill _ _ _
    rw [hkill, hP.pd y hy hyp]
    by_cases hxy : x ∈ adj y
    · have hyn : y ∈ nb := (hmemnb y).mpr ⟨hA.symm y x hxy, hyp⟩
      have hxp : x ∈ palive adj p.rm y := List.mem_filter.mpr ⟨hxy, by simpa using hxa⟩
      have := length_filter_ne (l := palive adj p.rm y) ((hA.nodup y).filter _) hxp
      simp only [hyn, ↓reduceIte]
      omega
    · have hyn : y ∉ nb := fun h => hxy (hA.symm x y ((hmemnb y).mp h).1)
      have hxp : x ∉ palive adj p.rm y := fun h => hxy (List.mem_filter.mp h).1
      simp only [hyn, ↓reduceIte, filter_ne_of_not_mem hxp]
  · -- spd
    intro z hz
    rw [hpd]
    rcases (hmemst z).mp hz with ⟨hz1, hz2⟩ | hz
    · simp only [hz1, ↓reduceIte]; omega
    · have := hP.spd z (hrest z hz)
      split_ifs <;> omega
  · -- push
    intro y hy hya hy2
    rw [hrm] at hya
    obtain ⟨hyx, hyp⟩ := (hrm'x y).mp hya
    rw [hpd] at hy2
    rw [hmemst]
    have hin : p.pd y ≤ 2 → y ∈ rest := fun h => by
      have := hP.push y hy hyp h
      rw [hs] at this
      rcases List.mem_cons.mp this with e | e
      · exact absurd e hyx
      · exact e
    by_cases hyn : y ∈ nb
    · simp only [hyn, ↓reduceIte] at hy2
      by_cases h2 : p.pd y - 1 = 2
      · exact Or.inl ⟨hyn, h2⟩
      · exact Or.inr (hin (by omega))
    · simp only [hyn, ↓reduceIte] at hy2
      exact Or.inr (hin hy2)
  · -- orient
    intro a ha b hb
    rw [hrm] at ha ⊢
    rw [ho1, ho2]
    by_cases hax : a = x
    · subst hax
      by_cases hbr : p.rm b = false
      · have hbn : b ∈ nb := (hmemnb b).mpr ⟨hb, hbr⟩
        left
        rcases mem_getD_of_le_two hnblen hbn a with h | h
        · left; rw [Function.update_self]; exact h
        · right; rw [Function.update_self]; exact h
      · have hbt : p.rm b = true := by simpa using hbr
        have hba : b ≠ a := fun e => by rw [e] at hbt; rw [hxa] at hbt; exact Bool.false_ne_true hbt
        rcases hP.orient b hbt a (hA.symm a b hb) with h | ⟨h, -⟩
        · right
          refine ⟨by simp [hrm', Function.update_of_ne hba, hbt], ?_⟩
          simpa [Function.update_of_ne hba] using h
        · rw [hxa] at h; exact absurd h Bool.false_ne_true
    · have hat : p.rm a = true := by simpa [hrm', Function.update_of_ne hax] using ha
      rcases hP.orient a hat b hb with h | ⟨hbt, h⟩
      · left; simpa [Function.update_of_ne hax] using h
      · have hbx : b ≠ x := fun e => by rw [e, hxa] at hbt; exact Bool.false_ne_true hbt
        right
        refine ⟨by simp [hrm', Function.update_of_ne hbx, hbt], ?_⟩
        simpa [Function.update_of_ne hbx] using h
  · -- sound
    intro a ha
    rw [hrm] at ha
    rw [ho1, ho2]
    by_cases hax : a = x
    · subst hax
      simp only [Function.update_self]
      have hsub : ∀ y ∈ nb, y ∈ adj a := fun y hy => ((hmemnb y).mp hy).1
      constructor
      · rcases getD_mem_or (l := nb) 0 a with h | h
        · exact Or.inl h
        · exact Or.inr (hsub _ h)
      · rcases getD_mem_or (l := nb) 1 a with h | h
        · exact Or.inl h
        · exact Or.inr (hsub _ h)
    · have hat : p.rm a = true := by simpa [hrm', Function.update_of_ne hax] using ha
      simpa [Function.update_of_ne hax] using hP.sound a hat

/-- One round of `pstep` keeps the invariant. -/
theorem PInv.pstep (hA : AdjOK N adj) (hP : PInv N adj p) : PInv N adj (pstep adj p) := by
  unfold Ear.pstep
  split
  · exact hP
  · next x rest hs => exact hP.step hA hs

end Step

/-! ### The potential -/

/-- The potential of the peeling: degree plus one, summed over the alive vertices below `N`. -/
def ppot (N : ℕ) (adj : ℕ → List ℕ) (p : PState) : ℕ :=
  ∑ x ∈ Finset.range N, if p.rm x = true then 0 else (adj x).length + 1

/-- **Every round removes a vertex**: the potential drops by its degree plus one. -/
theorem ppot_step {N : ℕ} {adj : ℕ → List ℕ} {p : PState} (hP : PInv N adj p) {x : ℕ}
    {rest : List ℕ} (hs : p.stack = x :: rest) :
    ppot N adj (premove adj { p with stack := rest } x) + ((adj x).length + 1) = ppot N adj p := by
  have hxs : x ∈ p.stack := by rw [hs]; exact List.mem_cons_self ..
  have hxN : x ∈ Finset.range N := Finset.mem_range.mpr (hP.lt x hxs)
  have hxa := hP.alive x hxs
  have hrm : (premove adj { p with stack := rest } x).rm = Function.update p.rm x true :=
    foldl_pdec_rm _ _
  unfold ppot
  rw [hrm, ← Finset.add_sum_erase _ _ hxN, ← Finset.add_sum_erase _ _ hxN]
  have hc : ∑ y ∈ (Finset.range N).erase x,
      (if Function.update p.rm x true y = true then 0 else (adj y).length + 1) =
      ∑ y ∈ (Finset.range N).erase x, (if p.rm y = true then 0 else (adj y).length + 1) :=
    Finset.sum_congr rfl fun y hy => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hy)]
  rw [hc]
  simp [hxa]
  omega

theorem ppot_le (N : ℕ) (adj : ℕ → List ℕ) (p : PState) :
    ppot N adj p ≤ ∑ x ∈ Finset.range N, ((adj x).length + 1) :=
  Finset.sum_le_sum fun x _ => by split <;> omega

/-! ### Completeness and the orientation, under the hypothesis -/

section Final

variable {N : ℕ} {adj : ℕ → List ℕ} {p : PState}

/-- **Under the degeneracy hypothesis, the stopped peeling has removed every vertex.** -/
theorem PInv.all_removed (hA : AdjOK N adj) (hP : PInv N adj p) (hs : p.stack = [])
    (hdeg : ∀ U : List ℕ, U ≠ [] → (∀ u ∈ U, u < N) → ∃ u ∈ U, ∀ a b c, a ∈ U → b ∈ U →
      c ∈ U → a ∈ adj u → b ∈ adj u → c ∈ adj u → a = b ∨ a = c ∨ b = c) :
    ∀ x, x < N → p.rm x = true := by
  by_contra hc
  push Not at hc
  obtain ⟨x, hxN, hx⟩ := hc
  set U := (List.range N).filter fun y => p.rm y = false with hU
  have hmU : ∀ y, y ∈ U ↔ y < N ∧ p.rm y = false := fun y => by simp [hU]
  have hUne : U ≠ [] := List.ne_nil_of_mem ((hmU x).mpr ⟨hxN, by simpa using hx⟩)
  obtain ⟨u, huU, hmax⟩ := hdeg U hUne fun y hy => ((hmU y).mp hy).1
  obtain ⟨huN, hua⟩ := (hmU u).mp huU
  have hle : (palive adj p.rm u).length ≤ 2 := by
    by_contra hlt
    push Not at hlt
    have hnd : (palive adj p.rm u).Nodup := (hA.nodup u).filter _
    have hmem : ∀ i (hi : i < (palive adj p.rm u).length), (palive adj p.rm u)[i] ∈ U ∧
        (palive adj p.rm u)[i] ∈ adj u := by
      intro i hi
      have h := List.mem_filter.mp (List.getElem_mem hi)
      exact ⟨(hmU _).mpr ⟨hA.lt u _ h.1, by simpa using h.2⟩, h.1⟩
    rcases hmax _ _ _ (hmem 0 (by omega)).1 (hmem 1 (by omega)).1 (hmem 2 (by omega)).1
      (hmem 0 (by omega)).2 (hmem 1 (by omega)).2 (hmem 2 (by omega)).2 with e | e | e
    · have := hnd.getElem_inj_iff.mp e; omega
    · have := hnd.getElem_inj_iff.mp e; omega
    · have := hnd.getElem_inj_iff.mp e; omega
  have := hP.push u huN hua (by rw [hP.pd u huN hua]; exact hle)
  rw [hs] at this
  exact List.not_mem_nil this

/-- **The orientation**, once every vertex is removed: `b` is a neighbour of `a` iff one of them
is an out-neighbour of the other. -/
theorem PInv.orientation (hA : AdjOK N adj) (hP : PInv N adj p)
    (hall : ∀ x, x < N → p.rm x = true) {a b : ℕ} (ha : a < N) (hb : b < N) (hab : a ≠ b) :
    b ∈ adj a ↔ (p.o1 a = b ∨ p.o2 a = b) ∨ (p.o1 b = a ∨ p.o2 b = a) := by
  constructor
  · intro h
    rcases hP.orient a (hall a ha) b h with h1 | ⟨-, h1⟩
    · exact Or.inl h1
    · exact Or.inr h1
  · rintro ((h | h) | (h | h))
    · rcases (hP.sound a (hall a ha)).1 with h1 | h1
      · exact absurd (h.symm.trans h1) (Ne.symm hab)
      · rwa [h] at h1
    · rcases (hP.sound a (hall a ha)).2 with h1 | h1
      · exact absurd (h.symm.trans h1) (Ne.symm hab)
      · rwa [h] at h1
    · rcases (hP.sound b (hall b hb)).1 with h1 | h1
      · exact absurd (h.symm.trans h1) hab
      · rw [h] at h1; exact hA.symm b a h1
    · rcases (hP.sound b (hall b hb)).2 with h1 | h1
      · exact absurd (h.symm.trans h1) hab
      · rw [h] at h1; exact hA.symm b a h1

end Final

/-! ### The adjacency lists of an edge list -/

theorem adjOK_initAdj {N : ℕ} {L : List Edge} (hL : ∀ e ∈ L, e.1 < e.2 ∧ e.2 < N)
    (hnd : L.Nodup) : AdjOK N (initAdj L) := by
  have hL1 : ∀ e ∈ L, e.1 < e.2 := fun e he => (hL e he).1
  refine ⟨nodup_initAdj hL1 hnd, fun a b h => ?_, fun a b h => ?_, fun a h => ?_⟩
  · rcases (mem_initAdj hL1).mp h with h | h
    · exact (mem_initAdj hL1).mpr (Or.inr h)
    · exact (mem_initAdj hL1).mpr (Or.inl h)
  · rcases (mem_initAdj hL1).mp h with h | h
    · exact (hL _ h).2
    · have := hL _ h; simp only at this; omega
  · rcases (mem_initAdj hL1).mp h with h | h <;> (have := hL _ h; simp only at this; omega)

/-- **The peeling orients the edges of `L`** when `L` has an outerplanar Hamiltonian cycle
through all of `0, …, N - 1`: once the stack is empty, `u w` (`u ≠ w`, both below `N`) is an
edge of `L` iff `w` is an out-neighbour of `u` or `u` one of `w`. -/
theorem peel_orient {N : ℕ} {L : List Edge} (hL : ∀ e ∈ L, e.1 < e.2 ∧ e.2 < N) (hnd : L.Nodup)
    {ham0 : List ℕ} (h0 : OuterplanarHam L ham0) (hv : ∀ v, v < N → v ∈ ham0) {p : PState}
    (hP : PInv N (initAdj L) p) (hs : p.stack = []) {a b : ℕ} (ha : a < N) (hb : b < N)
    (hab : a ≠ b) : Adj L a b ↔ (p.o1 a = b ∨ p.o2 a = b) ∨ (p.o1 b = a ∨ p.o2 b = a) := by
  have hL1 : ∀ e ∈ L, e.1 < e.2 := fun e he => (hL e he).1
  have hA := adjOK_initAdj hL hnd
  have hadj : ∀ x y, y ∈ initAdj L x ↔ Adj L x y := fun x y =>
    (mem_initAdj hL1).trans (adj_iff_mem hL1).symm
  have hall := hP.all_removed hA hs fun U hU hUN => by
    obtain ⟨u, hu, hmax⟩ := outerplanarHam_degenerate h0 hU fun u hu => hv u (hUN u hu)
    exact ⟨u, hu, fun a b c ha hb hc hua hub huc =>
      hmax a b c ha hb hc ((hadj u a).mp hua) ((hadj u b).mp hub) ((hadj u c).mp huc)⟩
  rw [← hadj]
  exact hP.orientation hA hall ha hb hab

end STACS2027.Ear

module

public import Outerplanar.RAM.R1
import Mathlib.Tactic

/-!
# Phase R2 (low points and heads), abstract side

The machine of phase R2 mirrors the two folds of `Outerplanar/Algo/Graph.lean` exactly:

* `lowOf s nb` is a `foldr` over the preorder list `s.ord`: the machine processes
  `v = ord[N - 1 - i]` for `i = 0, 1, …, N - 1` (`vOf g i`), and after `i` vertices its table
  holds the function `lowF g i` (the fold over the last `i` vertices; `lowF_zero`, `lowF_succ`,
  `lowF_full`). One step `lowStep` is a `foldl` over the neighbour list of `v`; its prefixes
  are `accF` (`accF_zero`, `accF_succ`, `accF_full`), where the test "`w` is the parent of `v`
  through a tree edge" is the comparison of `w` with `skOf g v` (the parent, or `N` for a
  root), and `w ≠ v` always holds (no loops).
* `headOf s low` is a `foldl` over `s.ord`: after `i` vertices the table holds `headF g low i`
  (`headF_zero`, `headF_succ`, `headF_full`).

Facts about the final search `dfsOf g`: its preorder list is a permutation of
`0, …, N - 1` (`ord_perm`, `length_ord`, `mem_ord_iff`), parents of vertices are vertices
(`par_lt`); the neighbour lists are segments of the CSR array (`arr_csrAdj_seg`); the total
length of the neighbour lists in the order of the low-point pass is `2 |E|` (`sum_deg`).

Transfer of the interfaces `GraphBase`, `R1Post` to a later configuration that keeps the
registers below `gR2` (other than `rT`, `rFREE`) and the memory below the old `rFREE`
(`base_transfer`, `r1_transfer`).
-/

@[expose] public section

namespace STACS2027.RAM.R2

open STACS2027.Algo

/-! ### The final state of the search -/

theorem dfs_inv (g : Graph) : DFS.Inv (List.range (numV g)) (nbOf (idEdges g)) (dfsOf g) :=
  DFS.final_inv (ok_idEdges g)

theorem dfs_ordInv (g : Graph) : DFS.OrdInv (dfsOf g) := DFS.final_ordInv

theorem dfs_halted (g : Graph) : DFS.Halted (dfsOf g) := DFS.final_halted (ok_idEdges g)

/-- Every vertex is visited. -/
theorem pre_ne_of_lt {g : Graph} {v : ℕ} (hv : v < numV g) : (dfsOf g).pre v ≠ 0 := by
  rcases (dfs_inv g).roots v (List.mem_range.mpr hv) with h | h
  · rw [(dfs_halted g).2] at h; simp at h
  · exact h

theorem mem_ord_iff {g : Graph} {v : ℕ} : v ∈ (dfsOf g).ord ↔ v < numV g := by
  constructor
  · intro h; exact R1.lt_of_pre_ne (dfs_inv g) (((dfs_ordInv g).mem v).mpr h)
  · intro h; exact ((dfs_ordInv g).mem v).mp (pre_ne_of_lt h)

/-- The preorder list is a permutation of the vertices. -/
theorem ord_perm (g : Graph) : (dfsOf g).ord.Perm (List.range (numV g)) :=
  (List.perm_ext_iff_of_nodup (dfs_ordInv g).nodup List.nodup_range).mpr fun v => by
    rw [mem_ord_iff, List.mem_range]

theorem length_ord (g : Graph) : (dfsOf g).ord.length = numV g := by
  simpa using (ord_perm g).length_eq

/-- The parent of a vertex is a vertex. -/
theorem par_lt {g : Graph} {v : ℕ} (hv : v < numV g) : (dfsOf g).par v < numV g := by
  by_cases hr : (dfsOf g).par v = v
  · rw [hr]; exact hv
  · exact R1.lt_of_pre_ne (dfs_inv g) ((dfs_inv g).par_vis v (pre_ne_of_lt hv) hr)

theorem ord_getD {g : Graph} {k : ℕ} (hk : k < numV g) :
    (dfsOf g).ord.getD k 0 = (dfsOf g).ord[k]'(by rw [length_ord]; exact hk) :=
  getD_eq_getElem' _

theorem ord_getD_lt {g : Graph} {k : ℕ} (hk : k < numV g) : (dfsOf g).ord.getD k 0 < numV g := by
  rw [ord_getD hk, ← mem_ord_iff]; exact List.getElem_mem _

/-! ### The CSR segments -/

/-- The neighbour list of `v` is the segment of the CSR array starting at `ps E v`. -/
theorem arr_csrAdj_seg {m : ℕ → ℕ} {b : ℕ} {E : List Edge} :
    ∀ {N : ℕ}, Arr m b (csrAdj E N) → ∀ {v : ℕ}, v < N → Arr m (b + R1.ps E v) (nbOf E v)
  | 0, _, _, hv => absurd hv (Nat.not_lt_zero _)
  | N + 1, h, v, hv => by
    rw [R1.csrAdj_succ, arr_append, R1.length_csrAdj] at h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hv with hv | rfl
    · exact arr_csrAdj_seg h.1 hv
    · exact h.2

/-! ### The low-point pass -/

/-- The vertex processed at round `i` of the low-point pass: `ord[N - 1 - i]`. -/
def vOf (g : Graph) (i : ℕ) : ℕ := (dfsOf g).ord.getD (numV g - 1 - i) 0

theorem vOf_lt {g : Graph} {i : ℕ} (hi : i < numV g) : vOf g i < numV g :=
  ord_getD_lt (by omega)

/-- The low points after the last `i` vertices of the preorder list (the `foldr` of `lowOf`
over a suffix). -/
def lowF (g : Graph) (i : ℕ) : ℕ → ℕ :=
  ((dfsOf g).ord.drop (numV g - i)).foldr
    (fun v lowf => Function.update lowf v (lowStep (dfsOf g) (nbOf (idEdges g)) lowf v))
    (fun _ => 0)

theorem lowF_zero (g : Graph) : lowF g 0 = fun _ => 0 := by
  rw [lowF, Nat.sub_zero, List.drop_of_length_le (by rw [length_ord])]
  rfl

theorem lowF_succ (g : Graph) {i : ℕ} (hi : i < numV g) :
    lowF g (i + 1) = Function.update (lowF g i) (vOf g i)
      (lowStep (dfsOf g) (nbOf (idEdges g)) (lowF g i) (vOf g i)) := by
  have hl : numV g - 1 - i < (dfsOf g).ord.length := by rw [length_ord]; omega
  unfold lowF
  rw [show numV g - (i + 1) = numV g - 1 - i by omega, List.drop_eq_getElem_cons hl,
    show numV g - 1 - i + 1 = numV g - i by omega, List.foldr_cons, vOf,
    getD_eq_getElem' hl]

theorem lowF_full (g : Graph) : lowF g (numV g) = lowsOf g := by
  simp [lowF, lowsOf, lowOf]

/-- The vertex skipped among the neighbours of `v` (its parent through the tree edge), or
`N` (no vertex) for a root. -/
def skOf (g : Graph) (v : ℕ) : ℕ := if (dfsOf g).par v = v then numV g else (dfsOf g).par v

/-- The low-point step of `v` after the first `k` neighbours. -/
def accF (g : Graph) (f : ℕ → ℕ) (v k : ℕ) : ℕ :=
  ((nbOf (idEdges g) v).take k).foldl (fun acc w =>
    if w = (dfsOf g).par v ∧ (dfsOf g).par v ≠ v then acc
    else min acc (if (dfsOf g).par w = v ∧ w ≠ v then f w else (dfsOf g).pre w)) ((dfsOf g).pre v)

theorem accF_zero (g : Graph) (f : ℕ → ℕ) (v : ℕ) : accF g f v 0 = (dfsOf g).pre v := by
  simp [accF]

theorem accF_full (g : Graph) (f : ℕ → ℕ) (v : ℕ) :
    accF g f v (nbOf (idEdges g) v).length = lowStep (dfsOf g) (nbOf (idEdges g)) f v := by
  simp [accF, lowStep]

/-- One more neighbour `w` of `v`: skipped if it is `skOf g v`, else the minimum with the
low point of `w` (a child) or the preorder number of `w`. -/
theorem accF_succ (g : Graph) (f : ℕ → ℕ) {v k : ℕ}
    (hk : k < (nbOf (idEdges g) v).length) :
    accF g f v (k + 1) =
      if (nbOf (idEdges g) v)[k] = skOf g v then accF g f v k
      else min (accF g f v k) (if (dfsOf g).par (nbOf (idEdges g) v)[k] = v
        then f (nbOf (idEdges g) v)[k] else (dfsOf g).pre (nbOf (idEdges g) v)[k]) := by
  have hmem := List.getElem_mem hk
  have hw : (nbOf (idEdges g) v)[k] < numV g := R1.lt_of_mem_nbOf hmem
  have hwv : (nbOf (idEdges g) v)[k] ≠ v := fun h => by
    have h' := hmem
    rw [h] at h'
    exact (ok_idEdges g).noloop v h'
  have h1 : ((nbOf (idEdges g) v)[k] = (dfsOf g).par v ∧ (dfsOf g).par v ≠ v) ↔
      (nbOf (idEdges g) v)[k] = skOf g v := by
    unfold skOf
    by_cases hp : (dfsOf g).par v = v
    · simp only [hp, ne_eq, not_true_eq_false, and_false, ↓reduceIte, false_iff]; omega
    · simp only [hp, ne_eq, not_false_eq_true, and_true, ↓reduceIte]
  have h2 : ((dfsOf g).par (nbOf (idEdges g) v)[k] = v ∧ (nbOf (idEdges g) v)[k] ≠ v) ↔
      (dfsOf g).par (nbOf (idEdges g) v)[k] = v := by simp [hwv]
  unfold accF
  rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, List.foldl_append,
    List.foldl_cons, List.foldl_nil]
  simp only [h1, h2]

/-! ### The head pass -/

/-- The heads after the first `i` vertices of the preorder list. -/
def headF (g : Graph) (low : ℕ → ℕ) (i : ℕ) : ℕ → ℕ :=
  ((dfsOf g).ord.take i).foldl (fun hf v => Function.update hf v
    (if (dfsOf g).par v = v then v
      else if (dfsOf g).pre ((dfsOf g).par v) ≤ low v then v else hf ((dfsOf g).par v)))
    (fun _ => 0)

theorem headF_zero (g : Graph) (low : ℕ → ℕ) : headF g low 0 = fun _ => 0 := by
  simp [headF]

theorem headF_succ (g : Graph) (low : ℕ → ℕ) {i : ℕ} (hi : i < numV g) :
    headF g low (i + 1) = Function.update (headF g low i) ((dfsOf g).ord.getD i 0)
      (if (dfsOf g).par ((dfsOf g).ord.getD i 0) = (dfsOf g).ord.getD i 0
        then (dfsOf g).ord.getD i 0
        else if (dfsOf g).pre ((dfsOf g).par ((dfsOf g).ord.getD i 0)) ≤
            low ((dfsOf g).ord.getD i 0) then (dfsOf g).ord.getD i 0
          else headF g low i ((dfsOf g).par ((dfsOf g).ord.getD i 0))) := by
  have hl : i < (dfsOf g).ord.length := by rw [length_ord]; exact hi
  unfold headF
  rw [List.take_add_one, List.getElem?_eq_getElem hl, Option.toList_some, List.foldl_append,
    List.foldl_cons, List.foldl_nil, getD_eq_getElem' hl]

theorem headF_full (g : Graph) : headF g (lowsOf g) (numV g) = headsOf g := by
  rw [headF, ← length_ord, List.take_length]
  rfl

/-! ### The running time of the low-point pass -/

theorem sum_range_getD (f : ℕ → ℕ) (l : List ℕ) :
    ∑ j ∈ Finset.range l.length, f (l.getD j 0) = (l.map f).sum := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l x ih =>
    rw [List.length_append, List.length_singleton, Finset.sum_range_succ, List.map_append,
      List.sum_append, ← ih]
    congr 1
    · apply Finset.sum_congr rfl
      intro j hj
      have hj' := Finset.mem_range.mp hj
      rw [getD_eq_getElem' (by simp; omega), getD_eq_getElem' hj', List.getElem_append_left hj']
    · simp

/-- The neighbour lists of the vertices in the order of the low-point pass have total length
`2 |E|`. -/
theorem sum_deg (g : Graph) :
    ∑ i ∈ Finset.range (numV g), (nbOf (idEdges g) (vOf g i)).length = 2 * (idEdges g).length := by
  unfold vOf
  rw [Finset.sum_range_reflect (fun j => (nbOf (idEdges g) ((dfsOf g).ord.getD j 0)).length),
    ← length_ord g, sum_range_getD (fun u => (nbOf (idEdges g) u).length),
    ((ord_perm g).map _).sum_eq]
  exact R1.idEdges_ps g

/-! ### Transfer of the interfaces -/

/-- `GraphBase` survives a run keeping the registers below `gR2` (other than `rT`, `rFREE`)
and the memory below the old `rFREE`. -/
theorem base_transfer {g : Graph} {c₀ c : Config} (h : GraphBase g c₀)
    (hreg : ∀ r, r < gR2 → r ≠ rT → r ≠ rFREE → c.reg r = c₀.reg r)
    (hS : SameOn (· < c₀.reg rFREE) c₀.mem c.mem) (hF : c₀.reg rFREE ≤ c.reg rFREE)
    (hZ : ZeroFrom c.mem (c.reg rFREE)) : GraphBase g c := by
  have hb := h.below
  have e1 : c.reg gLB = c₀.reg gLB := hreg _ (by decide) (by decide) (by decide)
  have e2 : c.reg gEU = c₀.reg gEU := hreg _ (by decide) (by decide) (by decide)
  have e3 : c.reg gEV = c₀.reg gEV := hreg _ (by decide) (by decide) (by decide)
  refine ⟨(hreg _ (by decide) (by decide) (by decide)).trans h.zero,
    (hreg _ (by decide) (by decide) (by decide)).trans h.one,
    (hreg _ (by decide) (by decide) (by decide)).trans h.m,
    (hreg _ (by decide) (by decide) (by decide)).trans h.n,
    (hreg _ (by decide) (by decide) (by decide)).trans h.ne, ?_, ?_, ?_, hZ, ?_⟩
  · rw [e1]; exact h.lb.of_below hS (by have : numV g = (labels g).length := rfl; omega)
  · rw [e2]; exact h.eu.of_below hS (by simpa using hb.2.1)
  · rw [e3]; exact h.ev.of_below hS (by simpa using hb.2.2)
  · rw [e1, e2, e3]; omega

/-- `R1Post` survives a run keeping the registers below `gR2` (other than `rT`, `rFREE`) and
the memory below the old `rFREE`. -/
theorem r1_transfer {g : Graph} {c₀ c : Config} (h : R1Post g c₀)
    (hreg : ∀ r, r < gR2 → r ≠ rT → r ≠ rFREE → c.reg r = c₀.reg r)
    (hS : SameOn (· < c₀.reg rFREE) c₀.mem c.mem) (hF : c₀.reg rFREE ≤ c.reg rFREE)
    (hZ : ZeroFrom c.mem (c.reg rFREE)) : R1Post g c := by
  have hb := h.below
  have e1 : c.reg gOFF = c₀.reg gOFF := hreg _ (by decide) (by decide) (by decide)
  have e2 : c.reg gADJ = c₀.reg gADJ := hreg _ (by decide) (by decide) (by decide)
  have e3 : c.reg gPRE = c₀.reg gPRE := hreg _ (by decide) (by decide) (by decide)
  have e4 : c.reg gPAR = c₀.reg gPAR := hreg _ (by decide) (by decide) (by decide)
  have e5 : c.reg gORD = c₀.reg gORD := hreg _ (by decide) (by decide) (by decide)
  refine ⟨base_transfer h.base hreg hS hF hZ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e1]; exact h.off.of_below hS (by simpa [R1.csrOff_eq] using hb.1)
  · rw [e2]; exact h.adj.of_below hS hb.2.1
  · rw [e3]; exact h.pre.of_below hS hb.2.2.1
  · rw [e4]; exact h.par.of_below hS hb.2.2.2.1
  · rw [e5]; exact h.ord.of_below hS hb.2.2.2.2
  · rw [e1, e2, e3, e4, e5]; omega

end STACS2027.RAM.R2

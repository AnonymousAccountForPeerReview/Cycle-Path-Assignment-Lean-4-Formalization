module

public import BoundedCost
public import Outerplanar.RAM.R0Spec
public import Outerplanar.RAM.PairIdsRank
import Mathlib.Tactic

/-!
# Corollary 5 on the RAM: the abstract side

The machine of Corollary 5 receives the enumerated cycles `C_0, …, C_{t-1}` of `cycles g k`
as the list `verts g k` of their vertices, cycle after cycle (each cycle has `k` vertices).
Occurrence `q = i k + j` (`i < t`, `j < k`) is the edge at position `j` of `C_i`; the list of
these edges is `occs g k` (`occs_getD`: `edge (verts[q]) (verts[ik + next k j])`), and the
number `q` is the variable `b_{C_i,e}` of Section 4.

This file describes, as functions of the prefix of the input already read, what the RAM phases
compute:

* the largest label `maxV` (below `labelBound g`, `maxV_lt_labelBound`: the cycles are cycles of
  `g`), the vertex list `vl` with its dictionary `dictOf (vprefix q)` and the ids `idv`; the id
  pairs `prs = occs.map idPr`, `idPr e = (idv e.1, idv e.2)` (injective on the edges of the
  cycles, `idPr_inj`), whose first-occurrence identifiers (`PairIds.eids`, computed by
  outerplanar package's module `PairIds.pairIds` without an `N × N` table) are the `eidOf q` below
  (`eids_prs`), with the class sizes `cntF (kt)` (`count_eids_prs`);
* the distinct edges in order of first occurrence `eprefix q` (with `eprefix (kt) =
  edgesOnCycles g k`), the identifier `eidOf q` of occurrence `q` (the index of its edge in
  `edgesOnCycles g k`), the counts `cntF q e`, the rank `rank q` of an occurrence among the
  occurrences of its edge, and the offsets `offF e` (the number of the variable `s_{e,1}`);
* `cntF_final`, `offF_eidOf`, `rank_spec`: these are `|cyclesThrough g k e|`,
  `prefixOffset g k e`, and the position of `C_i` among the cycles through `e`.

The formula built from these (`zcf`) and its equivalence with `zeroCostFormula g k` are in
`Runtimes/ZeroCostFormula.lean`.
-/

@[expose] public section

namespace STACS2027.Runtimes.ZeroCost

open STACS2027 Complexity.SAT STACS2027.RAM STACS2027.RAM.R0

/-! ### Uniform flattening -/

theorem length_flatten_uniform {α : Type} {k : ℕ} : ∀ (L : List (List α)), (∀ l ∈ L, l.length = k) →
    L.flatten.length = k * L.length
  | [], _ => by simp
  | l :: L, h => by
    rw [List.flatten_cons, List.length_append, h l (by simp),
      length_flatten_uniform L (fun l' hl' => h l' (by simp [hl']))]
    simp only [List.length_cons]; ring

theorem getD_flatten_uniform {α : Type} {k : ℕ} (d : α) : ∀ (L : List (List α)), (∀ l ∈ L, l.length = k) →
    ∀ {i j : ℕ}, i < L.length → j < k → L.flatten.getD (i * k + j) d = (L.getD i []).getD j d
  | [], _, _, _, hi, _ => by simp at hi
  | l :: L, h, i, j, hi, hj => by
    have hl := h l (by simp)
    cases i with
    | zero =>
      simp only [zero_mul, zero_add, List.flatten_cons, List.getD_cons_zero]
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega)]
    | succ i =>
      have ih := getD_flatten_uniform d L (fun l' hl' => h l' (by simp [hl']))
        (i := i) (j := j) (by simp at hi; omega) hj
      rw [List.flatten_cons, List.getD_cons_succ, ← ih, List.getD_eq_getElem?_getD,
        List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hl]; nlinarith)]
      congr 2
      rw [hl]; ring_nf; omega

theorem take_flatten_uniform {α : Type} {k : ℕ} : ∀ (L : List (List α)), (∀ l ∈ L, l.length = k) →
    ∀ {i j : ℕ}, i < L.length → j ≤ k →
      L.flatten.take (i * k + j) = (L.take i).flatten ++ (L.getD i []).take j
  | [], _, _, _, hi, _ => by simp at hi
  | l :: L, h, i, j, hi, hj => by
    have hl := h l (by simp)
    cases i with
    | zero =>
      simp only [zero_mul, zero_add, List.flatten_cons, List.take_zero, List.flatten_nil,
        List.nil_append, List.getD_cons_zero, List.take_append, hl, Nat.sub_eq_zero_of_le hj,
        List.take_zero, List.append_nil]
    | succ i =>
      have ih := take_flatten_uniform L (fun l' hl' => h l' (by simp [hl']))
        (i := i) (j := j) (by simp at hi; omega) hj
      rw [List.flatten_cons, List.take_append, hl, List.take_of_length_le (by rw [hl]; nlinarith),
        show (i + 1) * k + j - k = i * k + j by rw [Nat.add_mul, one_mul]; omega, ih,
        List.take_succ_cons, List.flatten_cons, List.getD_cons_succ, List.append_assoc]

/-! ### The cycle part of the input and the occurrences -/

section cyc

variable (g : Graph) (k : ℕ)

/-- The vertices of the enumerated cycles, cycle after cycle. -/
def verts : List ℕ := (cycles g k).flatten

/-- The occurrences: the edges of the enumerated cycles, cycle after cycle (`occs[ik + j]` is the
edge at position `j` of `C_i`). -/
def occs : List Edge := (cycles g k).flatMap cycleEdges

theorem cycles_length {c : Cycle} (hc : c ∈ cycles g k) : c.length = k := (enumerated_isCycle hc).2.1

theorem length_verts : (verts g k).length = k * (cycles g k).length :=
  length_flatten_uniform _ fun _ hc => cycles_length g k hc

theorem length_occs : (occs g k).length = k * (cycles g k).length := by
  rw [occs, List.flatMap_def, length_flatten_uniform _ (k := k), List.length_map]
  intro l hl
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hl
  exact (enumerated_isCycle hc).edge_length

variable {g k}

theorem verts_getD {i j : ℕ} (hi : i < (cycles g k).length) (hj : j < k) :
    (verts g k).getD (i * k + j) 0 = (kCycle g k i).getD j 0 :=
  getD_flatten_uniform 0 _ (fun _ hc => cycles_length g k hc) hi hj

theorem occs_getD_cycleEdgeAt {i j : ℕ} (hi : i < (cycles g k).length) (hj : j < k) :
    (occs g k).getD (i * k + j) (0, 0) = cycleEdgeAt g k i j := by
  rw [occs, List.flatMap_def, getD_flatten_uniform (0, 0) _ (k := k) _ (by simpa using hi) hj]
  · unfold cycleEdgeAt kCycle
    congr 1
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem hi]
    rfl
  · intro l hl
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hl
    exact (enumerated_isCycle hc).edge_length

/-- The edge at position `j` of `C_i`, read from the vertices. -/
theorem occs_getD {i j : ℕ} (hi : i < (cycles g k).length) (hj : j < k) :
    (occs g k).getD (i * k + j) (0, 0) =
      edge ((verts g k).getD (i * k + j) 0) ((verts g k).getD (i * k + next k j) 0) := by
  have hc := kCycle_isCycle g hi
  have hk := hc.1
  rw [occs_getD_cycleEdgeAt hi hj, verts_getD hi hj, verts_getD hi (next_lt (by omega)),
    cycleEdgeAt, cycleEdges_getD (by rw [hc.2.1]; omega) (by rw [hc.2.1]; exact hj), hc.2.1]

theorem pathEdges_mem {l : List ℕ} {e : Edge} (he : e ∈ pathEdges l) : e.1 ∈ l ∧ e.2 ∈ l := by
  induction l with
  | nil => simp [pathEdges] at he
  | cons a l ih =>
    cases l with
    | nil => simp [pathEdges] at he
    | cons b rest =>
      simp only [pathEdges, List.mem_cons] at he
      rcases he with rfl | he
      · simp only [edge]
        constructor
        · rcases Nat.le_total a b with h | h
          · simp [Nat.min_eq_left h]
          · simp [Nat.min_eq_right h]
        · rcases Nat.le_total a b with h | h
          · simp [Nat.max_eq_right h]
          · simp [Nat.max_eq_left h]
      · have := ih he
        exact ⟨List.mem_cons_of_mem _ this.1, List.mem_cons_of_mem _ this.2⟩

/-- The ends of every occurrence are vertices of the input. -/
theorem occs_mem_verts {e : Edge} (he : e ∈ occs g k) : e.1 ∈ verts g k ∧ e.2 ∈ verts g k := by
  simp only [occs, List.mem_flatMap] at he
  obtain ⟨c, hc, he⟩ := he
  have h := pathEdges_mem he
  have hsub : ∀ x ∈ c ++ c.take 1, x ∈ verts g k := by
    intro x hx
    simp only [List.mem_append] at hx
    have hx' : x ∈ c := hx.elim id (fun h => List.mem_of_mem_take h)
    exact List.mem_flatten.mpr ⟨c, hc, hx'⟩
  exact ⟨hsub _ h.1, hsub _ h.2⟩

theorem occs_getD_mem {q : ℕ} (hq : q < k * (cycles g k).length) :
    (occs g k).getD q (0, 0) ∈ occs g k := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [length_occs]; exact hq)]
  exact List.getElem_mem _

theorem verts_getD_mem {q : ℕ} (hq : q < k * (cycles g k).length) :
    (verts g k).getD q 0 ∈ verts g k := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [length_verts]; exact hq)]
  exact List.getElem_mem _

/-- Decomposing an occurrence number. -/
theorem occ_decomp {q : ℕ} (hk : 0 < k) (hq : q < k * (cycles g k).length) :
    q / k < (cycles g k).length ∧ q % k < k ∧ q = q / k * k + q % k := by
  refine ⟨?_, Nat.mod_lt _ hk, (Nat.div_add_mod' q k).symm⟩
  rw [Nat.div_lt_iff_lt_mul hk, Nat.mul_comm]; exact hq

end cyc

/-! ### The largest label and the vertex dictionary -/

section dict

variable (g : Graph) (k : ℕ)

/-- The largest vertex label of the input cycles. -/
def maxV : ℕ := (verts g k).foldl max 0

/-- The vertices of the first `q` entries, in order of first appearance. -/
def vprefix (q : ℕ) : List ℕ := ((verts g k).take q).eraseDups

/-- All the vertices of the cycles, in order of first appearance. -/
def vl : List ℕ := (verts g k).eraseDups

/-- The number of vertices. -/
def nV : ℕ := (vl g k).length

/-- The id of a vertex: its position in `vl`. -/
def idv (x : ℕ) : ℕ := (vl g k).idxOf x

variable {g k}

theorem le_maxV {x : ℕ} (hx : x ∈ verts g k) : x ≤ maxV g k := le_foldl_max hx 0

theorem vprefix_succ {q : ℕ} (hq : q < (verts g k).length) :
    vprefix g k (q + 1) = ext (vprefix g k q) ((verts g k).getD q 0) := by
  unfold vprefix
  rw [List.take_add_one, List.getElem?_eq_getElem hq, Option.toList_some,
    eraseDups_append_singleton, getD_eq_getElem' hq]

theorem vprefix_full : vprefix g k (k * (cycles g k).length) = vl g k := by
  rw [vprefix, ← length_verts, List.take_length]; rfl

theorem length_vprefix_le (q : ℕ) : (vprefix g k q).length ≤ q :=
  (length_eraseDups_le _).trans (List.length_take_le _ _)

theorem nV_le : nV g k ≤ k * (cycles g k).length := by
  have := length_vprefix_le (g := g) (k := k) (k * (cycles g k).length)
  rwa [vprefix_full] at this

theorem mem_vprefix_le {q : ℕ} {x : ℕ} (hx : x ∈ vprefix g k q) : x ≤ maxV g k := by
  simp only [vprefix, List.mem_eraseDups] at hx
  exact le_maxV (List.mem_of_mem_take hx)

theorem mem_vl {x : ℕ} : x ∈ vl g k ↔ x ∈ verts g k := List.mem_eraseDups

theorem idv_lt {x : ℕ} (hx : x ∈ verts g k) : idv g k x < nV g k :=
  List.idxOf_lt_length_of_mem (mem_vl.mpr hx)

/-- The final dictionary: a vertex maps to its id `+ 1`. -/
theorem dictOf_vl {x : ℕ} (hx : x ∈ verts g k) : dictOf (vl g k) x = idv g k x + 1 := by
  simp [dictOf, mem_vl.mpr hx, idv]

theorem idv_inj {x y : ℕ} (hx : x ∈ verts g k) (h : idv g k x = idv g k y) : x = y :=
  (List.idxOf_inj (mem_vl.mpr hx)).mp h

end dict

/-! ### Edge keys, edge identifiers, counts and ranks -/

section edges

variable (g : Graph) (k : ℕ)

/-- The distinct edges among the first `q` occurrences, in order of first occurrence. -/
def eprefix (q : ℕ) : List Edge := ((occs g k).take q).eraseDups

/-- The identifier of occurrence `q`: the index of its edge in `edgesOnCycles g k`. -/
def eidOf (q : ℕ) : ℕ := (edgesOnCycles g k).idxOf ((occs g k).getD q (0, 0))

/-- The number of occurrences among the first `q` whose identifier is `e`. -/
def cntF (q e : ℕ) : ℕ := (List.range q).countP fun q' => eidOf g k q' = e

/-- The rank of occurrence `q` among the occurrences of its edge. -/
def rank (q : ℕ) : ℕ := cntF g k q (eidOf g k q)

/-- The number of the variable `s_{e,1}` for the edge with identifier `e`: `kt` plus the sum of
`p - 1` over the earlier edges. -/
def offF (e : ℕ) : ℕ :=
  k * (cycles g k).length + ((List.range e).map fun e' => cntF g k (k * (cycles g k).length) e' - 1).sum

variable {g k}

theorem edgesOnCycles_eq : edgesOnCycles g k = (occs g k).eraseDups := rfl

theorem eprefix_full : eprefix g k (k * (cycles g k).length) = edgesOnCycles g k := by
  rw [eprefix, ← length_occs, List.take_length]; rfl

theorem eprefix_succ {q : ℕ} (hq : q < k * (cycles g k).length) :
    eprefix g k (q + 1) = ext (eprefix g k q) ((occs g k).getD q (0, 0)) := by
  have hq' : q < (occs g k).length := by rw [length_occs]; exact hq
  unfold eprefix
  rw [List.take_add_one, List.getElem?_eq_getElem hq', Option.toList_some,
    eraseDups_append_singleton, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq',
    Option.getD_some]

theorem mem_eprefix {q : ℕ} {e : Edge} (he : e ∈ eprefix g k q) : e ∈ occs g k := by
  simp only [eprefix, List.mem_eraseDups] at he
  exact List.mem_of_mem_take he

theorem length_eprefix_le (q : ℕ) : (eprefix g k q).length ≤ q :=
  (length_eraseDups_le _).trans (List.length_take_le _ _)

/-- `eprefix q` is a prefix of `edgesOnCycles g k`. -/
theorem eprefix_prefix (q : ℕ) : ∃ L, edgesOnCycles g k = eprefix g k q ++ L := by
  refine ⟨(((occs g k).drop q).removeAll ((occs g k).take q)).eraseDups, ?_⟩
  rw [edgesOnCycles_eq, eprefix, ← List.eraseDups_append, List.take_append_drop]

theorem idxOf_edgesOnCycles {q : ℕ} {e : Edge} (he : e ∈ eprefix g k q) :
    (edgesOnCycles g k).idxOf e = (eprefix g k q).idxOf e := by
  obtain ⟨L, hL⟩ := eprefix_prefix (g := g) (k := k) q
  rw [hL, List.idxOf_append_of_mem he]

theorem mem_edgesOnCycles_iff {e : Edge} : e ∈ edgesOnCycles g k ↔ e ∈ occs g k := List.mem_eraseDups

theorem occs_getD_mem_eoc {q : ℕ} (hq : q < k * (cycles g k).length) :
    (occs g k).getD q (0, 0) ∈ edgesOnCycles g k :=
  mem_edgesOnCycles_iff.mpr (occs_getD_mem hq)

theorem eidOf_lt {q : ℕ} (hq : q < k * (cycles g k).length) : eidOf g k q < (edgesOnCycles g k).length :=
  List.idxOf_lt_length_of_mem (occs_getD_mem_eoc hq)

theorem eidOf_eq_iff {q q' : ℕ} (hq : q < k * (cycles g k).length) :
    eidOf g k q = eidOf g k q' ↔ (occs g k).getD q (0, 0) = (occs g k).getD q' (0, 0) :=
  List.idxOf_inj (occs_getD_mem_eoc hq)

theorem cntF_zero : cntF g k 0 = fun _ => 0 := by funext e; simp [cntF]

theorem cntF_succ (q : ℕ) :
    cntF g k (q + 1) = Function.update (cntF g k q) (eidOf g k q) (cntF g k q (eidOf g k q) + 1) := by
  funext e
  by_cases he : e = eidOf g k q
  · subst he; simp [cntF, List.range_succ, List.countP_append]
  · rw [Function.update_of_ne he]
    simp [cntF, List.range_succ, List.countP_append, Ne.symm he]

theorem cntF_le (q e : ℕ) : cntF g k q e ≤ q := by
  unfold cntF
  exact (List.countP_le_length).trans (by simp)

/-- The occurrences of the edge with identifier `eidOf q` among the first `q'` occurrences. -/
theorem cntF_eidOf (q q' : ℕ) (hq : q < k * (cycles g k).length) (hq' : q' ≤ k * (cycles g k).length) :
    cntF g k q' (eidOf g k q) = ((occs g k).take q').count ((occs g k).getD q (0, 0)) := by
  unfold cntF
  rw [List.count, ← map_getD_range ((occs g k).take q') (0, 0), List.countP_map]
  have hl : ((occs g k).take q').length = q' := by
    rw [List.length_take, length_occs]; omega
  rw [hl]
  apply List.countP_congr
  intro q'' hq''
  have hq''' := List.mem_range.mp hq''
  have e1 : ((occs g k).take q').getD q'' (0, 0) = (occs g k).getD q'' (0, 0) := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hq''']
  simp only [Function.comp_apply, e1, beq_iff_eq, decide_eq_true_eq]
  rw [eq_comm, eidOf_eq_iff hq, eq_comm]

/-! #### The cycles through an edge -/

theorem sum_indicator {α : Type} (l : List α) (p : α → Bool) :
    (l.map fun x => if p x then 1 else 0).sum = l.countP p := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, ih, List.countP_cons]
    by_cases h : p a <;> simp [h]
    omega

theorem count_occs (e : Edge) : (occs g k).count e = (cyclesThrough g k e).length := by
  rw [occs, List.count_flatMap, cyclesThrough, ← List.countP_eq_length_filter,
    ← sum_indicator]
  conv_lhs => rw [← map_getD_range (cycles g k) []]
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hc := kCycle_isCycle g (List.mem_range.mp hi)
  simp only [Function.comp_apply]
  change (cycleEdges (kCycle g k i)).count e = _
  rw [List.Nodup.count hc.edges_nodup]
  simp

/-- The final count of an identifier is the number of cycles through its edge. -/
theorem cntF_final {q : ℕ} (hq : q < k * (cycles g k).length) :
    cntF g k (k * (cycles g k).length) (eidOf g k q) =
      (cyclesThrough g k ((occs g k).getD q (0, 0))).length := by
  rw [cntF_eidOf q _ hq le_rfl, ← length_occs, List.take_length, count_occs]

/-- Every identifier occurs. -/
theorem cntF_final_pos {e : ℕ} (he : e < (edgesOnCycles g k).length) :
    1 ≤ cntF g k (k * (cycles g k).length) e := by
  have hmem := List.getElem_mem he
  have hocc := mem_edgesOnCycles_iff.mp hmem
  obtain ⟨q, hq, hqe⟩ := List.getElem_of_mem hocc
  rw [length_occs] at hq
  have hid : eidOf g k q = e := by
    unfold eidOf
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [length_occs]; exact hq)]
    simp only [Option.getD_some, hqe]
    exact (edgesOnCycles_nodup g k).idxOf_getElem e he
  rw [← hid]
  unfold cntF
  apply List.countP_pos_iff.mpr
  exact ⟨q, List.mem_range.mpr hq, by simp⟩

theorem filter_range_split (p : ℕ → Bool) {i t : ℕ} (hi : i < t) :
    (List.range t).filter p = (List.range i).filter p ++ (List.range' i (t - i)).filter p := by
  rw [← List.filter_append]
  congr 1
  have h := @List.range'_append_1 0 i (t - i)
  rw [Nat.zero_add, show i + (t - i) = t by omega] at h
  rw [List.range_eq_range', List.range_eq_range', h]

/-- The position of `C_i` among the cycles through an edge `e` of `C_i` is the number of earlier
cycles through `e`. -/
theorem cyclesThrough_getD_count (e : Edge) {i : ℕ} (hi : i < (cycles g k).length)
    (he : e ∈ cycleEdges (kCycle g k i)) :
    (cyclesThrough g k e).getD ((List.range i).countP fun i' => (cycleEdges (kCycle g k i')).contains e) 0 = i ∧
      (List.range i).countP (fun i' => (cycleEdges (kCycle g k i')).contains e) < (cyclesThrough g k e).length := by
  unfold cyclesThrough
  rw [filter_range_split _ hi, List.countP_eq_length_filter,
    show (cycles g k).length - i = (((cycles g k).length - i - 1) + 1) by omega, List.range'_succ,
    List.filter_cons_of_pos (by simpa using he)]
  constructor
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl, Nat.sub_self]; rfl
  · simp

/-- **The rank of an occurrence**: occurrence `q = ik + j` is the `rank q`-th occurrence of its
edge, and `C_i` is the `rank q`-th cycle through it. -/
theorem rank_spec {q : ℕ} (hq : q < k * (cycles g k).length) (hk : 0 < k) :
    (cyclesThrough g k ((occs g k).getD q (0, 0))).getD (rank g k q) 0 = q / k ∧
      rank g k q < (cyclesThrough g k ((occs g k).getD q (0, 0))).length := by
  obtain ⟨hi, hj, hqe⟩ := occ_decomp hk hq
  set i := q / k
  set j := q % k
  set e := (occs g k).getD q (0, 0)
  have hc := kCycle_isCycle g hi
  have heq : e = cycleEdgeAt g k i j := by
    simp only [e]; rw [hqe]; exact occs_getD_cycleEdgeAt hi hj
  have he : e ∈ cycleEdges (kCycle g k i) := heq ▸ cycleEdgeAt_mem hi hj
  have hr : rank g k q = (List.range i).countP fun i' => (cycleEdges (kCycle g k i')).contains e := by
    unfold rank
    rw [cntF_eidOf q q hq hq.le]
    show List.count e (List.take q (occs g k)) = _
    have htake : (occs g k).take q = ((cycles g k).take i).flatMap cycleEdges ++
        (cycleEdges (kCycle g k i)).take j := by
      rw [hqe, occs, List.flatMap_def, take_flatten_uniform _ _ (by simpa using hi) hj.le,
        List.flatMap_def, ← List.map_take]
      · congr 2
        unfold kCycle
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_eq_getElem hi]; rfl
      · intro l hl
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hl
        exact (enumerated_isCycle hc).edge_length
    rw [htake, List.count_append]
    have h2 : ((cycleEdges (kCycle g k i)).take j).count e = 0 := by
      apply List.count_eq_zero.mpr
      intro hm
      obtain ⟨j', hj', hje⟩ := List.getElem_of_mem hm
      simp only [List.length_take, hc.edge_length] at hj'
      rw [List.getElem_take] at hje
      have : (cycleEdges (kCycle g k i)).getD j' (0, 0) = cycleEdgeAt g k i j := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hc.edge_length]; omega)]
        simp [hje, heq]
      have := edgeAt_inj hc (by omega) hj this
      omega
    rw [h2, Nat.add_zero, List.count_flatMap, ← sum_indicator]
    have hti : ((cycles g k).take i) = (List.range i).map (kCycle g k) := by
      apply List.ext_getElem
      · simp; omega
      · intro n h1 h2
        simp only [List.getElem_take, List.getElem_map, List.getElem_range, kCycle]
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp at h1; omega)]; rfl
    rw [hti, List.map_map]
    congr 1
    apply List.map_congr_left
    intro i' hi'
    have hc' := kCycle_isCycle g (by have := List.mem_range.mp hi'; omega : i' < (cycles g k).length)
    simp only [Function.comp_apply]
    rw [List.Nodup.count hc'.edges_nodup]
    by_cases hm : e ∈ cycleEdges (kCycle g k i') <;> simp [hm]
  rw [hr]
  exact cyclesThrough_getD_count e hi he

/-! #### Offsets -/

theorem offF_succ (e : ℕ) : offF g k (e + 1) = offF g k e + (cntF g k (k * (cycles g k).length) e - 1) := by
  simp only [offF, List.range_succ, List.map_append, List.sum_append, List.map_singleton,
    List.sum_singleton]; omega

theorem offF_zero : offF g k 0 = k * (cycles g k).length := by simp [offF]

theorem takeWhile_ne_eq_take {α : Type} [BEq α] [LawfulBEq α] :
    ∀ {L : List α} {a : α}, a ∈ L → L.takeWhile (fun x => x != a) = L.take (L.idxOf a)
  | [], _, h => by simp at h
  | x :: L, a, h => by
    by_cases hx : x = a
    · subst hx; simp
    · have ha : a ∈ L := by simpa [Ne.symm hx] using h
      rw [List.takeWhile_cons_of_pos (by simpa using hx), List.idxOf_cons_ne _ hx, List.take_succ_cons,
        takeWhile_ne_eq_take ha]

/-- The offset of an occurrence's identifier is the number of `s_{e,1}`. -/
theorem offF_eidOf {q : ℕ} (hq : q < k * (cycles g k).length) :
    offF g k (eidOf g k q) = prefixOffset g k ((occs g k).getD q (0, 0)) := by
  unfold offF prefixOffset
  rw [takeWhile_ne_eq_take (occs_getD_mem_eoc hq)]
  congr 1
  have hlt := eidOf_lt hq
  rw [show (edgesOnCycles g k).idxOf ((occs g k).getD q (0, 0)) = eidOf g k q from rfl]
  rw [← map_getD_range ((edgesOnCycles g k).take (eidOf g k q)) (0, 0), List.map_map,
    List.length_take, Nat.min_eq_left hlt.le]
  congr 1
  apply List.map_congr_left
  intro e' he'
  have he'l := List.mem_range.mp he'
  simp only [Function.comp_apply]
  have hgd : ((edgesOnCycles g k).take (eidOf g k q)).getD e' (0, 0) = (edgesOnCycles g k)[e'] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt he'l, List.getElem?_eq_getElem (by omega)]
    rfl
  rw [hgd]
  -- the identifier `e'` is that of an occurrence of the edge `(edgesOnCycles g k)[e']`
  have hmem := mem_edgesOnCycles_iff.mp (List.getElem_mem (show e' < (edgesOnCycles g k).length by omega))
  obtain ⟨q', hq', hq'e⟩ := List.getElem_of_mem hmem
  rw [length_occs] at hq'
  have hgd' : (occs g k).getD q' (0, 0) = (edgesOnCycles g k)[e'] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [length_occs]; exact hq')]
    exact congrArg (Option.getD · (0, 0)) (congrArg some hq'e)
  have hid : eidOf g k q' = e' := by
    unfold eidOf; rw [hgd']; exact (edgesOnCycles_nodup g k).idxOf_getElem e' (by omega)
  have hf := cntF_final (g := g) (k := k) hq'
  rw [hid, hgd'] at hf
  rw [hf]

end edges

/-! ### The id pairs of the occurrences and their first-occurrence identifiers -/

section pairs

/-- `eraseDups` commutes with a map that is injective on the list. -/
theorem eraseDups_map_injOn {α β : Type} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β] (f : α → β) :
    ∀ (l : List α), (∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) →
      (l.map f).eraseDups = l.eraseDups.map f := by
  intro l
  induction l using List.reverseRecOn with
  | nil => intro _; rfl
  | append_singleton l a ih =>
    intro h
    rw [List.map_append, List.map_singleton, eraseDups_append_singleton, eraseDups_append_singleton,
      ih (fun x hx y hy => h x (by simp [hx]) y (by simp [hy]))]
    unfold ext
    by_cases ha : a ∈ l.eraseDups
    · have : f a ∈ l.eraseDups.map f := List.mem_map_of_mem ha
      simp [ha, this]
    · have : f a ∉ l.eraseDups.map f := by
        intro hm
        obtain ⟨y, hy, hya⟩ := List.mem_map.mp hm
        have hyl := List.mem_eraseDups.mp hy
        exact ha (by rw [← h y (by simp [hyl]) a (by simp) hya]; exact hy)
      simp [ha, this]

/-- The index of an image, for a map injective at the element. -/
theorem idxOf_map_injOn {α β : Type} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β] (f : α → β)
    {x : α} : ∀ (L : List α), (∀ y ∈ L, f y = f x → y = x) → (L.map f).idxOf (f x) = L.idxOf x
  | [], _ => by simp
  | a :: L, h => by
    by_cases hax : a = x
    · subst hax; simp
    · have hf : f a ≠ f x := fun he => hax (h a (by simp) he)
      rw [List.map_cons, List.idxOf_cons_ne _ hf, List.idxOf_cons_ne _ hax,
        idxOf_map_injOn f L (fun y hy => h y (by simp [hy]))]

/-- The first-occurrence identifiers do not change under a map injective on the list. -/
theorem eids_map_injOn {α β : Type} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β] (f : α → β)
    (l : List α) (h : ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) :
    PairIds.eids (l.map f) = PairIds.eids l := by
  unfold PairIds.eids
  rw [eraseDups_map_injOn f l h, List.map_map]
  apply List.map_congr_left
  intro x hx
  exact idxOf_map_injOn f _ fun y hy hyx => h y (List.mem_eraseDups.mp hy) x hx hyx

variable (g : Graph) (k : ℕ)

/-- The pair of vertex ids of an edge. -/
def idPr (e : Edge) : ℕ × ℕ := (idv g k e.1, idv g k e.2)

/-- The id pairs of the occurrences, in order (the input of `PairIds.pairIds`). -/
def prs : List (ℕ × ℕ) := (occs g k).map (idPr g k)

variable {g k}

theorem length_prs : (prs g k).length = k * (cycles g k).length := by
  rw [prs, List.length_map, length_occs]

theorem prs_below : ∀ p ∈ prs g k, p.1 < nV g k ∧ p.2 < nV g k := by
  intro p hp
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hp
  exact ⟨idv_lt (occs_mem_verts he).1, idv_lt (occs_mem_verts he).2⟩

/-- The id pair is injective on the edges of the cycles. -/
theorem idPr_inj : ∀ e ∈ occs g k, ∀ e' ∈ occs g k, idPr g k e = idPr g k e' → e = e' := by
  intro e he e' _ h
  simp only [idPr, Prod.mk.injEq] at h
  exact Prod.ext (idv_inj (occs_mem_verts he).1 h.1) (idv_inj (occs_mem_verts he).2 h.2)

theorem eids_occs :
    PairIds.eids (occs g k) = (List.range (k * (cycles g k).length)).map (eidOf g k) := by
  apply List.ext_getElem
  · simp [length_occs]
  · intro q h₁ h₂
    simp only [PairIds.eids, List.getElem_map, List.getElem_range, eidOf, edgesOnCycles_eq]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using h₁), Option.getD_some]

/-- **The identifiers of the id pairs are the edge identifiers** `eidOf`. -/
theorem eids_prs :
    PairIds.eids (prs g k) = (List.range (k * (cycles g k).length)).map (eidOf g k) := by
  rw [prs, eids_map_injOn _ _ idPr_inj, eids_occs]

/-- The class sizes of the identifiers are the counts `cntF`. -/
theorem count_eids_prs (e : ℕ) :
    (PairIds.eids (prs g k)).count e = cntF g k (k * (cycles g k).length) e := by
  rw [eids_prs, List.count, List.countP_map, cntF]
  apply List.countP_congr
  intro q _
  simp

/-- The number of distinct id pairs is the number of distinct edges. -/
theorem length_eraseDups_prs : (prs g k).eraseDups.length = (edgesOnCycles g k).length := by
  rw [prs, eraseDups_map_injOn _ _ idPr_inj, List.length_map]; rfl

/-- The first ids, occurrence by occurrence. -/
theorem map_fst_prs : (List.range (k * (cycles g k).length)).map
    (fun q => idv g k ((occs g k).getD q (0, 0)).1) = (prs g k).map Prod.fst := by
  apply List.ext_getElem
  · simp [length_prs]
  · intro q h₁ _
    simp only [List.getElem_map, List.getElem_range, prs, idPr]
    rw [List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by simp at h₁; rw [length_occs]; exact h₁), Option.getD_some]

/-- The second ids, occurrence by occurrence. -/
theorem map_snd_prs : (List.range (k * (cycles g k).length)).map
    (fun q => idv g k ((occs g k).getD q (0, 0)).2) = (prs g k).map Prod.snd := by
  apply List.ext_getElem
  · simp [length_prs]
  · intro q h₁ _
    simp only [List.getElem_map, List.getElem_range, prs, idPr]
    rw [List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by simp at h₁; rw [length_occs]; exact h₁), Option.getD_some]

end pairs

/-! ### The labels of the cycles are labels of the graph -/

section labels

variable {g k}

theorem occs_mem_graph {e : Edge} (he : e ∈ occs g k) : e ∈ g := by
  simp only [occs, List.mem_flatMap] at he
  obtain ⟨c, hc, he⟩ := he
  exact (enumerated_isCycle hc).2.2.2 e he

theorem foldl_max_le {l : List ℕ} {a B : ℕ} (ha : a ≤ B) (h : ∀ x ∈ l, x ≤ B) : l.foldl max a ≤ B := by
  induction l generalizing a with
  | nil => simpa
  | cons x l ih =>
    simp only [List.foldl_cons]
    exact ih (max_le ha (h x (by simp))) (fun y hy => h y (by simp [hy]))

/-- Every vertex of an enumerated cycle is a label of `g`. -/
theorem verts_le_maxLab {x : ℕ} (hx : x ∈ verts g k) : x ≤ maxLab g := by
  obtain ⟨q, hq, rfl⟩ := List.getElem_of_mem hx
  have hq' : q < k * (cycles g k).length := by rw [← length_verts]; exact hq
  have hk : 0 < k := Nat.pos_of_ne_zero fun h => by subst h; simp at hq'
  obtain ⟨hi, hj, hqe⟩ := occ_decomp hk hq'
  have he := occs_getD (g := g) (k := k) hi hj
  rw [← hqe] at he
  have hmem := occs_mem_graph (occs_getD_mem hq')
  rw [he] at hmem
  set y := (verts g k).getD (q / k * k + next k (q % k)) 0
  have hxq : (verts g k).getD q 0 = (verts g k)[q] := getD_eq_getElem' hq
  rw [hxq] at hmem
  have h1 : (edge (verts g k)[q] y).1 ∈ ents g := List.mem_flatMap.mpr ⟨_, hmem, by simp⟩
  have h2 : (edge (verts g k)[q] y).2 ∈ ents g := List.mem_flatMap.mpr ⟨_, hmem, by simp⟩
  have l1 := le_maxLab h1
  have l2 := le_maxLab h2
  simp only [edge] at l1 l2
  omega

/-- **The dictionary of the cycle labels fits in `labelBound g`.** -/
theorem maxV_lt_labelBound : maxV g k < labelBound g := by
  rw [labelBound_eq]
  have := foldl_max_le (l := verts g k) (Nat.zero_le (maxLab g)) fun x hx => verts_le_maxLab hx
  unfold maxV; omega

end labels

end STACS2027.Runtimes.ZeroCost

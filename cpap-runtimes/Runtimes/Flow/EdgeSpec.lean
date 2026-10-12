module

public import Runtimes.Flow.Four
public import BoundedCost.CyclePositions
public import Outerplanar.RAM.R0Spec
public import Outerplanar.RAM.PairIdsRank
public import Runtimes.ZeroCostSpec
import Mathlib.Tactic

/-!
# The edge pass of the network construction: the abstract side

The construction machines receive a list `cs` of simple `k`-cycles as the list `verts cs` of
their vertices, cycle after cycle. Occurrence `q = i k + j` (`i < t`, `j < k`) is the edge at
position `j` of `C_i`: `(occs cs).getD q = edge (verts[q]) (verts[ik + next k j])`
(`occs_getD`). The edge pass assigns to every occurrence the identifier `eid cs q` of its edge
— its index in `eList cs` (first occurrences first) — and counts the occurrences of every
identifier (`cntF`); finally `cntF … r = wcount cs (eList cs)[r]` = `ϖ(e)` (`cntF_final`).

**The identifiers** are computed as in Corollary 5, with no
table indexed by pairs of labels: a label dictionary (`M + 1` cells, `M = maxV cs`, below
`labelBound g`: `maxV_lt_labelBound`) gives every vertex its id `idv cs x` (its position in
`vl cs`, the vertices in order of first appearance), and outerplanar package's module `PairIds.pairIds`
numbers the id pairs `prs cs` of the occurrences by first occurrence. As the id pair is
injective on the edges of the cycles (`idPr_inj`), these numbers are the `eid cs q`
(`eids_prs`) and their class sizes the counts `cntF` (`count_eids_prs`).
-/

@[expose] public section

namespace STACS2027.Runtimes.Flow

open STACS2027 STACS2027.RAM STACS2027.RAM.R0

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

theorem occ_lt {k i j t : ℕ} (hi : i < t) (hj : j < k) : i * k + j < k * t := by
  have : (i + 1) * k ≤ t * k := Nat.mul_le_mul_right k hi
  rw [Nat.add_mul, one_mul] at this; rw [Nat.mul_comm k]; omega

/-! ### Vertices and occurrences -/

/-- The vertices of the cycles, cycle after cycle (the cycle part of the machines' input). -/
def verts (cs : List Cycle) : List ℕ := cs.flatten

section occ

variable {g : Graph} {k : ℕ} {cs : List Cycle}

theorem length_verts (hcs : ∀ c ∈ cs, IsCycle g k c) : (verts cs).length = k * cs.length :=
  length_flatten_uniform _ fun c hc => (hcs c hc).2.1

theorem verts_getD (hcs : ∀ c ∈ cs, IsCycle g k c) {i j : ℕ} (hi : i < cs.length) (hj : j < k) :
    (verts cs).getD (i * k + j) 0 = (cyc cs i).getD j 0 :=
  getD_flatten_uniform 0 _ (fun c hc => (hcs c hc).2.1) hi hj

theorem occs_getD_cyc (hcs : ∀ c ∈ cs, IsCycle g k c) {i j : ℕ} (hi : i < cs.length) (hj : j < k) :
    (occs cs).getD (i * k + j) (0, 0) = (cycleEdges (cyc cs i)).getD j (0, 0) := by
  rw [occs, List.flatMap_def, getD_flatten_uniform (0, 0) _ (k := k) _ (by simpa using hi) hj]
  · congr 1
    simp only [cyc, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi,
      Option.map_some, Option.getD_some]
  · intro l hl
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hl
    exact (hcs c hc).edge_length

/-- The edge of occurrence `ik + j`, read from the vertices. -/
theorem occs_getD (hcs : ∀ c ∈ cs, IsCycle g k c) {i j : ℕ} (hi : i < cs.length) (hj : j < k) :
    (occs cs).getD (i * k + j) (0, 0) =
      edge ((verts cs).getD (i * k + j) 0) ((verts cs).getD (i * k + next k j) 0) := by
  have hc : IsCycle g k (cyc cs i) := hcs _ (cyc_mem hi)
  have hk := hc.1
  rw [occs_getD_cyc hcs hi hj, verts_getD hcs hi hj, verts_getD hcs hi (next_lt (by omega)),
    cycleEdges_getD (by rw [hc.2.1]; omega) (by rw [hc.2.1]; exact hj), hc.2.1]

theorem occs_getD_mem {q : ℕ} (hq : q < (occs cs).length) : (occs cs).getD q (0, 0) ∈ occs cs := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq]
  exact List.getElem_mem _

theorem pathEdges_mem' {l : List ℕ} {e : Edge} (he : e ∈ pathEdges l) : e.1 ∈ l ∧ e.2 ∈ l := by
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
theorem occs_mem_verts {e : Edge} (he : e ∈ occs cs) : e.1 ∈ verts cs ∧ e.2 ∈ verts cs := by
  simp only [occs, List.mem_flatMap] at he
  obtain ⟨c, hc, he⟩ := he
  have h := pathEdges_mem' he
  have hsub : ∀ x ∈ c ++ c.take 1, x ∈ verts cs := by
    intro x hx
    simp only [List.mem_append] at hx
    have hx' : x ∈ c := hx.elim id (fun h => List.mem_of_mem_take h)
    exact List.mem_flatten.mpr ⟨c, hc, hx'⟩
  exact ⟨hsub _ h.1, hsub _ h.2⟩

/-- An occurrence is ordered: its smaller end first. -/
theorem occs_ordered {e : Edge} (he : e ∈ occs cs) : e.1 ≤ e.2 := by
  simp only [occs, List.mem_flatMap] at he
  obtain ⟨c, _, he⟩ := he
  unfold cycleEdges at he
  generalize c ++ c.take 1 = l at he
  induction l with
  | nil => simp [pathEdges] at he
  | cons a l ih =>
    cases l with
    | nil => simp [pathEdges] at he
    | cons b rest =>
      simp only [pathEdges, List.mem_cons] at he
      rcases he with rfl | he
      · simp only [edge]; omega
      · exact ih he

end occ

/-! ### The largest label -/

/-- The largest vertex label of the cycles. -/
def maxV (cs : List Cycle) : ℕ := (verts cs).foldl max 0

theorem le_maxV {cs : List Cycle} {x : ℕ} (hx : x ∈ verts cs) : x ≤ maxV cs := le_foldl_max hx 0

theorem occs_le_maxV {cs : List Cycle} {e : Edge} (he : e ∈ occs cs) :
    e.1 ≤ maxV cs ∧ e.2 ≤ maxV cs :=
  ⟨le_maxV (occs_mem_verts he).1, le_maxV (occs_mem_verts he).2⟩

/-! ### Edge identifiers and counts -/

section ids

variable {cs : List Cycle}

/-- The identifier of occurrence `q`: the index of its edge in `eList cs`. -/
def eid (cs : List Cycle) (q : ℕ) : ℕ := (eList cs).idxOf ((occs cs).getD q (0, 0))

/-- The number of occurrences among the first `q` whose identifier is `r`. -/
def cntF (cs : List Cycle) (q r : ℕ) : ℕ := (List.range q).countP fun q' => eid cs q' = r

theorem eid_lt {q : ℕ} (hq : q < (occs cs).length) : eid cs q < (eList cs).length :=
  List.idxOf_lt_length_of_mem (mem_eList_occs.mpr (occs_getD_mem hq))

theorem cntF_zero : cntF cs 0 = fun _ => 0 := by funext r; simp [cntF]

theorem cntF_succ (q : ℕ) :
    cntF cs (q + 1) = Function.update (cntF cs q) (eid cs q) (cntF cs q (eid cs q) + 1) := by
  funext r
  by_cases hr : r = eid cs q
  · subst hr; simp [cntF, List.range_succ, List.countP_append]
  · rw [Function.update_of_ne hr]
    simp [cntF, List.range_succ, List.countP_append, Ne.symm hr]

theorem cntF_le (q r : ℕ) : cntF cs q r ≤ q := by
  unfold cntF
  exact (List.countP_le_length).trans (by simp)

/-- **The final counts** are the multiplicities `ϖ(e)`. -/
theorem cntF_final (hn : ∀ c ∈ cs, (cycleEdges c).Nodup) {r : ℕ} (hr : r < (eList cs).length) :
    cntF cs (occs cs).length r = wcount cs ((eList cs).getD r (0, 0)) := by
  rw [wcount_eq_count hn, cntF, List.count]
  conv_rhs => rw [← map_getD_range (occs cs) (0, 0)]
  rw [List.countP_map]
  apply List.countP_congr
  intro q hq
  have hq' := List.mem_range.mp hq
  have hm : (occs cs).getD q (0, 0) ∈ eList cs := mem_eList_occs.mpr (occs_getD_mem hq')
  have hget : (eList cs).getD r (0, 0) = (eList cs)[r] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr]; rfl
  have key : eid cs q = r ↔ (occs cs).getD q (0, 0) = (eList cs)[r] := by
    unfold eid
    constructor
    · intro h
      rw [← List.getElem_idxOf (List.idxOf_lt_length_of_mem hm)]
      simp only [h]
    · intro h
      rw [h]; exact (eList_nodup cs).idxOf_getElem r hr
  simp only [Function.comp_apply, beq_iff_eq, decide_eq_true_eq, hget]
  exact key

end ids

/-! ### The vertex dictionary and the id pairs -/

section dict

variable {g : Graph} {k : ℕ} {cs : List Cycle}

/-- The vertices of the first `q` entries of the cycle part, in order of first appearance. -/
def vprefix (cs : List Cycle) (q : ℕ) : List ℕ := ((verts cs).take q).eraseDups

/-- All the vertices of the cycles, in order of first appearance. -/
def vl (cs : List Cycle) : List ℕ := (verts cs).eraseDups

/-- The number of vertices of the cycles. -/
def nV (cs : List Cycle) : ℕ := (vl cs).length

/-- The id of a vertex: its position in `vl`. -/
def idv (cs : List Cycle) (x : ℕ) : ℕ := (vl cs).idxOf x

theorem vprefix_succ {q : ℕ} (hq : q < (verts cs).length) :
    vprefix cs (q + 1) = ext (vprefix cs q) ((verts cs).getD q 0) := by
  unfold vprefix
  rw [List.take_add_one, List.getElem?_eq_getElem hq, Option.toList_some,
    eraseDups_append_singleton, getD_eq_getElem' hq]

theorem vprefix_full (hcs : ∀ c ∈ cs, IsCycle g k c) : vprefix cs (k * cs.length) = vl cs := by
  rw [vprefix, ← length_verts hcs, List.take_length]; rfl

theorem length_vprefix_le (q : ℕ) : (vprefix cs q).length ≤ q :=
  (STACS2027.length_eraseDups_le _).trans (List.length_take_le _ _)

theorem nV_le (hcs : ∀ c ∈ cs, IsCycle g k c) : nV cs ≤ k * cs.length := by
  have := length_vprefix_le (cs := cs) (k * cs.length)
  rwa [vprefix_full hcs] at this

theorem mem_vl {x : ℕ} : x ∈ vl cs ↔ x ∈ verts cs := List.mem_eraseDups

theorem idv_lt {x : ℕ} (hx : x ∈ verts cs) : idv cs x < nV cs :=
  List.idxOf_lt_length_of_mem (mem_vl.mpr hx)

/-- The final dictionary: a vertex maps to its id `+ 1`. -/
theorem dictOf_vl {x : ℕ} (hx : x ∈ verts cs) : dictOf (vl cs) x = idv cs x + 1 := by
  simp [dictOf, mem_vl.mpr hx, idv]

theorem idv_inj {x y : ℕ} (hx : x ∈ verts cs) (h : idv cs x = idv cs y) : x = y :=
  (List.idxOf_inj (mem_vl.mpr hx)).mp h

theorem verts_getD_mem (hcs : ∀ c ∈ cs, IsCycle g k c) {q : ℕ} (hq : q < k * cs.length) :
    (verts cs).getD q 0 ∈ verts cs := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [length_verts hcs]; exact hq)]
  exact List.getElem_mem _

/-- Decomposing an occurrence number. -/
theorem occ_decomp {q : ℕ} (hk : 0 < k) (hq : q < k * cs.length) :
    q / k < cs.length ∧ q % k < k ∧ q = q / k * k + q % k := by
  refine ⟨?_, Nat.mod_lt _ hk, (Nat.div_add_mod' q k).symm⟩
  rw [Nat.div_lt_iff_lt_mul hk, Nat.mul_comm]; exact hq

/-- The pair of vertex ids of an edge. -/
def idPr (cs : List Cycle) (e : Edge) : ℕ × ℕ := (idv cs e.1, idv cs e.2)

/-- The id pairs of the occurrences, in order (the input of `PairIds.pairIds`). -/
def prs (cs : List Cycle) : List (ℕ × ℕ) := (occs cs).map (idPr cs)

theorem length_prs (hcs : ∀ c ∈ cs, IsCycle g k c) : (prs cs).length = k * cs.length := by
  rw [prs, List.length_map, length_occs hcs]

theorem prs_below : ∀ p ∈ prs cs, p.1 < nV cs ∧ p.2 < nV cs := by
  intro p hp
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hp
  exact ⟨idv_lt (occs_mem_verts he).1, idv_lt (occs_mem_verts he).2⟩

/-- The id pair is injective on the edges of the cycles. -/
theorem idPr_inj : ∀ e ∈ occs cs, ∀ e' ∈ occs cs, idPr cs e = idPr cs e' → e = e' := by
  intro e he e' _ h
  simp only [idPr, Prod.mk.injEq] at h
  exact Prod.ext (idv_inj (occs_mem_verts he).1 h.1) (idv_inj (occs_mem_verts he).2 h.2)

theorem eids_occs (hcs : ∀ c ∈ cs, IsCycle g k c) :
    PairIds.eids (occs cs) = (List.range (k * cs.length)).map (eid cs) := by
  apply List.ext_getElem
  · simp [length_occs hcs]
  · intro q h₁ h₂
    simp only [PairIds.eids, List.getElem_map, List.getElem_range, eid, eList]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using h₁), Option.getD_some]

/-- **The identifiers of the id pairs are the edge identifiers** `eid`. -/
theorem eids_prs (hcs : ∀ c ∈ cs, IsCycle g k c) :
    PairIds.eids (prs cs) = (List.range (k * cs.length)).map (eid cs) := by
  rw [prs, ZeroCost.eids_map_injOn _ _ idPr_inj, eids_occs hcs]

/-- The class sizes of the identifiers are the counts `cntF`. -/
theorem count_eids_prs (hcs : ∀ c ∈ cs, IsCycle g k c) (e : ℕ) :
    (PairIds.eids (prs cs)).count e = cntF cs (k * cs.length) e := by
  rw [eids_prs hcs, List.count, List.countP_map, cntF]
  apply List.countP_congr
  intro q _
  simp

/-- The number of distinct id pairs is the number of distinct edges. -/
theorem length_eraseDups_prs : (prs cs).eraseDups.length = (eList cs).length := by
  rw [prs, ZeroCost.eraseDups_map_injOn _ _ idPr_inj, List.length_map]; rfl

/-- The first ids, occurrence by occurrence. -/
theorem map_fst_prs (hcs : ∀ c ∈ cs, IsCycle g k c) : (List.range (k * cs.length)).map
    (fun q => idv cs ((occs cs).getD q (0, 0)).1) = (prs cs).map Prod.fst := by
  apply List.ext_getElem
  · simp [length_prs hcs]
  · intro q h₁ _
    simp only [List.getElem_map, List.getElem_range, prs, idPr]
    rw [List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by simp at h₁; rw [length_occs hcs]; exact h₁), Option.getD_some]

/-- The second ids, occurrence by occurrence. -/
theorem map_snd_prs (hcs : ∀ c ∈ cs, IsCycle g k c) : (List.range (k * cs.length)).map
    (fun q => idv cs ((occs cs).getD q (0, 0)).2) = (prs cs).map Prod.snd := by
  apply List.ext_getElem
  · simp [length_prs hcs]
  · intro q h₁ _
    simp only [List.getElem_map, List.getElem_range, prs, idPr]
    rw [List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by simp at h₁; rw [length_occs hcs]; exact h₁), Option.getD_some]

/-! #### The labels of the cycles are labels of the graph -/

theorem occs_mem_graph (hcs : ∀ c ∈ cs, IsCycle g k c) {e : Edge} (he : e ∈ occs cs) : e ∈ g := by
  simp only [occs, List.mem_flatMap] at he
  obtain ⟨c, hc, he⟩ := he
  exact (hcs c hc).2.2.2 e he

/-- Every vertex of a cycle of `g` is a label of `g`. -/
theorem verts_le_maxLab (hcs : ∀ c ∈ cs, IsCycle g k c) {x : ℕ} (hx : x ∈ verts cs) :
    x ≤ maxLab g := by
  obtain ⟨q, hq, rfl⟩ := List.getElem_of_mem hx
  have hq' : q < k * cs.length := by rw [← length_verts hcs]; exact hq
  have hk : 0 < k := Nat.pos_of_ne_zero fun h => by subst h; simp at hq'
  obtain ⟨hi, hj, hqe⟩ := occ_decomp (cs := cs) hk hq'
  have he := occs_getD hcs hi hj
  rw [← hqe] at he
  have hmem := occs_mem_graph hcs (occs_getD_mem (by rw [length_occs hcs]; exact hq'))
  rw [he] at hmem
  set y := (verts cs).getD (q / k * k + next k (q % k)) 0
  have hxq : (verts cs).getD q 0 = (verts cs)[q] := getD_eq_getElem' hq
  rw [hxq] at hmem
  have h2 : (edge (verts cs)[q] y).2 ∈ ents g := List.mem_flatMap.mpr ⟨_, hmem, by simp⟩
  have l2 := le_maxLab h2
  simp only [edge] at l2
  omega

/-- **The label dictionary fits in `labelBound g`.** -/
theorem maxV_lt_labelBound (hcs : ∀ c ∈ cs, IsCycle g k c) : maxV cs < labelBound g := by
  rw [labelBound_eq]
  have := ZeroCost.foldl_max_le (l := verts cs) (Nat.zero_le (maxLab g))
    fun x hx => verts_le_maxLab hcs hx
  unfold maxV; omega

end dict

end STACS2027.Runtimes.Flow

module

public import Runtimes.C4.Spec
import Runtimes.C4.Buckets
import Mathlib.Tactic

/-!
# Phase ENUM: the inserted prefixes, loop by loop

The generation loops of ENUM write the 2-paths of `ins g pos`
in order: vertex by
vertex (`insPre g v`: the entries of the vertices `u < v`); at a vertex `v` with out-list `l`,
first the type-1 wedges, out-neighbour by out-neighbour (`t1Pre g v a`: those of `l[0..a)`,
`t1In g v a b`: and the first `b` of `l[a]`), then the type-2 wedges, index by index
(`t2Pre g v a`: the pairs `(l[a'], l[b])`, `a' < a`, `t2In g v a b`: and `b ∈ [a + 1, b)`).
Here every list is stated for an arbitrary ranking `pos`.

* the step lemmas (`t1In_succ`, `t1In_full`, `t2In_succ`, `t2In_full`, `insPre_succ`) used to
  move the loop invariants;
* the prefix lemmas (every intermediate list, extended by the next entry, is a prefix of
  `ins g pos`), needed for the writes (`GRep.pre`);
* `wt`: the weight `KW' · |reports L| + KI · |L|` of the telescoping cost bounds of the report
  walk (`EnumScan.lean`), monotone along prefixes (`wt_snoc`, `wt_mono`).
-/

@[expose] public section

namespace STACS2027.Runtimes.C4

open STACS2027 STACS2027.Algo

variable (g : Graph) (pos : ℕ → ℕ)

/-- The insertions of the vertices `u < v`. -/
def insPre (v : ℕ) : Ins := (List.range v).flatMap fun u => (wedges g pos u).map entry

/-- The type-1 insertions `(v, j, k)` of `v` for the out-neighbours `j ∈ l[0..a)`. -/
def t1Pre (v a : ℕ) : Ins :=
  ((outL g pos v).take a).flatMap fun j => (outL g pos j).map fun k => entry (v, j, k)

/-- … and the first `b` out-neighbours `k` of `j = l[a]`. -/
def t1In (v a b : ℕ) : Ins :=
  t1Pre g pos v a ++ ((outL g pos ((outL g pos v).getD a 0)).take b).map fun k =>
    entry (v, (outL g pos v).getD a 0, k)

/-- The type-2 insertions `(l[a], v, l[b])`, `b ∈ [a + 1, |l|)`. -/
def blk2 (v a : ℕ) : Ins :=
  (List.range' (a + 1) ((outL g pos v).length - (a + 1))).map fun b =>
    entry ((outL g pos v).getD a 0, v, (outL g pos v).getD b 0)

/-- The type-2 insertions of `v` for the first indices `a' < a`. -/
def t2Pre (v a : ℕ) : Ins := (List.range a).flatMap fun a' => blk2 g pos v a'

/-- … and `b' ∈ [a + 1, b)` for the index `a`. -/
def t2In (v a b : ℕ) : Ins :=
  t2Pre g pos v a ++ (List.range' (a + 1) (b - (a + 1))).map fun b' =>
    entry ((outL g pos v).getD a 0, v, (outL g pos v).getD b' 0)

variable {g pos}

theorem t1Pre_zero (v : ℕ) : t1Pre g pos v 0 = [] := by simp [t1Pre]
theorem t2Pre_zero (v : ℕ) : t2Pre g pos v 0 = [] := by simp [t2Pre]
theorem t1In_zero (v a : ℕ) : t1In g pos v a 0 = t1Pre g pos v a := by simp [t1In]
theorem t2In_start (v a : ℕ) : t2In g pos v a (a + 1) = t2Pre g pos v a := by simp [t2In]
theorem insPre_zero : insPre g pos 0 = [] := by simp [insPre]
theorem insPre_numV : insPre g pos (numV g) = ins g pos := rfl

theorem t1In_succ {v a b : ℕ} (hb : b < (outL g pos ((outL g pos v).getD a 0)).length) :
    t1In g pos v a (b + 1) = t1In g pos v a b ++
      [entry (v, (outL g pos v).getD a 0, (outL g pos ((outL g pos v).getD a 0)).getD b 0)] := by
  simp only [t1In, List.take_succ_eq_append_getElem hb, List.map_append, List.append_assoc,
    List.map_singleton]
  generalize (outL g pos v).getD a 0 = j at hb ⊢
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hb]

theorem t1In_full {v a : ℕ} (ha : a < (outL g pos v).length) :
    t1In g pos v a (outL g pos ((outL g pos v).getD a 0)).length = t1Pre g pos v (a + 1) := by
  simp only [t1In, t1Pre, List.take_length, List.take_succ_eq_append_getElem ha,
    List.flatMap_append, List.flatMap_singleton]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ha]

theorem t2In_succ {v a b : ℕ} (hab : a + 1 ≤ b) :
    t2In g pos v a (b + 1) = t2In g pos v a b ++
      [entry ((outL g pos v).getD a 0, v, (outL g pos v).getD b 0)] := by
  simp only [t2In, List.append_assoc]
  rw [show b + 1 - (a + 1) = (b - (a + 1)) + 1 by omega, List.range'_1_concat, List.map_append,
    List.map_singleton, show a + 1 + (b - (a + 1)) = b by omega]

theorem t2In_full (v a : ℕ) :
    t2In g pos v a (outL g pos v).length = t2Pre g pos v (a + 1) := by
  simp [t2In, t2Pre, List.range_succ, List.flatMap_append, blk2]

theorem map_wedges1 (v : ℕ) :
    (wedges1 g pos v).map entry = t1Pre g pos v (outL g pos v).length := by
  simp [wedges1, t1Pre, List.map_flatMap, Function.comp_def]

theorem map_wedges2 (v : ℕ) :
    (wedges2 g pos v).map entry = t2Pre g pos v (outL g pos v).length := by
  simp [wedges2, t2Pre, pairsOf, blk2, List.map_flatMap, Function.comp_def]

theorem insPre_succ (v : ℕ) :
    insPre g pos (v + 1) = insPre g pos v ++ t1Pre g pos v (outL g pos v).length ++
      t2Pre g pos v (outL g pos v).length := by
  simp only [insPre, List.range_succ, List.flatMap_append, List.flatMap_singleton, wedges,
    List.map_append, map_wedges1, map_wedges2, List.append_assoc]

/-! ### Prefixes -/

theorem flatMap_prefix {α β : Type*} {l₁ l₂ : List α} (h : l₁ <+: l₂) (f : α → List β) :
    l₁.flatMap f <+: l₂.flatMap f := by
  obtain ⟨t, rfl⟩ := h
  rw [List.flatMap_append]
  exact List.prefix_append _ _

theorem insPre_prefix {v w : ℕ} (h : v ≤ w) : insPre g pos v <+: insPre g pos w :=
  flatMap_prefix (List.prefix_iff_eq_take.mpr (by simp [List.take_range, Nat.min_eq_left h])) _

theorem t1Pre_prefix {v a a' : ℕ} (h : a ≤ a') : t1Pre g pos v a <+: t1Pre g pos v a' :=
  flatMap_prefix (List.take_prefix_take_left h) _

theorem t2Pre_prefix {v a a' : ℕ} (h : a ≤ a') : t2Pre g pos v a <+: t2Pre g pos v a' :=
  flatMap_prefix (List.prefix_iff_eq_take.mpr (by simp [List.take_range, Nat.min_eq_left h])) _

theorem t1In_prefix {v a : ℕ} (ha : a < (outL g pos v).length) (b : ℕ) :
    t1In g pos v a b <+: t1Pre g pos v (a + 1) := by
  rw [← t1In_full ha]
  refine (List.prefix_append_right_inj _).mpr (List.IsPrefix.map _ ?_)
  rw [List.take_length]
  exact List.take_prefix _ _

theorem t2In_prefix {v a b : ℕ} (ha : a < (outL g pos v).length) (hb : b ≤ (outL g pos v).length) :
    t2In g pos v a b <+: t2Pre g pos v (a + 1) := by
  rw [← t2In_full v a]
  refine (List.prefix_append_right_inj _).mpr (List.IsPrefix.map _ ?_)
  by_cases hab : a + 1 ≤ b
  · rw [show (outL g pos v).length - (a + 1) = (b - (a + 1)) + ((outL g pos v).length - b) by
      have := hb; omega, ← List.range'_append_1]
    exact List.prefix_append _ _
  · rw [show b - (a + 1) = 0 by omega]
    exact List.nil_prefix

/-! ### The weight -/

/-- The weight of the telescoping bounds. -/
def wt (KW KI : ℕ) (L : Ins) : ℕ := KW * (reports L).length + KI * L.length

theorem wt_snoc (KW KI : ℕ) (L : Ins) (k : ℕ × ℕ) (z : ℕ) :
    wt KW KI (L ++ [(k, z)]) = wt KW KI L + (KW * (bucket L k).length + KI) := by
  simp only [wt, length_reports_snoc, List.length_append, List.length_singleton]
  ring

theorem wt_mono (KW KI : ℕ) {L L' : Ins} (h : L <+: L') : wt KW KI L ≤ wt KW KI L' := by
  have h1 := length_reports_le_of_prefix h
  have h2 := h.length_le
  simp only [wt]
  gcongr

end STACS2027.Runtimes.C4

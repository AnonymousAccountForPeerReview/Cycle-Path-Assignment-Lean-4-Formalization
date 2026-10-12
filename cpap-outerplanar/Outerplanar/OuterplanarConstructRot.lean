module

public import Outerplanar.OuterplanarConstructSph
public import Mathlib.Data.Nat.Find
import Mathlib.Data.List.GetD
import Mathlib.Tactic

/-!
# Hypermaps from rotation systems

An embedding of a simple graph is given by its rotation system: at every vertex `w` a
cyclic order of the neighbours of `w` (`rot w`, with inverse `rotInv w`). This file builds
the corresponding hypermap on the half-edges of an edge list `es` of natural numbers
(`RotSystem.hypermap`):

* the half-edge `d` goes from `dtail es d` to `dhead es d` (half-edges `2i`, `2i + 1` are the
  two ends of edge `i`), and a simple edge list (`SimpleList`) has at most one half-edge from
  `u` to `v` (`dart_inj`), found by `findDart`;
* `edge` is the pairing `2i ↔ 2i + 1`; `node d` is the half-edge from `dtail d` to the next
  neighbour `rot (dtail d) (dhead d)`; `face d` is the half-edge from `dhead d` to
  `rotInv (dhead d) (dtail d)`.

It proves the edge and node conditions of an embedding (`RotSystem.edge_eq`,
`RotSystem.nodeCond`), the endpoint formulas for `node` and `face`, a lower bound on the
number of nodes (`RotSystem.nodes_ge`) and the assembly into `SphOuter` from bounds on the
numbers of faces and components (`RotSystem.sphOuter`).
-/

@[expose] public section

namespace STACS2027

open Complexity Complexity.Planar PlanarGluing

/-- The vertex at half-edge `d` of `es`: half-edges `2i` and `2i + 1` are the first and the
second end of edge `i`. -/
def dtail (es : List (ℕ × ℕ)) (d : ℕ) : ℕ :=
  if d % 2 = 0 then (es.getD (d / 2) (0, 0)).1 else (es.getD (d / 2) (0, 0)).2

/-- The other end of the edge of half-edge `d`. -/
def dhead (es : List (ℕ × ℕ)) (d : ℕ) : ℕ :=
  if d % 2 = 0 then (es.getD (d / 2) (0, 0)).2 else (es.getD (d / 2) (0, 0)).1

theorem dtail_even (es : List (ℕ × ℕ)) {d : ℕ} (h : d % 2 = 0) :
    dtail es d = (es.getD (d / 2) (0, 0)).1 := by simp [dtail, h]

theorem dtail_odd (es : List (ℕ × ℕ)) {d : ℕ} (h : d % 2 = 1) :
    dtail es d = (es.getD (d / 2) (0, 0)).2 := by simp [dtail, h]

theorem dhead_even (es : List (ℕ × ℕ)) {d : ℕ} (h : d % 2 = 0) :
    dhead es d = (es.getD (d / 2) (0, 0)).2 := by simp [dhead, h]

theorem dhead_odd (es : List (ℕ × ℕ)) {d : ℕ} (h : d % 2 = 1) :
    dhead es d = (es.getD (d / 2) (0, 0)).1 := by simp [dhead, h]

theorem halfEdgeEnd_eq_dtail (es : List (ℕ × ℕ)) {d : ℕ} (hd : d < 2 * es.length) :
    halfEdgeEnd es d = some (dtail es d) := by
  have hi : d / 2 < es.length := by omega
  unfold halfEdgeEnd
  rw [List.getElem?_eq_getElem hi, Option.map_some]
  rcases Nat.mod_two_eq_zero_or_one d with h | h
  · rw [dtail_even es h, List.getD_eq_getElem _ _ hi]; simp [h]
  · rw [dtail_odd es h, List.getD_eq_getElem _ _ hi]; simp [h]

theorem ed_lt {m d : ℕ} (h : d < 2 * m) : ed d < 2 * m := by
  unfold ed
  rcases Nat.mod_two_eq_zero_or_one d with h2 | h2 <;> simp [h2] <;> omega

theorem ed_even {d : ℕ} (h : d % 2 = 0) : ed d = d + 1 := by simp [ed, h]

theorem ed_odd {d : ℕ} (h : d % 2 = 1) : ed d = d - 1 := by simp [ed, h]

theorem dtail_ed (es : List (ℕ × ℕ)) (d : ℕ) : dtail es (ed d) = dhead es d := by
  rcases Nat.mod_two_eq_zero_or_one d with h | h
  · rw [ed_even h, dtail_odd es (by omega), dhead_even es h, show (d + 1) / 2 = d / 2 by omega]
  · rw [ed_odd h, dtail_even es (by omega), dhead_odd es h, show (d - 1) / 2 = d / 2 by omega]

theorem dhead_ed (es : List (ℕ × ℕ)) (d : ℕ) : dhead es (ed d) = dtail es d := by
  rcases Nat.mod_two_eq_zero_or_one d with h | h
  · rw [ed_even h, dhead_odd es (by omega), dtail_even es h, show (d + 1) / 2 = d / 2 by omega]
  · rw [ed_odd h, dhead_even es (by omega), dtail_odd es h, show (d - 1) / 2 = d / 2 by omega]

/-- A simple edge list: no loops, and no two entries with the same two ends (in either
order). -/
def SimpleList (es : List (ℕ × ℕ)) : Prop :=
  (∀ e ∈ es, e.1 ≠ e.2) ∧
  ∀ i j, i < es.length → j < es.length →
    (es.getD i (0, 0) = es.getD j (0, 0) ∨
      es.getD i (0, 0) = ((es.getD j (0, 0)).2, (es.getD j (0, 0)).1)) → i = j

/-- In a simple edge list a half-edge is determined by its two ends. -/
theorem dart_inj {es : List (ℕ × ℕ)} (hs : SimpleList es) {d d' : ℕ}
    (hd : d < 2 * es.length) (hd' : d' < 2 * es.length)
    (ht : dtail es d = dtail es d') (hh : dhead es d = dhead es d') : d = d' := by
  have hi : d / 2 < es.length := by omega
  have hj : d' / 2 < es.length := by omega
  have hloop := hs.1 _ (List.getElem_mem hi)
  rw [← List.getD_eq_getElem _ (0, 0) hi] at hloop
  rcases Nat.mod_two_eq_zero_or_one d with h | h <;>
    rcases Nat.mod_two_eq_zero_or_one d' with h' | h'
  · rw [dtail_even es h, dtail_even es h'] at ht
    rw [dhead_even es h, dhead_even es h'] at hh
    have := hs.2 _ _ hi hj (Or.inl (Prod.ext ht hh)); omega
  · rw [dtail_even es h, dtail_odd es h'] at ht
    rw [dhead_even es h, dhead_odd es h'] at hh
    have := hs.2 _ _ hi hj (Or.inr (Prod.ext ht hh))
    rw [this] at ht hloop
    exact absurd ht hloop
  · rw [dtail_odd es h, dtail_even es h'] at ht
    rw [dhead_odd es h, dhead_even es h'] at hh
    have := hs.2 _ _ hi hj (Or.inr (Prod.ext hh ht))
    rw [this] at ht hloop
    exact absurd ht.symm hloop
  · rw [dtail_odd es h, dtail_odd es h'] at ht
    rw [dhead_odd es h, dhead_odd es h'] at hh
    have := hs.2 _ _ hi hj (Or.inl (Prod.ext hh ht)); omega

/-- `u` and `v` are joined by a half-edge from `u` to `v`. -/
def Adjs (es : List (ℕ × ℕ)) (u v : ℕ) : Prop :=
  ∃ d, d < 2 * es.length ∧ dtail es d = u ∧ dhead es d = v

theorem adjs_dart (es : List (ℕ × ℕ)) {d : ℕ} (hd : d < 2 * es.length) :
    Adjs es (dtail es d) (dhead es d) := ⟨d, hd, rfl, rfl⟩

theorem Adjs.symm {es : List (ℕ × ℕ)} {u v : ℕ} (h : Adjs es u v) : Adjs es v u := by
  obtain ⟨d, hd, rfl, rfl⟩ := h
  exact ⟨ed d, ed_lt hd, dtail_ed es d, dhead_ed es d⟩

theorem adjs_iff (es : List (ℕ × ℕ)) (u v : ℕ) :
    Adjs es u v ↔ (u, v) ∈ es ∨ (v, u) ∈ es := by
  constructor
  · rintro ⟨d, hd, rfl, rfl⟩
    have hi : d / 2 < es.length := by omega
    have hm := List.getElem_mem hi
    rw [← List.getD_eq_getElem _ (0, 0) hi] at hm
    rcases Nat.mod_two_eq_zero_or_one d with h | h
    · rw [dtail_even es h, dhead_even es h]; exact Or.inl hm
    · rw [dtail_odd es h, dhead_odd es h]; exact Or.inr hm
  · rintro (h | h)
    · obtain ⟨i, hi, he⟩ := List.getElem_of_mem h
      refine ⟨2 * i, by omega, ?_, ?_⟩
      · rw [dtail_even es (by omega), show 2 * i / 2 = i by omega,
          List.getD_eq_getElem _ _ hi, he]
      · rw [dhead_even es (by omega), show 2 * i / 2 = i by omega,
          List.getD_eq_getElem _ _ hi, he]
    · obtain ⟨i, hi, he⟩ := List.getElem_of_mem h
      refine ⟨2 * i + 1, by omega, ?_, ?_⟩
      · rw [dtail_odd es (by omega), show (2 * i + 1) / 2 = i by omega,
          List.getD_eq_getElem _ _ hi, he]
      · rw [dhead_odd es (by omega), show (2 * i + 1) / 2 = i by omega,
          List.getD_eq_getElem _ _ hi, he]

open Classical in
/-- The half-edge from `u` to `v` (if any). -/
noncomputable def findDart (es : List (ℕ × ℕ)) (u v : ℕ) : ℕ :=
  if h : Adjs es u v then Nat.find h else 0

theorem findDart_spec {es : List (ℕ × ℕ)} {u v : ℕ} (h : Adjs es u v) :
    findDart es u v < 2 * es.length ∧ dtail es (findDart es u v) = u ∧
      dhead es (findDart es u v) = v := by
  simp only [findDart, h, ↓reduceDIte]
  exact Nat.find_spec h

theorem findDart_self {es : List (ℕ × ℕ)} (hs : SimpleList es) {d : ℕ}
    (hd : d < 2 * es.length) : findDart es (dtail es d) (dhead es d) = d := by
  obtain ⟨h1, h2, h3⟩ := findDart_spec (adjs_dart es hd)
  exact dart_inj hs h1 hd h2 h3

/-- Two half-edges with the same ends are equal. -/
theorem fin_dart_inj {es : List (ℕ × ℕ)} (hs : SimpleList es) {d d' : Fin (2 * es.length)}
    (ht : dtail es d.val = dtail es d'.val) (hh : dhead es d.val = dhead es d'.val) : d = d' :=
  Fin.ext (dart_inj hs d.isLt d'.isLt ht hh)

/-- A rotation system on the neighbours (`Adjs`) of every vertex: `rot w` permutes the
neighbours of `w` in one cycle, with inverse `rotInv w`. -/
structure RotSystem (es : List (ℕ × ℕ)) where
  rot : ℕ → ℕ → ℕ
  rotInv : ℕ → ℕ → ℕ
  rot_adj : ∀ w u, Adjs es w u → Adjs es w (rot w u)
  rotInv_adj : ∀ w u, Adjs es w u → Adjs es w (rotInv w u)
  rot_rotInv : ∀ w u, Adjs es w u → rot w (rotInv w u) = u
  reach : ∀ w u u', Adjs es w u → Adjs es w u' → ∃ k, iterate (rot w) k u = u'

namespace RotSystem

variable {es : List (ℕ × ℕ)} (R : RotSystem es)

/-- The `node` permutation of a rotation system, on half-edge numbers. -/
noncomputable def nodeN (d : ℕ) : ℕ := findDart es (dtail es d) (R.rot (dtail es d) (dhead es d))

/-- The `face` permutation of a rotation system, on half-edge numbers. -/
noncomputable def faceN (d : ℕ) : ℕ :=
  findDart es (dhead es d) (R.rotInv (dhead es d) (dtail es d))

theorem nodeN_spec {d : ℕ} (hd : d < 2 * es.length) :
    R.nodeN d < 2 * es.length ∧ dtail es (R.nodeN d) = dtail es d ∧
      dhead es (R.nodeN d) = R.rot (dtail es d) (dhead es d) :=
  findDart_spec (R.rot_adj _ _ (adjs_dart es hd))

theorem faceN_spec {d : ℕ} (hd : d < 2 * es.length) :
    R.faceN d < 2 * es.length ∧ dtail es (R.faceN d) = dhead es d ∧
      dhead es (R.faceN d) = R.rotInv (dhead es d) (dtail es d) :=
  findDart_spec (R.rotInv_adj _ _ (adjs_dart es hd).symm)

/-- The hypermap of a rotation system on a simple edge list. -/
noncomputable def hypermap (hs : SimpleList es) : Hypermap (2 * es.length) where
  edge d := graphEdge d
  node d := ⟨R.nodeN d.val, (R.nodeN_spec d.isLt).1⟩
  face d := ⟨R.faceN d.val, (R.faceN_spec d.isLt).1⟩
  edgeK x := by
    apply Fin.ext
    have hx := x.isLt
    have he : (graphEdge x).val = ed x.val := rfl
    have hf := R.faceN_spec (ed_lt hx)
    rw [dtail_ed, dhead_ed] at hf
    change R.nodeN (R.faceN (graphEdge x).val) = x.val
    rw [he]
    unfold nodeN
    rw [hf.2.1, hf.2.2, R.rot_rotInv _ _ (adjs_dart es hx)]
    exact findDart_self hs hx

variable (hs : SimpleList es)

theorem edge_eq (d : Fin (2 * es.length)) : (R.hypermap hs).edge d = graphEdge d := rfl

theorem dtail_node (d : Fin (2 * es.length)) :
    dtail es ((R.hypermap hs).node d).val = dtail es d.val := (R.nodeN_spec d.isLt).2.1

theorem dhead_node (d : Fin (2 * es.length)) :
    dhead es ((R.hypermap hs).node d).val = R.rot (dtail es d.val) (dhead es d.val) :=
  (R.nodeN_spec d.isLt).2.2

theorem dtail_face (d : Fin (2 * es.length)) :
    dtail es ((R.hypermap hs).face d).val = dhead es d.val := (R.faceN_spec d.isLt).2.1

theorem dhead_face (d : Fin (2 * es.length)) :
    dhead es ((R.hypermap hs).face d).val = R.rotInv (dhead es d.val) (dtail es d.val) :=
  (R.faceN_spec d.isLt).2.2

theorem dtail_edge (d : Fin (2 * es.length)) :
    dtail es ((R.hypermap hs).edge d).val = dhead es d.val := dtail_ed es d.val

theorem dhead_edge (d : Fin (2 * es.length)) :
    dhead es ((R.hypermap hs).edge d).val = dtail es d.val := dhead_ed es d.val

theorem iterate_node (k : ℕ) (d : Fin (2 * es.length)) :
    dtail es (iterate (R.hypermap hs).node k d).val = dtail es d.val ∧
      dhead es (iterate (R.hypermap hs).node k d).val =
        iterate (R.rot (dtail es d.val)) k (dhead es d.val) := by
  induction k generalizing d with
  | zero => exact ⟨rfl, rfl⟩
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih ((R.hypermap hs).node d)
    simp only [iterate]
    rw [h1, h2, R.dtail_node hs, R.dhead_node hs]
    exact ⟨rfl, rfl⟩

/-- The node condition of an embedding: the node cycles are the half-edges at a vertex. -/
theorem nodeCond (d d' : Fin (2 * es.length)) :
    (∃ k, iterate (R.hypermap hs).node k d = d') ↔
      halfEdgeEnd es d.val = halfEdgeEnd es d'.val := by
  rw [halfEdgeEnd_eq_dtail es d.isLt, halfEdgeEnd_eq_dtail es d'.isLt, Option.some.injEq]
  constructor
  · rintro ⟨k, rfl⟩
    exact ((R.iterate_node hs k d).1).symm
  · intro ht
    have h1 := adjs_dart es d.isLt
    have h2 := adjs_dart es d'.isLt
    rw [← ht] at h2
    obtain ⟨k, hk⟩ := R.reach _ _ _ h1 h2
    refine ⟨k, fin_dart_inj hs ?_ ?_⟩
    · rw [(R.iterate_node hs k d).1, ht]
    · rw [(R.iterate_node hs k d).2, hk]

/-- Half-edges at pairwise different vertices lie in different node cycles. -/
theorem nodes_ge (xs : List (Fin (2 * es.length)))
    (hnd : (xs.map fun d => dtail es d.val).Nodup) :
    xs.length ≤ cycleCount (R.hypermap hs).node :=
  cycleCount_ge _ (fun d => dtail es d.val) (fun d => R.dtail_node hs d) xs hnd

/-- **Assembly**: a rotation system with enough faces and few enough components gives a
spherical outerplanar embedding. -/
theorem sphOuter (v f c : ℕ) (hv : v ≤ cycleCount (R.hypermap hs).node)
    (hf : f ≤ cycleCount (R.hypermap hs).face) (hc : (R.hypermap hs).componentCount ≤ c)
    (hcount : 2 * c + es.length ≤ v + f) (ho : OuterFaceCond (R.hypermap hs)) :
    SphOuter es := by
  refine ⟨R.hypermap hs, fun d => rfl, R.nodeCond hs, ?_, ho⟩
  have he : es.length ≤ cycleCount (R.hypermap hs).edge :=
    cycleCount_graphEdge_ge (E := es.length) (fun d => rfl)
  unfold Hypermap.eulerRhs
  omega

end RotSystem

end STACS2027

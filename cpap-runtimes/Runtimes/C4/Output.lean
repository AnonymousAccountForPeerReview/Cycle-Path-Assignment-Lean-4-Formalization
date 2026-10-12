module

public import Runtimes.C4.Paths
public import Runtimes.C4.Buckets
public import Runtimes.C4.Canon
import Outerplanar.Algo.Combine
import Outerplanar.Algo.LowPoint
import Mathlib.Tactic

/-!
# Four-cycle listing: each 4-cycle is reported exactly once

For any ranking `pos` injective on the vertices:

* ids and labels: `idOf_labelOf`, `edge_mem_of_nb` (an edge of the id graph is an edge of
  `g` in labels), `nb_of_edge` (and conversely);
* **A1** (`report_shape`, `report_nodup`, `report_isCycle`, `phi_mem_cycles`): a report
  `((x, y), z, z')` has `x < y`, two admissible centres `z ≠ z'`, and its cycle
  `x – z – y – z'` is a simple 4-cycle; its canonical label form `phi g r` is in `cycles g 4`;
* **A3** (`report_inj`): two reports whose cycles have the same edges are equal — by the
  diagonals, either the keys agree (and the order of insertion fixes the centres) or the key of
  each is the centre pair of the other, which contradicts admissibility;
* **A4** (`sameCycle_map`): relabelling preserves "same edges", and `phi_inj`;
* **A5** (`exists_report`): every member of `cycles g 4` is reported, from the diagonal that
  holds its latest vertex;
* **Theorem A** (`enumOutP_perm`, `enumOut_perm`): the output is a permutation of
  `cycles g 4`; in particular `(reports (ins g pos)).length = (cycles g 4).length`
  (`length_reports_ins`, `length_enumOut`, `length_flatten_enumOut`).
-/

@[expose] public section

namespace STACS2027.Runtimes.C4

open STACS2027 STACS2027.Algo

variable {g : Graph} {pos : ℕ → ℕ}

/-! ### Ids and labels -/

theorem idOf_labelOf {x : ℕ} (hx : x < numV g) : idOf g (labelOf g x) = x := by
  have h := (Comb.labels_nodup g).idxOf_getElem x hx
  simpa [idOf, labelOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hx] using h

/-- An edge of the id graph is an edge of `g` between the labels. -/
theorem edge_mem_of_nb {u w : ℕ} (hu : u < numV g) (hw : w ∈ nb g u) :
    edge (labelOf g u) (labelOf g w) ∈ g := by
  have hadj := adj_iff_mem_nbOf.mpr hw
  have hwN := (nbOk g).lt u w hw
  have hne : labelOf g u ≠ labelOf g w := fun h => hadj.1 (Comb.labelOf_inj u hu w hwN h)
  refine (Comb.edge_iff_idEdges g _ _ hne).mpr ?_
  exact List.mem_map.mpr ⟨edge u w, hadj.2, mapEdge_edge _ _ _⟩

theorem edge_mem_proper {a b : ℕ} (hab : a ≠ b) (h : edge a b ∈ g) : edge a b ∈ proper g :=
  Comb.mem_proper.mpr ⟨h, by simp only [edge]; omega⟩

theorem mem_labels_of_edge {a b : ℕ} (hab : a ≠ b) (h : edge a b ∈ g) :
    a ∈ labels g ∧ b ∈ labels g := by
  have h1 := Comb.mem_labels_of_proper (edge_mem_proper hab h)
  rcases Nat.lt_or_gt_of_ne hab with h2 | h2
  · simpa [edge, Nat.min_eq_left h2.le, Nat.max_eq_right h2.le] using h1
  · simpa [edge, Nat.min_eq_right h2.le, Nat.max_eq_left h2.le, and_comm] using h1

/-- An edge of `g` between distinct labels is an edge of the id graph. -/
theorem nb_of_edge {a b : ℕ} (hab : a ≠ b) (h : edge a b ∈ g) : idOf g b ∈ nb g (idOf g a) := by
  have hl := mem_labels_of_edge hab h
  refine adj_iff_mem_nbOf.mp ⟨fun e => hab (idOf_inj hl.1 e), ?_⟩
  refine Comb.mem_idEdges.mpr ⟨edge a b, edge_mem_proper hab h, ?_⟩
  rcases Nat.lt_or_gt_of_ne hab with h2 | h2
  · simp [edge, Nat.min_eq_left h2.le, Nat.max_eq_right h2.le]
  · simp only [edge, Nat.min_eq_right h2.le, Nat.max_eq_left h2.le]
    rw [Nat.min_comm, Nat.max_comm]

/-- Relabelling preserves having the same edges. -/
theorem sameCycle_map (f : ℕ → ℕ) {c d : Cycle} (h : SameCycle c d) :
    SameCycle (c.map f) (d.map f) := by
  constructor <;> intro e he <;> rw [cycleEdges_map] at he ⊢ <;>
    obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
  · exact List.mem_map.mpr ⟨e', h.1 e' he', rfl⟩
  · exact List.mem_map.mpr ⟨e', h.2 e' he', rfl⟩

theorem nodup_getElem?_inj {l : Ins} (hl : l.Nodup) {i j : ℕ} {a : (ℕ × ℕ) × ℕ}
    (hi : l[i]? = some a) (hj : l[j]? = some a) : i = j := by
  obtain ⟨hi', rfl⟩ := List.getElem?_eq_some_iff.mp hi
  obtain ⟨hj', h⟩ := List.getElem?_eq_some_iff.mp hj
  exact (hl.getElem_inj_iff).mp h.symm

/-! ### A1: the shape of a report -/

theorem report_shape (hpos : Set.InjOn pos (Set.Iio (numV g))) {x y z z' : ℕ}
    (hr : ((x, y), z, z') ∈ reports (ins g pos)) :
    x < y ∧ Adm g pos x z y ∧ Adm g pos x z' y ∧ z ≠ z' := by
  obtain ⟨h1, h2⟩ := mem_of_mem_reports hr
  obtain ⟨hxy, hz⟩ := (mem_ins hpos).mp h1
  obtain ⟨-, hz'⟩ := (mem_ins hpos).mp h2
  refine ⟨hxy, hz, hz', ?_⟩
  rintro rfl
  obtain ⟨i, j, hij, -, hi, hj⟩ := mem_reports.mp hr
  have := nodup_getElem?_inj (nodup_ins hpos) hi hj
  omega

theorem report_nodup (hpos : Set.InjOn pos (Set.Iio (numV g))) {x y z z' : ℕ}
    (hr : ((x, y), z, z') ∈ reports (ins g pos)) : [x, z, y, z'].Nodup := by
  obtain ⟨hxy, ⟨-, -, -, hz, hyz, -⟩, ⟨-, -, -, hz', hyz', -⟩, hne⟩ := report_shape hpos hr
  have hok := nbOk g
  have h1 : z ≠ x := fun e => hok.noloop x (e ▸ hz)
  have h2 : z ≠ y := fun e => hok.noloop z (e ▸ hyz)
  have h3 : z' ≠ x := fun e => hok.noloop x (e ▸ hz')
  have h4 : z' ≠ y := fun e => hok.noloop z' (e ▸ hyz')
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil,
    not_false_eq_true, and_true]
  omega

/-- The cycle of a report, in labels, is a simple 4-cycle of `g`. -/
theorem report_isCycle (hpos : Set.InjOn pos (Set.Iio (numV g))) {x y z z' : ℕ}
    (hr : ((x, y), z, z') ∈ reports (ins g pos)) :
    IsCycle g 4 [labelOf g x, labelOf g z, labelOf g y, labelOf g z'] := by
  obtain ⟨hxy, ⟨hx, hy, -, hz, hyz, -⟩, ⟨-, -, -, hz', hyz', -⟩, -⟩ := report_shape hpos hr
  have hok := nbOk g
  have hnd := report_nodup hpos hr
  have hzN := hok.lt _ _ hz
  have hzN' := hok.lt _ _ hz'
  refine ⟨by norm_num, rfl, ?_, ?_⟩
  · have := hnd.map_on (f := labelOf g) fun a ha b hb h => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
      exact Comb.labelOf_inj a (by rcases ha with rfl | rfl | rfl | rfl <;> assumption)
        b (by rcases hb with rfl | rfl | rfl | rfl <;> assumption) h
    simpa using this
  · intro e he
    rw [cycleEdges4] at he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact edge_mem_of_nb hx hz
    · exact edge_mem_of_nb hzN hyz
    · rw [edge_comm]; exact edge_mem_of_nb hzN' hyz'
    · rw [edge_comm]; exact edge_mem_of_nb hx hz'

/-- **A1.** Every reported cycle is a member of `cycles g 4`. -/
theorem phi_mem_cycles (hpos : Set.InjOn pos (Set.Iio (numV g))) {r : (ℕ × ℕ) × ℕ × ℕ}
    (hr : r ∈ reports (ins g pos)) : phi g r ∈ cycles g 4 := by
  obtain ⟨⟨x, y⟩, z, z'⟩ := r
  have hc := report_isCycle hpos hr
  exact mem_cycles4.mpr ⟨isCycle_canon4 hc, canon4_isCanon hc.2.2.1⟩

/-! ### A3: injectivity -/

/-- **A3.** Two reports whose cycles have the same edges are equal. -/
theorem report_inj (hpos : Set.InjOn pos (Set.Iio (numV g))) {x₁ y₁ z₁ w₁ x₂ y₂ z₂ w₂ : ℕ}
    (h₁ : ((x₁, y₁), z₁, w₁) ∈ reports (ins g pos)) (h₂ : ((x₂, y₂), z₂, w₂) ∈ reports (ins g pos))
    (hs : SameCycle [x₁, z₁, y₁, w₁] [x₂, z₂, y₂, w₂]) :
    ((x₁, y₁), z₁, w₁) = ((x₂, y₂), z₂, w₂) := by
  obtain ⟨hxy₁, ⟨-, -, -, -, -, hp₁⟩, ⟨-, -, -, -, -, hq₁⟩, -⟩ := report_shape hpos h₁
  obtain ⟨hxy₂, ⟨-, -, -, -, -, hp₂⟩, ⟨-, -, -, -, -, hq₂⟩, -⟩ := report_shape hpos h₂
  rcases diagonals (report_nodup hpos h₁) (report_nodup hpos h₂) hs with
    ⟨hk, hc⟩ | ⟨hk, hc⟩
  · have hx : x₁ = x₂ := by omega
    have hy : y₁ = y₂ := by omega
    subst hx hy
    rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exfalso
      obtain ⟨i₁, j₁, hij₁, -, hi₁, hj₁⟩ := mem_reports.mp h₁
      obtain ⟨i₂, j₂, hij₂, -, hi₂, hj₂⟩ := mem_reports.mp h₂
      have e1 := nodup_getElem?_inj (nodup_ins hpos) hi₁ hj₂
      have e2 := nodup_getElem?_inj (nodup_ins hpos) hj₁ hi₂
      omega
  · exfalso
    rcases hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      omega

/-- The label cycle of a report, mapped back to ids, is its id cycle. -/
theorem map_idOf_report (hpos : Set.InjOn pos (Set.Iio (numV g))) {x y z z' : ℕ}
    (hr : ((x, y), z, z') ∈ reports (ins g pos)) :
    [labelOf g x, labelOf g z, labelOf g y, labelOf g z'].map (idOf g) = [x, z, y, z'] := by
  obtain ⟨-, ⟨hx, hy, -, hz, -, -⟩, ⟨-, -, -, hz', -, -⟩, -⟩ := report_shape hpos hr
  have hok := nbOk g
  simp [idOf_labelOf hx, idOf_labelOf hy, idOf_labelOf (hok.lt _ _ hz),
    idOf_labelOf (hok.lt _ _ hz')]

/-- `phi g` is injective on the reports. -/
theorem phi_inj (hpos : Set.InjOn pos (Set.Iio (numV g))) {r₁ r₂ : (ℕ × ℕ) × ℕ × ℕ}
    (h₁ : r₁ ∈ reports (ins g pos)) (h₂ : r₂ ∈ reports (ins g pos)) (h : phi g r₁ = phi g r₂) :
    r₁ = r₂ := by
  obtain ⟨⟨x₁, y₁⟩, z₁, w₁⟩ := r₁
  obtain ⟨⟨x₂, y₂⟩, z₂, w₂⟩ := r₂
  have s1 := canon4_same (labelOf g x₁) (labelOf g z₁) (labelOf g y₁) (labelOf g w₁)
  have s2 := canon4_same (labelOf g x₂) (labelOf g z₂) (labelOf g y₂) (labelOf g w₂)
  have s : SameCycle [labelOf g x₁, labelOf g z₁, labelOf g y₁, labelOf g w₁]
      [labelOf g x₂, labelOf g z₂, labelOf g y₂, labelOf g w₂] := by
    refine s1.trans ?_
    change SameCycle (phi g ((x₁, y₁), z₁, w₁)) _
    rw [h]
    exact s2.symm
  have s' := sameCycle_map (idOf g) s
  rw [map_idOf_report hpos h₁, map_idOf_report hpos h₂] at s'
  exact report_inj hpos h₁ h₂ s'

/-! ### A5: every 4-cycle is reported -/

theorem eq4_of_length {c : Cycle} (h : c.length = 4) : ∃ a b x d, c = [a, b, x, d] := by
  match c, h with
  | [a, b, x, d], _ => exact ⟨a, b, x, d, rfl⟩

/-- The 4-cycle `x – w – y – w'` built on the diagonal `{x, y} = {p, r}` and the centres
`{w, w'} = {q, s}` has the edges of `p q r s`. -/
theorem sameCycle_diag {p q r s x y w w' : ℕ} (hxy : (x = p ∧ y = r) ∨ (x = r ∧ y = p))
    (hw : (w = q ∧ w' = s) ∨ (w = s ∧ w' = q)) : SameCycle [x, w, y, w'] [p, q, r, s] := by
  rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    refine sameCycle4 fun e => ?_ <;> constructor <;>
    rintro (rfl | rfl | rfl | rfl) <;> simp [edge_comm]

theorem sameCycle_rotate (p q r s : ℕ) : SameCycle [q, r, s, p] [p, q, r, s] :=
  sameCycle4 fun _ => by tauto

/-- The report of a 4-cycle given in ids: diagonal `{a, c}`, centres `b` and `d`, both
admissible. -/
theorem exists_report_diag (hpos : Set.InjOn pos (Set.Iio (numV g))) {a b c d : ℕ}
    (hac : a ≠ c) (hbd : b ≠ d) (hb : Adm g pos (key a c).1 b (key a c).2)
    (hd : Adm g pos (key a c).1 d (key a c).2) :
    ∃ w w', ((w = b ∧ w' = d) ∨ (w = d ∧ w' = b)) ∧ (key a c, w, w') ∈ reports (ins g pos) := by
  have hlt := key_lt hac
  have h1 : ((key a c).1, (key a c).2) = key a c := rfl
  have hb' : (key a c, b) ∈ ins g pos := by rw [← h1]; exact (mem_ins hpos).mpr ⟨hlt, hb⟩
  have hd' : (key a c, d) ∈ ins g pos := by rw [← h1]; exact (mem_ins hpos).mpr ⟨hlt, hd⟩
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hb'
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hd'
  have hij : i ≠ j := by
    rintro rfl
    rw [hi] at hj
    simp only [Option.some.injEq, Prod.mk.injEq, true_and] at hj
    exact hbd hj
  have hjl : j < (ins g pos).length := by
    by_contra h; rw [List.getElem?_eq_none (by omega)] at hj; simp at hj
  have hil : i < (ins g pos).length := by
    by_contra h; rw [List.getElem?_eq_none (by omega)] at hi; simp at hi
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · exact ⟨d, b, Or.inr ⟨rfl, rfl⟩, mem_reports.mpr ⟨i, j, h, hjl, hi, hj⟩⟩
  · exact ⟨b, d, Or.inl ⟨rfl, rfl⟩, mem_reports.mpr ⟨j, i, h, hil, hj, hi⟩⟩

theorem key_cases (a c : ℕ) : ((key a c).1 = a ∧ (key a c).2 = c) ∨ ((key a c).1 = c ∧ (key a c).2 = a) := by
  simp only [key]; omega

/-- **A5.** Every member of `cycles g 4` is reported. -/
theorem exists_report (hpos : Set.InjOn pos (Set.Iio (numV g))) {c : Cycle}
    (hc : c ∈ cycles g 4) : ∃ r ∈ reports (ins g pos), phi g r = c := by
  obtain ⟨hcyc, hcan⟩ := mem_cycles4.mp hc
  obtain ⟨a, b, x, d, rfl⟩ := eq4_of_length hcyc.2.1
  have hnd := hcyc.2.2.1
  have hnd' := hnd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil,
    not_false_eq_true, and_true] at hnd'
  have eab := hcyc.2.2.2 (edge a b) (by simp [cycleEdges4])
  have ebx := hcyc.2.2.2 (edge b x) (by simp [cycleEdges4])
  have exd := hcyc.2.2.2 (edge x d) (by simp [cycleEdges4])
  have eda := hcyc.2.2.2 (edge d a) (by simp [cycleEdges4])
  have hok := nbOk g
  -- the ids
  have la := (mem_labels_of_edge (by omega) eab).1
  have lb := (mem_labels_of_edge (by omega) ebx).1
  have lx := (mem_labels_of_edge (by omega) exd).1
  have ld := (mem_labels_of_edge (by omega) eda).1
  set i₀ := idOf g a
  set i₁ := idOf g b
  set i₂ := idOf g x
  set i₃ := idOf g d
  have n01 : i₁ ∈ nb g i₀ := nb_of_edge (by omega) eab
  have n12 : i₂ ∈ nb g i₁ := nb_of_edge (by omega) ebx
  have n23 : i₃ ∈ nb g i₂ := nb_of_edge (by omega) exd
  have n30 : i₀ ∈ nb g i₃ := nb_of_edge (by omega) eda
  have n10 := hok.symm _ _ n01
  have n21 := hok.symm _ _ n12
  have n32 := hok.symm _ _ n23
  have n03 := hok.symm _ _ n30
  have h0 : i₀ < numV g := Comb.idOf_lt la
  have h1 : i₁ < numV g := Comb.idOf_lt lb
  have h2 : i₂ < numV g := Comb.idOf_lt lx
  have h3 : i₃ < numV g := Comb.idOf_lt ld
  have d01 : i₀ ≠ i₁ := fun e => hnd'.1.1 (idOf_inj la e)
  have d02 : i₀ ≠ i₂ := fun e => hnd'.1.2.1 (idOf_inj la e)
  have d03 : i₀ ≠ i₃ := fun e => hnd'.1.2.2 (idOf_inj la e)
  have d12 : i₁ ≠ i₂ := fun e => hnd'.2.1.1 (idOf_inj lb e)
  have d13 : i₁ ≠ i₃ := fun e => hnd'.2.1.2 (idOf_inj lb e)
  have d23 : i₂ ≠ i₃ := fun e => hnd'.2.2 (idOf_inj lx e)
  have p01 : pos i₀ ≠ pos i₁ := fun e => d01 (hpos h0 h1 e)
  have p03 : pos i₀ ≠ pos i₃ := fun e => d03 (hpos h0 h3 e)
  have p21 : pos i₂ ≠ pos i₁ := fun e => d12 (hpos h1 h2 e.symm)
  have p23 : pos i₂ ≠ pos i₃ := fun e => d23 (hpos h2 h3 e)
  -- labels of the ids
  have lab0 : labelOf g i₀ = a := Comb.labelOf_idOf la
  have lab1 : labelOf g i₁ = b := Comb.labelOf_idOf lb
  have lab2 : labelOf g i₂ = x := Comb.labelOf_idOf lx
  have lab3 : labelOf g i₃ = d := Comb.labelOf_idOf ld
  -- the report found, and its cycle
  suffices H : ∃ r ∈ reports (ins g pos),
      SameCycle [r.1.1, r.2.1, r.1.2, r.2.2] [i₀, i₁, i₂, i₃] by
    obtain ⟨⟨⟨y₁, y₂⟩, w, w'⟩, hr, hs⟩ := H
    refine ⟨_, hr, ?_⟩
    have hs' := sameCycle_map (labelOf g) hs
    simp only [List.map_cons, List.map_nil, lab0, lab1, lab2, lab3] at hs'
    have hcyc' := report_isCycle hpos hr
    have hcan' := canon4_isCanon hcyc'.2.2.1
    obtain ⟨q₀, q₁, q₂, q₃, hq⟩ := eq4_of_length (length_canon4 (labelOf g y₁) (labelOf g w)
      (labelOf g y₂) (labelOf g w'))
    change canon4 (labelOf g y₁) (labelOf g w) (labelOf g y₂) (labelOf g w') = _
    rw [hq] at hcan' ⊢
    refine canon4_unique hnd hcan' hcan ?_
    rw [← hq]
    exact (canon4_same _ _ _ _).symm.trans hs'
  rcases Nat.lt_or_gt_of_ne (show max (pos i₀) (pos i₂) ≠ max (pos i₁) (pos i₃) by omega)
    with hm | hm
  · -- the latest vertex is on the diagonal `{i₁, i₃}`: key `{i₁, i₃}`, centres `i₀, i₂`
    have hA : ∀ w, w ∈ nb g i₁ → w ∈ nb g i₃ → pos w < max (pos i₁) (pos i₃) →
        Adm g pos (key i₁ i₃).1 w (key i₁ i₃).2 := by
      intro w hw1 hw3 hp
      rcases key_cases i₁ i₃ with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2]
      · exact ⟨h1, h3, d13, hw1, hok.symm _ _ hw3, hp⟩
      · exact ⟨h3, h1, d13.symm, hw3, hok.symm _ _ hw1, by omega⟩
    obtain ⟨w, w', hww, hr⟩ := exists_report_diag hpos d13 d02
      (hA i₀ n10 n30 (by omega)) (hA i₂ n12 n32 (by omega))
    refine ⟨_, hr, ?_⟩
    refine (sameCycle_diag (p := i₁) (q := i₂) (r := i₃) (s := i₀) ?_ ?_).trans
      (sameCycle_rotate _ _ _ _)
    · exact key_cases i₁ i₃
    · rcases hww with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
      · exact Or.inl ⟨rfl, rfl⟩
  · -- the latest vertex is on the diagonal `{i₀, i₂}`: key `{i₀, i₂}`, centres `i₁, i₃`
    have hA : ∀ w, w ∈ nb g i₀ → w ∈ nb g i₂ → pos w < max (pos i₀) (pos i₂) →
        Adm g pos (key i₀ i₂).1 w (key i₀ i₂).2 := by
      intro w hw0 hw2 hp
      rcases key_cases i₀ i₂ with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2]
      · exact ⟨h0, h2, d02, hw0, hok.symm _ _ hw2, hp⟩
      · exact ⟨h2, h0, d02.symm, hw2, hok.symm _ _ hw0, by omega⟩
    obtain ⟨w, w', hww, hr⟩ := exists_report_diag hpos d02 d13
      (hA i₁ n01 n21 (by omega)) (hA i₃ n03 n23 (by omega))
    exact ⟨_, hr, sameCycle_diag (key_cases i₀ i₂) hww⟩

/-! ### Theorem A -/

theorem nodup_enumOutP (hpos : Set.InjOn pos (Set.Iio (numV g))) : (enumOutP g pos).Nodup :=
  (nodup_reports (nodup_ins hpos)).map_on fun _ h₁ _ h₂ h => phi_inj hpos h₁ h₂ h

/-- **Theorem A** (exactly once): for any ranking injective on the vertices, the reported
cycles are a permutation of `cycles g 4`. -/
theorem enumOutP_perm (g : Graph) (pos : ℕ → ℕ) (hpos : Set.InjOn pos (Set.Iio (numV g))) :
    (enumOutP g pos).Perm (cycles g 4) := by
  refine (List.perm_ext_iff_of_nodup (nodup_enumOutP hpos) (cycles_nodup g 4)).mpr fun c => ?_
  constructor
  · intro h
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp h
    exact phi_mem_cycles hpos hr
  · intro h
    obtain ⟨r, hr, rfl⟩ := exists_report hpos h
    exact List.mem_map.mpr ⟨r, hr, rfl⟩

/-- The number of reports is the number of 4-cycles. -/
theorem length_reports_ins (g : Graph) (pos : ℕ → ℕ) (hpos : Set.InjOn pos (Set.Iio (numV g))) :
    (reports (ins g pos)).length = (cycles g 4).length := by
  have := (enumOutP_perm g pos hpos).length_eq
  rwa [enumOutP, List.length_map] at this

/-- **Theorem A** for the machine's order: the output is a permutation of `cycles g 4`. -/
theorem enumOut_perm (g : Graph) : (enumOut g).Perm (cycles g 4) :=
  enumOutP_perm g (peelPos g) (peelPos_injOn g)

theorem length_enumOut (g : Graph) : (enumOut g).length = (cycles g 4).length :=
  (enumOut_perm g).length_eq

/-- The machine's output array has four cells per cycle. -/
theorem length_flatten_enumOut (g : Graph) :
    (enumOut g).flatten.length = 4 * (cycles g 4).length := by
  rw [enumOut, length_flatten_enumOutP, ← enumOut, length_enumOut]

end STACS2027.Runtimes.C4

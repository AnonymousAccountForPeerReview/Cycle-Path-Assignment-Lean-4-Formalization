module

public import Outerplanar.Algo.PolyFacts
import Mathlib.Tactic

/-!
# The polygon solver: segments, children and owned edges

Facts about the enumerations of `Outerplanar.Algo.Poly` that do not involve cycles, on a
polygon `pg` on the positions `0, …, n - 1`:

* `mem_pairs`, `pairs_nodup`: the consecutive pairs of a list are its length-two infixes,
  listed once when the list has no repetition;
* `mem_segEnum`, `segEnum_nodup`, `mem_segOrder`, `segOrder_nodup`, `segOrder_size`: the
  segment lists list each segment once, `segOrder` smaller segments first;
* `mem_slots`: the slots of a segment are the pairs of consecutive face vertices;
* `mem_childSegs`, `childSegs_nodup`: `childSegs s` lists the children of `s` once each
  (`child_iff`);
* `mem_owned`, `owned_nodup`: `owned s` lists the edges owned by `s` once each: `s` itself
  and the sides `(x, x + 1)` that are slots of the face of `s`.
-/

@[expose] public section

namespace STACS2027.Poly

open IsPolygon

variable {pg : Graph} {n : ℕ}

/-! ### Consecutive pairs -/

/-- The consecutive pairs of a list are its infixes of length two. -/
theorem mem_pairs : ∀ {l : List ℕ} {t : ℕ × ℕ}, t ∈ pairs l ↔ [t.1, t.2] <:+: l
  | [], t => by
    simp only [pairs, List.not_mem_nil, false_iff]
    intro h
    have := h.length_le
    simp at this
  | [x], t => by
    simp only [pairs, List.not_mem_nil, false_iff]
    intro h
    have := h.length_le
    simp at this
  | x :: y :: rest, t => by
    rw [pairs, List.mem_cons, mem_pairs, List.infix_cons_iff (a := x) (l₂ := y :: rest)]
    constructor
    · rintro (rfl | h)
      · exact Or.inl ⟨rest, by simp⟩
      · exact Or.inr h
    · rintro (⟨r, hr⟩ | h)
      · left
        simp only [List.cons_append, List.nil_append, List.cons.injEq] at hr
        exact Prod.ext hr.1 hr.2.1
      · exact Or.inr h

/-- The first components of the consecutive pairs: all entries but the last. -/
theorem map_fst_pairs : ∀ l : List ℕ, (pairs l).map Prod.fst = l.dropLast
  | [] => rfl
  | [_] => rfl
  | x :: y :: rest => by
    rw [pairs, List.map_cons, map_fst_pairs (y :: rest), List.dropLast_cons_cons]

/-- A list without repetitions has its consecutive pairs listed once. -/
theorem pairs_nodup {l : List ℕ} (h : l.Nodup) : (pairs l).Nodup :=
  List.Nodup.of_map Prod.fst (by rw [map_fst_pairs]; exact h.sublist (List.dropLast_sublist l))

/-! ### Segments -/

/-- `segEnum` lists the segments. -/
theorem mem_segEnum {s : ℕ × ℕ} : s ∈ segEnum pg n ↔ s ∈ segs pg n := by
  obtain ⟨a, b⟩ := s
  simp only [segEnum, nbP, segs, List.mem_flatMap, List.mem_range, List.mem_map, List.mem_filter,
    decide_eq_true_eq, Prod.mk.injEq, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  constructor
  · rintro ⟨a', ha', b', ⟨⟨hb', hadj⟩, h2⟩, rfl, rfl⟩
    exact ⟨⟨ha', hb'⟩, hadj, h2⟩
  · rintro ⟨⟨ha, hb⟩, hadj, h2⟩
    exact ⟨a, ha, b, ⟨⟨hb, hadj⟩, h2⟩, rfl, rfl⟩

/-- `segEnum` lists each segment once. -/
theorem segEnum_nodup : (segEnum pg n).Nodup := by
  rw [segEnum, List.nodup_flatMap]
  refine ⟨fun a _ => ?_, ?_⟩
  · refine List.Nodup.map (fun b b' h => by simpa using h) ?_
    exact ((List.nodup_range.filter _).filter _)
  · refine List.Pairwise.imp (fun {a a'} hne => ?_) List.nodup_range
    intro x hx hx'
    simp only [List.mem_map] at hx hx'
    obtain ⟨b, -, rfl⟩ := hx
    obtain ⟨b', -, he⟩ := hx'
    exact hne (congrArg Prod.fst he).symm

/-- `segOrder` lists the segments. -/
theorem mem_segOrder {s : ℕ × ℕ} : s ∈ segOrder pg n ↔ s ∈ segs pg n := by
  simp only [segOrder, List.mem_flatMap, List.mem_range, List.mem_filter, mem_segEnum,
    decide_eq_true_eq]
  constructor
  · rintro ⟨d, -, hs, -⟩
    exact hs
  · intro hs
    have : s.2 < n := by
      simp only [segs, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hs
      exact hs.1.2
    exact ⟨s.2 - s.1, by omega, hs, rfl⟩

/-- `segOrder` lists each segment once. -/
theorem segOrder_nodup : (segOrder pg n).Nodup := by
  rw [segOrder, List.nodup_flatMap]
  refine ⟨fun d _ => segEnum_nodup.filter _, ?_⟩
  refine List.Pairwise.imp (fun {d d'} hne => ?_) List.nodup_range
  intro x hx hx'
  simp only [List.mem_filter, decide_eq_true_eq] at hx hx'
  exact hne (hx.2.symm.trans hx'.2)

/-- `segOrder` lists smaller segments first. -/
theorem segOrder_size : (segOrder pg n).Pairwise fun s t => s.2 - s.1 ≤ t.2 - t.1 := by
  rw [segOrder, List.pairwise_flatMap]
  refine ⟨fun d _ => List.pairwise_of_forall_mem_list fun a ha b hb => ?_, ?_⟩
  · simp only [List.mem_filter, decide_eq_true_eq] at ha hb
    omega
  · refine List.Pairwise.imp (fun {d d'} hlt => ?_) List.pairwise_lt_range
    intro x hx y hy
    simp only [List.mem_filter, decide_eq_true_eq] at hx hy
    omega

/-! ### Slots, children and owned edges -/

/-- The slots of `s` are the pairs of consecutive face vertices. -/
theorem mem_slots {s t : ℕ × ℕ} : t ∈ slots pg n s ↔ [t.1, t.2] <:+: faceVerts pg n s := by
  rw [slots, mem_pairs]

/-- The slots of a segment are listed once. -/
theorem slots_nodup (s : ℕ × ℕ) : (slots pg n s).Nodup :=
  pairs_nodup (faceVerts_pairwise.imp Nat.ne_of_lt)

/-- `childSegs s` lists each child once. -/
theorem childSegs_nodup (s : ℕ × ℕ) : (childSegs pg n s).Nodup :=
  (slots_nodup s).filter _

/-- **The children**: `childSegs s` lists the child segments of `s`. -/
theorem mem_childSegs (hP : IsPolygon pg n) (s t : ℕ × ℕ) :
    t ∈ childSegs pg n s ↔ t ∈ segs pg n ∧ IsChild pg n s t := by
  rw [childSegs, List.mem_filter, mem_slots, hP.child_iff, decide_eq_true_eq]

/-- `owned s` lists each owned edge once. -/
theorem owned_nodup {s : ℕ × ℕ} (hs : s ∈ segs pg n) : (owned pg n s).Nodup := by
  rw [owned, List.nodup_cons]
  refine ⟨?_, (slots_nodup s).filter _⟩
  intro h
  rw [List.mem_filter, decide_eq_true_eq] at h
  have := (of_mem_segs hs).2
  omega

/-- **The owned edges**: `owned s` lists the edges owned by `s`: itself and the sides of its
face. -/
theorem mem_owned (hP : IsPolygon pg n) {s : ℕ × ℕ} (hs : s ∈ segs pg n) (e : ℕ × ℕ) :
    e ∈ owned pg n s ↔ e ∈ polyEdges pg n ∧ (own hP e).1 = s := by
  have hs' := hP.mem_segs.mp hs
  rw [owned, List.mem_cons, List.mem_filter, mem_slots, hP.mem_polyEdges, decide_eq_true_eq]
  constructor
  · rintro (rfl | ⟨hi, he⟩)
    · exact ⟨⟨hs'.1, by omega⟩, hP.own_of_seg hs⟩
    · have hadj := hP.adj_of_infix_faceVerts hs hi
      obtain ⟨hx, hy, hxy, -⟩ := (infix_pair_iff faceVerts_pairwise).mp hi
      have hx' := mem_faceVerts.mp hx
      have hy' := mem_faceVerts.mp hy
      refine ⟨⟨hadj, hxy⟩, ?_⟩
      obtain ⟨h1, h2⟩ := hP.own_spec hadj hxy
      have hos := h2 s hs ⟨hx'.1, hy'.2.1⟩
      have ho := (own hP e).2
      have ho' := hP.mem_segs.mp ho
      by_contra hne
      have h3 := hx'.2.2 (own hP e).1 ho hos hne
      have h4 := hy'.2.2 (own hP e).1 ho hos hne
      simp only [Within] at h1
      omega
  · rintro ⟨⟨hadj, hlt⟩, ho⟩
    by_cases h2 : e.1 + 2 ≤ e.2
    · left
      have he : e ∈ segs pg n := hP.mem_segs.mpr ⟨hadj, h2⟩
      rw [← ho, hP.own_of_seg he]
    · right
      have he2 : e.2 = e.1 + 1 := by omega
      refine ⟨?_, he2⟩
      obtain ⟨h1, h2⟩ := hP.own_spec hadj hlt
      rw [ho] at h1 h2
      rw [infix_pair_iff faceVerts_pairwise]
      have hfv : ∀ x, e.1 ≤ x → x ≤ e.2 → x ∈ faceVerts pg n s := by
        intro x hx1 hx2
        have hw := h1
        simp only [Within] at hw
        rw [mem_faceVerts]
        refine ⟨by omega, by omega, ?_⟩
        intro t ht hts hne hxt
        have := h2 t ht ⟨by omega, by omega⟩
        exact hne (Within.antisymm hts this)
      exact ⟨hfv _ le_rfl hlt.le, hfv _ hlt.le le_rfl, hlt, fun z _ hz => by omega⟩

end STACS2027.Poly

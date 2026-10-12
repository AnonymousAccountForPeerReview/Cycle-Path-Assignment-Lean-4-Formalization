module

public import Runtimes.C4.Spec
import Mathlib.Tactic

/-!
# Four-cycle listing: the bucket process

Facts about `bucket` and `reports` (`Spec.lean`) for an arbitrary insertion list `l`:

* `mem_bucket`: the bucket of `k` holds the centres inserted with key `k`;
* **B1** `length_reports_snoc`: an insertion adds as many reports as its bucket holds;
* **B2** `length_le_card_keys_add`: `|l| ≤ #keys + |reports l|` (an insertion either opens a new
  key or reports at least once);
* **B3** `mem_reports`: `(k, z, z')` is reported iff `(k, z')` is inserted before `(k, z)`;
* **B4** `nodup_reports`: without repeated insertions there are no repeated reports;
* `reports_prefix`: the reports of a prefix are a prefix of the reports (for the machine's
  time accounting).
-/

@[expose] public section

namespace STACS2027.Runtimes.C4

open STACS2027

theorem mem_bucket {l : Ins} {k : ℕ × ℕ} {z : ℕ} : z ∈ bucket l k ↔ (k, z) ∈ l := by
  simp only [bucket, List.mem_reverse, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨k', z'⟩, ⟨h, rfl⟩, rfl⟩; exact h
  · intro h; exact ⟨(k, z), ⟨h, rfl⟩, rfl⟩

theorem bucket_eq_nil {l : Ins} {k : ℕ × ℕ} : bucket l k = [] ↔ ∀ z, (k, z) ∉ l := by
  rw [List.eq_nil_iff_forall_not_mem]
  exact forall_congr' fun _ => not_congr mem_bucket

/-- **B1.** -/
theorem length_reports_snoc (l : Ins) (k : ℕ × ℕ) (z : ℕ) :
    (reports (l ++ [(k, z)])).length = (reports l).length + (bucket l k).length := by
  rw [reports_snoc, List.length_append, List.length_map]

/-- **B2.** Every insertion opens a new key or reports at least once. -/
theorem length_le_card_keys_add (l : Ins) :
    l.length ≤ (l.map Prod.fst).toFinset.card + (reports l).length := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l e ih =>
    obtain ⟨k, z⟩ := e
    rw [length_reports_snoc, List.map_append, List.toFinset_append, List.length_append]
    simp only [List.map_cons, List.map_nil, List.toFinset_cons, List.toFinset_nil,
      insert_empty_eq, List.length_singleton]
    by_cases hk : k ∈ (l.map Prod.fst).toFinset
    · rw [Finset.union_eq_left.mpr (Finset.singleton_subset_iff.mpr hk)]
      have : bucket l k ≠ [] := by
        rw [Ne, bucket_eq_nil]
        simp only [List.mem_toFinset, List.mem_map] at hk
        obtain ⟨⟨k', z'⟩, h, rfl⟩ := hk
        exact fun hn => hn z' h
      have := List.length_pos_iff.mpr this
      omega
    · rw [Finset.card_union_of_disjoint (Finset.disjoint_singleton_right.mpr hk),
        Finset.card_singleton]
      omega

theorem getElem?_snoc_lt {l : Ins} {e : (ℕ × ℕ) × ℕ} {i : ℕ} (hi : i < l.length) :
    (l ++ [e])[i]? = l[i]? := List.getElem?_append_left hi

theorem getElem?_snoc_length (l : Ins) (e : (ℕ × ℕ) × ℕ) : (l ++ [e])[l.length]? = some e := by
  simp

/-- **B3.** `(k, z, z')` is reported iff `(k, z')` is inserted before `(k, z)`. -/
theorem mem_reports {l : Ins} {k : ℕ × ℕ} {z z' : ℕ} :
    (k, z, z') ∈ reports l ↔
      ∃ i j, i < j ∧ j < l.length ∧ l[i]? = some (k, z') ∧ l[j]? = some (k, z) := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l e ih =>
    obtain ⟨k₀, z₀⟩ := e
    rw [reports_snoc, List.mem_append, ih]
    simp only [List.mem_map, mem_bucket, Prod.mk.injEq, List.length_append,
      List.length_singleton]
    constructor
    · rintro (⟨i, j, hij, hj, hi, hj'⟩ | ⟨z'', hz, rfl, rfl, rfl⟩)
      · refine ⟨i, j, hij, by omega, ?_, ?_⟩
        · rw [getElem?_snoc_lt (by omega)]; exact hi
        · rw [getElem?_snoc_lt hj]; exact hj'
      · obtain ⟨i, hie⟩ := List.mem_iff_getElem?.mp hz
        have hil : i < l.length := by
          by_contra h
          rw [List.getElem?_eq_none (by omega)] at hie
          simp at hie
        exact ⟨i, l.length, hil, by omega, by rw [getElem?_snoc_lt hil]; exact hie,
          getElem?_snoc_length _ _⟩
    · rintro ⟨i, j, hij, hj, hi, hj'⟩
      rcases Nat.lt_or_ge j l.length with hjl | hjl
      · left
        refine ⟨i, j, hij, hjl, ?_, ?_⟩
        · rw [getElem?_snoc_lt (by omega)] at hi; exact hi
        · rw [getElem?_snoc_lt hjl] at hj'; exact hj'
      · right
        have hje : j = l.length := by omega
        subst hje
        rw [getElem?_snoc_length] at hj'
        simp only [Option.some.injEq, Prod.mk.injEq] at hj'
        obtain ⟨rfl, rfl⟩ := hj'
        refine ⟨z', ?_, rfl, rfl, rfl⟩
        rw [getElem?_snoc_lt hij] at hi
        exact List.mem_of_getElem? hi

/-- The two insertions behind a report. -/
theorem mem_of_mem_reports {l : Ins} {k : ℕ × ℕ} {z z' : ℕ} (h : (k, z, z') ∈ reports l) :
    (k, z) ∈ l ∧ (k, z') ∈ l := by
  obtain ⟨i, j, -, -, hi, hj⟩ := mem_reports.mp h
  exact ⟨List.mem_of_getElem? hj, List.mem_of_getElem? hi⟩

theorem nodup_bucket {l : Ins} (hl : l.Nodup) (k : ℕ × ℕ) : (bucket l k).Nodup := by
  unfold bucket
  rw [List.nodup_reverse]
  refine (hl.filter _).map_on ?_
  intro x hx y hy hxy
  simp only [List.mem_filter, decide_eq_true_eq] at hx hy
  exact Prod.ext (hx.2.trans hy.2.symm) hxy

/-- **B4.** Without repeated insertions there are no repeated reports. -/
theorem nodup_reports {l : Ins} (hl : l.Nodup) : (reports l).Nodup := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l e ih =>
    obtain ⟨k, z⟩ := e
    have hl' : l.Nodup := hl.sublist (List.sublist_append_left _ _)
    have he : (k, z) ∉ l := by
      have := List.nodup_append.mp hl
      exact fun h => this.2.2 _ h _ (List.mem_singleton_self _) rfl
    rw [reports_snoc]
    refine List.nodup_append.mpr ⟨ih hl', ?_, ?_⟩
    · exact (nodup_bucket hl' k).map fun a b h => by simpa using h
    · rintro ⟨k', z₁, z₂⟩ h r hr rfl
      simp only [List.mem_map, Prod.mk.injEq] at hr
      obtain ⟨z'', -, rfl, rfl, rfl⟩ := hr
      exact he (mem_of_mem_reports h).1

/-- The reports of a prefix are a prefix of the reports. -/
theorem reports_prefix {l₁ l₂ : Ins} (h : l₁ <+: l₂) : reports l₁ <+: reports l₂ := by
  obtain ⟨t, rfl⟩ := h
  induction t using List.reverseRecOn with
  | nil => simp
  | append_singleton t e ih =>
    obtain ⟨k, z⟩ := e
    rw [← List.append_assoc, reports_snoc]
    exact ih.trans (List.prefix_append _ _)

theorem length_reports_le_of_prefix {l₁ l₂ : Ins} (h : l₁ <+: l₂) :
    (reports l₁).length ≤ (reports l₂).length :=
  (reports_prefix h).length_le

end STACS2027.Runtimes.C4

module

public import NPHardness.PlanarSourceComputableComb

/-!
Finite comparison guards for cyclic successors. A complete list of local
incident candidates can replace the registered sorted incidence list: the
same-page key comparisons plus the page order uniquely characterize its
successor. The proofs preserve occurrence identities and multiplicities.
-/

@[expose] public section
namespace STACS2027.PlanarSource.RotationTable
open Complexity Complexity.SAT Complexity.Planar Comb

/-- A cyclic successor is the next larger item, or the minimum after the
maximum. The second alternative also handles a singleton incidence list. -/
def NextIn (lt : Nat → Nat → Prop) (candidates : List Nat) (a b : Nat) : Prop :=
  (lt a b ∧ ∀ z ∈ candidates, ¬ (lt a z ∧ lt z b)) ∨
  ((∀ z ∈ candidates, ¬ lt a z) ∧ (∀ z ∈ candidates, ¬ lt z b))

theorem nextIn_congr (lt : Nat → Nat → Prop) {xs ys : List Nat}
    (hmem : ∀ z, z ∈ xs ↔ z ∈ ys) (a b : Nat) : NextIn lt xs a b ↔ NextIn lt ys a b := by
  unfold NextIn
  constructor <;> intro h
  · rcases h with ⟨hab,hn⟩ | ⟨ha,hb⟩
    · exact Or.inl ⟨hab, fun z hz => hn z ((hmem z).mpr hz)⟩
    · exact Or.inr ⟨fun z hz => ha z ((hmem z).mpr hz), fun z hz => hb z ((hmem z).mpr hz)⟩
  · rcases h with ⟨hab,hn⟩ | ⟨ha,hb⟩
    · exact Or.inl ⟨hab, fun z hz => hn z ((hmem z).mp hz)⟩
    · exact Or.inr ⟨fun z hz => ha z ((hmem z).mp hz), fun z hz => hb z ((hmem z).mp hz)⟩

theorem sorted_index_iff {lt : Nat → Nat → Prop} {xs : List Nat}
    (hs : xs.Pairwise lt) (hi : ∀ a, ¬ lt a a)
    (ha : ∀ a b, lt a b → ¬ lt b a)
    (p q : Nat) (hp : p < xs.length) (hq : q < xs.length) :
    lt xs[p] xs[q] ↔ p < q := by
  constructor
  · intro h
    by_cases he : p = q
    · subst q; exact False.elim (hi _ h)
    by_cases hn : p < q
    · exact hn
    exact False.elim (ha _ _ (List.pairwise_iff_getElem.mp hs q p hq hp (by omega)) h)
  · exact List.pairwise_iff_getElem.mp hs p q hp hq

theorem nextIn_indices {lt : Nat → Nat → Prop} {xs : List Nat}
    (hs : xs.Pairwise lt) (hi : ∀ a, ¬ lt a a)
    (ha : ∀ a b, lt a b → ¬ lt b a)
    (p q : Nat) (hp : p < xs.length) (hq : q < xs.length) :
    NextIn lt xs xs[p] xs[q] ↔ q = (p + 1) % xs.length := by
  have hs' := sorted_index_iff hs hi ha
  constructor
  · intro h
    rcases h with ⟨hab, hn⟩ | ⟨hmax, hmin⟩
    · have hpq := (hs' p q hp hq).mp hab
      have hpn : p + 1 < xs.length := by omega
      have hsucc : q = p + 1 := by
        by_cases hne : q = p + 1
        · exact hne
        exact False.elim (hn xs[p+1] (List.getElem_mem hpn)
          ⟨(hs' p (p+1) hp hpn).mpr (by omega), (hs' (p+1) q hpn hq).mpr (by omega)⟩)
      rw [Nat.mod_eq_of_lt hpn]
      exact hsucc
    · have hpmax : p + 1 = xs.length := by
        by_cases hne : p + 1 = xs.length
        · exact hne
        have hpn : p + 1 < xs.length := by omega
        exact False.elim (hmax xs[p+1] (List.getElem_mem hpn) ((hs' p (p+1) hp hpn).mpr (by omega)))
      have hqmin : q = 0 := by
        by_cases hne : q = 0
        · exact hne
        have hz : 0 < xs.length := by omega
        exact False.elim (hmin xs[0] (List.getElem_mem hz) ((hs' 0 q hz hq).mpr (by omega)))
      rw [hpmax, Nat.mod_self]
      exact hqmin
  · intro hqeq
    by_cases hpn : p + 1 < xs.length
    · have hqsucc : q = p + 1 := by rwa [Nat.mod_eq_of_lt hpn] at hqeq
      apply Or.inl
      refine ⟨(hs' p q hp hq).mpr (by omega), ?_⟩
      intro z hz hbetween
      obtain ⟨r, hr, rfl⟩ := mem_getElem hz
      have hl := (hs' p r hp hr).mp hbetween.1
      have hu := (hs' r q hr hq).mp hbetween.2
      omega
    · have hpmax : p + 1 = xs.length := by omega
      have hqzero : q = 0 := by simpa [hpmax] using hqeq
      apply Or.inr
      constructor
      · intro z hz hlt
        obtain ⟨r, hr, rfl⟩ := mem_getElem hz
        have hh := (hs' p r hp hr).mp hlt
        omega
      · intro z hz hlt
        obtain ⟨r, hr, rfl⟩ := mem_getElem hz
        have hh := (hs' r q hr hq).mp hlt
        omega

/-- A complete fixed candidate list needs only comparisons, not sorting. -/
theorem nextIn_iff_rnext {lt : Nat → Nat → Prop} {xs candidates : List Nat}
    (hs : xs.Pairwise lt) (hi : ∀ a, ¬ lt a a)
    (ha : ∀ a b, lt a b → ¬ lt b a)
    (hmem : ∀ z, z ∈ candidates ↔ z ∈ xs)
    {a b : Nat} (hamem : a ∈ xs) (hbmem : b ∈ xs) :
    NextIn lt candidates a b ↔ rnext xs a = b := by
  rw [nextIn_congr lt hmem]
  obtain ⟨p,hp,rfl⟩ := mem_getElem hamem
  obtain ⟨q,hq,rfl⟩ := mem_getElem hbmem
  have hnd : xs.Nodup := hs.imp (fun hab he => by cases he; exact hi _ hab)
  rw [nextIn_indices hs hi ha p q hp hq, rnext_getElem hnd hp]
  constructor
  · intro h; subst q; rfl
  · intro h
    have hh := congrArg xs.idxOf h
    rw [idxOf_getElem hnd (Nat.mod_lt _ (by omega)), idxOf_getElem hnd hq] at hh
    exact hh.symm

/-- Top legs precede bottom legs; on each page use the registered angular key. -/
def Before (f : CNF) (a b : Nat) : Prop :=
  (isTop f (oj f a) = true ∧ isTop f (oj f b) = false) ∨
  (isTop f (oj f a) = isTop f (oj f b) ∧ key f a < key f b)

theorem before_irrefl (f : CNF) (a : Nat) : ¬ Before f a a := by
  intro h
  rcases h with ⟨ht,hf⟩ | ⟨_,hk⟩ <;> simp_all

theorem before_asymm (f : CNF) (a b : Nat) : Before f a b → ¬ Before f b a := by
  intro hab hba
  rcases hab with ⟨ha,hb⟩ | ⟨he,hk⟩ <;>
    rcases hba with ⟨hb',ha'⟩ | ⟨he',hk'⟩ <;> simp_all <;> omega

/-- Actual incidence order at a variable, with the two spine darts removed. -/
def incidenceOrder (f : CNF) (v : Nat) : List Nat :=
  group f true v ++ group f false (nK f - 1 - v)

theorem incidenceOrder_sorted {f : CNF} (h : CombOK f) (v : Nat) :
    (incidenceOrder f v).Pairwise (Before f) := by
  apply List.pairwise_append.mpr
  refine ⟨?_, ?_, ?_⟩
  · apply (group_sorted (s := true) (v := v) h).imp_of_mem
    intro a b ha hb hk
    exact Or.inr ⟨(mem_group.mp ha).2.1.trans (mem_group.mp hb).2.1.symm, hk⟩
  · apply (group_sorted (s := false) (v := nK f - 1 - v) h).imp_of_mem
    intro a b ha hb hk
    exact Or.inr ⟨(mem_group.mp ha).2.1.trans (mem_group.mp hb).2.1.symm, hk⟩
  · intro a ha b hb
    exact Or.inl ⟨(mem_group.mp ha).2.1, (mem_group.mp hb).2.1⟩

theorem incidenceOrder_nodup {f : CNF} (h : CombOK f) (v : Nat) :
    (incidenceOrder f v).Nodup :=
  (incidenceOrder_sorted h v).imp (fun hab he => by cases he; exact before_irrefl f _ hab)

/-- Matching all local incident occurrences is enough to replace the
registered sorted order by a finite conjunction of comparison guards. -/
theorem incidence_next_iff {f : CNF} (h : CombOK f) (v : Nat) (candidates : List Nat)
    (hmem : ∀ z, z ∈ candidates ↔ z ∈ incidenceOrder f v)
    {a b : Nat} (ha : a ∈ candidates) (hb : b ∈ candidates) :
    NextIn (Before f) candidates a b ↔ rnext (incidenceOrder f v) a = b :=
  nextIn_iff_rnext (incidenceOrder_sorted h v) (before_irrefl f) (before_asymm f)
    hmem ((hmem a).mp ha) ((hmem b).mp hb)

/-- The list contains precisely the literal occurrences of this variable. -/
theorem mem_incidenceOrder (f : CNF) {v e : Nat} (hv : v < nK f) :
    e ∈ incidenceOrder f v ↔ e < nM f ∧ vr f (oj f e) (ot f e) = v := by
  simp only [incidenceOrder, List.mem_append, mem_group]
  constructor
  · intro he
    rcases he with ⟨hb,ht,he⟩ | ⟨hb,ht,he⟩
    · refine ⟨hb, ?_⟩
      simpa [ov,opos,ht] using he
    · refine ⟨hb, ?_⟩
      have ho := occ_spec f e hb
      have hh := vr_lt (f := f) _ _ ho.1 ho.2.1
      have hh' : nK f - 1 - vr f (oj f e) (ot f e) = nK f - 1 - v := by
        simpa [ov,opos,ht] using he
      omega
  · rintro ⟨hb,he⟩
    cases ht : isTop f (oj f e)
    · apply Or.inr
      exact ⟨hb,ht,by simp [ov,opos,ht,he]⟩
    · apply Or.inl
      exact ⟨hb,ht,by simp [ov,opos,ht,he]⟩

/-- The finite descriptor table only needs an ordinary occurrence-membership
proof; all ordering is supplied by the registered angular key. -/
theorem variable_next_iff {f : CNF} (h : CombOK f) {v : Nat} (hv : v < nK f)
    (candidates : List Nat)
    (hmem : ∀ z, z ∈ candidates ↔ z < nM f ∧ vr f (oj f z) (ot f z) = v)
    {a b : Nat} (ha : a ∈ candidates) (hb : b ∈ candidates) :
    NextIn (Before f) candidates a b ↔ rnext (incidenceOrder f v) a = b :=
  incidence_next_iff h v candidates (fun z => (hmem z).trans (mem_incidenceOrder f hv).symm) ha hb

end STACS2027.PlanarSource.RotationTable

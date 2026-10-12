module

public import NPHardness.PlanarSourceEmbeddingCounts
public import NPHardness.PlanarGluingTransposition
import Lean.Elab.Tactic.Omega

/-!
# First-return permutations

For a permutation `p` of `Fin n` and a set `S` of darts, the first-return map sends a dart of `S`
to the first later dart of its `p`-orbit that lies in `S`; outside `S` it is the identity
(`firstReturn`). Its orbits on `S` are the traces on `S` of the orbits of `p`
(`reaches_firstReturn_iff`), so when every orbit of `p` meets `S`, it has exactly as many cycles as
`p` plus one fixed point for every dart outside `S` (`cycleCount_firstReturn`).

This is the counting tool behind the planarity test: contracting a spanning forest of an embedded
graph replaces the face permutation by its first return to the non-forest darts.
-/

@[expose] public section

namespace STACS2027.Embed

open Complexity Complexity.Planar STACS2027.PlanarGluing STACS2027.PlanarSource.Embedding

variable {n : Nat}

/-- The orbit of `x` meets `S` after at least one step. -/
def Meets (p : Fin n → Fin n) (S : Fin n → Bool) (x : Fin n) : Prop :=
  ∃ k, 0 < k ∧ S (iterate p k x) = true

/-- The first positive time at which the orbit of `x` meets `S` (`0` if it never does). -/
noncomputable def hitTime (p : Fin n → Fin n) (S : Fin n → Bool) (x : Fin n) : Nat :=
  open Classical in
  if h : Meets p S x then Classical.choose (exists_least h) else 0

theorem hitTime_spec {p : Fin n → Fin n} {S : Fin n → Bool} {x : Fin n} (h : Meets p S x) :
    0 < hitTime p S x ∧ S (iterate p (hitTime p S x) x) = true ∧
      ∀ k, 0 < k → k < hitTime p S x → S (iterate p k x) = false := by
  unfold hitTime
  rw [dite_eq_left h]
  obtain ⟨⟨h1, h2⟩, h3⟩ := Classical.choose_spec (exists_least h)
  refine ⟨h1, h2, fun k hk hkt => ?_⟩
  cases hs : S (iterate p k x)
  · rfl
  · exact absurd ⟨hk, hs⟩ (h3 k hkt)

/-- The first-return map of `p` to `S`, the identity outside `S`. -/
noncomputable def firstReturn (p : Fin n → Fin n) (S : Fin n → Bool) (x : Fin n) : Fin n :=
  if S x then iterate p (hitTime p S x) x else x

theorem meets_of_perm {p : Fin n → Fin n} (hp : ∀ a b, p a = p b → a = b) (S : Fin n → Bool)
    {x : Fin n} (hx : S x = true) : Meets p S x := by
  obtain ⟨T, hT, _, he⟩ := period hp x
  exact ⟨T, hT, by rw [he]; exact hx⟩

theorem firstReturn_mem {p : Fin n → Fin n} (hp : ∀ a b, p a = p b → a = b) {S : Fin n → Bool}
    {x : Fin n} (hx : S x = true) : S (firstReturn p S x) = true := by
  unfold firstReturn
  rw [ite_eq_left hx]
  exact (hitTime_spec (meets_of_perm hp S hx)).2.1

theorem firstReturn_of_not {p : Fin n → Fin n} {S : Fin n → Bool} {x : Fin n} (hx : S x = false) :
    firstReturn p S x = x := by
  unfold firstReturn
  rw [ite_eq_right (by simp [hx])]

theorem firstReturn_of_mem {p : Fin n → Fin n} {S : Fin n → Bool} {x : Fin n} (hx : S x = true) :
    firstReturn p S x = iterate p (hitTime p S x) x := by
  unfold firstReturn
  rw [ite_eq_left hx]

/-- A dart of `S` reached from a dart of `S` is reached by the first-return map. -/
theorem reaches_firstReturn_of_iterate {p : Fin n → Fin n} (hp : ∀ a b, p a = p b → a = b)
    {S : Fin n → Bool} : ∀ k (x : Fin n), S x = true → S (iterate p k x) = true →
      Reaches (firstReturn p S) x (iterate p k x) := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro x hx hk
    by_cases hk0 : k = 0
    · subst hk0; exact Reaches.refl _ _
    · obtain ⟨h1, _, h3⟩ := hitTime_spec (meets_of_perm hp S hx)
      by_cases hlt : k < hitTime p S x
      · rw [h3 k (by omega) hlt] at hk; exact absurd hk (by simp)
      · have hsplit : iterate p k x = iterate p (k - hitTime p S x) (firstReturn p S x) := by
          rw [firstReturn_of_mem hx, ← iterate_add, show hitTime p S x + (k - hitTime p S x) = k by omega]
        rw [hsplit] at hk ⊢
        exact (Reaches.step _ x).trans
          (ih (k - hitTime p S x) (by omega) _ (firstReturn_mem hp hx) hk)

/-- The first-return map reaches exactly the darts of `S` on the same `p`-orbit. -/
theorem reaches_firstReturn_iff {p : Fin n → Fin n} (hp : ∀ a b, p a = p b → a = b)
    {S : Fin n → Bool} {x y : Fin n} (hx : S x = true) :
    Reaches (firstReturn p S) x y ↔ S y = true ∧ Reaches p x y := by
  constructor
  · rintro ⟨k, rfl⟩
    induction k generalizing x with
    | zero => exact ⟨hx, Reaches.refl _ _⟩
    | succ k ih =>
      obtain ⟨h1, h2⟩ := ih (firstReturn_mem hp hx)
      refine ⟨h1, ?_⟩
      have hstep : Reaches p x (firstReturn p S x) := by
        rw [firstReturn_of_mem hx]; exact ⟨_, rfl⟩
      exact hstep.trans h2
  · rintro ⟨hy, k, rfl⟩
    exact reaches_firstReturn_of_iterate hp k x hx hy

theorem firstReturn_injective {p : Fin n → Fin n} (hp : ∀ a b, p a = p b → a = b)
    (S : Fin n → Bool) : ∀ a b, firstReturn p S a = firstReturn p S b → a = b := by
  intro a b h
  cases ha : S a <;> cases hb : S b
  · rwa [firstReturn_of_not ha, firstReturn_of_not hb] at h
  · -- `a ∉ S`, `b ∈ S`: impossible
    have := firstReturn_mem hp hb
    rw [← h, firstReturn_of_not ha, ha] at this
    exact absurd this (by simp)
  · have := firstReturn_mem hp ha
    rw [h, firstReturn_of_not hb, hb] at this
    exact absurd this (by simp)
  · -- both in `S`: compare the hit times
    have hra := firstReturn_of_mem (p := p) ha
    have hrb := firstReturn_of_mem (p := p) hb
    obtain ⟨a1, a2, a3⟩ := hitTime_spec (meets_of_perm hp S ha)
    obtain ⟨b1, b2, b3⟩ := hitTime_spec (meets_of_perm hp S hb)
    rw [hra, hrb] at h
    rcases Nat.lt_trichotomy (hitTime p S a) (hitTime p S b) with hl | he | hl
    · -- `a` is reached from `b` strictly before `b`'s first hit
      have h' : iterate p (hitTime p S a) a =
          iterate p (hitTime p S a) (iterate p (hitTime p S b - hitTime p S a) b) := by
        rw [h, ← iterate_add, show hitTime p S b - hitTime p S a + hitTime p S a = hitTime p S b by omega]
      have hab := iterate_inj hp _ h'
      have := b3 (hitTime p S b - hitTime p S a) (by omega) (by omega)
      rw [← hab, ha] at this
      exact absurd this (by simp)
    · rw [he] at h
      exact iterate_inj hp _ h
    · have h' : iterate p (hitTime p S b) b =
          iterate p (hitTime p S b) (iterate p (hitTime p S a - hitTime p S b) a) := by
        rw [← h, ← iterate_add, show hitTime p S a - hitTime p S b + hitTime p S b = hitTime p S a by omega]
      have hab := iterate_inj hp _ h'
      have := a3 (hitTime p S a - hitTime p S b) (by omega) (by omega)
      rw [← hab, hb] at this
      exact absurd this (by simp)

/-! ### Counting cycles -/

/-- The orbit of `x` meets `S` (as a Boolean test over the first `n` iterates). -/
def MeetsB (p : Fin n → Fin n) (S : Fin n → Bool) (x : Fin n) : Bool :=
  (List.range n).any fun k => S (iterate p k x)

theorem meetsB_iff {p : Fin n → Fin n} (hp : ∀ a b, p a = p b → a = b) (S : Fin n → Bool) (x : Fin n) :
    MeetsB p S x = true ↔ ∃ k, S (iterate p k x) = true := by
  unfold MeetsB
  rw [List.any_eq_true]
  constructor
  · rintro ⟨k, -, hk⟩; exact ⟨k, hk⟩
  · rintro ⟨k, hk⟩
    obtain ⟨i, hi, he⟩ := iterate_mod hp x k
    exact ⟨i, List.mem_range.mpr hi, by rw [← he]; exact hk⟩

theorem meetsB_of_reaches {p : Fin n → Fin n} (hp : ∀ a b, p a = p b → a = b) (S : Fin n → Bool)
    {x y : Fin n} (h : Reaches p x y) : MeetsB p S x = MeetsB p S y := by
  obtain ⟨j, rfl⟩ := h
  apply Bool.eq_iff_iff.mpr
  rw [meetsB_iff hp, meetsB_iff hp]
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨r, hr⟩ := back hp j x
    exact ⟨r + k, by rw [iterate_add, hr]; exact hk⟩
  · rintro ⟨k, hk⟩
    exact ⟨j + k, by rw [iterate_add]; exact hk⟩

/-- The number of orbits of `p` that do not meet `S`. -/
def avoidCount (p : Fin n → Fin n) (S : Fin n → Bool) : Nat :=
  (List.finRange n).countP fun x => CycleMin p x && !MeetsB p S x

theorem exists_smin {p : Fin n → Fin n} {S : Fin n → Bool} {x : Fin n}
    (h : ∃ k, S (iterate p k x) = true) :
    ∃ m : Nat, (∃ y : Fin n, y.val = m ∧ S y = true ∧ Reaches p x y) ∧
      ∀ m', m' < m → ¬ ∃ y : Fin n, y.val = m' ∧ S y = true ∧ Reaches p x y := by
  obtain ⟨k, hk⟩ := h
  exact exists_least ⟨_, iterate p k x, rfl, hk, k, rfl⟩

/-- The least dart of `S` on the orbit of `x` (`x` itself if the orbit avoids `S`). -/
noncomputable def smin (p : Fin n → Fin n) (S : Fin n → Bool) (x : Fin n) : Fin n :=
  open Classical in
  if h : ∃ k, S (iterate p k x) = true then Classical.choose (Classical.choose_spec (exists_smin h)).1
  else x

theorem smin_spec {p : Fin n → Fin n} {S : Fin n → Bool} {x : Fin n} (h : ∃ k, S (iterate p k x) = true) :
    S (smin p S x) = true ∧ Reaches p x (smin p S x) ∧
      ∀ y : Fin n, S y = true → Reaches p x y → (smin p S x).val ≤ y.val := by
  unfold smin
  rw [dite_eq_left h]
  have hm := Classical.choose_spec (exists_smin h)
  obtain ⟨hv, hs, hr⟩ := Classical.choose_spec hm.1
  refine ⟨hs, hr, fun y hy hry => ?_⟩
  rcases Nat.lt_or_ge y.val (Classical.choose (Classical.choose_spec (exists_smin h)).1).val with hlt | hge
  · exact absurd ⟨y, rfl, hy, hry⟩ (hm.2 y.val (by rw [← hv]; exact hlt))
  · exact hge

theorem smin_eq_of_reaches {p : Fin n → Fin n} (hp : ∀ a b, p a = p b → a = b) {S : Fin n → Bool}
    {x y : Fin n} (hm : ∃ k, S (iterate p k x) = true) (hxy : Reaches p x y) : smin p S x = smin p S y := by
  have hm' : ∃ k, S (iterate p k y) = true := (meetsB_iff hp S y).mp
    ((meetsB_of_reaches hp S hxy) ▸ (meetsB_iff hp S x).mpr hm)
  obtain ⟨s1, r1, m1⟩ := smin_spec hm
  obtain ⟨s2, r2, m2⟩ := smin_spec hm'
  have a := m1 _ s2 (hxy.trans r2)
  have b := m2 _ s1 ((hxy.symm hp).trans r1)
  exact Fin.ext (by omega)

/-- **Cycle count of a first-return map.** The first-return map has one cycle for every orbit of
`p` meeting `S`, and a fixed point for every dart outside `S`. -/
theorem cycleCount_firstReturn_avoid {p : Fin n → Fin n} (hp : ∀ a b, p a = p b → a = b)
    (S : Fin n → Bool) :
    cycleCount (firstReturn p S) + avoidCount p S =
      cycleCount p + (List.finRange n).countP (fun x => !S x) := by
  let q := firstReturn p S
  have hq := firstReturn_injective hp S
  let mins : List (Fin n) := (List.finRange n).filter fun x => decide (S x = true ∧ smin p S x = x)
  let amins : List (Fin n) := (List.finRange n).filter fun x => CycleMin p x && !MeetsB p S x
  let outs : List (Fin n) := (List.finRange n).filter fun x => !S x
  have hmins_nd : mins.Nodup := (List.nodup_finRange n).filter _
  have hamins_nd : amins.Nodup := (List.nodup_finRange n).filter _
  have houts_nd : outs.Nodup := (List.nodup_finRange n).filter _
  have hmem_mins : ∀ x, x ∈ mins ↔ S x = true ∧ smin p S x = x := by intro x; simp [mins]
  have hmem_amins : ∀ x, x ∈ amins ↔ CycleMin p x = true ∧ MeetsB p S x = false := by
    intro x; simp [amins]
  have hmem_outs : ∀ x, x ∈ outs ↔ S x = false := by intro x; simp [outs]
  have hmeets : ∀ x, MeetsB p S x = true ↔ ∃ k, S (iterate p k x) = true := meetsB_iff hp S
  have hsmin_mins : ∀ x, MeetsB p S x = true → smin p S x ∈ mins := by
    intro x hx
    have h := (hmeets x).mp hx
    rw [hmem_mins]
    exact ⟨(smin_spec h).1, (smin_eq_of_reaches hp h (smin_spec h).2.1).symm⟩
  have hmins_meet : ∀ x, x ∈ mins → MeetsB p S x = true := by
    intro x hx
    exact (hmeets x).mpr ⟨0, ((hmem_mins x).mp hx).1⟩
  -- the cycles of `p`: one minimum of `S` or one cycle minimum each
  let labp : Fin n → Sum (Fin n) (Fin n) := fun x => if MeetsB p S x then .inl (smin p S x) else .inr (cmin p x)
  have hlabp : ∀ x, labp (p x) = labp x := by
    intro x
    have hr := Reaches.step p x
    have hm := meetsB_of_reaches hp S hr
    by_cases h : MeetsB p S x = true
    · have h' : MeetsB p S (p x) = true := hm ▸ h
      simp only [labp, h, h', ↓reduceIte]
      rw [smin_eq_of_reaches hp ((hmeets x).mp h) hr]
    · have h' : MeetsB p S (p x) = false := by rw [← hm]; simpa using h
      have h'' : MeetsB p S x = false := by simpa using h
      simp only [labp, h', h'', Bool.false_eq_true, ↓reduceIte]
      rw [cmin_step hp]
  have hp_ge : (mins ++ amins).length ≤ cycleCount p := by
    apply cycleCount_ge p labp hlabp
    rw [List.map_append, List.nodup_append]
    refine ⟨?_, ?_, ?_⟩
    · apply nodup_map_of_injOn' _ hmins_nd
      intro a ha b hb hab
      have ma := hmins_meet a ha
      have mb := hmins_meet b hb
      simp only [labp, ma, mb, ↓reduceIte, Sum.inl.injEq] at hab
      rw [← ((hmem_mins a).mp ha).2, ← ((hmem_mins b).mp hb).2, hab]
    · apply nodup_map_of_injOn' _ hamins_nd
      intro a ha b hb hab
      obtain ⟨ca, ma⟩ := (hmem_amins a).mp ha
      obtain ⟨cb, mb⟩ := (hmem_amins b).mp hb
      simp only [labp, ma, mb, Bool.false_eq_true, ↓reduceIte, Sum.inr.injEq] at hab
      rw [← (cmin_eq_iff hp a).mpr ca, ← (cmin_eq_iff hp b).mpr cb, hab]
    · intro u hu v hv huv
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hu
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hv
      have ma := hmins_meet a ha
      have mb := ((hmem_amins b).mp hb).2
      simp [labp, ma, mb] at huv
  have hp_le : cycleCount p ≤ (mins ++ amins).length := by
    apply cycleCount_le_representatives hp (fun x => if MeetsB p S x then smin p S x else cmin p x)
      (mins ++ amins)
    · intro x
      split
      · exact (smin_spec ((hmeets x).mp ‹_›)).2.1
      · exact reaches_cmin p x
    · intro x
      split
      · exact List.mem_append_left _ (hsmin_mins x ‹_›)
      · rename_i h
        apply List.mem_append_right
        rw [hmem_amins]
        refine ⟨(cmin_eq_iff hp _).mp ?_, ?_⟩
        · rw [cmin_eq_iff_reaches hp]; exact (reaches_cmin p x).symm hp
        · rw [← meetsB_of_reaches hp S (reaches_cmin p x)]; simpa using h
  -- the cycles of `q`
  let lab : Fin n → Sum (Fin n) (Fin n) := fun x => if S x then .inl (smin p S x) else .inr x
  have hlab : ∀ x, lab (q x) = lab x := by
    intro x
    cases hx : S x
    · simp only [lab, q, firstReturn_of_not hx, hx]
    · have hm := firstReturn_mem hp hx
      have hr : Reaches p x (firstReturn p S x) := by
        rw [firstReturn_of_mem hx]; exact ⟨_, rfl⟩
      simp only [lab, q, hm, hx, ↓reduceIte]
      rw [smin_eq_of_reaches hp ⟨0, hx⟩ hr]
  have hq_ge : (mins ++ outs).length ≤ cycleCount q := by
    apply cycleCount_ge q lab hlab
    rw [List.map_append, List.nodup_append]
    refine ⟨?_, ?_, ?_⟩
    · apply nodup_map_of_injOn' _ hmins_nd
      intro a ha b hb hab
      obtain ⟨sa, ma⟩ := (hmem_mins a).mp ha
      obtain ⟨sb, mb⟩ := (hmem_mins b).mp hb
      simp only [lab, sa, sb, ↓reduceIte, Sum.inl.injEq] at hab
      rw [← ma, ← mb, hab]
    · apply nodup_map_of_injOn' _ houts_nd
      intro a ha b hb hab
      have sa := (hmem_outs a).mp ha
      have sb := (hmem_outs b).mp hb
      simpa [lab, sa, sb] using hab
    · intro u hu v hv huv
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hu
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hv
      have sa := ((hmem_mins a).mp ha).1
      have sb := (hmem_outs b).mp hb
      simp [lab, sa, sb] at huv
  have hq_le : cycleCount q ≤ (mins ++ outs).length := by
    apply cycleCount_le_representatives hq (fun x => if S x then smin p S x else x) (mins ++ outs)
    · intro x
      cases hx : S x
      · simp only [Bool.false_eq_true, ↓reduceIte]; exact Reaches.refl _ _
      · simp only [↓reduceIte]
        have h : ∃ k, S (iterate p k x) = true := ⟨0, hx⟩
        exact (reaches_firstReturn_iff hp hx).mpr ⟨(smin_spec h).1, (smin_spec h).2.1⟩
    · intro x
      cases hx : S x
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact List.mem_append_right _ ((hmem_outs x).mpr hx)
      · simp only [↓reduceIte]
        exact List.mem_append_left _ (hsmin_mins x ((hmeets x).mpr ⟨0, hx⟩))
  have hlen : outs.length = (List.finRange n).countP (fun x => !S x) := by
    simp only [outs, List.countP_eq_length_filter]
  have hlen2 : amins.length = avoidCount p S := by
    simp only [amins, avoidCount, List.countP_eq_length_filter]
  rw [List.length_append] at hq_ge hq_le hp_ge hp_le
  show cycleCount q + _ = cycleCount p + _
  omega

/-- Every orbit of `p` meets `S`. -/
def AllMeet (p : Fin n → Fin n) (S : Fin n → Bool) : Prop := ∀ x, ∃ k, S (iterate p k x) = true

theorem avoidCount_eq_zero {p : Fin n → Fin n} (hp : ∀ a b, p a = p b → a = b) {S : Fin n → Bool}
    (h : AllMeet p S) : avoidCount p S = 0 := by
  unfold avoidCount
  rw [List.countP_eq_zero]
  intro x _
  have := (meetsB_iff hp S x).mpr (h x)
  simp [this]

/-- If every orbit of `p` meets `S`, the first-return map has the cycles of `p` and a fixed point
for every dart outside `S`. -/
theorem cycleCount_firstReturn {p : Fin n → Fin n} (hp : ∀ a b, p a = p b → a = b) {S : Fin n → Bool}
    (h : AllMeet p S) :
    cycleCount (firstReturn p S) = cycleCount p + (List.finRange n).countP (fun x => !S x) := by
  have := cycleCount_firstReturn_avoid hp S
  rw [avoidCount_eq_zero hp h] at this
  omega

end STACS2027.Embed

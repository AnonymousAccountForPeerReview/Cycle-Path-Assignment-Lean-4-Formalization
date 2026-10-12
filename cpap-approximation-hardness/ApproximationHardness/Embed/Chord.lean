module

public import ApproximationHardness.Embed.NextIn
import Lean.Elab.Tactic.Omega

/-!
# Chord diagrams

A chord diagram on the darts `Fin n` is a set `S` of darts, a permutation `tour` of `S` (the
identity outside `S`) and a fixed-point-free involution `chord` of `S` pairing every dart with a
dart of its own `tour`-cycle. Its faces are the cycles of `tour ∘ chord`. Every `tour`-cycle is a
cyclic word, and the diagram is non-crossing (`NonCrossing`) when no two chords of a cycle
cross.

**Theorem** (`chord_excess`). `2 · faces ≤ 2 · cycles + |S|`, with equality iff the diagram is
non-crossing; for a crossing diagram the gap is at least `3`.

The proof removes a short chord (a chord joining two consecutive darts of a cycle) as long as one
exists: this keeps the gap and the crossings. A non-crossing diagram with a chord has a short
chord (a chord of least span is short), and a diagram without short chords has no fixed faces,
and not only faces of length `2` (a diagram whose faces all have length `2` is a reflection of
each cycle, which has a short chord or a fixed dart).
-/

@[expose] public section

namespace STACS2027.Embed

open Complexity Complexity.Planar STACS2027.PlanarGluing

variable {n : Nat}

/-! ### Counting helpers -/

theorem countP_congr' {α : Type} (l : List α) (P Q : α → Bool) (h : ∀ z ∈ l, P z = Q z) :
    l.countP P = l.countP Q := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.countP_cons, List.countP_cons, h x (List.mem_cons_self ..),
      ih (fun z hz => h z (List.mem_cons_of_mem _ hz))]

theorem countP_one {α : Type} [DecidableEq α] (l : List α) (hnd : l.Nodup) (P Q : α → Bool) {a : α}
    (ha : a ∈ l) (hQa : Q a = false) (h : ∀ z, z ≠ a → P z = Q z) :
    l.countP P = l.countP Q + (if P a then 1 else 0) := by
  induction l with
  | nil => exact absurd ha (List.not_mem_nil)
  | cons x l ih =>
    obtain ⟨hx, hl⟩ := List.nodup_cons.mp hnd
    rw [List.countP_cons, List.countP_cons]
    by_cases hxa : x = a
    · subst hxa
      rw [countP_congr' l P Q (fun z hz => h z (fun e => hx (e ▸ hz))), hQa]
      simp
    · have ha' : a ∈ l := by
        rcases List.mem_cons.mp ha with e | e
        · exact absurd e.symm hxa
        · exact e
      rw [ih hl ha', h x hxa]
      omega

theorem countP_two {α : Type} [DecidableEq α] (l : List α) (hnd : l.Nodup) (P Q : α → Bool) {a b : α}
    (hab : a ≠ b) (ha : a ∈ l) (hb : b ∈ l) (hQa : Q a = false) (hQb : Q b = false)
    (h : ∀ z, z ≠ a → z ≠ b → P z = Q z) :
    l.countP P = l.countP Q + (if P a then 1 else 0) + (if P b then 1 else 0) := by
  let R : α → Bool := fun z => if z = b then false else P z
  have h1 := countP_one l hnd P R hb (by simp [R]) (fun z hz => by simp [R, hz])
  have h2 := countP_one l hnd R Q ha (hQa) (fun z hz => by
    by_cases hzb : z = b
    · subst hzb; simp [R, hQb]
    · simp [R, hzb]; exact h z hz hzb)
  have hRa : R a = P a := by simp [R, hab]
  rw [h1, h2, hRa]

theorem countP_split {α : Type} (l : List α) (P Q : α → Bool) :
    l.countP P = l.countP (fun z => P z && Q z) + l.countP (fun z => P z && !Q z) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.countP_cons, ih]
    cases P x <;> cases Q x <;> simp <;> omega

theorem countP_add_not {α : Type} (l : List α) (P : α → Bool) :
    l.countP P + l.countP (fun z => !P z) = l.length := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.countP_cons, List.length_cons]
    cases P x <;> simp <;> omega

/-! ### Permutation helpers -/

theorem cycleMin_of_fixed {p : Fin n → Fin n} {z : Fin n} (h : p z = z) : CycleMin p z = true := by
  have hit : ∀ k, iterate p k z = z := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [iterate_succ', ih, h]
  simp [CycleMin, hit]

theorem iterate_of_fixed {p : Fin n → Fin n} {z : Fin n} (h : p z = z) : ∀ k, iterate p k z = z := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih => rw [iterate_succ', ih, h]

theorem meetsB_false {p : Fin n → Fin n} (hp : ∀ a b, p a = p b → a = b) {S : Fin n → Bool} {z : Fin n}
    (h : ∀ k, S (iterate p k z) = false) : MeetsB p S z = false := by
  cases hm : MeetsB p S z
  · rfl
  · obtain ⟨k, hk⟩ := (meetsB_iff hp S z).mp hm
    rw [h k] at hk; exact absurd hk (by simp)

theorem meetsB_true {p : Fin n → Fin n} (hp : ∀ a b, p a = p b → a = b) {S : Fin n → Bool} {z : Fin n}
    (k : Nat) (h : S (iterate p k z) = true) : MeetsB p S z = true :=
  (meetsB_iff hp S z).mpr ⟨k, h⟩

theorem hitTime0_le {p : Fin n → Fin n} {S : Fin n → Bool} {y : Fin n} {k : Nat}
    (h : S (iterate p k y) = true) : hitTime0 p S y ≤ k := by
  rcases Nat.lt_or_ge k (hitTime0 p S y) with hl | hl
  · have := (hitTime0_spec ⟨k, h⟩).2 k hl
    rw [h] at this; exact absurd this (by simp)
  · exact hl

theorem hitTime_le {p : Fin n → Fin n} {S : Fin n → Bool} {y : Fin n} {k : Nat} (hk : 0 < k)
    (h : S (iterate p k y) = true) : hitTime p S y ≤ k := by
  have hm : Meets p S y := ⟨k, hk, h⟩
  rcases Nat.lt_or_ge k (hitTime p S y) with hl | hl
  · have := (hitTime_spec hm).2.2 k hk hl
    rw [h] at this; exact absurd this (by simp)
  · exact hl

/-- The first dart of a pair `{u, c}`. -/
def pairSet (u c : Fin n) : Fin n → Bool := fun z => decide (z = u) || decide (z = c)

theorem nextIn_pair_iff {p : Fin n → Fin n} {w u c : Fin n} (huc : u ≠ c)
    (hm : MeetsFrom p (pairSet u c) w) :
    nextIn p (pairSet u c) w = u ↔ ∃ j, iterate p j w = u ∧ ∀ i, i ≤ j → iterate p i w ≠ c := by
  obtain ⟨h1, h2⟩ := hitTime0_spec hm
  constructor
  · intro h
    refine ⟨hitTime0 p (pairSet u c) w, h, fun i hi => ?_⟩
    rcases Nat.lt_or_eq_of_le hi with hl | he
    · have := h2 i hl
      intro hc
      rw [hc] at this; simp [pairSet] at this
    · rw [he]; unfold nextIn at h; rw [h]; exact huc
  · rintro ⟨j, hj, hno⟩
    have hle : hitTime0 p (pairSet u c) w ≤ j := hitTime0_le (by rw [hj]; simp [pairSet])
    have hmem := h1
    simp only [pairSet, Bool.or_eq_true, decide_eq_true_eq] at hmem
    rcases hmem with hm | hm
    · exact hm
    · exact absurd hm (hno _ hle)

/-! ### Diagrams -/

/-- A chord diagram: a permutation `tour` of `S` and an involution `chord` of `S`, without fixed
points, inside the cycles of `tour`. -/
structure Diagram (n : Nat) where
  S : Fin n → Bool
  tour : Fin n → Fin n
  chord : Fin n → Fin n
  tour_inj : ∀ a b, tour a = tour b → a = b
  tour_fix : ∀ x, S x = false → tour x = x
  chord_invol : ∀ x, chord (chord x) = x
  chord_fix : ∀ x, S x = false → chord x = x
  chord_ne : ∀ x, S x = true → chord x ≠ x
  chord_reach : ∀ x, Reaches tour x (chord x)

namespace Diagram

variable (D : Diagram n)

/-- The face permutation `tour ∘ chord`. -/
def faces (z : Fin n) : Fin n := D.tour (D.chord z)

theorem chord_inj {a b : Fin n} (h : D.chord a = D.chord b) : a = b := by
  rw [← D.chord_invol a, h, D.chord_invol]

theorem chord_mem {x : Fin n} (hx : D.S x = true) : D.S (D.chord x) = true := by
  cases h : D.S (D.chord x)
  · have := D.chord_fix _ h
    rw [D.chord_invol] at this
    exact absurd this.symm (D.chord_ne x hx)
  · rfl

theorem tour_mem {x : Fin n} (hx : D.S x = true) : D.S (D.tour x) = true := by
  cases h : D.S (D.tour x)
  · have h2 := D.tour_inj _ _ (D.tour_fix _ h)
    rw [h2, hx] at h; exact absurd h (by simp)
  · rfl

theorem iterate_mem {x : Fin n} (hx : D.S x = true) : ∀ k, D.S (iterate D.tour k x) = true := by
  intro k
  induction k with
  | zero => exact hx
  | succ k ih => rw [iterate_succ']; exact D.tour_mem ih

theorem faces_inj : ∀ a b, D.faces a = D.faces b → a = b :=
  fun _ _ h => D.chord_inj (D.tour_inj _ _ h)

theorem faces_fix {z : Fin n} (hz : D.S z = false) : D.faces z = z := by
  unfold faces; rw [D.chord_fix z hz, D.tour_fix z hz]

theorem faces_mem {z : Fin n} (hz : D.S z = true) : D.S (D.faces z) = true :=
  D.tour_mem (D.chord_mem hz)

theorem tour_ne_self {x : Fin n} (hx : D.S x = true) : D.tour x ≠ x := by
  intro h
  obtain ⟨k, hk⟩ := D.chord_reach x
  rw [iterate_of_fixed h] at hk
  exact D.chord_ne x hx hk.symm

theorem reach_chord_pos {x : Fin n} (hx : D.S x = true) :
    ∃ k, iterate D.tour k (D.tour x) = D.chord x := by
  obtain ⟨k, hk⟩ := D.chord_reach x
  cases k with
  | zero => exact absurd hk.symm (D.chord_ne x hx)
  | succ k => exact ⟨k, hk⟩

/-! ### Arcs -/

/-- `y` lies strictly inside the arc from `x` to its partner, along the tour. -/
def InArc (x y : Fin n) : Prop :=
  y ≠ D.chord x ∧ nextIn D.tour (pairSet y (D.chord x)) (D.tour x) = y

/-- No two chords cross. -/
def NonCrossing : Prop :=
  ∀ x y, D.S x = true → D.S y = true → y ≠ x → y ≠ D.chord x →
    (D.InArc x y ↔ D.InArc x (D.chord y))

theorem meetsFrom_pair {x : Fin n} (hx : D.S x = true) (y : Fin n) :
    MeetsFrom D.tour (pairSet y (D.chord x)) (D.tour x) := by
  obtain ⟨k, hk⟩ := D.reach_chord_pos hx
  exact ⟨k, by rw [hk]; simp [pairSet]⟩

theorem inArc_iff {x y : Fin n} (hx : D.S x = true) :
    D.InArc x y ↔ y ≠ D.chord x ∧
      ∃ j, iterate D.tour j (D.tour x) = y ∧ ∀ i, i ≤ j → iterate D.tour i (D.tour x) ≠ D.chord x := by
  constructor
  · rintro ⟨hy, h⟩
    exact ⟨hy, (nextIn_pair_iff hy (D.meetsFrom_pair hx y)).mp h⟩
  · rintro ⟨hy, h⟩
    exact ⟨hy, (nextIn_pair_iff hy (D.meetsFrom_pair hx y)).mpr h⟩

/-- Two consecutive darts other than `x` and its partner lie on the same side of the chord. -/
theorem inArc_adjacent {x u v : Fin n} (hx : D.S x = true) (huv : D.tour u = v) (hu : u ≠ x)
    (hux : u ≠ D.chord x) (hvx : v ≠ D.chord x) : D.InArc x u ↔ D.InArc x v := by
  rw [D.inArc_iff hx, D.inArc_iff hx]
  constructor
  · rintro ⟨_, j, hj, hno⟩
    refine ⟨hvx, j + 1, by rw [iterate_succ', hj, huv], fun i hi => ?_⟩
    rcases Nat.lt_or_eq_of_le hi with hl | he
    · exact hno i (by omega)
    · rw [he, iterate_succ', hj, huv]; exact hvx
  · rintro ⟨_, j, hj, hno⟩
    cases j with
    | zero =>
      exact absurd (D.tour_inj _ _ (hj.trans huv.symm)).symm hu
    | succ j =>
      refine ⟨hux, j, ?_, fun i hi => hno i (by omega)⟩
      rw [iterate_succ', ← huv] at hj
      exact D.tour_inj _ _ hj

/-! ### Short chords -/

/-- A short chord: the partner of `a` follows `a` on the tour. -/
def Short (a : Fin n) : Prop := D.S a = true ∧ D.tour a = D.chord a

/-- The span of the chord at `x`: the number of tour steps from `x` to its partner. -/
noncomputable def span (x : Fin n) : Nat := hitTime D.tour (fun z => decide (z = D.chord x)) x

theorem span_spec {x : Fin n} (hx : D.S x = true) :
    0 < D.span x ∧ iterate D.tour (D.span x) x = D.chord x := by
  obtain ⟨k, hk⟩ := D.reach_chord_pos hx
  have hm : Meets D.tour (fun z => decide (z = D.chord x)) x :=
    ⟨k + 1, by omega, by rw [iterate_succ_apply, hk]; simp⟩
  obtain ⟨h1, h2, _⟩ := hitTime_spec hm
  exact ⟨h1, of_decide_eq_true h2⟩

/-- **A non-crossing diagram with a chord has a short chord**: a chord of least span. -/
theorem exists_short (hnc : D.NonCrossing) {x0 : Fin n} (hx0 : D.S x0 = true) : ∃ a, D.Short a := by
  have hex : ∃ m, ∃ x, D.S x = true ∧ D.span x = m := ⟨_, x0, hx0, rfl⟩
  obtain ⟨m, ⟨x, hx, hxm⟩, hmin⟩ := exists_least hex
  refine ⟨x, hx, ?_⟩
  apply Classical.byContradiction
  intro hne
  let y := D.tour x
  have hy : D.S y = true := D.tour_mem hx
  have hyx : y ≠ x := D.tour_ne_self hx
  have hin : D.InArc x y := (D.inArc_iff hx).mpr ⟨hne, 0, rfl, fun i hi => by
    rw [show i = 0 by omega]; exact hne⟩
  have hin' := (hnc x y hx hy hyx hne).mp hin
  obtain ⟨_, j, hj, hno⟩ := (D.inArc_iff hx).mp hin'
  have hj0 : j ≠ 0 := by
    intro h0; rw [h0] at hj
    exact D.chord_ne y hy hj.symm
  have hsy : D.span y ≤ j := hitTime_le (by omega) (by
    show decide (iterate D.tour j y = D.chord y) = true
    exact decide_eq_true hj)
  obtain ⟨hs0, hs⟩ := D.span_spec hx
  have hsx : j + 1 < D.span x := by
    rcases Nat.lt_or_ge (j + 1) (D.span x) with h | h
    · exact h
    · exfalso
      have := hno (D.span x - 1) (by omega)
      rw [← iterate_succ_apply, show D.span x - 1 + 1 = D.span x by omega, hs] at this
      exact this rfl
  exact hmin (D.span y) (by omega) ⟨y, hy, rfl⟩

/-! ### Reflections -/

/-- **Reflection.** If every face of a nonempty diagram has length at most `2`, some chord is
short. -/
theorem exists_short_of_faces_invol (hf : ∀ z, D.S z = true → D.faces (D.faces z) = z)
    {x0 : Fin n} (hx0 : D.S x0 = true) : ∃ a, D.Short a := by
  have hstep : ∀ z, D.S z = true → D.tour (D.chord (D.tour z)) = D.chord z := by
    intro z hz
    have := hf (D.chord z) (D.chord_mem hz)
    unfold faces at this
    rwa [D.chord_invol] at this
  obtain ⟨hc0, hc⟩ := D.span_spec hx0
  have key : ∀ k, k ≤ D.span x0 →
      D.chord (iterate D.tour k x0) = iterate D.tour (D.span x0 - k) x0 := by
    intro k
    induction k with
    | zero => intro _; rw [Nat.sub_zero, hc]; rfl
    | succ k ih =>
      intro hk
      have h1 := hstep (iterate D.tour k x0) (D.iterate_mem hx0 k)
      have e1 : D.tour (iterate D.tour k x0) = iterate D.tour (k + 1) x0 := (iterate_succ' _ _ _).symm
      have e2 : iterate D.tour (D.span x0 - k) x0 = D.tour (iterate D.tour (D.span x0 - (k + 1)) x0) := by
        rw [show D.span x0 - k = (D.span x0 - (k + 1)) + 1 by omega, iterate_succ']
      rw [e1, ih (by omega), e2] at h1
      exact D.tour_inj _ _ h1
  have hdm := Nat.div_add_mod (D.span x0) 2
  rcases Nat.mod_two_eq_zero_or_one (D.span x0) with hj | hj
  · exfalso
    let j := D.span x0 / 2
    have := key j (by omega)
    rw [show D.span x0 - j = j by omega] at this
    exact D.chord_ne _ (D.iterate_mem hx0 j) this
  · let j := D.span x0 / 2
    refine ⟨iterate D.tour j x0, D.iterate_mem hx0 j, ?_⟩
    rw [key j (by omega), show D.span x0 - j = j + 1 by omega, iterate_succ']

/-! ### Removing a short chord -/

/-- The darts kept when the chord at `a` is removed. -/
def keepS (a : Fin n) : Fin n → Bool :=
  fun z => D.S z && !decide (z = a) && !decide (z = D.chord a)

theorem keepS_iff {a z : Fin n} :
    D.keepS a z = true ↔ D.S z = true ∧ z ≠ a ∧ z ≠ D.chord a := by
  simp [keepS, and_assoc]

theorem keepS_false {a z : Fin n} (h : D.keepS a z = false) :
    D.S z = false ∨ z = a ∨ z = D.chord a := by
  have : ¬ (D.S z = true ∧ z ≠ a ∧ z ≠ D.chord a) := by
    rw [← D.keepS_iff]; simp [h]
  by_cases h1 : D.S z = true
  · by_cases h2 : z = a
    · exact Or.inr (Or.inl h2)
    · by_cases h3 : z = D.chord a
      · exact Or.inr (Or.inr h3)
      · exact absurd ⟨h1, h2, h3⟩ this
  · exact Or.inl (by simpa using h1)

theorem keepS_chord {a z : Fin n} (h : D.keepS a z = true) : D.keepS a (D.chord z) = true := by
  obtain ⟨h1, h2, h3⟩ := D.keepS_iff.mp h
  refine D.keepS_iff.mpr ⟨D.chord_mem h1, fun e => h3 ?_, fun e => h2 (D.chord_inj e)⟩
  rw [← e, D.chord_invol]

theorem keepS_sub {a z : Fin n} (h : D.keepS a z = true) : D.S z = true := (D.keepS_iff.mp h).1

/-- The diagram without the chord at `a`. -/
noncomputable def remove (a : Fin n) : Diagram n where
  S := D.keepS a
  tour := firstReturn D.tour (D.keepS a)
  chord := fun z => if D.keepS a z = true then D.chord z else z
  tour_inj := firstReturn_injective D.tour_inj _
  tour_fix := fun _ h => firstReturn_of_not h
  chord_invol := by
    intro z
    by_cases h : D.keepS a z = true
    · simp only [h, ite_true, D.keepS_chord h, D.chord_invol]
    · simp [h]
  chord_fix := fun z h => by simp [h]
  chord_ne := fun z h => by simp only [h, ite_true]; exact D.chord_ne z (D.keepS_sub h)
  chord_reach := by
    intro z
    by_cases h : D.keepS a z = true
    · simp only [h, ite_true]
      exact (reaches_firstReturn_iff D.tour_inj h).mpr ⟨D.keepS_chord h, D.chord_reach z⟩
    · simp only [h]; exact Reaches.refl _ _

theorem remove_S (a : Fin n) : (D.remove a).S = D.keepS a := rfl
theorem remove_tour (a : Fin n) : (D.remove a).tour = firstReturn D.tour (D.keepS a) := rfl
theorem remove_chord {a z : Fin n} (h : D.keepS a z = true) : (D.remove a).chord z = D.chord z := by
  simp [remove, h]

/-- The value `1` if the chord at `a` forms a whole cycle of the tour. -/
noncomputable def delta (a : Fin n) : Nat := open Classical in if D.tour (D.chord a) = a then 1 else 0

section short

variable {D} {a : Fin n} (hs : D.Short a)
include hs

theorem short_ne : a ≠ D.chord a := fun h => D.chord_ne a hs.1 h.symm

theorem short_tour_chord_ne : D.tour (D.chord a) ≠ D.chord a := by
  intro h
  have := D.tour_inj _ _ (h.trans hs.2.symm)
  exact short_ne hs this.symm

/-- The number of darts outside the kept set. -/
theorem countP_not_keepS :
    (List.finRange n).countP (fun z => !D.keepS a z) = (List.finRange n).countP (fun z => !D.S z) + 2 := by
  have h := countP_two (List.finRange n) (List.nodup_finRange n) (fun z => !D.keepS a z) (fun z => !D.S z)
    (short_ne hs) (List.mem_finRange _) (List.mem_finRange _) (by simp [hs.1])
    (by simp [D.chord_mem hs.1]) (fun z h1 h2 => by simp [keepS, h1, h2])
  rw [h]; simp [keepS]

theorem countP_keepS :
    (List.finRange n).countP (D.keepS a) + 2 = (List.finRange n).countP D.S := by
  have h1 := countP_add_not (List.finRange n) (D.keepS a)
  have h2 := countP_add_not (List.finRange n) D.S
  have h3 := countP_not_keepS hs
  omega


theorem avoid_generic (p : Fin n → Fin n) (hp : ∀ a b, p a = p b → a = b)
    (hfix : ∀ z, D.S z = false → p z = z) :
    avoidCount p (D.keepS a) = (List.finRange n).countP (fun z => !D.S z) +
      (if (CycleMin p a && !MeetsB p (D.keepS a) a) then 1 else 0) +
      (if (CycleMin p (D.chord a) && !MeetsB p (D.keepS a) (D.chord a)) then 1 else 0) := by
  unfold avoidCount
  apply countP_two _ (List.nodup_finRange n) _ _ (short_ne hs) (List.mem_finRange _) (List.mem_finRange _)
    (by simp [hs.1]) (by simp [D.chord_mem hs.1])
  intro z h1 h2
  cases hz : D.S z
  · have hpz := hfix z hz
    rw [cycleMin_of_fixed hpz, meetsB_false hp (fun k => by
      rw [iterate_of_fixed hpz]; simp [keepS, hz])]
    rfl
  · have hk : D.keepS a z = true := D.keepS_iff.mpr ⟨hz, h1, h2⟩
    rw [meetsB_true hp 0 hk]; simp

theorem avoid_tour :
    avoidCount D.tour (D.keepS a) = (List.finRange n).countP (fun z => !D.S z) + D.delta a := by
  rw [avoid_generic hs D.tour D.tour_inj D.tour_fix]
  unfold delta
  have hb := hs.2
  by_cases hd : D.tour (D.chord a) = a
  · simp only [hd, ite_true]
    -- the cycle `{a, chord a}`
    have hcyc : ∀ k, iterate D.tour k a = a ∨ iterate D.tour k a = D.chord a := by
      intro k
      induction k with
      | zero => exact Or.inl rfl
      | succ k ih =>
        rw [iterate_succ']
        rcases ih with h | h
        · rw [h, hb]; exact Or.inr rfl
        · rw [h, hd]; exact Or.inl rfl
    have hmA : MeetsB D.tour (D.keepS a) a = false := meetsB_false D.tour_inj (fun k => by
      rcases hcyc k with h | h <;> rw [h] <;> simp [keepS])
    have hmB : MeetsB D.tour (D.keepS a) (D.chord a) = false := by
      rw [← hb]
      exact meetsB_false D.tour_inj (fun k => by
        rw [← iterate_succ_apply]; rcases hcyc (k + 1) with h | h <;> rw [h] <;> simp [keepS])
    rw [hmA, hmB]
    have hcm : cmin D.tour (D.chord a) = cmin D.tour a := by rw [← hb]; exact cmin_step D.tour_inj a
    obtain ⟨i, _, hi⟩ := cmin_mem (p := D.tour) a
    have hmin : cmin D.tour a = a ∨ cmin D.tour a = D.chord a := by rw [← hi]; exact hcyc i
    have hne := short_ne hs
    rcases hmin with h | h
    · have e1 : CycleMin D.tour a = true := (cmin_eq_iff D.tour_inj a).mp h
      have e2 : CycleMin D.tour (D.chord a) = false := by
        cases e : CycleMin D.tour (D.chord a)
        · rfl
        · have := (cmin_eq_iff D.tour_inj _).mpr e
          rw [hcm, h] at this; exact absurd this hne
      simp [e1, e2]
    · have e1 : CycleMin D.tour (D.chord a) = true := (cmin_eq_iff D.tour_inj _).mp (by rw [hcm, h])
      have e2 : CycleMin D.tour a = false := by
        cases e : CycleMin D.tour a
        · rfl
        · have := (cmin_eq_iff D.tour_inj _).mpr e
          rw [h] at this; exact absurd this.symm hne
      simp [e1, e2]
  · simp only [hd, ite_false]
    have hk : D.keepS a (D.tour (D.chord a)) = true :=
      D.keepS_iff.mpr ⟨D.tour_mem (D.chord_mem hs.1), hd, short_tour_chord_ne hs⟩
    have hmA : MeetsB D.tour (D.keepS a) a = true :=
      meetsB_true D.tour_inj 2 (by show D.keepS a (iterate D.tour 1 (D.tour a)) = true; rw [hb]; exact hk)
    have hmB : MeetsB D.tour (D.keepS a) (D.chord a) = true := meetsB_true D.tour_inj 1 hk
    simp [hmA, hmB]

theorem avoid_faces :
    avoidCount D.faces (D.keepS a) = (List.finRange n).countP (fun z => !D.S z) + 1 + D.delta a := by
  rw [avoid_generic hs D.faces D.faces_inj (fun z h => D.faces_fix h)]
  unfold delta
  have hb := hs.2
  have hfb : D.faces (D.chord a) = D.chord a := by unfold faces; rw [D.chord_invol, hb]
  have hB : (CycleMin D.faces (D.chord a) && !MeetsB D.faces (D.keepS a) (D.chord a)) = true := by
    rw [cycleMin_of_fixed hfb, meetsB_false D.faces_inj (fun k => by rw [iterate_of_fixed hfb]; simp [keepS])]
    rfl
  rw [hB]
  by_cases hd : D.tour (D.chord a) = a
  · have hfa : D.faces a = a := hd
    rw [cycleMin_of_fixed hfa, meetsB_false D.faces_inj (fun k => by rw [iterate_of_fixed hfa]; simp [keepS])]
    simp [hd]
  · have hk : D.keepS a (D.tour (D.chord a)) = true :=
      D.keepS_iff.mpr ⟨D.tour_mem (D.chord_mem hs.1), hd, short_tour_chord_ne hs⟩
    rw [meetsB_true D.faces_inj 1 hk]
    simp [hd]

theorem remove_faces : (D.remove a).faces = firstReturn D.faces (D.keepS a) := by
  funext z
  by_cases hz : D.keepS a z = true
  · show firstReturn D.tour (D.keepS a) (D.remove a |>.chord z) = _
    rw [D.remove_chord hz, firstReturn_eq_nextIn D.tour_inj (D.keepS_chord hz),
      firstReturn_eq_nextIn D.faces_inj hz]
    show nextIn D.tour (D.keepS a) (D.faces z) = nextIn D.faces (D.keepS a) (D.faces z)
    have hb := hs.2
    by_cases hw : D.keepS a (D.faces z) = true
    · rw [nextIn_of_mem hw, nextIn_of_mem hw]
    · have hzS := D.keepS_sub hz
      rcases D.keepS_false (Bool.eq_false_iff.mpr hw) with h | h | h
      · rw [D.faces_mem hzS] at h; exact absurd h (by simp)
      · -- `faces z = a`
        have hd : D.tour (D.chord a) ≠ a := by
          intro hd
          have : D.faces z = D.faces a := h.trans hd.symm
          have := D.faces_inj _ _ this
          exact (D.keepS_iff.mp hz).2.1 this
        have hk : D.keepS a (D.tour (D.chord a)) = true :=
          D.keepS_iff.mpr ⟨D.tour_mem (D.chord_mem hs.1), hd, short_tour_chord_ne hs⟩
        rw [h]
        have hS1 : D.keepS a a = false := by simp [keepS]
        have hS2 : D.keepS a (D.chord a) = false := by simp [keepS]
        have m1 : MeetsFrom D.tour (D.keepS a) a := ⟨2, by
          show D.keepS a (iterate D.tour 1 (D.tour a)) = true; rw [hb]; exact hk⟩
        have m2 : MeetsFrom D.tour (D.keepS a) (D.chord a) := ⟨1, hk⟩
        have m3 : MeetsFrom D.faces (D.keepS a) a := ⟨1, hk⟩
        rw [nextIn_of_not hS1 m1, hb, nextIn_of_not hS2 m2, nextIn_of_mem hk,
          nextIn_of_not hS1 m3]
        show D.tour (D.chord a) = nextIn D.faces (D.keepS a) (D.tour (D.chord a))
        rw [nextIn_of_mem hk]
      · -- `faces z = chord a`: impossible
        exfalso
        have hfb : D.faces (D.chord a) = D.chord a := by unfold faces; rw [D.chord_invol, hb]
        have := D.faces_inj _ _ (h.trans hfb.symm)
        exact (D.keepS_iff.mp hz).2.2 this
  · have hz' : D.keepS a z = false := Bool.eq_false_iff.mpr hz
    rw [firstReturn_of_not hz']
    show firstReturn D.tour (D.keepS a) ((D.remove a).chord z) = z
    simp only [remove, hz', Bool.false_eq_true, ite_false]
    exact firstReturn_of_not hz'

theorem remove_tour_count :
    cycleCount (D.remove a).tour + D.delta a = cycleCount D.tour + 2 := by
  have h := cycleCount_firstReturn_avoid D.tour_inj (D.keepS a)
  rw [avoid_tour hs, countP_not_keepS hs] at h
  rw [remove_tour]; omega

theorem remove_faces_count :
    cycleCount (D.remove a).faces + (1 + D.delta a) = cycleCount D.faces + 2 := by
  have h := cycleCount_firstReturn_avoid D.faces_inj (D.keepS a)
  rw [avoid_faces hs, countP_not_keepS hs] at h
  rw [remove_faces hs]; omega

end short

/-! ### Arcs after removal -/

/-- Walking along the first-return map to `S` meets a subset `T` of `S` where walking along `p`
does. -/
theorem nextIn_firstReturn {p : Fin n → Fin n} (hp : ∀ a b, p a = p b → a = b) {S T : Fin n → Bool}
    (hTS : ∀ x, T x = true → S x = true) {w : Fin n} (hw : S w = true) (hm : MeetsFrom p T w) :
    nextIn (firstReturn p S) T w = nextIn p T w := by
  have hm' : ∀ w, S w = true → MeetsFrom p T w → MeetsFrom (firstReturn p S) T w := by
    intro w hw ⟨k, hk⟩
    obtain ⟨j, hj⟩ := (reaches_firstReturn_iff hp hw).mpr ⟨hTS _ hk, k, rfl⟩
    exact ⟨j, by rw [hj]; exact hk⟩
  have key : ∀ k w, S w = true → MeetsFrom p T w → hitTime0 (firstReturn p S) T w = k →
      nextIn (firstReturn p S) T w = nextIn p T w := by
    intro k
    induction k with
    | zero =>
      intro w hw hm hk
      have h := (hitTime0_spec (hm' w hw hm)).1
      rw [hk] at h
      have h' : T w = true := h
      rw [nextIn_of_mem h', nextIn_of_mem h']
    | succ k ih =>
      intro w hw hm hk
      have hTw : T w = false := by
        cases h : T w
        · rfl
        · rw [hitTime0_of_mem h] at hk; omega
      have hfw := firstReturn_mem hp hw (S := S) (p := p)
      have hreach : Reaches p w (firstReturn p S w) := by rw [firstReturn_of_mem hw]; exact ⟨_, rfl⟩
      have hmf : MeetsFrom p T (firstReturn p S w) := by
        obtain ⟨j, hj⟩ := hm
        obtain ⟨r, hr⟩ := (hreach.symm hp)
        exact ⟨r + j, by rw [iterate_add, hr]; exact hj⟩
      have hk' : hitTime0 (firstReturn p S) T (firstReturn p S w) = k := by
        rw [hitTime0_of_not hTw (hm' w hw hm)] at hk; omega
      rw [nextIn_of_not hTw (hm' w hw hm), ih _ hfw hmf hk', nextIn_of_not hTw hm,
        nextIn_nextIn hTS (meetsFrom_step hTw hm), ← firstReturn_eq_nextIn hp hw]
  exact key _ w hw hm rfl

section short

variable {D} {a : Fin n} (hs : D.Short a)
include hs

omit hs in
theorem remove_inArc {x y : Fin n} (hx : D.keepS a x = true) (hy : D.keepS a y = true) :
    (D.remove a).InArc x y ↔ D.InArc x y := by
  unfold InArc
  rw [D.remove_chord hx]
  have hxS := D.keepS_sub hx
  have hcx := D.keepS_chord hx
  have hT : ∀ z, pairSet y (D.chord x) z = true → D.keepS a z = true := by
    intro z hz
    simp only [pairSet, Bool.or_eq_true, decide_eq_true_eq] at hz
    rcases hz with h | h <;> rw [h]
    · exact hy
    · exact hcx
  have hmx : MeetsFrom D.tour (D.keepS a) (D.tour x) := by
    obtain ⟨k, hk⟩ := D.reach_chord_pos hxS
    exact ⟨k, by rw [hk]; exact hcx⟩
  have hw := nextIn_mem hmx
  have hmT : MeetsFrom D.tour (pairSet y (D.chord x)) (nextIn D.tour (D.keepS a) (D.tour x)) := by
    obtain ⟨k, hk⟩ := D.reach_chord_pos hxS
    obtain ⟨r, hr⟩ := (reaches_nextIn (p := D.tour) (D.keepS a) (D.tour x)).symm D.tour_inj
    exact ⟨r + k, by rw [iterate_add, hr, hk]; simp [pairSet]⟩
  show _ ∧ nextIn (firstReturn D.tour (D.keepS a)) _ (firstReturn D.tour (D.keepS a) x) = y ↔ _
  rw [firstReturn_eq_nextIn D.tour_inj hx, nextIn_firstReturn D.tour_inj hT hw hmT,
    ← nextIn_nextIn hT (D.meetsFrom_pair hxS y)]

theorem inArc_short_false (y : Fin n) : ¬ D.InArc a y := by
  rintro ⟨hy, h⟩
  rw [hs.2, nextIn_of_mem (by simp [pairSet])] at h
  exact hy h.symm

theorem inArc_short_partner {y : Fin n} (hy1 : y ≠ a) (hy2 : y ≠ D.chord a) :
    D.InArc (D.chord a) y ↔ Reaches D.tour (D.chord a) y := by
  have hbS : D.S (D.chord a) = true := D.chord_mem hs.1
  rw [D.inArc_iff hbS, D.chord_invol]
  constructor
  · rintro ⟨_, j, hj, _⟩
    exact ⟨j + 1, hj⟩
  · rintro ⟨k, hk⟩
    cases k with
    | zero => exact absurd hk.symm hy2
    | succ k =>
      have hex : ∃ j, iterate D.tour j (D.tour (D.chord a)) = y := ⟨k, hk⟩
      obtain ⟨j, hj, hmin⟩ := exists_least hex
      refine ⟨hy1, j, hj, fun i hi hia => ?_⟩
      have hij : i ≠ j := by intro e; rw [e, hj] at hia; exact hy1 hia
      have h1 : iterate D.tour (i + 1) (D.tour (D.chord a)) = D.chord a := by
        rw [iterate_succ', hia, hs.2]
      by_cases hj1 : j = i + 1
      · rw [← hj1, hj] at h1; exact hy2 h1
      · apply hmin (j - i - 2) (by omega)
        have e : iterate D.tour (i + 2) (D.tour (D.chord a)) = D.tour (D.chord a) := by
          rw [show i + 2 = (i + 1) + 1 by omega, iterate_succ', h1]
        obtain ⟨d, rfl⟩ : ∃ d, j = i + 2 + d := ⟨j - i - 2, by omega⟩
        rw [iterate_add, e] at hj
        rw [show i + 2 + d - i - 2 = d by omega]
        exact hj

theorem noncrossing_remove_iff : (D.remove a).NonCrossing ↔ D.NonCrossing := by
  have ha := hs.1
  have hne := short_ne hs
  constructor
  · intro hnc x y hx hy hyx hyc
    by_cases hkx : D.keepS a x = true
    · by_cases hky : D.keepS a y = true
      · rw [← remove_inArc hkx hky, ← remove_inArc hkx (D.keepS_chord hky)]
        have := hnc x y hkx hky hyx (by rw [D.remove_chord hkx]; exact hyc)
        rwa [D.remove_chord hky] at this
      · obtain ⟨_, hxa, hxb⟩ := D.keepS_iff.mp hkx
        have hcx := D.keepS_iff.mp (D.keepS_chord hkx)
        rcases D.keepS_false (Bool.eq_false_iff.mpr hky) with h | h | h
        · rw [hy] at h; exact absurd h (by simp)
        · subst h
          exact D.inArc_adjacent hx hs.2 (Ne.symm hxa) (Ne.symm hcx.2.1) (Ne.symm hcx.2.2)
        · subst h
          rw [D.chord_invol]
          exact (D.inArc_adjacent hx hs.2 (Ne.symm hxa) (Ne.symm hcx.2.1) (Ne.symm hcx.2.2)).symm
    · rcases D.keepS_false (Bool.eq_false_iff.mpr hkx) with h | h | h
      · rw [hx] at h; exact absurd h (by simp)
      · subst h
        exact ⟨fun h => absurd h (inArc_short_false hs y), fun h => absurd h (inArc_short_false hs _)⟩
      · subst h
        have hy1 : y ≠ a := by rw [D.chord_invol] at hyc; exact hyc
        have hc1 : D.chord y ≠ a := fun e => hyx (by rw [← e, D.chord_invol])
        have hc2 : D.chord y ≠ D.chord a := fun e => hy1 (D.chord_inj e)
        rw [inArc_short_partner hs hy1 hyx, inArc_short_partner hs hc1 hc2]
        exact ⟨fun h => h.trans (D.chord_reach y), fun h => h.trans
          (by have := D.chord_reach y; exact this.symm D.tour_inj)⟩
  · intro hnc x y hx hy hyx hyc
    have hxS := D.keepS_sub hx
    have hyS := D.keepS_sub hy
    rw [D.remove_chord hx] at hyc
    rw [D.remove_chord hy, remove_inArc hx hy, remove_inArc hx (D.keepS_chord hy)]
    exact hnc x y hxS hyS hyx hyc

end short

/-! ### Minima of cycles -/

theorem preserves_S {p : Fin n → Fin n} (hp : ∀ a b, p a = p b → a = b) {S : Fin n → Bool}
    (hfix : ∀ z, S z = false → p z = z) {z : Fin n} (hz : S z = true) : S (p z) = true := by
  cases h : S (p z)
  · have := hp _ _ (hfix _ h); rw [this, hz] at h; exact absurd h (by simp)
  · rfl

theorem iterate_preserves_S {p : Fin n → Fin n} (hp : ∀ a b, p a = p b → a = b) {S : Fin n → Bool}
    (hfix : ∀ z, S z = false → p z = z) {z : Fin n} (hz : S z = true) : ∀ k, S (iterate p k z) = true := by
  intro k
  induction k with
  | zero => exact hz
  | succ k ih => rw [iterate_succ']; exact preserves_S hp hfix ih

theorem cmin_preserves_S {p : Fin n → Fin n} (hp : ∀ a b, p a = p b → a = b) {S : Fin n → Bool}
    (hfix : ∀ z, S z = false → p z = z) {z : Fin n} (hz : S z = true) : S (cmin p z) = true := by
  obtain ⟨i, _, hi⟩ := cmin_mem (p := p) z
  rw [← hi]; exact iterate_preserves_S hp hfix hz i

theorem cycleCount_split {p : Fin n → Fin n} {S : Fin n → Bool} (hfix : ∀ z, S z = false → p z = z) :
    cycleCount p = (List.finRange n).countP (fun z => !S z) +
      (List.finRange n).countP (fun z => S z && CycleMin p z) := by
  rw [cycleCount_eq, countP_split _ (CycleMin p) S]
  rw [Nat.add_comm]
  congr 1
  · apply countP_congr'; intro z _
    cases h : S z
    · simp [cycleMin_of_fixed (hfix z h)]
    · simp
  · apply countP_congr'; intro z _; exact Bool.and_comm _ _

/-- Without fixed points in `S`, at most half of the darts of `S` are minima of their cycles; fewer
if some cycle is longer than `2`. -/
theorem minima_bound {p : Fin n → Fin n} (hp : ∀ a b, p a = p b → a = b) {S : Fin n → Bool}
    (hfix : ∀ z, S z = false → p z = z) (hnf : ∀ z, S z = true → p z ≠ z) :
    2 * (List.finRange n).countP (fun z => S z && CycleMin p z) ≤ (List.finRange n).countP S ∧
      ((∃ z, S z = true ∧ p (p z) ≠ z) →
        2 * (List.finRange n).countP (fun z => S z && CycleMin p z) + 1 ≤ (List.finRange n).countP S) := by
  let mins := (List.finRange n).filter (fun z => S z && CycleMin p z)
  let others := (List.finRange n).filter (fun z => S z && !CycleMin p z)
  have hsplit := countP_split (List.finRange n) S (CycleMin p)
  have hmins : mins.length = (List.finRange n).countP (fun z => S z && CycleMin p z) :=
    (List.countP_eq_length_filter ..).symm
  have hothers : others.length = (List.finRange n).countP (fun z => S z && !CycleMin p z) :=
    (List.countP_eq_length_filter ..).symm
  have hmem_m : ∀ z, z ∈ mins ↔ S z = true ∧ CycleMin p z = true := by intro z; simp [mins]
  have hmem_o : ∀ z, z ∈ others ↔ S z = true ∧ CycleMin p z = false := by intro z; simp [others]
  have hnot_min : ∀ m, m ∈ mins → CycleMin p (p m) = false := by
    intro m hm
    obtain ⟨hS, hc⟩ := (hmem_m m).mp hm
    cases h : CycleMin p (p m)
    · rfl
    · have e1 := (cmin_eq_iff hp _).mpr h
      have e2 := (cmin_eq_iff hp _).mpr hc
      rw [cmin_step hp, e2] at e1
      exact absurd e1.symm (hnf m hS)
  have hnd : (mins.map p).Nodup :=
    nodup_map_of_injOn' p ((List.nodup_finRange n).filter _) (fun a _ b _ h => hp a b h)
  have hsub : ∀ z ∈ mins.map p, z ∈ others := by
    intro z hz
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hz
    exact (hmem_o _).mpr ⟨preserves_S hp hfix ((hmem_m m).mp hm).1, hnot_min m hm⟩
  have h1 := List.Nodup.length_le_of_subset hnd hsub
  rw [List.length_map] at h1
  refine ⟨by omega, ?_⟩
  rintro ⟨z0, hz0, hpp⟩
  let m0 := cmin p z0
  have hm0S : S m0 = true := cmin_preserves_S hp hfix hz0
  have hm0 : CycleMin p m0 = true := (cmin_eq_iff hp _).mp (by
    obtain ⟨i, _, hi⟩ := cmin_mem (p := p) z0
    show cmin p (cmin p z0) = cmin p z0
    rw [← hi, cmin_iterate hp]; exact hi.symm)
  have hpp0 : p (p m0) ≠ m0 := by
    intro h
    obtain ⟨r, hr⟩ := from_cmin hp z0
    have hcyc : ∀ k, iterate p k m0 = m0 ∨ iterate p k m0 = p m0 := by
      intro k
      induction k with
      | zero => exact Or.inl rfl
      | succ k ih =>
        rw [iterate_succ']
        rcases ih with e | e
        · rw [e]; exact Or.inr rfl
        · rw [e, h]; exact Or.inl rfl
    rcases hcyc r with e | e
    · rw [hr] at e; rw [e] at hpp; exact hpp h
    · rw [hr] at e; rw [e, h] at hpp; exact hpp rfl
  let w := p (p m0)
  have hwS : S w = true := preserves_S hp hfix (preserves_S hp hfix hm0S)
  have hwmin : CycleMin p w = false := by
    cases h : CycleMin p w
    · rfl
    · have e1 := (cmin_eq_iff hp _).mpr h
      have e2 := (cmin_eq_iff hp _).mpr hm0
      rw [show w = p (p m0) from rfl, cmin_step hp, cmin_step hp, e2] at e1
      exact absurd e1.symm hpp0
  have hwnot : w ∉ mins.map p := by
    intro hw
    obtain ⟨m, hm, he⟩ := List.mem_map.mp hw
    have := hp _ _ he
    rw [this] at hm
    have := hnot_min m0 ((hmem_m m0).mpr ⟨hm0S, hm0⟩)
    rw [((hmem_m _).mp hm).2] at this
    exact absurd this (by simp)
  have hnd2 : (w :: mins.map p).Nodup := List.nodup_cons.mpr ⟨hwnot, hnd⟩
  have hsub2 : ∀ z ∈ w :: mins.map p, z ∈ others := by
    intro z hz
    rcases List.mem_cons.mp hz with e | e
    · rw [e]; exact (hmem_o _).mpr ⟨hwS, hwmin⟩
    · exact hsub z e
  have h2 := List.Nodup.length_le_of_subset hnd2 hsub2
  simp only [List.length_cons, List.length_map] at h2
  omega

/-! ### The excess theorem -/

theorem cycleCount_tour_pos {x0 : Fin n} (hx0 : D.S x0 = true) :
    (List.finRange n).countP (fun z => !D.S z) + 1 ≤ cycleCount D.tour := by
  rw [cycleCount_split (S := D.S) D.tour_fix]
  have : 0 < (List.finRange n).countP (fun z => D.S z && CycleMin D.tour z) := by
    apply List.countP_pos_iff.mpr
    refine ⟨cmin D.tour x0, List.mem_finRange _, ?_⟩
    simp only [Bool.and_eq_true]
    refine ⟨cmin_preserves_S D.tour_inj D.tour_fix hx0, (cmin_eq_iff D.tour_inj _).mp ?_⟩
    obtain ⟨i, _, hi⟩ := cmin_mem (p := D.tour) x0
    rw [← hi, cmin_iterate D.tour_inj]; exact hi.symm
  omega

/-- A diagram without short chords and with a chord has a gap of at least `3`. -/
theorem excess_no_short (hns : ∀ a, ¬ D.Short a) {x0 : Fin n} (hx0 : D.S x0 = true) :
    2 * cycleCount D.faces + 3 ≤ 2 * cycleCount D.tour + (List.finRange n).countP D.S := by
  have hnf : ∀ z, D.S z = true → D.faces z ≠ z := by
    intro z hz h
    apply hns (D.chord z)
    refine ⟨D.chord_mem hz, ?_⟩
    rw [D.chord_invol]; exact h
  have hlong : ∃ z, D.S z = true ∧ D.faces (D.faces z) ≠ z := by
    apply Classical.byContradiction
    intro hno
    have hall : ∀ z, D.S z = true → D.faces (D.faces z) = z := by
      intro z hz
      apply Classical.byContradiction
      intro h
      exact hno ⟨z, hz, h⟩
    obtain ⟨a, ha⟩ := D.exists_short_of_faces_invol hall hx0
    exact hns a ha
  have hb := (minima_bound D.faces_inj (fun z h => D.faces_fix h) hnf).2 hlong
  have hf := cycleCount_split (S := D.S) (p := D.faces) (fun z h => D.faces_fix h)
  have ht := D.cycleCount_tour_pos hx0
  omega

/-- **The excess theorem for chord diagrams.** -/
theorem chord_excess (D : Diagram n) :
    (D.NonCrossing → 2 * cycleCount D.faces = 2 * cycleCount D.tour + (List.finRange n).countP D.S) ∧
      (¬ D.NonCrossing →
        2 * cycleCount D.faces + 3 ≤ 2 * cycleCount D.tour + (List.finRange n).countP D.S) := by
  have key : ∀ k (D : Diagram n), (List.finRange n).countP D.S = k →
      (D.NonCrossing → 2 * cycleCount D.faces = 2 * cycleCount D.tour + (List.finRange n).countP D.S) ∧
        (¬ D.NonCrossing →
          2 * cycleCount D.faces + 3 ≤ 2 * cycleCount D.tour + (List.finRange n).countP D.S) := by
    intro k
    induction k using Nat.strongRecOn with
    | _ k ih =>
      intro D hk
      by_cases hshort : ∃ a, D.Short a
      · obtain ⟨a, hs⟩ := hshort
        have hc := countP_keepS hs
        obtain ⟨i1, i2⟩ := ih ((List.finRange n).countP (D.keepS a)) (by omega) (D.remove a) rfl
        have t1 := remove_tour_count hs
        have t2 := remove_faces_count hs
        have hnc := noncrossing_remove_iff hs
        rw [remove_S] at i1 i2
        refine ⟨fun h => ?_, fun h => ?_⟩
        · have := i1 (hnc.mpr h); omega
        · have := i2 (fun h' => h (hnc.mp h')); omega
      · by_cases hne : ∃ x, D.S x = true
        · obtain ⟨x0, hx0⟩ := hne
          have hns : ∀ a, ¬ D.Short a := fun a h => hshort ⟨a, h⟩
          refine ⟨fun hnc => absurd (D.exists_short hnc hx0) hshort, fun _ => D.excess_no_short hns hx0⟩
        · have hS : ∀ x, D.S x = false := by
            intro x; cases h : D.S x
            · rfl
            · exact absurd ⟨x, h⟩ hne
          have ht : D.tour = id := funext fun x => D.tour_fix x (hS x)
          have hf : D.faces = id := funext fun x => D.faces_fix (hS x)
          have hc : (List.finRange n).countP D.S = 0 := by
            rw [List.countP_eq_zero]; intro x _; simp [hS x]
          refine ⟨fun _ => by rw [ht, hf, hc]; omega, fun h => absurd ?_ h⟩
          intro x y hx; rw [hS x] at hx; exact absurd hx (by simp)
  exact key _ D rfl

end Diagram

end STACS2027.Embed

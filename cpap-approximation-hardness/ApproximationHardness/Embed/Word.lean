module

public import Init
import Lean.Elab.Tactic.Omega

/-!
# Words of darts with chords

A word is a list of darts; an involution `α` pairs darts into chords. `Before l a b`: `a` occurs
before `b` in `l`. A word is well nested (`WN`) when every dart strictly inside a chord has its
partner strictly inside the same chord: no two chords cross, and no chord encloses a dart whose
partner lies outside the word. The open ends of a word are its darts whose partners lie outside.

A side function `s` (`false` = left, `true` = right) and a key function order the open ends: a
word is a valley (`Valley`) when its open ends are the left ends by decreasing key followed by the
right ends by increasing key.
-/

@[expose] public section

namespace STACS2027.Embed

/-! ### Order of occurrence -/

/-- `a` occurs before `b` in `l`. -/
def Before (l : List Nat) (a b : Nat) : Prop := List.Sublist [a, b] l

theorem before_mem {l : List Nat} {a b : Nat} (h : Before l a b) : a ∈ l ∧ b ∈ l :=
  ⟨h.subset (by simp), h.subset (by simp)⟩

theorem before_cons_iff {x : Nat} {l : List Nat} {a b : Nat} :
    Before (x :: l) a b ↔ (a = x ∧ b ∈ l) ∨ Before l a b := by
  unfold Before
  rw [List.sublist_cons_iff]
  constructor
  · rintro (h | ⟨r, hr, hs⟩)
    · exact Or.inr h
    · simp only [List.cons.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact Or.inl ⟨rfl, List.singleton_sublist.mp hs⟩
  · rintro (⟨rfl, hb⟩ | h)
    · exact Or.inr ⟨[b], rfl, List.singleton_sublist.mpr hb⟩
    · exact Or.inl h

theorem before_nil {a b : Nat} : ¬ Before [] a b := fun h => by simpa using (before_mem h).1

theorem before_append_iff {A B : List Nat} {a b : Nat} :
    Before (A ++ B) a b ↔ Before A a b ∨ Before B a b ∨ (a ∈ A ∧ b ∈ B) := by
  induction A with
  | nil => simp [before_nil]
  | cons x A ih =>
    rw [List.cons_append, before_cons_iff, ih, before_cons_iff]
    simp only [List.mem_append, List.mem_cons]
    constructor
    · rintro (⟨rfl, hb | hb⟩ | h | h | ⟨ha, hb⟩)
      · exact Or.inl (Or.inl ⟨rfl, hb⟩)
      · exact Or.inr (Or.inr ⟨Or.inl rfl, hb⟩)
      · exact Or.inl (Or.inr h)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨Or.inr ha, hb⟩)
    · rintro ((⟨rfl, hb⟩ | h) | h | ⟨rfl | ha, hb⟩)
      · exact Or.inl ⟨rfl, Or.inl hb⟩
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inl ⟨rfl, Or.inr hb⟩
      · exact Or.inr (Or.inr (Or.inr ⟨ha, hb⟩))

theorem before_append_left {A B : List Nat} {a b : Nat} (h : Before A a b) : Before (A ++ B) a b :=
  before_append_iff.mpr (Or.inl h)

theorem before_append_right {A B : List Nat} {a b : Nat} (h : Before B a b) : Before (A ++ B) a b :=
  before_append_iff.mpr (Or.inr (Or.inl h))

theorem before_append_mid {A B : List Nat} {a b : Nat} (ha : a ∈ A) (hb : b ∈ B) : Before (A ++ B) a b :=
  before_append_iff.mpr (Or.inr (Or.inr ⟨ha, hb⟩))

theorem before_irrefl {l : List Nat} (hl : l.Nodup) (a : Nat) : ¬ Before l a a := by
  induction l with
  | nil => exact before_nil
  | cons x l ih =>
    obtain ⟨hx, hl'⟩ := List.nodup_cons.mp hl
    rw [before_cons_iff]
    rintro (⟨rfl, ha⟩ | h)
    · exact hx ha
    · exact ih hl' h

theorem before_asymm {l : List Nat} (hl : l.Nodup) {a b : Nat} (h : Before l a b) : ¬ Before l b a := by
  induction l with
  | nil => exact absurd h before_nil
  | cons x l ih =>
    obtain ⟨hx, hl'⟩ := List.nodup_cons.mp hl
    rw [before_cons_iff] at h ⊢
    rintro (⟨rfl, ha⟩ | h')
    · rcases h with ⟨rfl, _⟩ | h
      · exact hx ha
      · exact hx (before_mem h).2
    · rcases h with ⟨rfl, _⟩ | h
      · exact hx (before_mem h').2
      · exact ih hl' h h'

theorem before_total {l : List Nat} {a b : Nat} (ha : a ∈ l) (hb : b ∈ l) (hab : a ≠ b) :
    Before l a b ∨ Before l b a := by
  induction l with
  | nil => simp at ha
  | cons x l ih =>
    rw [before_cons_iff, before_cons_iff]
    rcases List.mem_cons.mp ha with rfl | ha'
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact absurd rfl hab
      · exact Or.inl (Or.inl ⟨rfl, hb'⟩)
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact Or.inr (Or.inl ⟨rfl, ha'⟩)
      · rcases ih ha' hb' with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr (Or.inr h)

theorem before_trans {l : List Nat} (hl : l.Nodup) {a b c : Nat} (h1 : Before l a b) (h2 : Before l b c) :
    Before l a c := by
  induction l with
  | nil => exact absurd h1 before_nil
  | cons x l ih =>
    obtain ⟨hx, hl'⟩ := List.nodup_cons.mp hl
    rw [before_cons_iff] at h1 h2 ⊢
    rcases h1 with ⟨rfl, _⟩ | h1
    · rcases h2 with ⟨rfl, _⟩ | h2
      · exact Or.inl ⟨rfl, by assumption⟩
      · exact Or.inl ⟨rfl, (before_mem h2).2⟩
    · rcases h2 with ⟨rfl, _⟩ | h2
      · exact absurd (before_mem h1).2 hx
      · exact Or.inr (ih hl' h1 h2)

theorem before_filter_iff {l : List Nat} {p : Nat → Bool} {a b : Nat} :
    Before (l.filter p) a b ↔ Before l a b ∧ p a = true ∧ p b = true := by
  induction l with
  | nil => simp [before_nil]
  | cons x l ih =>
    rw [List.filter_cons]
    split
    · rename_i hx
      rw [before_cons_iff, ih, before_cons_iff, List.mem_filter]
      constructor
      · rintro (⟨rfl, hb, hpb⟩ | ⟨h, hpa, hpb⟩)
        · exact ⟨Or.inl ⟨rfl, hb⟩, hx, hpb⟩
        · exact ⟨Or.inr h, hpa, hpb⟩
      · rintro ⟨⟨rfl, hb⟩ | h, hpa, hpb⟩
        · exact Or.inl ⟨rfl, hb, hpb⟩
        · exact Or.inr ⟨h, hpa, hpb⟩
    · rename_i hx
      rw [ih, before_cons_iff]
      constructor
      · rintro ⟨h, hpa, hpb⟩; exact ⟨Or.inr h, hpa, hpb⟩
      · rintro ⟨⟨rfl, hb⟩ | h, hpa, hpb⟩
        · exact absurd hpa hx
        · exact ⟨h, hpa, hpb⟩

theorem before_reverse_iff {l : List Nat} {a b : Nat} : Before l.reverse a b ↔ Before l b a := by
  unfold Before
  have : [a, b] = [b, a].reverse := rfl
  rw [this, List.reverse_sublist]

/-- In a word without repetitions, `Before` on two darts of a sub-block is `Before` in the block. -/
theorem before_of_append_left {A B : List Nat} (hnd : (A ++ B).Nodup) {a b : Nat} (ha : a ∈ A)
    (hb : b ∈ A) (h : Before (A ++ B) a b) : Before A a b := by
  rcases before_append_iff.mp h with h | h | ⟨_, hb'⟩
  · exact h
  · exact absurd (before_mem h).1 ((List.nodup_append.mp hnd).2.2 a ha a · rfl)
  · exact absurd rfl ((List.nodup_append.mp hnd).2.2 b hb b hb')

theorem before_of_append_right {A B : List Nat} (hnd : (A ++ B).Nodup) {a b : Nat} (ha : a ∈ B)
    (_hb : b ∈ B) (h : Before (A ++ B) a b) : Before B a b := by
  rcases before_append_iff.mp h with h | h | ⟨ha', _⟩
  · exact absurd rfl ((List.nodup_append.mp hnd).2.2 a (before_mem h).1 a ha)
  · exact h
  · exact absurd rfl ((List.nodup_append.mp hnd).2.2 a ha' a ha)

/-! ### Well-nested words -/

/-- Every dart strictly inside a chord has its partner strictly inside it. -/
def WN (α : Nat → Nat) (l : List Nat) : Prop :=
  ∀ x z, Before l x z → Before l z (α x) → Before l x (α z) ∧ Before l (α z) (α x)

theorem wn_nil (α : Nat → Nat) : WN α [] := fun _ _ h => absurd h before_nil

theorem wn_singleton (α : Nat → Nat) (d : Nat) : WN α [d] := by
  intro x z h
  rw [before_cons_iff] at h
  rcases h with ⟨_, hz⟩ | h
  · simp at hz
  · exact absurd h before_nil

theorem wn_append {α : Nat → Nat} {A B : List Nat} (hA : WN α A) (hB : WN α B) (hnd : (A ++ B).Nodup)
    (hAB : ∀ a ∈ A, α a ∉ B) (hBA : ∀ b ∈ B, α b ∉ A) : WN α (A ++ B) := by
  intro x z h1 h2
  have hx := (before_mem h1).1
  have hz := (before_mem h1).2
  have hax := (before_mem h2).2
  rw [List.mem_append] at hx hz hax
  have hdisj := (List.nodup_append.mp hnd).2.2
  rcases hx with hx | hx
  · have hax' : α x ∈ A := hax.resolve_right (hAB x hx)
    have hz' : z ∈ A := by
      rcases hz with hz | hz
      · exact hz
      · exfalso
        rcases before_append_iff.mp h2 with h | h | ⟨hzA, _⟩
        · exact hdisj z (before_mem h).1 z hz rfl
        · exact hAB x hx (before_mem h).2
        · exact hdisj z hzA z hz rfl
    obtain ⟨r1, r2⟩ := hA x z (before_of_append_left hnd hx hz' h1) (before_of_append_left hnd hz' hax' h2)
    exact ⟨before_append_left r1, before_append_left r2⟩
  · have hz' : z ∈ B := by
      rcases hz with hz | hz
      · exfalso
        rcases before_append_iff.mp h1 with h | h | ⟨hxA, _⟩
        · exact hdisj x (before_mem h).1 x hx rfl
        · exact hdisj z hz z (before_mem h).2 rfl
        · exact hdisj x hxA x hx rfl
      · exact hz
    have hax' : α x ∈ B := hax.resolve_left (hBA x hx)
    obtain ⟨r1, r2⟩ := hB x z (before_of_append_right hnd hx hz' h1) (before_of_append_right hnd hz' hax' h2)
    exact ⟨before_append_right r1, before_append_right r2⟩

theorem wn_reverse {α : Nat → Nat} (hα : ∀ x, α (α x) = x) {l : List Nat} (h : WN α l) :
    WN α l.reverse := by
  intro x z h1 h2
  rw [before_reverse_iff] at h1 h2 ⊢
  rw [before_reverse_iff]
  have := h (α x) z h2 (by rw [hα]; exact h1)
  rw [hα] at this
  exact ⟨this.2, this.1⟩

/-- Closing a chord at the front: `d` is put before a well-nested word containing its partner,
when no dart before the partner has its own partner outside the word. -/
theorem wn_cons_close {α : Nat → Nat} (hα : ∀ x, α (α x) = x) {d : Nat} {B : List Nat}
    (hnd : (d :: B).Nodup) (hB : WN α B) (hfirst : ∀ z, Before B z (α d) → α z ∈ B) :
    WN α (d :: B) := by
  obtain ⟨hdB, hndB⟩ := List.nodup_cons.mp hnd
  intro x z h1 h2
  rw [before_cons_iff] at h1 h2
  rcases h1 with ⟨rfl, hz⟩ | h1
  · have hzd : z ≠ x := fun e => hdB (e ▸ hz)
    have h2' : Before B z (α x) := by
      rcases h2 with ⟨e, _⟩ | h2
      · exact absurd e hzd
      · exact h2
    have haz := hfirst z h2'
    refine ⟨before_cons_iff.mpr (Or.inl ⟨rfl, haz⟩), before_cons_iff.mpr (Or.inr ?_)⟩
    have hne : α z ≠ α x := fun e => hzd (by rw [← hα z, e, hα])
    rcases before_total haz (before_mem h2').2 hne with h | h
    · exact h
    · exfalso
      have := (hB z (α x) h2' h).1
      rw [hα] at this
      exact hdB (before_mem this).2
  · have hzB := (before_mem h1).2
    have h2' : Before B z (α x) := by
      rcases h2 with ⟨rfl, _⟩ | h2
      · exact absurd hzB hdB
      · exact h2
    obtain ⟨r1, r2⟩ := hB x z h1 h2'
    exact ⟨before_cons_iff.mpr (Or.inr r1), before_cons_iff.mpr (Or.inr r2)⟩

/-- Closing a chord at the back. -/
theorem wn_snoc_close {α : Nat → Nat} (hα : ∀ x, α (α x) = x) {d : Nat} {B : List Nat}
    (hnd : (B ++ [d]).Nodup) (hB : WN α B) (hlast : ∀ z, Before B (α d) z → α z ∈ B) :
    WN α (B ++ [d]) := by
  have hr : B ++ [d] = (d :: B.reverse).reverse := by simp
  rw [hr]
  apply wn_reverse hα
  apply wn_cons_close hα
  · have : (d :: B.reverse) = (B ++ [d]).reverse := by simp
    rw [this]; exact ((List.reverse_perm _).nodup_iff).mpr hnd
  · exact wn_reverse hα hB
  · intro z hz
    rw [before_reverse_iff] at hz
    exact List.mem_reverse.mpr (hlast z hz)

/-- A dart between two darts of a block lies in the block. -/
theorem mem_of_between {A M B : List Nat} (hnd : (A ++ M ++ B).Nodup) {x w y : Nat} (hx : x ∈ M)
    (hy : y ∈ M) (h1 : Before (A ++ M ++ B) x w) (h2 : Before (A ++ M ++ B) w y) : w ∈ M := by
  have hndAM : (A ++ M).Nodup := (List.nodup_append.mp hnd).1
  have dAM := (List.nodup_append.mp hndAM).2.2
  have dAMB := (List.nodup_append.mp hnd).2.2
  rcases before_append_iff.mp h1 with h1 | h1 | ⟨_, hwB⟩
  · rcases before_append_iff.mp h1 with h1 | h1 | ⟨_, hwM⟩
    · exact absurd rfl (dAM x (before_mem h1).1 x hx)
    · exact (before_mem h1).2
    · exact hwM
  · exact absurd rfl (dAMB x (List.mem_append_right A hx) x (before_mem h1).1)
  · exfalso
    rcases before_append_iff.mp h2 with h2 | h2 | ⟨_, hyB⟩
    · exact dAMB w (before_mem h2).1 w hwB rfl
    · exact dAMB y (List.mem_append_right A hy) y (before_mem h2).2 rfl
    · exact dAMB y (List.mem_append_right A hy) y hyB rfl

theorem before_of_infix {A M B : List Nat} (hnd : (A ++ M ++ B).Nodup) {a b : Nat} (ha : a ∈ M)
    (hb : b ∈ M) (h : Before (A ++ M ++ B) a b) : Before M a b := by
  have hndAM : (A ++ M).Nodup := (List.nodup_append.mp hnd).1
  have h' := before_of_append_left hnd (List.mem_append_right A ha) (List.mem_append_right A hb) h
  exact before_of_append_right hndAM ha hb h'

theorem before_infix {A M B : List Nat} {a b : Nat} (h : Before M a b) : Before (A ++ M ++ B) a b :=
  before_append_left (before_append_right h)

/-- A block of a well-nested word is well nested. -/
theorem wn_infix {α : Nat → Nat} {A M B : List Nat} (hnd : (A ++ M ++ B).Nodup) (h : WN α (A ++ M ++ B)) :
    WN α M := by
  intro x z h1 h2
  have hx := (before_mem h1).1
  have hz := (before_mem h1).2
  have hax := (before_mem h2).2
  obtain ⟨r1, r2⟩ := h x z (before_infix h1) (before_infix h2)
  have haz : α z ∈ M := mem_of_between hnd hx hax r1 r2
  exact ⟨before_of_infix hnd hx haz r1, before_of_infix hnd haz hax r2⟩

theorem wn_congr {α α' : Nat → Nat} {l : List Nat} (h : ∀ x ∈ l, α x = α' x) : WN α l ↔ WN α' l := by
  unfold WN
  constructor
  · intro hw x z h1 h2
    have hx := (before_mem h1).1
    have hz := (before_mem h1).2
    rw [← h x hx, ← h z hz] at *
    exact hw x z h1 h2
  · intro hw x z h1 h2
    have hx := (before_mem h1).1
    have hz := (before_mem h1).2
    rw [h x hx, h z hz] at *
    exact hw x z h1 h2

/-! ### Open ends -/

/-- The darts of `l` whose partners are not in `l`. -/
def openEnds (α : Nat → Nat) (l : List Nat) : List Nat := l.filter fun e => decide (α e ∉ l)

theorem mem_openEnds {α : Nat → Nat} {l : List Nat} {e : Nat} :
    e ∈ openEnds α l ↔ e ∈ l ∧ α e ∉ l := by
  simp [openEnds]

theorem openEnds_append {α : Nat → Nat} {A B : List Nat} (hAB : ∀ a ∈ A, α a ∉ B)
    (hBA : ∀ b ∈ B, α b ∉ A) : openEnds α (A ++ B) = openEnds α A ++ openEnds α B := by
  unfold openEnds
  rw [List.filter_append]
  congr 1
  · apply List.filter_congr
    intro e he
    simp [hAB e he]
  · apply List.filter_congr
    intro e he
    simp [hBA e he]

theorem openEnds_cons_close {α : Nat → Nat} (hα : ∀ x, α (α x) = x) {d : Nat} {B : List Nat}
    (hd : α d ∈ B) : openEnds α (d :: B) = (openEnds α B).filter fun e => decide (e ≠ α d) := by
  unfold openEnds
  rw [List.filter_cons, List.filter_filter]
  have : decide (α d ∉ d :: B) = false := by simp [hd]
  rw [this]
  simp only [Bool.false_eq_true, ite_false]
  apply List.filter_congr
  intro e _
  have : (α e = d) ↔ (e = α d) := ⟨fun h => by rw [← h, hα], fun h => by rw [h, hα]⟩
  simp [this]

theorem openEnds_snoc_close {α : Nat → Nat} (hα : ∀ x, α (α x) = x) {d : Nat} {B : List Nat}
    (hd : α d ∈ B) : openEnds α (B ++ [d]) = (openEnds α B).filter fun e => decide (e ≠ α d) := by
  unfold openEnds
  rw [List.filter_append, List.filter_filter]
  have : decide (α d ∉ B ++ [d]) = false := by simp [hd]
  simp only [List.filter_cons, this, Bool.false_eq_true, ite_false, List.filter_nil, List.append_nil]
  apply List.filter_congr
  intro e _
  have : (α e = d) ↔ (e = α d) := ⟨fun h => by rw [← h, hα], fun h => by rw [h, hα]⟩
  simp [this, Bool.and_comm]

theorem openEnds_reverse {α : Nat → Nat} (l : List Nat) :
    openEnds α l.reverse = (openEnds α l).reverse := by
  unfold openEnds
  rw [List.filter_reverse]
  congr 1
  apply List.filter_congr
  intro e _; simp

/-! ### Valleys -/

/-- The order of two open ends in a valley: left before right, left ends by decreasing key, right
ends by increasing key. -/
def VR (s : Nat → Bool) (key : Nat → Nat) (e f : Nat) : Prop :=
  (s e = false ∧ s f = true) ∨ (s e = false ∧ s f = false ∧ key f < key e) ∨
    (s e = true ∧ s f = true ∧ key e < key f)

/-- The open ends are left ends by decreasing key, then right ends by increasing key. -/
def Valley (s : Nat → Bool) (key : Nat → Nat) (l : List Nat) : Prop := l.Pairwise (VR s key)

theorem valley_first {s : Nat → Bool} {key : Nat → Nat} {l : List Nat} (hv : Valley s key l)
    (_hnd : l.Nodup) {x : Nat} (hx : x ∈ l) (hs : s x = false)
    (hmax : ∀ y ∈ l, y ≠ x → key y < key x) : ∀ y ∈ l, y ≠ x → Before l x y := by
  intro y hy hyx
  rcases before_total hx hy (Ne.symm hyx) with h | h
  · exact h
  · exfalso
    have := List.pairwise_iff_forall_sublist.mp hv h
    have hk := hmax y hy hyx
    rcases this with ⟨_, h2⟩ | ⟨_, _, h3⟩ | ⟨_, h2, _⟩
    · rw [hs] at h2; exact absurd h2 (by simp)
    · omega
    · rw [hs] at h2; exact absurd h2 (by simp)

theorem valley_last {s : Nat → Bool} {key : Nat → Nat} {l : List Nat} (hv : Valley s key l)
    (_hnd : l.Nodup) {x : Nat} (hx : x ∈ l) (hs : s x = true)
    (hmax : ∀ y ∈ l, y ≠ x → key y < key x) : ∀ y ∈ l, y ≠ x → Before l y x := by
  intro y hy hyx
  rcases before_total hx hy (Ne.symm hyx) with h | h
  · exfalso
    have := List.pairwise_iff_forall_sublist.mp hv h
    have hk := hmax y hy hyx
    rcases this with ⟨h1, _⟩ | ⟨h1, _, _⟩ | ⟨_, _, h3⟩
    · rw [hs] at h1; exact absurd h1 (by simp)
    · rw [hs] at h1; exact absurd h1 (by simp)
    · omega
  · exact h

theorem valley_cons {s : Nat → Bool} {key : Nat → Nat} {x : Nat} {l : List Nat} (hv : Valley s key l)
    (hs : s x = false) (hmax : ∀ y ∈ l, key y < key x) : Valley s key (x :: l) := by
  refine List.pairwise_cons.mpr ⟨fun y hy => ?_, hv⟩
  cases hsy : s y
  · exact Or.inr (Or.inl ⟨hs, hsy, hmax y hy⟩)
  · exact Or.inl ⟨hs, hsy⟩

theorem valley_snoc {s : Nat → Bool} {key : Nat → Nat} {x : Nat} {l : List Nat} (hv : Valley s key l)
    (hs : s x = true) (hmax : ∀ y ∈ l, key y < key x) : Valley s key (l ++ [x]) := by
  refine List.pairwise_append.mpr ⟨hv, List.pairwise_singleton _ _, fun y hy z hz => ?_⟩
  rw [List.mem_singleton] at hz
  subst hz
  cases hsy : s y
  · exact Or.inl ⟨hsy, hs⟩
  · exact Or.inr (Or.inr ⟨hsy, hs, hmax y hy⟩)

end STACS2027.Embed

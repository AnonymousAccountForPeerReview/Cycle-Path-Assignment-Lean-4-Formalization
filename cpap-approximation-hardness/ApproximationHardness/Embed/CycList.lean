module

public import ApproximationHardness.Embed.Chord
public import ApproximationHardness.Embed.Word
import Lean.Elab.Tactic.Omega

/-!
# Permutations acting along lists

`Chain f l`: `f` maps every element of `l` to the next one; `Cyc f l`: moreover `f` maps the last
element to the first, so `l` is a cycle of `f`. For a permutation `p` of `Fin n` acting as a cycle
along a list of darts:

* its orbit through any dart of the list is the list (`reaches_iff_mem`);
* its first-return map to `S` acts as a cycle along the darts of the list in `S`
  (`cyc_firstReturn`);
* in a chord diagram whose tour acts as a cycle along a closed word, `InArc` is order of
  occurrence in the rotation of the word that ends at the chord's first dart (`inArc_iff_before`),
  and the chords of the word do not cross iff the word is well nested (`noncrossing_iff_wn`).
-/

@[expose] public section

namespace STACS2027.Embed

open Complexity Complexity.Planar STACS2027.PlanarGluing

/-! ### Chains -/

/-- `f` maps every element of the list to the next one. -/
inductive Chain (f : Nat → Nat) : List Nat → Prop where
  | nil : Chain f []
  | one (a : Nat) : Chain f [a]
  | cons (a b : Nat) (l : List Nat) : f a = b → Chain f (b :: l) → Chain f (a :: b :: l)

theorem chain_cons_iff {f : Nat → Nat} {a : Nat} {l : List Nat} :
    Chain f (a :: l) ↔ Chain f l ∧ ∀ b, l.head? = some b → f a = b := by
  constructor
  · intro h
    cases h with
    | one => exact ⟨Chain.nil, fun b hb => by simp at hb⟩
    | cons _ b l' hab hc => exact ⟨hc, fun b' hb => by simp at hb; rw [← hb]; exact hab⟩
  · rintro ⟨hc, hh⟩
    cases l with
    | nil => exact Chain.one a
    | cons b l' => exact Chain.cons a b l' (hh b rfl) hc

theorem chain_append {f : Nat → Nat} {A B : List Nat} :
    Chain f (A ++ B) ↔ Chain f A ∧ Chain f B ∧ ∀ a b, A.getLast? = some a → B.head? = some b → f a = b := by
  induction A with
  | nil => simp [Chain.nil]
  | cons x A ih =>
    rw [List.cons_append, chain_cons_iff, ih, chain_cons_iff]
    cases A with
    | nil =>
      simp only [List.nil_append, List.head?_nil, List.getLast?_singleton, Option.some.injEq]
      constructor
      · rintro ⟨⟨_, hB, _⟩, hh⟩
        exact ⟨⟨Chain.nil, fun b hb => by simp at hb⟩, hB, fun a b ha hb => by rw [← ha]; exact hh b hb⟩
      · rintro ⟨_, hB, hh⟩
        exact ⟨⟨Chain.nil, hB, fun a b ha => by simp at ha⟩, fun b hb => hh x b rfl hb⟩
    | cons y A' =>
      simp only [List.cons_append, List.head?_cons, Option.some.injEq, forall_eq', List.getLast?_cons_cons]
      constructor
      · rintro ⟨⟨hA, hB, hj⟩, hxy⟩
        exact ⟨⟨hA, hxy⟩, hB, hj⟩
      · rintro ⟨⟨hA, hxy⟩, hB, hj⟩
        exact ⟨⟨hA, hB, hj⟩, hxy⟩

theorem chain_iterate {f : Nat → Nat} {a : Nat} {l : List Nat} (h : Chain f (a :: l)) :
    ∀ k (hk : k < (a :: l).length), iterate f k a = (a :: l)[k] := by
  induction l generalizing a with
  | nil => intro k hk; simp at hk; subst hk; rfl
  | cons b l ih =>
    obtain ⟨hc, hh⟩ := chain_cons_iff.mp h
    have hab : f a = b := hh b rfl
    intro k hk
    cases k with
    | zero => rfl
    | succ k =>
      rw [iterate_succ_apply', hab]
      exact ih hc k (by simp at hk ⊢; omega)
where
  iterate_succ_apply' (k : Nat) (x : Nat) : iterate f (k + 1) x = iterate f k (f x) := rfl

theorem chain_maps {f : Nat → Nat} {l : List Nat} (h : Chain f l) :
    ∀ x ∈ l, (∃ y ∈ l, f x = y) ∨ l.getLast? = some x := by
  induction l with
  | nil => intro x hx; simp at hx
  | cons a l ih =>
    obtain ⟨hc, hh⟩ := chain_cons_iff.mp h
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · cases l with
      | nil => exact Or.inr rfl
      | cons b l' => exact Or.inl ⟨b, by simp, hh b rfl⟩
    · rcases ih hc x hx with ⟨y, hy, he⟩ | hl
      · exact Or.inl ⟨y, List.mem_cons_of_mem _ hy, he⟩
      · right
        cases l with
        | nil => simp at hx
        | cons b l' => rw [List.getLast?_cons_cons]; exact hl

/-- `l` is a cycle of `f`. -/
def Cyc (f : Nat → Nat) (l : List Nat) : Prop :=
  Chain f l ∧ ∀ a b, l.getLast? = some a → l.head? = some b → f a = b

theorem cyc_maps {f : Nat → Nat} {l : List Nat} (h : Cyc f l) : ∀ x ∈ l, f x ∈ l := by
  intro x hx
  rcases chain_maps h.1 x hx with ⟨y, hy, he⟩ | hl
  · rw [he]; exact hy
  · cases l with
    | nil => simp at hx
    | cons a l' => rw [h.2 x a hl rfl]; simp

/-- The rotation of a cycle starting after `x`, followed by `x`. -/
theorem cyc_rot {f : Nat → Nat} {A B : List Nat} {x : Nat} (h : Cyc f (A ++ x :: B)) :
    Chain f (x :: (B ++ A ++ [x])) := by
  obtain ⟨hc, hw⟩ := h
  obtain ⟨hA, hxB, hj⟩ := chain_append.mp hc
  have : x :: (B ++ A ++ [x]) = (x :: B) ++ (A ++ [x]) := by simp
  rw [this]
  refine chain_append.mpr ⟨hxB, chain_append.mpr ⟨hA, Chain.one x, fun a b ha hb => ?_⟩, fun a b ha hb => ?_⟩
  · simp at hb; rw [← hb]; exact hj a x ha rfl
  · apply hw a b
    · rw [List.getLast?_append]; simp [ha]
    · cases A with
      | nil => simpa using hb
      | cons y A' => simp at hb ⊢; exact hb

theorem chain_sublist_mem {f : Nat → Nat} {l : List Nat} (h : Chain f l) {x : Nat} (hx : x ∈ l)
    (k : Nat) : ∃ y, iterate f k x = y ∧ (y ∈ l ∨ ∃ j, j ≤ k ∧ l.getLast? = some (iterate f j x)) := by
  exact ⟨_, rfl, by
    induction k generalizing x with
    | zero => exact Or.inl hx
    | succ k ih =>
      rcases chain_maps h x hx with ⟨y, hy, he⟩ | hl
      · rcases ih hy with h1 | ⟨j, hj, h2⟩
        · left; show iterate f k (f x) ∈ l; rw [he]; exact h1
        · right; exact ⟨j + 1, by omega, by show l.getLast? = some (iterate f j (f x)); rw [he]; exact h2⟩
      · right; exact ⟨0, by omega, hl⟩⟩


theorem getLast?_append_cons (l l' : List Nat) (a : Nat) : (l ++ a :: l').getLast? = (a :: l').getLast? := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    cases l with
    | nil => exact List.getLast?_cons_cons ..
    | cons y l => rw [List.cons_append, List.cons_append, List.getLast?_cons_cons, ← List.cons_append, ih]

theorem cyc_one {f : Nat → Nat} {a : Nat} (h : Cyc f [a]) : f a = a := h.2 a a rfl rfl
theorem cyc_two {f : Nat → Nat} {a b : Nat} (h : Cyc f [a, b]) : f a = b ∧ f b = a := by
  obtain ⟨hc, hw⟩ := h
  exact ⟨(chain_cons_iff.mp hc).2 b rfl, hw b a rfl rfl⟩
theorem cyc_three {f : Nat → Nat} {a b c : Nat} (h : Cyc f [a, b, c]) : f a = b ∧ f b = c ∧ f c = a := by
  obtain ⟨hc, hw⟩ := h
  obtain ⟨hc', h1⟩ := chain_cons_iff.mp hc
  exact ⟨h1 b rfl, (chain_cons_iff.mp hc').2 c rfl, hw c a rfl rfl⟩

theorem cyc_append_comm {f : Nat → Nat} {A B : List Nat} (h : Cyc f (A ++ B)) : Cyc f (B ++ A) := by
  cases A with
  | nil => simpa using h
  | cons a A' =>
    cases B with
    | nil => simpa using h
    | cons b B' =>
      obtain ⟨hc, hw⟩ := h
      obtain ⟨hA, hB, hj⟩ := chain_append.mp hc
      refine ⟨chain_append.mpr ⟨hB, hA, fun x y hx hy => ?_⟩, fun x y hx hy => ?_⟩
      · apply hw x y
        · rw [getLast?_append_cons]; exact hx
        · simpa using hy
      · apply hj x y
        · rw [getLast?_append_cons] at hx; exact hx
        · simpa using hy


theorem chain_join {f : Nat → Nat} {A B : List Nat} {b : Nat} (hA : Chain f A) (hB : Chain f B)
    (hb : B.head? = some b) (hj : ∀ l, A.getLast? = some l → f l = b) : Chain f (A ++ B) :=
  chain_append.mpr ⟨hA, hB, fun x y hx hy => by rw [hb] at hy; cases hy; exact hj x hx⟩

theorem head?_append_of_some {A B : List Nat} {a : Nat} (h : A.head? = some a) : (A ++ B).head? = some a := by
  cases A with
  | nil => simp at h
  | cons x A => simpa using h

theorem getLast?_append_of_some {A B : List Nat} {b : Nat} (h : B.getLast? = some b) :
    (A ++ B).getLast? = some b := by
  cases B with
  | nil => simp at h
  | cons x B => rw [getLast?_append_cons]; exact h


theorem getLast?_of_head {A B : List Nat} {b l : Nat} (hb : B.head? = some b)
    (h : (A ++ B).getLast? = some l) : B.getLast? = some l := by
  cases B with
  | nil => simp at hb
  | cons x B => rw [getLast?_append_cons] at h; exact h

/-! ### Permutations of `Fin n` on lists of numbers -/

variable {n : Nat}

/-- A map of `Fin n` acting on numbers (the identity from `n` on). -/
def natp (p : Fin n → Fin n) (x : Nat) : Nat := if h : x < n then (p ⟨x, h⟩).val else x

theorem natp_val (p : Fin n → Fin n) (x : Fin n) : natp p x.val = (p x).val := by
  simp [natp, x.isLt]

theorem iterate_natp (p : Fin n → Fin n) (k : Nat) (x : Fin n) :
    iterate (natp p) k x.val = (iterate p k x).val := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih => show iterate (natp p) k (natp p x.val) = _; rw [natp_val, ih]; rfl

/-- A set of darts as a predicate on numbers. -/
def natS (S : Fin n → Bool) (x : Nat) : Bool := if h : x < n then S ⟨x, h⟩ else false

theorem natS_val (S : Fin n → Bool) (x : Fin n) : natS S x.val = S x := by simp [natS, x.isLt]

/-- The orbit of a dart of a cycle is the cycle. -/
theorem reaches_iff_mem {p : Fin n → Fin n} {l : List Nat} (h : Cyc (natp p) l) {x y : Fin n}
    (hx : x.val ∈ l) : Reaches p x y ↔ y.val ∈ l := by
  constructor
  · rintro ⟨k, rfl⟩
    induction k generalizing x with
    | zero => exact hx
    | succ k ih =>
      have := cyc_maps h _ hx
      rw [natp_val] at this
      exact ih this
  · intro hy
    obtain ⟨A, B, hl⟩ := List.append_of_mem hx
    rw [hl] at h hy
    have hc := cyc_rot h
    have hy' : y.val ∈ x.val :: (B ++ A ++ [x.val]) := by
      simp only [List.mem_append, List.mem_cons] at hy ⊢
      rcases hy with h | h | h
      · exact Or.inr (Or.inl (Or.inr h))
      · exact Or.inl h
      · exact Or.inr (Or.inl (Or.inl h))
    obtain ⟨k, hk, he⟩ := List.getElem_of_mem hy'
    refine ⟨k, Fin.ext ?_⟩
    rw [← iterate_natp, chain_iterate hc k hk, he]

/-- Along a chain, the first dart of `S` is the first dart of the chain in `S`. -/
theorem nextIn_chain {p : Fin n → Fin n} {S : Fin n → Bool} :
    ∀ (l : List Nat) (y : Fin n), Chain (natp p) (y.val :: l) → (∃ z ∈ y.val :: l, natS S z = true) →
      (nextIn p S y).val = ((y.val :: l).filter (natS S)).headD 0 := by
  intro l
  induction l with
  | nil =>
    intro y _ hz
    obtain ⟨z, hz, hs⟩ := hz
    simp at hz; subst hz
    rw [natS_val] at hs
    rw [nextIn_of_mem hs]; simp [natS_val, hs]
  | cons b l ih =>
    intro y hc hz
    obtain ⟨hc', hh⟩ := chain_cons_iff.mp hc
    have hyb : natp p y.val = b := hh b rfl
    rw [natp_val] at hyb
    cases hs : S y
    · have hm : MeetsFrom p S y := by
        obtain ⟨z, hz, hsz⟩ := hz
        rcases List.mem_cons.mp hz with rfl | hz
        · rw [natS_val, hs] at hsz; exact absurd hsz (by simp)
        · have hcyc : ∃ k, iterate (natp p) k y.val = z := by
            have hc2 := chain_iterate hc
            obtain ⟨k, hk, he⟩ := List.getElem_of_mem (List.mem_cons_of_mem y.val hz)
            exact ⟨k, by rw [chain_iterate hc k hk, he]⟩
          obtain ⟨k, hk⟩ := hcyc
          rw [iterate_natp] at hk
          exact ⟨k, by rw [← natS_val S, hk]; exact hsz⟩
      rw [nextIn_of_not hs hm]
      have := ih (p y) (by rw [hyb]; exact hc') (by
        obtain ⟨z, hz, hsz⟩ := hz
        rcases List.mem_cons.mp hz with rfl | hz
        · rw [natS_val, hs] at hsz; exact absurd hsz (by simp)
        · exact ⟨z, by rw [hyb]; exact hz, hsz⟩)
      rw [this, hyb]
      simp [List.filter_cons, natS_val, hs]
    · rw [nextIn_of_mem hs]; simp [List.filter_cons, natS_val, hs]

theorem filter_eq_append_cons {q : Nat → Bool} {l A' B' : List Nat} {x : Nat}
    (h : l.filter q = A' ++ x :: B') :
    ∃ A B, l = A ++ x :: B ∧ A.filter q = A' ∧ B.filter q = B' := by
  induction l generalizing A' with
  | nil => simp at h
  | cons a l ih =>
    rw [List.filter_cons] at h
    split at h
    · rename_i ha
      cases A' with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at h
        obtain ⟨rfl, h2⟩ := h
        exact ⟨[], l, rfl, rfl, h2⟩
      | cons a' A'' =>
        simp only [List.cons_append, List.cons.injEq] at h
        obtain ⟨rfl, h2⟩ := h
        obtain ⟨A, B, hl, hA, hB⟩ := ih h2
        exact ⟨a :: A, B, by rw [hl]; rfl, by simp [ha, hA], hB⟩
    · rename_i ha
      obtain ⟨A, B, hl, hA, hB⟩ := ih h
      exact ⟨a :: A, B, by rw [hl]; rfl, by simp [ha, hA], hB⟩

/-- The rotation characterization of cycles. -/
theorem cyc_of_rot {f : Nat → Nat} {l : List Nat}
    (h : ∀ A x B, l = A ++ x :: B → f x = (B ++ A ++ [x]).headD 0) : Cyc f l := by
  refine ⟨?_, fun a b ha hb => ?_⟩
  · have : ∀ A C, l = A ++ C → Chain f C := by
      intro A C
      induction C generalizing A with
      | nil => intro _; exact Chain.nil
      | cons x C ih =>
        intro hl
        refine chain_cons_iff.mpr ⟨ih (A ++ [x]) (by rw [hl]; simp), fun b hb => ?_⟩
        cases C with
        | nil => simp at hb
        | cons y C' =>
          simp at hb; subst hb
          rw [h A x (y :: C') hl]; rfl
    exact this [] l rfl
  · obtain ⟨l', hl⟩ := List.getLast?_eq_some_iff.mp ha
    rw [h l' a [] hl]
    rw [hl] at hb
    cases l' with
    | nil => simp at hb; simp [hb]
    | cons c l'' => simp at hb; simp [hb]

/-- **First return along a cycle.** The first-return map to `S` acts as a cycle along the darts of
the cycle in `S`. -/
theorem cyc_firstReturn {p : Fin n → Fin n} (hp : ∀ a b, p a = p b → a = b) {S : Fin n → Bool}
    {l : List Nat} (h : Cyc (natp p) l) (_hnd : l.Nodup) (hlt : ∀ x ∈ l, x < n) :
    Cyc (natp (firstReturn p S)) (l.filter (natS S)) := by
  apply cyc_of_rot
  intro A' x B' hf
  obtain ⟨A, B, hl, hA, hB⟩ := filter_eq_append_cons hf
  have hxl : x ∈ l := by rw [hl]; simp
  have hxn := hlt x hxl
  have hxS : natS S x = true := (List.mem_filter.mp (by rw [hf]; simp : x ∈ l.filter (natS S))).2
  rw [hl] at h
  have hc := cyc_rot h
  let xf : Fin n := ⟨x, hxn⟩
  have hSx : S xf = true := by rw [← natS_val S xf]; exact hxS
  show natp (firstReturn p S) xf.val = _
  rw [natp_val, firstReturn_eq_nextIn hp hSx]
  obtain ⟨hc', hh⟩ := chain_cons_iff.mp hc
  have hrne : B ++ A ++ [x] ≠ [] := by simp
  obtain ⟨y, R, hyR⟩ : ∃ y R, B ++ A ++ [x] = y :: R := by
    cases h' : B ++ A ++ [x] with
    | nil => exact absurd h' hrne
    | cons y R => exact ⟨y, R, rfl⟩
  have hpy : natp p x = y := hh y (by rw [hyR]; rfl)
  rw [show x = xf.val from rfl, natp_val] at hpy
  have hyn : y < n := by rw [← hpy]; exact (p xf).isLt
  have hpxf : p xf = ⟨y, hyn⟩ := Fin.ext hpy
  rw [hpxf, nextIn_chain R ⟨y, hyn⟩ (by rw [← hyR]; exact hc') ⟨x, by rw [← hyR]; simp, hxS⟩]
  show ((y :: R).filter (natS S)).headD 0 = _
  rw [← hyR, List.filter_append, List.filter_append, hA, hB]
  simp [hxS]

/-! ### Order of occurrence and indices -/

theorem before_iff_idx {l : List Nat} {a b : Nat} :
    Before l a b ↔ ∃ i j, ∃ (_ : i < j) (hj : j < l.length), l[i] = a ∧ l[j] = b := by
  induction l with
  | nil => simp [before_nil]
  | cons x l ih =>
    rw [before_cons_iff, ih]
    constructor
    · rintro (⟨rfl, hb⟩ | ⟨i, j, hij, hj, ha, hb⟩)
      · obtain ⟨j, hj, he⟩ := List.getElem_of_mem hb
        exact ⟨0, j + 1, by omega, by simp; omega, rfl, by simpa using he⟩
      · exact ⟨i + 1, j + 1, by omega, by simp; omega, by simpa using ha, by simpa using hb⟩
    · rintro ⟨i, j, hij, hj, ha, hb⟩
      cases i with
      | zero =>
        cases j with
        | zero => omega
        | succ j =>
          left
          simp at ha hb
          exact ⟨ha.symm, by rw [← hb]; exact List.getElem_mem _⟩
      | succ i =>
        cases j with
        | zero => omega
        | succ j =>
          right
          exact ⟨i, j, by omega, by simp at hj; omega, by simpa using ha, by simpa using hb⟩

theorem nodup_rot {A B : List Nat} {x : Nat} (h : (A ++ x :: B).Nodup) : (B ++ A ++ [x]).Nodup := by
  have p1 : (A ++ x :: B).Perm ((x :: B) ++ A) := List.perm_append_comm
  have p2 : ([x] ++ (B ++ A)).Perm ((B ++ A) ++ [x]) := List.perm_append_comm
  have : (A ++ x :: B).Perm (B ++ A ++ [x]) := p1.trans (by simpa using p2)
  exact this.nodup_iff.mp h

theorem mem_rot {A B : List Nat} {x u : Nat} : u ∈ B ++ A ++ [x] ↔ u ∈ A ++ x :: B := by
  simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false]
  constructor
  · rintro ((h | h) | h)
    · exact Or.inr (Or.inr h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · rintro (h | h | h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
    · exact Or.inl (Or.inl h)

theorem before_at_iff {A B : List Nat} {x z : Nat} (h : (A ++ x :: B).Nodup) :
    Before (A ++ x :: B) x z ↔ z ∈ B := by
  have hxA : x ∉ A := fun hx => (List.nodup_append.mp h).2.2 x hx x (by simp) rfl
  have hxB : x ∉ B := (List.nodup_cons.mp (List.nodup_append.mp h).2.1).1
  rw [before_append_iff, before_cons_iff]
  constructor
  · rintro (h1 | (⟨_, hz⟩ | h1) | ⟨h1, _⟩)
    · exact absurd (before_mem h1).1 hxA
    · exact hz
    · exact absurd (before_mem h1).1 hxB
    · exact absurd h1 hxA
  · intro hz; exact Or.inr (Or.inl (Or.inl ⟨rfl, hz⟩))

theorem before_in_B_iff {A B : List Nat} {x z u : Nat} (h : (A ++ x :: B).Nodup) (hz : z ∈ B) :
    Before (A ++ x :: B) z u ↔ Before B z u := by
  have d := (List.nodup_append.mp h).2.2
  have hzA : z ∉ A := fun hA => d z hA z (by simp [hz]) rfl
  have hzx : z ≠ x := fun e => (List.nodup_cons.mp (List.nodup_append.mp h).2.1).1 (e ▸ hz)
  rw [before_append_iff, before_cons_iff]
  constructor
  · rintro (h1 | (⟨e, _⟩ | h1) | ⟨h1, _⟩)
    · exact absurd (before_mem h1).1 hzA
    · exact absurd e hzx
    · exact h1
    · exact absurd h1 hzA
  · intro h1; exact Or.inr (Or.inl (Or.inr h1))

theorem before_rot_iff {A B : List Nat} {x y c : Nat} (h : (A ++ x :: B).Nodup) (_hy : y ∈ A ++ x :: B)
    (_hc : c ∈ A ++ x :: B) (_hyx : y ≠ x) (hcx : c ≠ x) :
    Before (B ++ A ++ [x]) y c ↔ Before B y c ∨ (y ∈ B ∧ c ∈ A) ∨ Before A y c := by
  have hnd := nodup_rot h
  rw [before_append_iff, before_append_iff]
  constructor
  · rintro ((h1 | h1 | ⟨h1, h2⟩) | h1 | ⟨_, h2⟩)
    · exact Or.inl h1
    · exact Or.inr (Or.inr h1)
    · exact Or.inr (Or.inl ⟨h1, h2⟩)
    · have := (before_mem h1).2; simp at this; exact absurd this hcx
    · simp at h2; exact absurd h2 hcx
  · rintro (h1 | ⟨h1, h2⟩ | h1)
    · exact Or.inl (Or.inl h1)
    · exact Or.inl (Or.inr (Or.inr ⟨h1, h2⟩))
    · exact Or.inl (Or.inr (Or.inl h1))

/-! ### Crossing chords in a word -/

/-- In a closed well-nested word, a dart is before the partner of `x` in the rotation after `x` iff
its own partner is. -/
theorem rot_between_iff {α : Nat → Nat} {A B : List Nat} {x : Nat} (hw : WN α (A ++ x :: B))
    (hnd : (A ++ x :: B).Nodup) (hα : ∀ u, α (α u) = u)
    (hcl : ∀ u ∈ A ++ x :: B, α u ∈ A ++ x :: B) (hfix : ∀ u ∈ A ++ x :: B, α u ≠ u)
    {y : Nat} (hy : y ∈ A ++ x :: B) (hyx : y ≠ x) (hyc : y ≠ α x) :
    Before (B ++ A ++ [x]) y (α x) ↔ Before (B ++ A ++ [x]) (α y) (α x) := by
  let w := A ++ x :: B
  have hxw : x ∈ w := by simp [w]
  have hcw := hcl x hxw
  have hcx : α x ≠ x := hfix x hxw
  have hay := hcl y hy
  have hayx : α y ≠ x := fun e => hyc (by rw [← e, hα])
  have hayc : α y ≠ α x := fun e => hyx (by rw [← hα y, e, hα])
  have d := (List.nodup_append.mp hnd).2.2
  have hxB : x ∉ B := (List.nodup_cons.mp (List.nodup_append.mp hnd).2.1).1
  have hndA : A.Nodup := (List.nodup_append.mp hnd).1
  have hndB : B.Nodup := (List.nodup_cons.mp (List.nodup_append.mp hnd).2.1).2
  have inAB : ∀ u ∈ w, u ≠ x → (u ∈ A ∧ u ∉ B) ∨ (u ∈ B ∧ u ∉ A) := by
    intro u hu hux
    simp [w] at hu
    rcases hu with h | h | h
    · exact Or.inl ⟨h, fun hb => d u h u (by simp [hb]) rfl⟩
    · exact absurd h hux
    · exact Or.inr ⟨h, fun ha => d u ha u (by simp [h]) rfl⟩
  rw [before_rot_iff hnd hy hcw hyx hcx, before_rot_iff hnd hay hcw hayx hcx]
  rcases inAB (α x) hcw hcx with ⟨hcA, hcB⟩ | ⟨hcB, hcA⟩
  · -- the partner lies before `x`: compare with the chord from `α x` to `x`
    have between : ∀ u ∈ w, u ≠ x → u ≠ α x →
        ((Before B u (α x) ∨ (u ∈ B ∧ α x ∈ A) ∨ Before A u (α x)) ↔ ¬ Before A (α x) u) := by
      intro u hu hux huc
      rcases inAB u hu hux with ⟨huA, huB⟩ | ⟨huB, huA⟩
      · constructor
        · rintro (h1 | ⟨h1, _⟩ | h1)
          · exact absurd (before_mem h1).2 hcB
          · exact absurd h1 huB
          · exact before_asymm hndA h1
        · intro h1
          rcases before_total huA hcA huc with h2 | h2
          · exact Or.inr (Or.inr h2)
          · exact absurd h2 h1
      · constructor
        · intro _ h1; exact huA (before_mem h1).2
        · intro _; exact Or.inr (Or.inl ⟨huB, hcA⟩)
    have hcwx : Before w (α x) x := before_append_mid hcA (by simp)
    have key : Before A (α x) y ↔ Before A (α x) (α y) := by
      have toW : ∀ u, u ∈ A → (Before A (α x) u ↔ Before w (α x) u ∧ Before w u x) := by
        intro u hu
        constructor
        · intro h1; exact ⟨before_append_left h1, before_append_mid hu (by simp)⟩
        · rintro ⟨h1, _⟩; exact before_of_append_left hnd hcA hu h1
      constructor
      · intro h1
        have hyA := (before_mem h1).2
        obtain ⟨r1, r2⟩ := hw (α x) y (before_append_left h1) (by rw [hα]; exact before_append_mid hyA (by simp))
        simp only [hα] at r2
        have hayA : α y ∈ A := by
          rcases inAB (α y) hay hayx with ⟨h, _⟩ | ⟨h, _⟩
          · exact h
          · exfalso; exact before_asymm hnd r2 (by rw [before_at_iff hnd]; exact h)
        exact (toW _ hayA).mpr ⟨r1, r2⟩
      · intro h1
        have hayA := (before_mem h1).2
        obtain ⟨r1, r2⟩ := hw (α x) (α y) (before_append_left h1)
          (by rw [hα]; exact before_append_mid hayA (by simp))
        simp only [hα] at r1 r2
        have hyA : y ∈ A := by
          rcases inAB y hy hyx with ⟨h, _⟩ | ⟨h, _⟩
          · exact h
          · exfalso; exact before_asymm hnd r2 (by rw [before_at_iff hnd]; exact h)
        exact (toW _ hyA).mpr ⟨r1, r2⟩
    rw [between y hy hyx hyc, between (α y) hay hayx hayc, key]
  · -- the partner lies after `x`
    have toW : ∀ u ∈ w, u ≠ x → u ≠ α x →
        ((Before B u (α x) ∨ (u ∈ B ∧ α x ∈ A) ∨ Before A u (α x)) ↔
          (Before w x u ∧ Before w u (α x))) := by
      intro u hu hux huc
      rw [before_at_iff hnd]
      constructor
      · rintro (h1 | ⟨_, h1⟩ | h1)
        · exact ⟨(before_mem h1).1, before_append_right (before_cons_iff.mpr (Or.inr h1))⟩
        · exact absurd h1 hcA
        · exact absurd (before_mem h1).2 hcA
      · rintro ⟨h1, h2⟩
        exact Or.inl ((before_in_B_iff hnd h1).mp h2)
    rw [toW y hy hyx hyc, toW (α y) hay hayx hayc]
    constructor
    · rintro ⟨h1, h2⟩; exact hw x y h1 h2
    · rintro ⟨h1, h2⟩
      have := hw x (α y) h1 h2
      rw [hα] at this; exact this

/-- If every dart sees the partners of the darts before its own partner (in the rotation after it)
before its own partner, the word is well nested. -/
theorem wn_of_rot {α : Nat → Nat} {w : List Nat} (hnd : w.Nodup)
    (h : ∀ A x B, w = A ++ x :: B → ∀ y ∈ w, y ≠ x → y ≠ α x →
      (Before (B ++ A ++ [x]) y (α x) ↔ Before (B ++ A ++ [x]) (α y) (α x))) : WN α w := by
  intro x z h1 h2
  obtain ⟨A, B, hw⟩ := List.append_of_mem (before_mem h1).1
  subst hw
  have hzB : z ∈ B := (before_at_iff hnd).mp h1
  have h2' := (before_in_B_iff hnd hzB).mp h2
  have hcB := (before_mem h2').2
  have hxB : x ∉ B := (List.nodup_cons.mp (List.nodup_append.mp hnd).2.1).1
  have hzx : z ≠ x := fun e => hxB (e ▸ hzB)
  have hzc : z ≠ α x := fun e => before_irrefl (List.nodup_cons.mp (List.nodup_append.mp hnd).2.1).2 z
    (by rw [e] at h2' ⊢; exact h2')
  have := (h A x B rfl z (by simp [hzB]) hzx hzc).mp (before_append_left (before_append_left h2'))
  have hrot := nodup_rot hnd
  have hcA : α x ∉ A := fun hA => (List.nodup_append.mp hnd).2.2 _ hA _ (by simp [hcB]) rfl
  have hcx : α x ≠ x := fun e => hxB (e ▸ hcB)
  rcases before_append_iff.mp this with h3 | h3 | ⟨_, h4⟩
  · rcases before_append_iff.mp h3 with h4 | h4 | ⟨_, h5⟩
    · exact ⟨(before_at_iff hnd).mpr (before_mem h4).1,
        (before_in_B_iff hnd (before_mem h4).1).mpr h4⟩
    · exact absurd (before_mem h4).2 hcA
    · exact absurd h5 hcA
  · exact absurd h3 (by simp [before_cons_iff, before_nil])
  · simp at h4; exact absurd h4 hcx

/-! ### Chord diagrams whose tour runs along words -/

theorem natp_invol {n : Nat} {c : Fin n → Fin n} (hc : ∀ x, c (c x) = x) (u : Nat) :
    natp c (natp c u) = u := by
  unfold natp
  by_cases hu : u < n
  · simp [hu, (c ⟨u, hu⟩).isLt, hc]
  · simp [hu]

theorem inArc_iff_before (D : Diagram n) {A B : List Nat} {x : Fin n}
    (hcyc : Cyc (natp D.tour) (A ++ x.val :: B)) (hnd : (A ++ x.val :: B).Nodup) (hxS : D.S x = true)
    (hcm : (D.chord x).val ∈ A ++ x.val :: B) (y : Fin n) :
    D.InArc x y ↔ y ≠ D.chord x ∧ Before (B ++ A ++ [x.val]) y.val (D.chord x).val := by
  rw [D.inArc_iff hxS]
  have hc := cyc_rot hcyc
  have hR := nodup_rot hnd
  have hit : ∀ k (hk : k < (B ++ A ++ [x.val]).length),
      (iterate D.tour k (D.tour x)).val = (B ++ A ++ [x.val])[k] := by
    intro k hk
    have := chain_iterate hc (k + 1) (by simp at hk ⊢; omega)
    rw [iterate_natp] at this
    have e : iterate D.tour (k + 1) x = iterate D.tour k (D.tour x) := rfl
    rw [e] at this
    simpa using this
  have hcx : (D.chord x).val ≠ x.val := fun e => D.chord_ne x hxS (Fin.ext e)
  have hcR : (D.chord x).val ∈ B ++ A ++ [x.val] := mem_rot.mpr hcm
  obtain ⟨c, hcl, hce⟩ := List.getElem_of_mem hcR
  constructor
  · rintro ⟨hy, j, hj, hno⟩
    have hjc : j < c := by
      apply Classical.byContradiction
      intro hjc
      exact hno c (by omega) (Fin.ext (by rw [hit c hcl, hce]))
    refine ⟨hy, before_iff_idx.mpr ⟨j, c, hjc, hcl, ?_, hce⟩⟩
    rw [← hit j (by omega), hj]
  · rintro ⟨hy, hb⟩
    obtain ⟨i, j', hij, hj', hi, hj⟩ := before_iff_idx.mp hb
    refine ⟨hy, i, Fin.ext (by rw [hit i (by omega), hi]), fun i' hi' he => ?_⟩
    have h1 : (B ++ A ++ [x.val])[i'] = (D.chord x).val := by
      rw [← hit i' (by omega), he]
    exact before_irrefl hR _ (before_iff_idx.mpr ⟨i', j', by omega, hj', h1, hj⟩)

/-- **Crossings in words.** If the tour of a diagram runs along closed words covering its darts,
the diagram is non-crossing iff every word is well nested. -/
theorem noncrossing_iff_wn (D : Diagram n) (Ws : List (List Nat))
    (hcyc : ∀ w ∈ Ws, Cyc (natp D.tour) w) (hnd : ∀ w ∈ Ws, w.Nodup) (hlt : ∀ w ∈ Ws, ∀ u ∈ w, u < n)
    (hS : ∀ w ∈ Ws, ∀ u ∈ w, natS D.S u = true) (hcl : ∀ w ∈ Ws, ∀ u ∈ w, natp D.chord u ∈ w)
    (hcover : ∀ x : Fin n, D.S x = true → ∃ w ∈ Ws, x.val ∈ w) :
    D.NonCrossing ↔ ∀ w ∈ Ws, WN (natp D.chord) w := by
  have hα := natp_invol D.chord_invol
  have hfix : ∀ w ∈ Ws, ∀ u ∈ w, natp D.chord u ≠ u := by
    intro w hw u hu e
    have hun := hlt w hw u hu
    have := hS w hw u hu
    rw [show u = (⟨u, hun⟩ : Fin n).val from rfl, natS_val] at this
    rw [show u = (⟨u, hun⟩ : Fin n).val from rfl, natp_val] at e
    exact D.chord_ne _ this (Fin.ext e)
  constructor
  · intro hnc w hw
    apply wn_of_rot (hnd w hw)
    intro A x B hwx y hy hyx hyc
    have hxw : x ∈ w := by rw [hwx]; simp
    have hxn := hlt w hw x hxw
    have hyn := hlt w hw y hy
    let xf : Fin n := ⟨x, hxn⟩
    let yf : Fin n := ⟨y, hyn⟩
    have hxS : D.S xf = true := by rw [← natS_val D.S xf]; exact hS w hw x hxw
    have hyS : D.S yf = true := by rw [← natS_val D.S yf]; exact hS w hw y hy
    have hcx : natp D.chord x = (D.chord xf).val := natp_val _ xf
    have hcy : natp D.chord y = (D.chord yf).val := natp_val _ yf
    rw [hwx] at hw
    have hcyc' := hcyc _ hw
    have hnd' := hnd _ hw
    have hcm : (D.chord xf).val ∈ A ++ x :: B := by rw [← hcx]; exact hcl _ hw x (by simp)
    have h1 := inArc_iff_before D hcyc' hnd' hxS hcm yf
    have h2 := inArc_iff_before D hcyc' hnd' hxS hcm (D.chord yf)
    have hne1 : yf ≠ xf := fun e => hyx (congrArg Fin.val e)
    have hne2 : yf ≠ D.chord xf := fun e => hyc (by rw [hcx]; exact congrArg Fin.val e)
    have hne3 : D.chord yf ≠ D.chord xf := fun e => hne1 (D.chord_inj e)
    have := hnc xf yf hxS hyS hne1 hne2
    rw [h1, h2] at this
    rw [hcx, hcy]
    exact ⟨fun h => (this.mp ⟨hne2, h⟩).2, fun h => (this.mpr ⟨hne3, h⟩).2⟩
  · intro hwn x y hxS hyS hyx hyc
    obtain ⟨w, hw, hxw⟩ := hcover x hxS
    obtain ⟨A, B, hwx⟩ := List.append_of_mem hxw
    have hcx : natp D.chord x.val = (D.chord x).val := natp_val _ x
    have hcm : (D.chord x).val ∈ w := by rw [← hcx]; exact hcl w hw _ hxw
    have hcyc' := hcyc w hw
    have hnd' := hnd w hw
    rw [hwx] at hcyc' hnd' hcm
    by_cases hyw : y.val ∈ w
    · rw [inArc_iff_before D hcyc' hnd' hxS hcm, inArc_iff_before D hcyc' hnd' hxS hcm]
      have hcy : natp D.chord y.val = (D.chord y).val := natp_val _ y
      have hwn' := hwn w hw
      rw [hwx] at hwn' hyw
      have key := rot_between_iff hwn' hnd' hα (by rw [← hwx]; exact hcl w hw) (by rw [← hwx]; exact hfix w hw)
        hyw (fun e => hyx (Fin.ext e)) (by rw [hcx]; exact fun e => hyc (Fin.ext e))
      rw [hcx, hcy] at key
      have hne3 : D.chord y ≠ D.chord x := fun e => hyx (D.chord_inj e)
      exact ⟨fun h => ⟨hne3, key.mp h.2⟩, fun h => ⟨hyc, key.mpr h.2⟩⟩
    · have hreach : ∀ z, D.InArc x z → z.val ∈ w := by
        intro z hz
        obtain ⟨_, j, hj, _⟩ := (D.inArc_iff hxS).mp hz
        exact (reaches_iff_mem (hcyc w hw) hxw).mp ⟨j + 1, hj⟩
      have hcyw : (D.chord y).val ∉ w := by
        intro h
        have := hcl w hw _ h
        rw [natp_val, D.chord_invol] at this
        exact hyw this
      exact ⟨fun h => absurd (hreach y h) hyw, fun h => absurd (hreach _ h) hcyw⟩

end STACS2027.Embed

module

public import ApproximationHardness.Embed.Solver
import Lean.Elab.Tactic.Omega

/-!
# Invariants of the solver

For a fixed choice of sides `s0` satisfying every fork, the result of a node with open ends `A`
satisfies `Inv s0 A`: its groups list exactly the ends of `A`; every class is sorted by strictly
decreasing key; the groups are nonempty and occupy disjoint ranges, the top one the deepest; the
two classes of a group lie on opposite sides of `s0`; and `low` is the least key plus one.
-/

@[expose] public section

namespace STACS2027.Embed

theorem mem_els {seg : List Grp} {e : Nat} : e ∈ els seg ↔ ∃ g ∈ seg, e ∈ g.els := by
  simp [els]

@[simp] theorem els_nil : els [] = [] := rfl

theorem els_cons (g : Grp) (seg : List Grp) : els (g :: seg) = g.els ++ els seg := by
  simp [els]

theorem els_append (a b : List Grp) : els (a ++ b) = els a ++ els b := by
  simp [els]

theorem mem_gels {g : Grp} {e : Nat} : e ∈ g.els ↔ e ∈ g.P ∨ e ∈ g.M := List.mem_append

namespace Sol

variable (S : Sol)

/-- Strictly decreasing keys. -/
def Desc (l : List Nat) : Prop := l.Pairwise (fun a b => S.key b < S.key a)

/-- The conditions on a stack of groups that do not depend on the node. -/
structure Core (s0 : Nat → Bool) (seg : List Grp) : Prop where
  ne : ∀ g ∈ seg, g.els ≠ []
  sortP : ∀ g ∈ seg, S.Desc g.P
  sortM : ∀ g ∈ seg, S.Desc g.M
  stack : seg.Pairwise (fun g h => ∀ a ∈ g.els, ∀ b ∈ h.els, S.key b < S.key a)
  cons : ∀ g ∈ seg, ∃ σ, (∀ e ∈ g.P, s0 e = σ) ∧ (∀ e ∈ g.M, s0 e = !σ)
  bound : ∀ e ∈ els seg, S.key e + 1 < S.INF

/-- **The invariant** of the result `r` of a node with open ends `A`. -/
structure Inv (s0 : Nat → Bool) (A : Nat → Prop) (r : Res) : Prop where
  core : S.Core s0 r.seg
  mem : ∀ e, e ∈ els r.seg ↔ A e
  low : (r.seg = [] ∧ r.low = S.INF) ∨
    (∃ m ∈ els r.seg, r.low = S.key m + 1 ∧ ∀ e ∈ els r.seg, S.key m ≤ S.key e)

variable {S}

/-! ### Sorted lists -/

theorem Desc.nodup {l : List Nat} (h : S.Desc l) : l.Nodup := by
  unfold Desc at h
  exact h.imp fun {a b} hab e => by subst e; omega

theorem Desc.sub {l l' : List Nat} (h : S.Desc l) (hs : l'.Sublist l) : S.Desc l' := h.sublist hs

theorem desc_append {l l' : List Nat} (h : S.Desc l) (h' : S.Desc l')
    (hlt : ∀ a ∈ l, ∀ b ∈ l', S.key b < S.key a) : S.Desc (l ++ l') :=
  List.pairwise_append.mpr ⟨h, h', hlt⟩

theorem desc_flatMap {L : List Grp} {f : Grp → List Nat} (h : ∀ g ∈ L, S.Desc (f g))
    (hlt : L.Pairwise fun g h => ∀ a ∈ f g, ∀ b ∈ f h, S.key b < S.key a) : S.Desc (L.flatMap f) := by
  induction L with
  | nil => exact List.Pairwise.nil
  | cons g L ih =>
    rw [List.flatMap_cons]
    obtain ⟨h1, h2⟩ := List.pairwise_cons.mp hlt
    refine desc_append (h g (List.mem_cons_self ..)) (ih (fun x hx => h x (List.mem_cons_of_mem _ hx)) h2) ?_
    intro a ha b hb
    obtain ⟨x, hx, hbx⟩ := List.mem_flatMap.mp hb
    exact h1 x hx a ha b hbx

theorem kh_ge {l : List Nat} (hd : S.Desc l) {e : Nat} (he : e ∈ l) : S.key e + 1 ≤ S.kh l := by
  cases l with
  | nil => simp at he
  | cons a t =>
    show S.key e + 1 ≤ S.key a + 1
    rcases List.mem_cons.mp he with rfl | h
    · exact Nat.le_refl _
    · have := List.rel_of_pairwise_cons hd h; omega

theorem kh_mem {l : List Nat} (h : l ≠ []) : ∃ e ∈ l, S.kh l = S.key e + 1 := by
  cases l with
  | nil => exact absurd rfl h
  | cons a t => exact ⟨a, List.mem_cons_self .., rfl⟩

theorem kh_nil : S.kh [] = 0 := rfl

theorem le_gtop {g : Grp} (hP : S.Desc g.P) (hM : S.Desc g.M) {e : Nat} (he : e ∈ g.els) :
    S.key e + 1 ≤ S.gtop g := by
  unfold gtop
  rcases mem_gels.mp he with h | h
  · have := kh_ge hP h; omega
  · have := kh_ge hM h; omega

theorem gtop_mem {g : Grp} (h : g.els ≠ []) : ∃ e ∈ g.els, S.gtop g = S.key e + 1 := by
  unfold gtop
  by_cases hP : g.P = []
  · have hM : g.M ≠ [] := by intro hM; apply h; simp [Grp.els, hP, hM]
    obtain ⟨e, he, hk⟩ := kh_mem (S := S) hM
    refine ⟨e, mem_gels.mpr (Or.inr he), ?_⟩
    rw [hP, kh_nil]; omega
  · obtain ⟨e, he, hk⟩ := kh_mem (S := S) hP
    by_cases hM : g.M = []
    · refine ⟨e, mem_gels.mpr (Or.inl he), ?_⟩
      rw [hM, kh_nil]; omega
    · obtain ⟨f, hf, hk'⟩ := kh_mem (S := S) hM
      by_cases hle : S.kh g.M ≤ S.kh g.P
      · exact ⟨e, mem_gels.mpr (Or.inl he), by omega⟩
      · exact ⟨f, mem_gels.mpr (Or.inr hf), by omega⟩

theorem head_of_max {l : List Nat} (hd : S.Desc l) {x : Nat} (hx : x ∈ l)
    (hmax : ∀ y ∈ l, y ≠ x → S.key y < S.key x) : l = x :: l.tail := by
  cases l with
  | nil => simp at hx
  | cons a t =>
    rcases List.mem_cons.mp hx with rfl | h
    · rfl
    · have h1 := List.rel_of_pairwise_cons hd h
      by_cases hax : a = x
      · subst hax; rfl
      · have := hmax a (List.mem_cons_self ..) hax; omega

/-! ### The core invariant -/

theorem core_nil (s0 : Nat → Bool) : S.Core s0 [] :=
  ⟨by simp, by simp, by simp, List.Pairwise.nil, by simp, by simp⟩

theorem Core.tail {s0 : Nat → Bool} {g : Grp} {seg : List Grp} (h : S.Core s0 (g :: seg)) : S.Core s0 seg :=
  ⟨fun x hx => h.ne x (List.mem_cons_of_mem _ hx), fun x hx => h.sortP x (List.mem_cons_of_mem _ hx),
    fun x hx => h.sortM x (List.mem_cons_of_mem _ hx), (List.pairwise_cons.mp h.stack).2,
    fun x hx => h.cons x (List.mem_cons_of_mem _ hx),
    fun e he => h.bound e (by rw [els_cons]; exact List.mem_append_right _ he)⟩

theorem Core.suffix {s0 : Nat → Bool} {A B : List Grp} (h : S.Core s0 (A ++ B)) : S.Core s0 B := by
  induction A with
  | nil => exact h
  | cons g A ih => exact ih h.tail

theorem Core.prefix {s0 : Nat → Bool} {A B : List Grp} (h : S.Core s0 (A ++ B)) : S.Core s0 A :=
  ⟨fun x hx => h.ne x (List.mem_append_left _ hx), fun x hx => h.sortP x (List.mem_append_left _ hx),
    fun x hx => h.sortM x (List.mem_append_left _ hx), (List.pairwise_append.mp h.stack).1,
    fun x hx => h.cons x (List.mem_append_left _ hx),
    fun e he => h.bound e (by rw [els_append]; exact List.mem_append_left _ he)⟩

theorem core_cons {s0 : Nat → Bool} {G : Grp} {seg : List Grp} (hc : S.Core s0 seg) (hG : G.els ≠ [])
    (hP : S.Desc G.P) (hM : S.Desc G.M) (hσ : ∃ σ, (∀ e ∈ G.P, s0 e = σ) ∧ (∀ e ∈ G.M, s0 e = !σ))
    (hb : ∀ e ∈ G.els, S.key e + 1 < S.INF) (hlt : ∀ h ∈ seg, ∀ a ∈ G.els, ∀ b ∈ h.els, S.key b < S.key a) :
    S.Core s0 (G :: seg) := by
  refine ⟨?_, ?_, ?_, List.pairwise_cons.mpr ⟨hlt, hc.stack⟩, ?_, ?_⟩
  · intro x hx; rcases List.mem_cons.mp hx with rfl | hx
    · exact hG
    · exact hc.ne x hx
  · intro x hx; rcases List.mem_cons.mp hx with rfl | hx
    · exact hP
    · exact hc.sortP x hx
  · intro x hx; rcases List.mem_cons.mp hx with rfl | hx
    · exact hM
    · exact hc.sortM x hx
  · intro x hx; rcases List.mem_cons.mp hx with rfl | hx
    · exact hσ
    · exact hc.cons x hx
  · intro e he; rw [els_cons] at he
    rcases List.mem_append.mp he with he | he
    · exact hb e he
    · exact hc.bound e he

theorem grp_nodup {s0 : Nat → Bool} {g : Grp} (hP : S.Desc g.P) (hM : S.Desc g.M)
    (hσ : ∃ σ, (∀ e ∈ g.P, s0 e = σ) ∧ (∀ e ∈ g.M, s0 e = !σ)) : g.els.Nodup := by
  obtain ⟨σ, h1, h2⟩ := hσ
  refine List.nodup_append.mpr ⟨hP.nodup, hM.nodup, fun a ha b hb e => ?_⟩
  subst e
  have := h1 a ha; have := h2 a hb
  cases σ <;> simp_all

theorem Core.nodup {s0 : Nat → Bool} {seg : List Grp} (h : S.Core s0 seg) : (els seg).Nodup := by
  induction seg with
  | nil => exact List.nodup_nil
  | cons g seg ih =>
    rw [els_cons]
    have hg := grp_nodup (h.sortP g (List.mem_cons_self ..)) (h.sortM g (List.mem_cons_self ..))
      (h.cons g (List.mem_cons_self ..))
    refine List.nodup_append.mpr ⟨hg, ih h.tail, fun a ha b hb e => ?_⟩
    subst e
    obtain ⟨x, hx, hax⟩ := mem_els.mp hb
    have := (List.pairwise_cons.mp h.stack).1 x hx a ha a hax
    omega

theorem Core.gtop_lt {s0 : Nat → Bool} {seg : List Grp} (h : S.Core s0 seg) :
    seg.Pairwise fun g g' => S.gtop g' < S.gtop g := by
  refine List.Pairwise.imp_of_mem ?_ h.stack
  intro g g' hg hg' hlt
  obtain ⟨b, hb, hkb⟩ := gtop_mem (S := S) (h.ne g' hg')
  obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil _ (h.ne g hg)
  have h1 := le_gtop (h.sortP g hg) (h.sortM g hg) ha
  have := hlt a ha b hb
  omega

theorem Core.lt_of_mem {s0 : Nat → Bool} {g : Grp} {seg : List Grp} (h : S.Core s0 (g :: seg)) {a b : Nat}
    (ha : a ∈ g.els) (hb : b ∈ els seg) : S.key b < S.key a := by
  obtain ⟨x, hx, hbx⟩ := mem_els.mp hb
  exact (List.pairwise_cons.mp h.stack).1 x hx a ha b hbx

/-! ### Empty results, darts and targets -/

theorem inv_empty (s0 : Nat → Bool) : S.Inv s0 (fun _ => False) S.empty :=
  ⟨core_nil s0, by simp [empty], Or.inl ⟨rfl, rfl⟩⟩

theorem inv_dart (s0 : Nat → Bool) {e : Nat} (he : S.key e + 1 < S.INF) : S.Inv s0 (· = e) (S.dartRes e) := by
  have hels : els (S.dartRes e).seg = [e] := by simp [dartRes, els, Grp.els]
  refine ⟨?_, ?_, Or.inr ⟨e, by rw [hels]; simp, rfl, fun x hx => by rw [hels] at hx; simp at hx; subst hx; omega⟩⟩
  · refine core_cons (core_nil s0) (by simp [Grp.els]) (List.pairwise_singleton _ _) List.Pairwise.nil
      ⟨s0 e, by simp, by simp⟩ (by simp [Grp.els]; exact he) (by simp)
  · intro x; rw [hels]; simp

theorem closeRes_cons {r : Res} {g : Grp} {rest : List Grp} (h : r.seg = g :: rest) (x : Nat) :
    S.closeRes x r =
      ⟨if (if g.P.head? = some x then (⟨g.id, g.P.tail, g.M⟩ : Grp) else ⟨g.id, g.P, g.M.tail⟩).P = [] ∧
          (if g.P.head? = some x then (⟨g.id, g.P.tail, g.M⟩ : Grp) else ⟨g.id, g.P, g.M.tail⟩).M = []
        then rest else (if g.P.head? = some x then (⟨g.id, g.P.tail, g.M⟩ : Grp) else ⟨g.id, g.P, g.M.tail⟩) :: rest,
        if r.low = S.key x + 1 then S.INF else r.low⟩ := by
  unfold closeRes; rw [h]

theorem mem_tail_of_nodup {x : Nat} {l : List Nat} (hnd : (x :: l).Nodup) {e : Nat} :
    e ∈ l ↔ e ∈ x :: l ∧ e ≠ x := by
  constructor
  · intro h; exact ⟨List.mem_cons_of_mem _ h, fun e' => (List.nodup_cons.mp hnd).1 (e' ▸ h)⟩
  · rintro ⟨h, h'⟩; rcases List.mem_cons.mp h with h | h
    · exact absurd h h'
    · exact h

/-- **Closing at a target** the deepest open end `x`. -/
theorem inv_close {s0 : Nat → Bool} {A : Nat → Prop} {r : Res} {x : Nat} (hI : S.Inv s0 A r) (hx : A x)
    (hmax : ∀ y, A y → y ≠ x → S.key y < S.key x) :
    S.Inv s0 (fun y => A y ∧ y ≠ x) (S.closeRes x r) := by
  obtain ⟨hc, hmem, hlow⟩ := hI
  have hxe : x ∈ els r.seg := (hmem x).mpr hx
  cases hr : r.seg with
  | nil => rw [hr] at hxe; simp at hxe
  | cons g rest =>
    rw [hr] at hc hxe hmem hlow
    rw [closeRes_cons hr]
    have hinA : ∀ y ∈ g.els, A y := fun y hy => (hmem y).mp (by rw [els_cons]; exact List.mem_append_left _ hy)
    have hg : x ∈ g.els := by
      rw [els_cons] at hxe
      rcases List.mem_append.mp hxe with h | h
      · exact h
      · exfalso
        obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil _ (hc.ne g (List.mem_cons_self ..))
        have h1 := hc.lt_of_mem ha h
        by_cases hax : a = x
        · subst hax; omega
        · have := hmax a (hinA a ha) hax; omega
    have hmax' : ∀ y ∈ g.els, y ≠ x → S.key y < S.key x := fun y hy hyx => hmax y (hinA y hy) hyx
    have hgP := hc.sortP g (List.mem_cons_self ..)
    have hgM := hc.sortM g (List.mem_cons_self ..)
    have hnd := hc.nodup
    rw [els_cons] at hnd
    have hgnd : g.els.Nodup := (List.nodup_append.mp hnd).1
    have hxrest : x ∉ els rest := fun h => (List.nodup_append.mp hnd).2.2 x hg x h rfl
    obtain ⟨g', hg'eq, hsP, hsM, hmem'⟩ : ∃ g' : Grp,
        (if g.P.head? = some x then (⟨g.id, g.P.tail, g.M⟩ : Grp) else ⟨g.id, g.P, g.M.tail⟩) = g' ∧
          g'.P.Sublist g.P ∧ g'.M.Sublist g.M ∧ ∀ e, e ∈ g'.els ↔ e ∈ g.els ∧ e ≠ x := by
      split
      · rename_i hh
        obtain ⟨t, ht⟩ : ∃ t, g.P = x :: t := by
          cases hp : g.P with
          | nil => rw [hp] at hh; simp at hh
          | cons a t => rw [hp] at hh; simp at hh; subst hh; exact ⟨t, rfl⟩
        refine ⟨_, rfl, List.tail_sublist _, List.Sublist.refl _, fun e => ?_⟩
        have hnd' : (x :: (t ++ g.M)).Nodup := by
          have := hgnd; unfold Grp.els at this; rw [ht] at this; simpa using this
        simp only [Grp.els, ht, List.tail_cons]
        rw [mem_tail_of_nodup hnd']; simp
      · rename_i hh
        have hxM : x ∈ g.M := by
          rcases mem_gels.mp hg with h | h
          · exfalso; apply hh
            rw [head_of_max hgP h (fun y hy hyx => hmax' y (mem_gels.mpr (Or.inl hy)) hyx)]; rfl
          · exact h
        obtain ⟨t, ht⟩ : ∃ t, g.M = x :: t :=
          ⟨_, head_of_max hgM hxM (fun y hy hyx => hmax' y (mem_gels.mpr (Or.inr hy)) hyx)⟩
        refine ⟨_, rfl, List.Sublist.refl _, List.tail_sublist _, fun e => ?_⟩
        have hperm : (g.P ++ x :: t).Perm (x :: (g.P ++ t)) := List.perm_middle
        have hnd' : (x :: (g.P ++ t)).Nodup := by
          have := hgnd; unfold Grp.els at this; rw [ht] at this; exact hperm.nodup_iff.mp this
        simp only [Grp.els, ht, List.tail_cons]
        rw [mem_tail_of_nodup hnd', hperm.mem_iff]
    rw [hg'eq]
    have hcg' : (∃ σ, (∀ e ∈ g'.P, s0 e = σ) ∧ (∀ e ∈ g'.M, s0 e = !σ)) := by
      obtain ⟨σ, h1, h2⟩ := hc.cons g (List.mem_cons_self ..)
      exact ⟨σ, fun e he => h1 e (hsP.subset he), fun e he => h2 e (hsM.subset he)⟩
    have hsub : ∀ e ∈ g'.els, e ∈ g.els := fun e he => ((hmem' e).mp he).1
    -- the new stack
    have hmn : ∀ e, e ∈ els (if g'.P = [] ∧ g'.M = [] then rest else g' :: rest) ↔ e ∈ g'.els ∨ e ∈ els rest := by
      intro e
      split
      · rename_i h
        have : g'.els = [] := by simp [Grp.els, h.1, h.2]
        rw [this]; simp
      · rw [els_cons, List.mem_append]
    have hcore : S.Core s0 (if g'.P = [] ∧ g'.M = [] then rest else g' :: rest) := by
      split
      · exact hc.tail
      · rename_i h
        refine core_cons hc.tail (by intro e; apply h; simp [Grp.els] at e; exact e) (hgP.sub hsP) (hgM.sub hsM) hcg'
          (fun e he => hc.bound e (by rw [els_cons]; exact List.mem_append_left _ (hsub e he)))
          (fun h' hh a ha b hb => (List.pairwise_cons.mp hc.stack).1 h' hh a (hsub a ha) b hb)
    have hnil : (if g'.P = [] ∧ g'.M = [] then rest else g' :: rest) = [] ↔ g'.els = [] ∧ rest = [] := by
      split
      · rename_i h; simp [Grp.els, h.1, h.2]
      · rename_i h; simp only [reduceCtorEq, false_iff, not_and]
        intro e; apply absurd _ h; simp [Grp.els] at e; exact e
    have hmemN : ∀ e, e ∈ els (if g'.P = [] ∧ g'.M = [] then rest else g' :: rest) ↔ A e ∧ e ≠ x := by
      intro e
      rw [hmn, hmem', ← hmem e, els_cons, List.mem_append]
      constructor
      · rintro (⟨h1, h2⟩ | h)
        · exact ⟨Or.inl h1, h2⟩
        · exact ⟨Or.inr h, fun e' => hxrest (e' ▸ h)⟩
      · rintro ⟨h1 | h1, h2⟩
        · exact Or.inl ⟨h1, h2⟩
        · exact Or.inr h1
    refine ⟨hcore, hmemN, ?_⟩
    rcases hlow with ⟨h, _⟩ | ⟨m, hm, hlm, hmin⟩
    · exact absurd h (by simp)
    · by_cases hmx : m = x
      · subst hmx
        left
        have hno : ∀ e, ¬ (A e ∧ e ≠ m) := by
          rintro e ⟨he, hne⟩
          have h1 := hmax e he hne
          have h2 := hmin e ((hmem e).mpr he)
          omega
        refine ⟨?_, by rw [ite_eq_left hlm]⟩
        apply hnil.mpr
        constructor
        · apply List.eq_nil_iff_forall_not_mem.mpr
          intro e he; exact hno e ((hmemN e).mp ((hmn e).mpr (Or.inl he)))
        · apply List.eq_nil_iff_forall_not_mem.mpr
          intro h hh
          obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ (hc.tail.ne h hh)
          exact hno e ((hmemN e).mp ((hmn e).mpr (Or.inr (mem_els.mpr ⟨h, hh, he⟩))))
      · right
        have hkm : S.key m < S.key x := hmax m ((hmem m).mp hm) hmx
        refine ⟨m, (hmemN m).mpr ⟨(hmem m).mp hm, hmx⟩, ?_, fun e he => hmin e ((hmem e).mpr ((hmemN e).mp he).1)⟩
        show (if r.low = S.key x + 1 then S.INF else r.low) = S.key m + 1
        rw [ite_eq_right (show ¬ r.low = S.key x + 1 by omega)]; exact hlm

/-! ### Forks -/

variable (S) in
/-- The fork condition for `s0`: the ends of `B` on one side, the ends of `A` reaching above them
on the other. -/
def LRC (s0 : Nat → Bool) (A B : Nat → Prop) : Prop :=
  ∃ σ, (∀ b, B b → s0 b = σ) ∧ (∀ a, A a → (∃ b, B b ∧ S.key b < S.key a) → s0 a = !σ)

theorem mem_takeWhile_imp' {p : Grp → Bool} {l : List Grp} {x : Grp} (h : x ∈ l.takeWhile p) : p x = true := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    rw [List.takeWhile_cons] at h
    split at h
    · rename_i hp
      rcases List.mem_cons.mp h with rfl | h
      · exact hp
      · exact ih h
    · simp at h

theorem popped_append_rest (lh : Nat) (rx : Res) : S.popped lh rx ++ S.rest lh rx = rx.seg :=
  List.takeWhile_append_dropWhile

theorem lt_gtop_of_popped {lh : Nat} {rx : Res} {g : Grp} (h : g ∈ S.popped lh rx) : lh < S.gtop g := by
  have := mem_takeWhile_imp' h; simpa using this

theorem gtop_le_of_rest {s0 : Nat → Bool} {lh : Nat} {rx : Res} (hc : S.Core s0 rx.seg) {g : Grp}
    (h : g ∈ S.rest lh rx) : S.gtop g ≤ lh := by
  have hm := hc.gtop_lt
  unfold rest at h
  generalize rx.seg = l at hm h
  induction l with
  | nil => simp at h
  | cons a l ih =>
    rw [List.dropWhile_cons] at h
    obtain ⟨h1, h2⟩ := List.pairwise_cons.mp hm
    split at h
    · exact ih h2 h
    · rename_i hp
      have hpa : ¬ lh < S.gtop a := by simpa using hp
      rcases List.mem_cons.mp h with rfl | h
      · omega
      · have := h1 g h; omega

theorem mem_upC_loC {lh : Nat} {g : Grp} {e : Nat} : e ∈ g.els ↔ e ∈ S.upC lh g ∨ e ∈ S.loC lh g := by
  rw [mem_gels]; unfold upC loC; split
  · exact Iff.rfl
  · exact Or.comm

theorem upC_sub {lh : Nat} {g : Grp} {e : Nat} (h : e ∈ S.upC lh g) : e ∈ g.els :=
  mem_upC_loC.mpr (Or.inl h)

theorem loC_sub {lh : Nat} {g : Grp} {e : Nat} (h : e ∈ S.loC lh g) : e ∈ g.els :=
  mem_upC_loC.mpr (Or.inr h)

theorem desc_upC {lh : Nat} {g : Grp} (hP : S.Desc g.P) (hM : S.Desc g.M) : S.Desc (S.upC lh g) := by
  unfold upC; split
  · exact hP
  · exact hM

theorem desc_loC {lh : Nat} {g : Grp} (hP : S.Desc g.P) (hM : S.Desc g.M) : S.Desc (S.loC lh g) := by
  unfold loC; split
  · exact hM
  · exact hP

/-- The classes of a group lie on opposite sides. -/
theorem side_upC_loC {s0 : Nat → Bool} {lh : Nat} {g : Grp}
    (hσ : ∃ σ, (∀ e ∈ g.P, s0 e = σ) ∧ (∀ e ∈ g.M, s0 e = !σ)) {u : Nat} (hu : u ∈ S.upC lh g) :
    (∀ e ∈ S.upC lh g, s0 e = s0 u) ∧ (∀ e ∈ S.loC lh g, s0 e = !s0 u) := by
  obtain ⟨σ, h1, h2⟩ := hσ
  unfold upC at hu ⊢; unfold loC
  split
  · rename_i h; rw [ite_eq_left h] at hu
    refine ⟨fun e he => by rw [h1 e he, h1 u hu], fun e he => by rw [h2 e he, h1 u hu]⟩
  · rename_i h; rw [ite_eq_right h] at hu
    refine ⟨fun e he => by rw [h2 e he, h2 u hu], fun e he => by rw [h1 e he, h2 u hu]; simp⟩

/-- A popped group has an end in its upper class reaching above `lh`. -/
theorem upC_reaches {lh : Nat} {g : Grp} (h : lh < S.gtop g) : ∃ u ∈ S.upC lh g, lh < S.key u + 1 := by
  unfold upC
  split
  · rename_i hP
    have hne : g.P ≠ [] := by intro e; rw [e, kh_nil] at hP; omega
    obtain ⟨u, hu, hk⟩ := kh_mem (S := S) hne
    exact ⟨u, hu, by omega⟩
  · rename_i hP
    unfold gtop at h
    have hM : lh < S.kh g.M := by omega
    have hne : g.M ≠ [] := by intro e; rw [e, kh_nil] at hM; omega
    obtain ⟨u, hu, hk⟩ := kh_mem (S := S) hne
    exact ⟨u, hu, by omega⟩

theorem els_merge (v : Nat) (rx ry : Res) (h : ry.seg ≠ []) :
    (S.mergeRes v rx ry).seg = ⟨S.gid v, (S.popped ry.low rx).flatMap (S.upC ry.low),
      els ry.seg ++ (S.popped ry.low rx).flatMap (S.loC ry.low)⟩ :: S.rest ry.low rx := by
  unfold mergeRes; rw [ite_eq_right h]

theorem low_merge (v : Nat) (rx ry : Res) : (S.mergeRes v rx ry).low = rx.low := by
  unfold mergeRes; split <;> rfl

/-- The facts behind a merge, for a nonempty `ry`. -/
structure MergeFacts (s0 : Nat → Bool) (A B : Nat → Prop) (rx ry : Res) (m' : Nat) (σ : Bool) : Prop where
  lh : ry.low = S.key m' + 1
  mB : B m'
  minB : ∀ b, B b → S.key m' ≤ S.key b
  sB : ∀ b, B b → s0 b = σ
  upS : ∀ g ∈ S.popped ry.low rx, ∀ e ∈ S.upC ry.low g, s0 e = !σ
  loS : ∀ g ∈ S.popped ry.low rx, ∀ e ∈ S.loC ry.low g, s0 e = σ
  loK : ∀ g ∈ S.popped ry.low rx, ∀ e ∈ S.loC ry.low g, S.key e < S.key m'
  restK : ∀ g ∈ S.rest ry.low rx, ∀ e ∈ g.els, S.key e < S.key m'
  oneSide : ∀ g ∈ ry.seg, g.P = [] ∨ g.M = []
  upAll : ∀ a, A a → S.key m' < S.key a → ∃ g ∈ S.popped ry.low rx, a ∈ S.upC ry.low g

theorem merge_facts {s0 : Nat → Bool} {A B : Nat → Prop} {rx ry : Res} (hx : S.Inv s0 A rx) (hy : S.Inv s0 B ry)
    (hne : ∀ a b, A a → B b → S.key a ≠ S.key b) (hL : S.LRC s0 A B) (hy0 : ry.seg ≠ []) :
    ∃ m' σ, S.MergeFacts s0 A B rx ry m' σ := by
  obtain ⟨σ0, hB, hA⟩ := hL
  rcases hy.low with ⟨h, _⟩ | ⟨m', hm', hlm', hmin'⟩
  · exact absurd h hy0
  have hmB : B m' := (hy.mem m').mp hm'
  have hminB : ∀ b, B b → S.key m' ≤ S.key b := fun b hb => hmin' b ((hy.mem b).mpr hb)
  have hreach : ∀ a, A a → ry.low < S.key a + 1 → s0 a = !σ0 := by
    intro a ha hk
    exact hA a ha ⟨m', hmB, by
      have := hne a m' ha hmB
      omega⟩
  have hcx := hx.core
  have hsplit := S.popped_append_rest ry.low rx
  have hpop_mem : ∀ g ∈ S.popped ry.low rx, g ∈ rx.seg := fun g hg => by
    rw [← hsplit]; exact List.mem_append_left _ hg
  have hrest_mem : ∀ g ∈ S.rest ry.low rx, g ∈ rx.seg := fun g hg => by
    rw [← hsplit]; exact List.mem_append_right _ hg
  have hinA : ∀ g ∈ rx.seg, ∀ e ∈ g.els, A e := fun g hg e he => (hx.mem e).mp (mem_els.mpr ⟨g, hg, he⟩)
  have upS : ∀ g ∈ S.popped ry.low rx, ∀ e ∈ S.upC ry.low g, s0 e = !σ0 := by
    intro g hg e he
    obtain ⟨u, hu, hk⟩ := upC_reaches (lt_gtop_of_popped hg)
    have := (side_upC_loC (hcx.cons g (hpop_mem g hg)) hu).1 e he
    rw [this]; exact hreach u (hinA g (hpop_mem g hg) u (upC_sub hu)) hk
  have loS : ∀ g ∈ S.popped ry.low rx, ∀ e ∈ S.loC ry.low g, s0 e = σ0 := by
    intro g hg e he
    obtain ⟨u, hu, hk⟩ := upC_reaches (lt_gtop_of_popped hg)
    have := (side_upC_loC (hcx.cons g (hpop_mem g hg)) hu).2 e he
    rw [this, hreach u (hinA g (hpop_mem g hg) u (upC_sub hu)) hk]; simp
  refine ⟨m', σ0, hlm', hmB, hminB, hB, upS, loS, ?_, ?_, ?_, ?_⟩
  · intro g hg e he
    have heA := hinA g (hpop_mem g hg) e (loC_sub he)
    have h1 := loS g hg e he
    have h2 := hne e m' heA hmB
    rcases Nat.lt_or_ge (S.key e) (S.key m') with hk | hk
    · exact hk
    · exfalso
      have := hreach e heA (by omega)
      rw [h1] at this; cases σ0 <;> simp at this
  · intro g hg e he
    have h1 := gtop_le_of_rest hcx hg
    have h2 := le_gtop (hcx.sortP g (hrest_mem g hg)) (hcx.sortM g (hrest_mem g hg)) he
    have h3 := hne e m' (hinA g (hrest_mem g hg) e he) hmB
    omega
  · intro g hg
    obtain ⟨σ, h1, h2⟩ := hy.core.cons g hg
    by_cases hP : g.P = []
    · exact Or.inl hP
    · right
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro b hb
      obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil _ hP
      have e1 := hB a ((hy.mem a).mp (mem_els.mpr ⟨g, hg, mem_gels.mpr (Or.inl ha)⟩))
      have e2 := hB b ((hy.mem b).mp (mem_els.mpr ⟨g, hg, mem_gels.mpr (Or.inr hb)⟩))
      rw [h1 a ha] at e1; rw [h2 b hb] at e2
      cases σ <;> cases σ0 <;> simp_all
  · intro a ha hk
    obtain ⟨g, hg, hag⟩ := mem_els.mp ((hx.mem a).mpr ha)
    have hgt : ry.low < S.gtop g := by
      have := le_gtop (hcx.sortP g hg) (hcx.sortM g hg) hag; omega
    have hgp : g ∈ S.popped ry.low rx := by
      rw [← hsplit] at hg
      rcases List.mem_append.mp hg with h | h
      · exact h
      · have := gtop_le_of_rest hcx h; omega
    refine ⟨g, hgp, ?_⟩
    rcases mem_upC_loC.mp hag with h | h
    · exact h
    · exfalso
      have h1 := loS g hgp a h
      have h2 := hreach a ha (by omega)
      rw [h1] at h2; cases σ0 <;> simp at h2

/-- **Merging at a fork.** -/
theorem inv_merge {s0 : Nat → Bool} {A B : Nat → Prop} {rx ry : Res} (v : Nat) (hx : S.Inv s0 A rx)
    (hy : S.Inv s0 B ry) (hne : ∀ a b, A a → B b → S.key a ≠ S.key b) (hlt : rx.low < ry.low)
    (hL : S.LRC s0 A B) : S.Inv s0 (fun e => A e ∨ B e) (S.mergeRes v rx ry) := by
  by_cases hy0 : ry.seg = []
  · have hmr : S.mergeRes v rx ry = rx := by unfold mergeRes; rw [ite_eq_left hy0]
    rw [hmr]
    have hB : ∀ b, ¬ B b := fun b hb => by have := (hy.mem b).mpr hb; rw [hy0] at this; simp at this
    exact ⟨hx.core, fun e => by rw [hx.mem e]; simp [hB e], hx.low⟩
  obtain ⟨m', σ0, F⟩ := merge_facts hx hy hne hL hy0
  have hcx := hx.core
  have hcy := hy.core
  have hsplit := S.popped_append_rest ry.low rx
  have hpop_mem : ∀ g ∈ S.popped ry.low rx, g ∈ rx.seg := fun g hg => by
    rw [← hsplit]; exact List.mem_append_left _ hg
  have hinA : ∀ g ∈ rx.seg, ∀ e ∈ g.els, A e := fun g hg e he => (hx.mem e).mp (mem_els.mpr ⟨g, hg, he⟩)
  have hinB : ∀ e ∈ els ry.seg, B e := fun e he => (hy.mem e).mp he
  have hcpop : S.Core s0 (S.popped ry.low rx) := by rw [← hsplit] at hcx; exact hcx.prefix
  have hcrest : S.Core s0 (S.rest ry.low rx) := by rw [← hsplit] at hcx; exact hcx.suffix
  -- the classes of the new group
  have dPp : S.Desc ((S.popped ry.low rx).flatMap (S.upC ry.low)) :=
    desc_flatMap (fun g hg => desc_upC (hcpop.sortP g hg) (hcpop.sortM g hg))
      (hcpop.stack.imp fun h a ha b hb => h a (upC_sub ha) b (upC_sub hb))
  have dLo : S.Desc ((S.popped ry.low rx).flatMap (S.loC ry.low)) :=
    desc_flatMap (fun g hg => desc_loC (hcpop.sortP g hg) (hcpop.sortM g hg))
      (hcpop.stack.imp fun h a ha b hb => h a (loC_sub ha) b (loC_sub hb))
  have dY : S.Desc (els ry.seg) := by
    unfold els
    refine desc_flatMap (fun g hg => ?_) hcy.stack
    unfold Grp.els
    rcases F.oneSide g hg with h | h
    · rw [h]; exact hcy.sortM g hg
    · rw [h, List.append_nil]; exact hcy.sortP g hg
  have dMp : S.Desc (els ry.seg ++ (S.popped ry.low rx).flatMap (S.loC ry.low)) := by
    refine desc_append dY dLo fun a ha b hb => ?_
    obtain ⟨g, hg, hbg⟩ := List.mem_flatMap.mp hb
    have := F.loK g hg b hbg
    have := F.minB a (hinB a ha)
    omega
  have hpopA : ∀ e, (e ∈ (S.popped ry.low rx).flatMap (S.upC ry.low) ∨
      e ∈ (S.popped ry.low rx).flatMap (S.loC ry.low)) ↔ e ∈ els (S.popped ry.low rx) := by
    intro e
    simp only [List.mem_flatMap, mem_els]
    constructor
    · rintro (⟨g, hg, h⟩ | ⟨g, hg, h⟩)
      · exact ⟨g, hg, upC_sub h⟩
      · exact ⟨g, hg, loC_sub h⟩
    · rintro ⟨g, hg, h⟩
      rcases mem_upC_loC.mp h with h | h
      · exact Or.inl ⟨g, hg, h⟩
      · exact Or.inr ⟨g, hg, h⟩
  have hmemN : ∀ e, e ∈ els (S.mergeRes v rx ry).seg ↔ A e ∨ B e := by
    intro e
    rw [els_merge v rx ry hy0, els_cons]
    simp only [Grp.els, List.mem_append]
    rw [← hx.mem e, ← hy.mem e, ← hsplit, els_append, List.mem_append, ← hpopA e]
    constructor
    · rintro ((h | h | h) | h)
      · exact Or.inl (Or.inl (Or.inl h))
      · exact Or.inr h
      · exact Or.inl (Or.inl (Or.inr h))
      · exact Or.inl (Or.inr h)
    · rintro (((h | h) | h) | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr (Or.inr h))
      · exact Or.inr h
      · exact Or.inl (Or.inr (Or.inl h))
  refine ⟨?_, hmemN, ?_⟩
  · rw [els_merge v rx ry hy0]
    refine core_cons hcrest ?_ dPp dMp ⟨!σ0, ?_, ?_⟩ ?_ ?_
    · obtain ⟨g, hg⟩ := List.exists_mem_of_ne_nil _ hy0
      obtain ⟨b, hb⟩ := List.exists_mem_of_ne_nil _ (hcy.ne g hg)
      apply List.ne_nil_of_mem (a := b)
      simp only [Grp.els, List.mem_append]
      exact Or.inr (Or.inl (mem_els.mpr ⟨g, hg, hb⟩))
    · intro e he
      obtain ⟨g, hg, h⟩ := List.mem_flatMap.mp he
      exact F.upS g hg e h
    · intro e he
      rcases List.mem_append.mp he with h | h
      · rw [F.sB e (hinB e h)]; simp
      · obtain ⟨g, hg, h⟩ := List.mem_flatMap.mp h
        rw [F.loS g hg e h]; simp
    · intro e he
      simp only [Grp.els, List.mem_append] at he
      rcases he with h | h | h
      · obtain ⟨g, hg, h⟩ := List.mem_flatMap.mp h
        exact hcx.bound e (mem_els.mpr ⟨g, hpop_mem g hg, upC_sub h⟩)
      · exact hcy.bound e h
      · obtain ⟨g, hg, h⟩ := List.mem_flatMap.mp h
        exact hcx.bound e (mem_els.mpr ⟨g, hpop_mem g hg, loC_sub h⟩)
    · intro h hh a ha b hb
      have hstack := (List.pairwise_append.mp (hsplit ▸ hcx.stack)).2.2
      simp only [Grp.els, List.mem_append] at ha
      rcases ha with ha | ha | ha
      · obtain ⟨g, hg, ha⟩ := List.mem_flatMap.mp ha
        exact hstack g hg h hh a (upC_sub ha) b hb
      · have := F.restK h hh b hb
        have := F.minB a (hinB a ha)
        omega
      · obtain ⟨g, hg, ha⟩ := List.mem_flatMap.mp ha
        exact hstack g hg h hh a (loC_sub ha) b hb
  · right
    rcases hx.low with ⟨h, hl⟩ | ⟨m, hm, hlm, hmin⟩
    · exfalso
      have := hcy.bound m' ((hy.mem m').mpr F.mB)
      have := F.lh
      omega
    · refine ⟨m, (hmemN m).mpr (Or.inl ((hx.mem m).mp hm)), by rw [low_merge]; exact hlm, ?_⟩
      intro e he
      rcases (hmemN e).mp he with h | h
      · exact hmin e ((hx.mem e).mpr h)
      · have := F.minB e h
        have := F.lh
        omega

/-! ### The fork condition from valleys, and back -/

theorem lrc_of_vr {s0 : Nat → Bool} {A B : Nat → Prop} (hm : ∃ m, A m ∧ ∀ b, B b → S.key m < S.key b)
    (hok : (∀ a b, A a → B b → VR s0 S.key a b) ∨ (∀ a b, A a → B b → VR s0 S.key b a)) : S.LRC s0 A B := by
  obtain ⟨m, hmA, hmB⟩ := hm
  rcases hok with h | h
  · refine ⟨true, fun b hb => ?_, fun a ha ⟨b, hb, hk⟩ => ?_⟩
    · have := hmB b hb
      rcases h m b hmA hb with ⟨_, h2⟩ | ⟨_, _, h3⟩ | ⟨_, h2, _⟩
      · exact h2
      · omega
      · exact h2
    · rcases h a b ha hb with ⟨h1, _⟩ | ⟨h1, _, _⟩ | ⟨_, _, h3⟩
      · simpa using h1
      · simpa using h1
      · omega
  · refine ⟨false, fun b hb => ?_, fun a ha ⟨b, hb, hk⟩ => ?_⟩
    · have := hmB b hb
      rcases h m b hmA hb with ⟨h1, _⟩ | ⟨h1, _, _⟩ | ⟨_, _, h3⟩
      · exact h1
      · exact h1
      · omega
    · rcases h a b ha hb with ⟨_, h2⟩ | ⟨_, _, h3⟩ | ⟨_, h2, _⟩
      · simpa using h2
      · omega
      · simpa using h2

theorem vr_of_lrc {s : Nat → Bool} {A B : Nat → Prop} {σ : Bool} (hne : ∀ a b, A a → B b → S.key a ≠ S.key b)
    (hB : ∀ b, B b → s b = σ) (hA : ∀ a, A a → (∃ b, B b ∧ S.key b < S.key a) → s a = !σ) :
    (σ = true → ∀ a b, A a → B b → VR s S.key a b) ∧ (σ = false → ∀ a b, A a → B b → VR s S.key b a) := by
  refine ⟨fun hσ a b ha hb => ?_, fun hσ a b ha hb => ?_⟩
  · subst hσ
    have hsb := hB b hb
    cases hsa : s a
    · exact Or.inl ⟨hsa, hsb⟩
    · right; right
      refine ⟨hsa, hsb, ?_⟩
      rcases Nat.lt_or_ge (S.key a) (S.key b) with h | h
      · exact h
      · have := hne a b ha hb
        have := hA a ha ⟨b, hb, by omega⟩
        rw [hsa] at this; simp at this
  · subst hσ
    have hsb := hB b hb
    cases hsa : s a
    · right; left
      refine ⟨hsb, hsa, ?_⟩
      rcases Nat.lt_or_ge (S.key a) (S.key b) with h | h
      · exact h
      · have := hne a b ha hb
        have := hA a ha ⟨b, hb, by omega⟩
        rw [hsa] at this; simp at this
    · exact Or.inl ⟨hsb, hsa⟩

theorem Inv.congr {s0 : Nat → Bool} {A B : Nat → Prop} {r : Res} (h : S.Inv s0 A r) (hAB : ∀ e, A e ↔ B e) :
    S.Inv s0 B r := ⟨h.core, fun e => (h.mem e).trans (hAB e), h.low⟩

theorem Inv.low_le {s0 : Nat → Bool} {A : Nat → Prop} {r : Res} (h : S.Inv s0 A r) : r.low ≤ S.INF := by
  rcases h.low with ⟨_, h1⟩ | ⟨m, hm, h1, _⟩
  · omega
  · have := h.core.bound m hm; omega

theorem Inv.low_lt {s0 : Nat → Bool} {A : Nat → Prop} {r : Res} (h : S.Inv s0 A r) (hr : r.seg ≠ []) :
    ∃ m, A m ∧ r.low = S.key m + 1 ∧ (∀ e, A e → S.key m ≤ S.key e) ∧ S.key m + 1 < S.INF := by
  rcases h.low with ⟨h1, _⟩ | ⟨m, hm, h1, h2⟩
  · exact absurd h1 hr
  · exact ⟨m, (h.mem m).mp hm, h1, fun e he => h2 e ((h.mem e).mpr he), h.core.bound m hm⟩

theorem Inv.empty_of {s0 : Nat → Bool} {A : Nat → Prop} {r : Res} (h : S.Inv s0 A r) (hr : r.seg = []) :
    ∀ e, ¬ A e := fun e he => by have := (h.mem e).mpr he; rw [hr] at this; simp at this

theorem Inv.low_eq {s0 : Nat → Bool} {A : Nat → Prop} {r : Res} (h : S.Inv s0 A r) (hr : r.seg = []) :
    r.low = S.INF := by
  rcases h.low with ⟨_, h1⟩ | ⟨m, hm, _, _⟩
  · exact h1
  · rw [hr] at hm; simp at hm

/-- **A fork**: parts with open ends `A` and `B` whose ends can be put in a valley. -/
theorem inv_fork {s0 : Nat → Bool} {A B : Nat → Prop} {rp rq : Res} (v : Nat) (hp : S.Inv s0 A rp)
    (hq : S.Inv s0 B rq) (hne : ∀ a b, A a → B b → S.key a ≠ S.key b)
    (hok : (∀ a b, A a → B b → VR s0 S.key a b) ∨ (∀ a b, A a → B b → VR s0 S.key b a)) :
    S.Inv s0 (fun e => A e ∨ B e) (S.forkRes v rp rq) := by
  unfold forkRes
  split
  · rename_i hlt
    refine inv_merge v hp hq hne hlt (lrc_of_vr ?_ hok)
    have hpe : rp.seg ≠ [] := by
      intro h; have := hp.low_eq h; have := hq.low_le; omega
    obtain ⟨m, hmA, hlm, -, -⟩ := hp.low_lt hpe
    refine ⟨m, hmA, fun b hb => ?_⟩
    have hqe : rq.seg ≠ [] := fun h => hq.empty_of h b hb
    obtain ⟨m', hmB, hlm', hmin', -⟩ := hq.low_lt hqe
    have := hmin' b hb
    omega
  · rename_i hge
    by_cases hlt : rq.low < rp.low
    · have hne' : ∀ b a, B b → A a → S.key b ≠ S.key a := fun b a hb ha e => hne a b ha hb e.symm
      have hok' : (∀ b a, B b → A a → VR s0 S.key b a) ∨ (∀ b a, B b → A a → VR s0 S.key a b) := by
        rcases hok with h | h
        · exact Or.inr fun b a hb ha => h a b ha hb
        · exact Or.inl fun b a hb ha => h a b ha hb
      refine (inv_merge v hq hp hne' hlt (lrc_of_vr ?_ hok')).congr (fun e => Or.comm)
      have hqe : rq.seg ≠ [] := by
        intro h; have := hq.low_eq h; have := hp.low_le; omega
      obtain ⟨m, hmB, hlm, -, -⟩ := hq.low_lt hqe
      refine ⟨m, hmB, fun a ha => ?_⟩
      have hpe : rp.seg ≠ [] := fun h => hp.empty_of h a ha
      obtain ⟨m', hmA, hlm', hmin', -⟩ := hp.low_lt hpe
      have := hmin' a ha
      omega
    · -- equal lows: both parts are closed
      have heq : rp.low = rq.low := by omega
      have hpe : rp.seg = [] := by
        apply Classical.byContradiction; intro hpe
        obtain ⟨m, hmA, hlm, -, hb⟩ := hp.low_lt hpe
        by_cases hqe : rq.seg = []
        · have := hq.low_eq hqe; omega
        · obtain ⟨m', hmB, hlm', -, -⟩ := hq.low_lt hqe
          exact hne m m' hmA hmB (by omega)
      have hmr : S.mergeRes v rq rp = rq := by unfold mergeRes; rw [ite_eq_left hpe]
      rw [hmr]
      exact hq.congr fun e => ⟨Or.inr, fun h => h.elim (fun h => absurd h (hp.empty_of hpe e)) id⟩

/-! ### Orientations -/

/-- The ends of every group lie on the sides of its orientation. -/
def OInv (o : Nat → Bool) (seg : List Grp) : Prop :=
  ∀ g ∈ seg, (∀ e ∈ g.P, o e = o g.id) ∧ (∀ e ∈ g.M, o e = !o g.id)

theorem oinv_nil (o : Nat → Bool) : OInv o [] := by simp [OInv]

theorem oinv_dart (o : Nat → Bool) (e : Nat) : OInv o (S.dartRes e).seg := by
  simp [OInv, dartRes]

theorem oinv_close {o : Nat → Bool} {r : Res} (h : OInv o r.seg) (x : Nat) : OInv o (S.closeRes x r).seg := by
  cases hr : r.seg with
  | nil => unfold closeRes; rw [hr]; exact oinv_nil o
  | cons g rest =>
    rw [hr] at h
    rw [closeRes_cons hr]
    have hg := h g (List.mem_cons_self ..)
    have hrest : OInv o rest := fun g' hg' => h g' (List.mem_cons_of_mem _ hg')
    have hg' : ∀ g', (if g.P.head? = some x then (⟨g.id, g.P.tail, g.M⟩ : Grp) else ⟨g.id, g.P, g.M.tail⟩) = g' →
        (∀ e ∈ g'.P, o e = o g'.id) ∧ (∀ e ∈ g'.M, o e = !o g'.id) := by
      intro g' e
      subst e
      split
      · exact ⟨fun e he => hg.1 e (List.mem_of_mem_tail he), hg.2⟩
      · exact ⟨hg.1, fun e he => hg.2 e (List.mem_of_mem_tail he)⟩
    generalize hG : (if g.P.head? = some x then (⟨g.id, g.P.tail, g.M⟩ : Grp) else ⟨g.id, g.P, g.M.tail⟩) = G
    have := hg' G hG
    split
    · exact hrest
    · intro g' hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact this
      · exact hrest g' hm

/-- **Orientations at a merge.** A consistent orientation puts the merged ends of `ry` on the side
opposite to the new group and the ends of `rx` reaching above them on its side. -/
theorem oinv_merge {s0 o : Nat → Bool} {A B : Nat → Prop} {rx ry : Res} (v : Nat) (hx : S.Inv s0 A rx)
    (hy : S.Inv s0 B ry) (hne : ∀ a b, A a → B b → S.key a ≠ S.key b) (hL : S.LRC s0 A B)
    (hox : OInv o rx.seg) (hoy : OInv o ry.seg) (hc : ∀ x ∈ S.mergeCons rx ry, o x.1 = (o (S.gid v) ^^ x.2)) :
    OInv o (S.mergeRes v rx ry).seg ∧
      (ry.seg ≠ [] → (∀ b, B b → o b = !o (S.gid v)) ∧
        (∀ a, A a → (∃ b, B b ∧ S.key b < S.key a) → o a = o (S.gid v))) := by
  by_cases hy0 : ry.seg = []
  · have hmr : S.mergeRes v rx ry = rx := by unfold mergeRes; rw [ite_eq_left hy0]
    rw [hmr]; exact ⟨hox, fun h => absurd hy0 h⟩
  obtain ⟨m', σ0, F⟩ := merge_facts hx hy hne hL hy0
  have hcons : S.mergeCons rx ry = ry.seg.map (fun g => (g.id, decide (g.P ≠ []))) ++
      (S.popped ry.low rx).map (fun g => (g.id, !decide (ry.low < S.kh g.P))) := by
    unfold mergeCons; rw [ite_eq_right hy0]
  have hsplit := S.popped_append_rest ry.low rx
  have hpop_mem : ∀ g ∈ S.popped ry.low rx, g ∈ rx.seg := fun g hg => by
    rw [← hsplit]; exact List.mem_append_left _ hg
  have hrest_mem : ∀ g ∈ S.rest ry.low rx, g ∈ rx.seg := fun g hg => by
    rw [← hsplit]; exact List.mem_append_right _ hg
  -- groups of `ry`
  have hY : ∀ g ∈ ry.seg, ∀ e ∈ g.els, o e = !o (S.gid v) := by
    intro g hg e he
    have hcg := hc (g.id, decide (g.P ≠ [])) (by rw [hcons]; exact List.mem_append_left _ (List.mem_map_of_mem hg))
    simp only at hcg
    rcases mem_gels.mp he with h | h
    · have hP : g.P ≠ [] := List.ne_nil_of_mem h
      rw [(hoy g hg).1 e h, hcg]; simp [hP]
    · have hP : g.P = [] := by
        rcases F.oneSide g hg with h' | h'
        · exact h'
        · rw [h'] at h; simp at h
      rw [(hoy g hg).2 e h, hcg]; simp [hP]
  -- popped groups of `rx`
  have hX : ∀ g ∈ S.popped ry.low rx, (∀ e ∈ S.upC ry.low g, o e = o (S.gid v)) ∧
      (∀ e ∈ S.loC ry.low g, o e = !o (S.gid v)) := by
    intro g hg
    have hcg := hc (g.id, !decide (ry.low < S.kh g.P))
      (by rw [hcons]; exact List.mem_append_right _ (List.mem_map_of_mem hg))
    simp only at hcg
    have hog := hox g (hpop_mem g hg)
    unfold upC loC
    by_cases hk : ry.low < S.kh g.P
    · rw [ite_eq_left hk, ite_eq_left hk]
      simp only [hk, decide_true, Bool.not_true, Bool.xor_false] at hcg
      exact ⟨fun e he => by rw [hog.1 e he, hcg], fun e he => by rw [hog.2 e he, hcg]⟩
    · rw [ite_eq_right hk, ite_eq_right hk]
      simp only [hk, decide_false, Bool.not_false, Bool.xor_true] at hcg
      exact ⟨fun e he => by rw [hog.2 e he, hcg]; simp, fun e he => by rw [hog.1 e he, hcg]⟩
  have hBo : ∀ b, B b → o b = !o (S.gid v) := by
    intro b hb
    obtain ⟨g, hg, h⟩ := mem_els.mp ((hy.mem b).mpr hb)
    exact hY g hg b h
  refine ⟨?_, fun _ => ⟨hBo, fun a ha ⟨b, hb, hk⟩ => ?_⟩⟩
  · rw [els_merge v rx ry hy0]
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hg
    · refine ⟨fun e he => ?_, fun e he => ?_⟩
      · obtain ⟨g, hg, h⟩ := List.mem_flatMap.mp he
        exact (hX g hg).1 e h
      · rcases List.mem_append.mp he with h | h
        · obtain ⟨g, hg, h⟩ := mem_els.mp h
          exact hY g hg e h
        · obtain ⟨g, hg, h⟩ := List.mem_flatMap.mp h
          exact (hX g hg).2 e h
    · exact hox g (hrest_mem g hg)
  · have := F.minB b hb
    obtain ⟨g, hg, h⟩ := F.upAll a ha (by omega)
    exact (hX g hg).1 a h

end Sol

end STACS2027.Embed

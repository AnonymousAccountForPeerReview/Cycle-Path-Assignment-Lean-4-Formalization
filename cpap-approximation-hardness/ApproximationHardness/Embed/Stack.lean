module

public import ApproximationHardness.Embed.Linked
import Lean.Elab.Tactic.Omega

/-!
# Linked stacks of solver groups

Class successor pointers and group successor pointers are distinct arrays.
The last group of a stack points to zero. Group identifiers in a stack are
distinct, so modifying the head of the top group preserves the lower groups.
-/

@[expose] public section

namespace STACS2027.Embed

namespace Sol

/-- The live groups of a stack, represented by the group-successor array. -/
inductive StackRep (m : SMem) : Nat → List Grp → Prop where
  | nil : StackRep m 0 []
  | cons (g : Grp) (rest : List Grp) (hg : GroupRep m g)
      (tail : StackRep m (m.gn g.id) rest)
      (fresh : ∀ g' ∈ rest, g'.id ≠ g.id) : StackRep m (g.id + 1) (g :: rest)

theorem StackRep.cons_iff {m : SMem} {h : Nat} {g : Grp} {rest : List Grp} :
    StackRep m h (g :: rest) ↔ h = g.id + 1 ∧ GroupRep m g ∧
      StackRep m (m.gn g.id) rest ∧ (∀ g' ∈ rest, g'.id ≠ g.id) := by
  constructor
  · intro H
    cases H with
    | cons _ _ Hg Hr Hf => exact ⟨rfl, Hg, Hr, Hf⟩
  · rintro ⟨rfl, Hg, Hr, Hf⟩
    exact StackRep.cons g rest Hg Hr Hf

theorem StackRep.head_zero_iff {m : SMem} {h : Nat} {seg : List Grp}
    (H : StackRep m h seg) : h = 0 ↔ seg = [] := by
  cases H <;> simp

theorem StackRep.group {m : SMem} {h : Nat} {seg : List Grp}
    (H : StackRep m h seg) : ∀ g ∈ seg, GroupRep m g := by
  induction H with
  | nil => simp
  | cons g rest Hg Htail fresh ih =>
    intro g' hg'
    rcases List.mem_cons.mp hg' with rfl | hg'
    · exact Hg
    · exact ih g' hg'

/-- An unrelated array change preserves a represented stack. -/
theorem StackRep.frame {m n : SMem} {h : Nat} {seg : List Grp}
    (H : StackRep m h seg) (hg : ∀ g ∈ seg, GroupRep n g)
    (hn : ∀ g ∈ seg, n.gn g.id = m.gn g.id) : StackRep n h seg := by
  induction H with
  | nil => exact StackRep.nil
  | cons g rest H Htail fresh ih =>
    refine StackRep.cons g rest (hg g (List.mem_cons_self ..)) ?_ fresh
    rw [hn g (List.mem_cons_self ..)]
    exact ih (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg'))
      (fun g' hg' => hn g' (List.mem_cons_of_mem _ hg'))

/-- Pointwise changes outside the live classes and group cells preserve a stack. -/
theorem StackRep.array_frame {m n : SMem} {h : Nat} {seg : List Grp}
    (H : StackRep m h seg)
    (hx : ∀ e ∈ els seg, n.nx e = m.nx e)
    (hp : ∀ g ∈ seg, n.ph g.id = m.ph g.id)
    (ht : ∀ g ∈ seg, n.pt g.id = m.pt g.id)
    (hm : ∀ g ∈ seg, n.mh g.id = m.mh g.id)
    (hu : ∀ g ∈ seg, n.mt g.id = m.mt g.id)
    (hn : ∀ g ∈ seg, n.gn g.id = m.gn g.id) : StackRep n h seg := by
  apply H.frame _ hn
  intro g hg
  have Hg := H.group g hg
  constructor
  · rw [hp g hg, ht g hg]
    exact Hg.positive.frame fun e he => hx e (List.mem_flatMap.mpr
      ⟨g, hg, List.mem_append_left _ he⟩)
  · rw [hm g hg, hu g hg]
    exact Hg.negative.frame fun e he => hx e (List.mem_flatMap.mpr
      ⟨g, hg, List.mem_append_right _ he⟩)

/-- Changing another group's positive head preserves both classes of a group. -/
theorem GroupRep.other_positive {m : SMem} {g : Grp} (H : GroupRep m g)
    {a v : Nat} (hne : g.id ≠ a) : GroupRep {m with ph := upd m.ph a v} g := by
  constructor
  · simpa [upd_ne _ _ hne] using H.positive
  · exact H.negative

/-- Changing another group's negative head preserves both classes of a group. -/
theorem GroupRep.other_negative {m : SMem} {g : Grp} (H : GroupRep m g)
    {a v : Nat} (hne : g.id ≠ a) : GroupRep {m with mh := upd m.mh a v} g := by
  constructor
  · exact H.positive
  · simpa [upd_ne _ _ hne] using H.negative

/-- Removing the head of a positive class changes only its head pointer. -/
theorem GroupRep.pop_positive {m : SMem} {g : Grp} (H : GroupRep m g)
    {e : Nat} {p : List Nat} (hp : g.P = e :: p) :
    GroupRep
      {m with ph := upd m.ph g.id (if m.ph g.id = m.pt g.id then 0 else m.nx e)}
      {g with P := p} := by
  constructor
  · have Hpos := H.positive
    rw [hp] at Hpos
    simpa using Hpos.pop
  · exact H.negative

/-- Removing the head of a negative class changes only its head pointer. -/
theorem GroupRep.pop_negative {m : SMem} {g : Grp} (H : GroupRep m g)
    {e : Nat} {p : List Nat} (hp : g.M = e :: p) :
    GroupRep
      {m with mh := upd m.mh g.id (if m.mh g.id = m.mt g.id then 0 else m.nx e)}
      {g with M := p} := by
  constructor
  · exact H.positive
  · have Hneg := H.negative
    rw [hp] at Hneg
    simpa using Hneg.pop

variable (S : Sol)

/-- Opening a dart initializes a singleton linked stack with the exact abstract result. -/
theorem itRes_dart (m : SMem) (e : Nat) :
    StackRep (S.itRes m (.dart e)).1 (S.itRes m (.dart e)).2.1 (S.dartRes e).seg ∧
      (S.itRes m (.dart e)).2.2 = (S.dartRes e).low := by
  constructor
  · dsimp only [itRes, dartRes]
    refine StackRep.cons ⟨e, [e], []⟩ [] ?_ ?_ ?_
    · constructor
      · simpa [itRes, dartRes] using Linked.singleton m.nx e
      · simpa [itRes, dartRes] using Linked.nil m.nx (m.mt e)
    · simpa [itRes, dartRes] using
        (StackRep.nil : StackRep
          {m with
            ph := upd m.ph e (e + 1)
            pt := upd m.pt e (e + 1)
            mh := upd m.mh e 0
            gn := upd m.gn e 0} 0 [])
    · simp
  · rfl

/-- The array close operation produces the represented positive-head removal. -/
theorem closeM_positive {m : SMem} {g : Grp} {e l : Nat} (H : GroupRep m g)
    (he : g.P.head? = some e) :
    GroupRep (S.closeM m e (g.id + 1) l).1 {g with P := g.P.tail} := by
  obtain ⟨p, hp⟩ : ∃ p, g.P = e :: p := by
    cases hp : g.P with
    | nil => simp [hp] at he
    | cons a p =>
      have ha : a = e := by simpa [hp] using he
      exact ⟨p, by rw [ha]⟩
  have hph : m.ph g.id = e + 1 := H.positive.head_some_iff.mpr he
  have hn := H.pop_positive hp
  simpa [closeM, hph, hp] using hn

/-- The array close operation produces the represented negative-head removal. -/
theorem closeM_negative {m : SMem} {g : Grp} {e l : Nat} (H : GroupRep m g)
    (hP : g.P.head? ≠ some e) (he : g.M.head? = some e) :
    GroupRep (S.closeM m e (g.id + 1) l).1 {g with M := g.M.tail} := by
  obtain ⟨p, hp⟩ : ∃ p, g.M = e :: p := by
    cases hp : g.M with
    | nil => simp [hp] at he
    | cons a p =>
      have ha : a = e := by simpa [hp] using he
      exact ⟨p, by rw [ha]⟩
  have hph : m.ph g.id ≠ e + 1 := fun h => hP (H.positive.head_some_iff.mp h)
  have hn := H.pop_negative hp
  simpa [closeM, hph, hp] using hn

theorem closeM_group_next (m : SMem) (e h l : Nat) :
    (S.closeM m e h l).1.gn = m.gn := by
  simp only [closeM]
  split
  · rfl
  · split <;> rfl

/-- The full close operation matches the abstract stack, including removal of an empty
top group and maintenance of the abstract least key. -/
theorem closeM_stack {m : SMem} {h e : Nat} {r : Res}
    (H : StackRep m h r.seg)
    (hhead : ∀ g rest, r.seg = g :: rest → g.P.head? = some e ∨ g.M.head? = some e) :
    StackRep (S.closeM m e h r.low).1 (S.closeM m e h r.low).2.1
      (S.closeRes e r).seg ∧ (S.closeM m e h r.low).2.2 = (S.closeRes e r).low := by
  cases r with
  | mk seg l =>
    cases H with
    | nil => simp [closeM, closeRes, empty, StackRep.nil]
    | cons g rest Hg Htail fresh =>
      let n := (S.closeM m e (g.id + 1) l).1
      let g' : Grp := if g.P.head? = some e then {g with P := g.P.tail} else {g with M := g.M.tail}
      have hid : g'.id = g.id := by dsimp [g']; split <;> rfl
      have Hnew : GroupRep n g' := by
        by_cases hp : g.P.head? = some e
        · simpa [n, g', hp] using S.closeM_positive Hg hp
        · have hm := (hhead g rest rfl).resolve_left hp
          simpa [n, g', hp] using S.closeM_negative Hg hp hm
      have Hlower : StackRep n (n.gn g.id) rest := by
        rw [S.closeM_group_next]
        apply Htail.frame
        · intro q hq
          have Hq := Htail.group q hq
          dsimp [n, closeM]
          split
          · exact Hq.other_positive (fresh q hq)
          · exact Hq.other_negative (fresh q hq)
        · intro q _
          exact congrFun (S.closeM_group_next m e (g.id + 1) l) q.id
      have hpz := Hnew.positive.head_zero_iff
      have hmz := Hnew.negative.head_zero_iff
      have hout : (S.closeM m e (g.id + 1) l).2.1 =
          if n.ph g.id = 0 ∧ n.mh g.id = 0 then n.gn g.id else g.id + 1 := by
        simp [n, closeM]
      have hlow : (S.closeM m e (g.id + 1) l).2.2 =
          if l = S.key e + 1 then S.INF else l := by simp [closeM]
      change StackRep n _ (if g'.P = [] ∧ g'.M = [] then rest else g' :: rest) ∧ _
      constructor
      · rw [hout]
        rw [hid] at hpz hmz
        by_cases he : g'.P = [] ∧ g'.M = []
        · rw [ite_eq_left he, ite_eq_left ⟨hpz.mpr he.1, hmz.mpr he.2⟩]
          exact Hlower
        · have hne : ¬ (n.ph g.id = 0 ∧ n.mh g.id = 0) :=
            fun h => he ⟨hpz.mp h.1, hmz.mp h.2⟩
          rw [ite_eq_right he, ite_eq_right hne, ← hid]
          exact StackRep.cons g' rest Hnew (by simpa [hid] using Hlower)
            (fun q hq => by simpa [hid] using fresh q hq)
      · simpa [closeRes] using hlow

end Sol

end STACS2027.Embed

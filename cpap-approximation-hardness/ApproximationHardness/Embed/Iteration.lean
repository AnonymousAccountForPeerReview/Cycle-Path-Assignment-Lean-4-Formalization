module

public import ApproximationHardness.Embed.Fork
public import Mathlib.Data.List.Perm.Basic
import Lean.Elab.Tactic.Omega

/-!
# Iterating the linked fork machine

The iteration proofs use lists only as ghost descriptions of the groups consumed
by the array machine. Each list entry corresponds to one actual machine step.
-/

@[expose] public section

namespace STACS2027.Embed.Sol

variable (S : Sol)

theorem up_lo_perm (lh : Nat) (g : Grp) :
    (S.upC lh g ++ S.loC lh g).Perm g.els := by
  by_cases h : lh < S.kh g.P
  · simp [upC, loC, h, Grp.els]
  · simpa [upC, loC, h, Grp.els] using
      (List.perm_append_comm : (g.M ++ g.P).Perm (g.P ++ g.M))

/-- Splitting a consumed group between the accumulators preserves the set of live ends. -/
theorem pop_ends_perm (lh : Nat) (A B R : List Nat) (g : Grp) :
    (((A ++ S.upC lh g) ++ (B ++ S.loC lh g)) ++ R).Perm
      ((A ++ B) ++ (g.els ++ R)) := by
  have H := (List.perm_append_comm_assoc (S.upC lh g) B (S.loC lh g ++ R)).append_left A
  have J := ((S.up_lo_perm lh g).append_right R).append_left (A ++ B)
  have H' : (((A ++ S.upC lh g) ++ (B ++ S.loC lh g)) ++ R).Perm
      ((A ++ B) ++ ((S.upC lh g ++ S.loC lh g) ++ R)) := by
    simpa only [List.append_assoc] using H
  exact H'.trans J

/-- A pop writes successor cells only in the two existing accumulated classes. -/
theorem popStep_cell_frame {s : SMS} {g : Grp} {A B : List Nat} {e : Nat}
    (hr : s.rxp = g.id + 1) (hpop : s.lh < S.gtop g) (Hg : GroupRep s.m g)
    (HA : Linked s.m.nx s.ah s.at' A) (HB : Linked s.m.nx s.bh s.bt B)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a ≠ b) (heA : e ∉ A) (heB : e ∉ B) :
    (S.popStep s).m.nx e = s.m.nx e := by
  have htop := S.gtopM_group Hg
  have hkey := S.khM_linked Hg.positive
  by_cases hup : s.lh < S.kh g.P
  · have HB' := Linked.append_frame (h₂ := s.m.ph g.id) (t₂ := s.m.pt g.id) HA HB hAB
    have H := Linked.append_cell_frame (h₂ := s.m.mh g.id) (t₂ := s.m.mt g.id) HB' heB
    rw [Linked.append_cell_frame HA heA] at H
    simpa [popStep, hr, htop, hpop, hkey, hup] using H
  · have HB' := Linked.append_frame (h₂ := s.m.mh g.id) (t₂ := s.m.mt g.id) HA HB hAB
    have H := Linked.append_cell_frame (h₂ := s.m.ph g.id) (t₂ := s.m.pt g.id) HB' heB
    rw [Linked.append_cell_frame HA heA] at H
    simpa [popStep, hr, htop, hpop, hkey, hup] using H

/-- Any disjoint stack remains represented while a group is popped. -/
theorem popStep_stack_frame {s : SMS} {g : Grp} {A B : List Nat}
    {h : Nat} {seg : List Grp}
    (hr : s.rxp = g.id + 1) (hpop : s.lh < S.gtop g) (Hg : GroupRep s.m g)
    (HA : Linked s.m.nx s.ah s.at' A) (HB : Linked s.m.nx s.bh s.bt B)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a ≠ b) (Hseg : StackRep s.m h seg)
    (hA : ∀ a ∈ A, ∀ e ∈ els seg, a ≠ e)
    (hB : ∀ b ∈ B, ∀ e ∈ els seg, b ≠ e) :
    StackRep (S.popStep s).m h seg := by
  apply Hseg.array_frame
  · intro e he
    exact S.popStep_cell_frame hr hpop Hg HA HB hAB
      (fun ha => hA e ha e he rfl) (fun hb => hB e hb e he rfl)
  all_goals intro q _; simp only [popStep]; split <;> rfl

/-- Run exactly one pop step for each listed group. The list is ghost data. -/
def popGroups (S : Sol) : List Grp → SMS → SMS
  | [], s => s
  | _ :: todo, s => popGroups S todo (S.popStep s)

theorem popGroups_iterate (todo : List Grp) (s : SMS) :
    S.popGroups todo s = (S.popStep)^[todo.length] s := by
  induction todo generalizing s with
  | nil => rfl
  | cons g todo ih =>
    simpa only [popGroups, List.length_cons, Function.iterate_succ_apply] using ih (S.popStep s)

/-- Reaching a top group below the lower-stack threshold switches to lower consumption. -/
theorem popStep_stop {s : SMS} {rest : List Grp} (H : StackRep s.m s.rxp rest)
    (hstop : ∀ g ∈ rest, S.gtop g ≤ s.lh) : S.popStep s = {s with mode := 2} := by
  cases rest with
  | nil =>
    have hz := H.head_zero_iff.mpr rfl
    simp [popStep, hz]
  | cons g rest =>
    obtain ⟨hr, Hg, _, _⟩ := StackRep.cons_iff.mp H
    have htop := S.gtopM_group Hg
    have hle := hstop g (List.mem_cons_self ..)
    have hn : ¬ s.lh < S.gtop g := by omega
    simp [popStep, hr, htop, hn]

/-- Every consumed upper group advances the represented stack once. -/
theorem popGroups_refines {todo rest : List Grp} {s : SMS} {A B : List Nat}
    (Hrx : StackRep s.m s.rxp (todo ++ rest))
    (HA : Linked s.m.nx s.ah s.at' A) (HB : Linked s.m.nx s.bh s.bt B)
    (hnd : ((A ++ B) ++ els (todo ++ rest)).Nodup)
    (hpop : ∀ g ∈ todo, s.lh < S.gtop g) :
    let t := S.popGroups todo s
    StackRep t.m t.rxp rest ∧
    Linked t.m.nx t.ah t.at' (A ++ todo.flatMap (S.upC s.lh)) ∧
    Linked t.m.nx t.bh t.bt (B ++ todo.flatMap (S.loC s.lh)) ∧
    t.cons = s.cons ++ todo.map Grp.id ∧ t.lh = s.lh ∧ t.G = s.G ∧
    (((A ++ todo.flatMap (S.upC s.lh)) ++
      (B ++ todo.flatMap (S.loC s.lh))) ++ els rest).Nodup ∧ t.mode = s.mode ∧
      ∀ post, s.mode = 1 → t = (S.mstep post)^[todo.length] s := by
  induction todo generalizing s A B with
  | nil =>
    simp only [popGroups, List.nil_append, List.flatMap_nil, List.append_nil,
      List.map_nil] at *
    exact ⟨Hrx, HA, HB, trivial, trivial, trivial, hnd, trivial, by intros; rfl⟩
  | cons g todo ih =>
    obtain ⟨Hr, Hg, Htail, _⟩ := StackRep.cons_iff.mp Hrx
    have Hnd : ((A ++ B) ++ (g.els ++ els (todo ++ rest))).Nodup := by
      simpa [els] using hnd
    have hab := (List.nodup_append.mp (List.nodup_append.mp Hnd).1).2.2
    have hacc := (List.nodup_append.mp Hnd).2.2
    have hgpop := hpop g (by simp)
    have Hstep := S.popStep_classes Hr hgpop Hg HA HB
      (List.nodup_append.mpr ⟨(List.nodup_append.mp Hnd).1,
        (List.nodup_append.mp (List.nodup_append.mp Hnd).2.1).1,
        fun a ha e he => hacc a ha e (List.mem_append_left _ he)⟩)
    have Htail' := S.popStep_stack_frame Hr hgpop Hg HA HB hab Htail
      (fun a ha e he => hacc a (List.mem_append_left _ ha) e (List.mem_append_right _ he))
      (fun b hb e he => hacc b (List.mem_append_right _ hb) e (List.mem_append_right _ he))
    rw [← Hstep.2.2.1] at Htail'
    have Hnd' := (S.pop_ends_perm s.lh A B (els (todo ++ rest)) g).symm.nodup Hnd
    have hlh : (S.popStep s).lh = s.lh := by simp only [popStep]; split <;> rfl
    have hG : (S.popStep s).G = s.G := by simp only [popStep]; split <;> rfl
    have hmode : (S.popStep s).mode = s.mode := by
      simp [popStep, Hr, S.gtopM_group Hg, hgpop]
    obtain ⟨Hr', HA', HB', Hcons, Hlh, HG, Hnd'', Hmode, Hiterate⟩ :=
      ih Htail' Hstep.1 Hstep.2.1 Hnd' (by
        intro q hq
        rw [hlh]
        exact hpop q (List.mem_cons_of_mem _ hq))
    refine ⟨Hr', ?_, ?_, ?_, ?_, ?_, ?_, Hmode.trans hmode, ?_⟩
    · simpa [popGroups, hlh, List.flatMap_cons, List.append_assoc] using HA'
    · simpa [popGroups, hlh, List.flatMap_cons, List.append_assoc] using HB'
    · simpa [popGroups, Hstep.2.2.2.1, List.append_assoc] using Hcons
    · exact Hlh.trans hlh
    · exact HG.trans hG
    · simpa [popGroups, hlh, List.flatMap_cons, List.append_assoc] using Hnd''
    · intro post hm
      have hm' : (S.popStep s).mode = 1 := hmode.trans hm
      have HstepMachine : S.mstep post s = S.popStep s := by simp [mstep, hm]
      simpa [popGroups, Function.iterate_succ_apply, HstepMachine] using Hiterate post hm'

theorem popGroups_arrays (todo : List Grp) (s : SMS) :
    (S.popGroups todo s).m.ph = s.m.ph ∧ (S.popGroups todo s).m.pt = s.m.pt ∧
    (S.popGroups todo s).m.mh = s.m.mh ∧ (S.popGroups todo s).m.mt = s.m.mt ∧
    (S.popGroups todo s).m.gn = s.m.gn ∧ (S.popGroups todo s).ryp = s.ryp ∧
    (S.popGroups todo s).ch = s.ch ∧ (S.popGroups todo s).ct = s.ct ∧
    (S.popGroups todo s).G = s.G ∧ (S.popGroups todo s).v = s.v ∧
    (S.popGroups todo s).lh = s.lh ∧ (S.popGroups todo s).lx = s.lx ∧
    (S.popGroups todo s).k = s.k ∧ (S.popGroups todo s).m.rs = s.m.rs ∧
    (S.popGroups todo s).m.rl = s.m.rl := by
  induction todo generalizing s with
  | nil => simp [popGroups]
  | cons g todo ih =>
    simp only [popGroups]
    have H := ih (S.popStep s)
    by_cases h : s.rxp ≠ 0 ∧ s.lh < S.gtopM s.m (s.rxp - 1)
    · simpa [popStep, h] using H
    · simpa [popStep, h] using H

/-- All successor writes in an upper loop lie among previously accumulated or consumed ends. -/
theorem popGroups_cell_frame {todo rest : List Grp} {s : SMS} {A B : List Nat} {e : Nat}
    (Hrx : StackRep s.m s.rxp (todo ++ rest))
    (HA : Linked s.m.nx s.ah s.at' A) (HB : Linked s.m.nx s.bh s.bt B)
    (hnd : ((A ++ B) ++ els (todo ++ rest)).Nodup)
    (hpop : ∀ g ∈ todo, s.lh < S.gtop g)
    (he : e ∉ (A ++ B) ++ els todo) : (S.popGroups todo s).m.nx e = s.m.nx e := by
  induction todo generalizing s A B with
  | nil => rfl
  | cons g todo ih =>
    obtain ⟨Hr, Hg, Htail, _⟩ := StackRep.cons_iff.mp Hrx
    have Hnd : ((A ++ B) ++ (g.els ++ els (todo ++ rest))).Nodup := by
      simpa [els] using hnd
    have hab := (List.nodup_append.mp (List.nodup_append.mp Hnd).1).2.2
    have hacc := (List.nodup_append.mp Hnd).2.2
    have hgpop := hpop g (by simp)
    have Hstep := S.popStep_classes Hr hgpop Hg HA HB
      (List.nodup_append.mpr ⟨(List.nodup_append.mp Hnd).1,
        (List.nodup_append.mp (List.nodup_append.mp Hnd).2.1).1,
        fun a ha e he => hacc a ha e (List.mem_append_left _ he)⟩)
    have Htail' := S.popStep_stack_frame Hr hgpop Hg HA HB hab Htail
      (fun a ha e he => hacc a (List.mem_append_left _ ha) e (List.mem_append_right _ he))
      (fun b hb e he => hacc b (List.mem_append_right _ hb) e (List.mem_append_right _ he))
    rw [← Hstep.2.2.1] at Htail'
    have Hnd' := (S.pop_ends_perm s.lh A B (els (todo ++ rest)) g).symm.nodup Hnd
    have hlh : (S.popStep s).lh = s.lh := by simp only [popStep]; split <;> rfl
    have he' : e ∉ ((A ++ S.upC s.lh g) ++ (B ++ S.loC s.lh g)) ++ els todo := by
      intro hm
      apply he
      simpa [els] using (S.pop_ends_perm s.lh A B (els todo) g).mem_iff.mp hm
    have HI := ih Htail' Hstep.1 Hstep.2.1 Hnd' (by
      intro q hq
      rw [hlh]
      exact hpop q (List.mem_cons_of_mem _ hq)) he'
    have heA : e ∉ A := fun h => he (by simp [els, h])
    have heB : e ∉ B := fun h => he (by simp [els, h])
    exact HI.trans (S.popStep_cell_frame Hr hgpop Hg HA HB hab heA heB)

/-- The entire upper loop preserves a disjoint live stack. -/
theorem popGroups_stack_frame {todo rest foreign : List Grp} {s : SMS}
    {A B : List Nat} {h : Nat}
    (Hrx : StackRep s.m s.rxp (todo ++ rest))
    (HA : Linked s.m.nx s.ah s.at' A) (HB : Linked s.m.nx s.bh s.bt B)
    (hnd : ((A ++ B) ++ els (todo ++ rest)).Nodup)
    (hpop : ∀ g ∈ todo, s.lh < S.gtop g) (HF : StackRep s.m h foreign)
    (hd : ∀ a ∈ (A ++ B) ++ els todo, ∀ e ∈ els foreign, a ≠ e) :
    StackRep (S.popGroups todo s).m h foreign := by
  obtain ⟨hp, ht, hm, hu, hn, _⟩ := S.popGroups_arrays todo s
  apply HF.array_frame
  · intro e he
    exact S.popGroups_cell_frame Hrx HA HB hnd hpop (fun hm => hd e hm e he rfl)
  · intro g _; rw [hp]
  · intro g _; rw [ht]
  · intro g _; rw [hm]
  · intro g _; rw [hu]
  · intro g _; rw [hn]

/-- Consuming a lower group writes only cells in the old accumulator or that group. -/
theorem consStep_cell_frame {s : SMS} {g : Grp} {C : List Nat} {e : Nat}
    (hr : s.ryp = g.id + 1) (Hg : GroupRep s.m g)
    (HC : Linked s.m.nx s.ch s.ct C) (hnd : (C ++ g.els).Nodup)
    (he : e ∉ C ++ g.els) : (consStep s).m.nx e = s.m.nx e := by
  have hCg := (List.nodup_append.mp hnd).2.2
  have HCP := Linked.append HC Hg.positive
    (fun c hc p hp => hCg c hc p (List.mem_append_left _ hp))
  have heCP : e ∉ C ++ g.P := by
    intro h
    apply he
    rcases List.mem_append.mp h with h | h
    · exact List.mem_append_left _ h
    · exact List.mem_append_right _ (List.mem_append_left _ h)
  have heC : e ∉ C := fun h => he (List.mem_append_left _ h)
  have H := Linked.append_cell_frame (h₂ := s.m.mh g.id) (t₂ := s.m.mt g.id) HCP heCP
  rw [Linked.append_cell_frame HC heC] at H
  simpa [consStep, hr] using H

/-- A lower consumption leaves a disjoint live stack represented. -/
theorem consStep_stack_frame {s : SMS} {g : Grp} {C : List Nat}
    {h : Nat} {seg : List Grp}
    (hr : s.ryp = g.id + 1) (Hg : GroupRep s.m g)
    (HC : Linked s.m.nx s.ch s.ct C) (hnd : (C ++ g.els).Nodup)
    (Hseg : StackRep s.m h seg)
    (hd : ∀ c ∈ C ++ g.els, ∀ e ∈ els seg, c ≠ e) :
    StackRep (consStep s).m h seg := by
  apply Hseg.array_frame
  · intro e he
    exact consStep_cell_frame hr Hg HC hnd (fun hc => hd e hc e he rfl)
  all_goals intro q _; simp [consStep, hr]

/-- Run exactly one lower-consumption step for each listed group. -/
def consGroups : List Grp → SMS → SMS
  | [], s => s
  | _ :: todo, s => consGroups todo (consStep s)

theorem consStep_index (s : SMS) : (consStep s).k = s.k := by
  simp only [consStep]
  split <;> rfl

theorem consGroups_index (todo : List Grp) (s : SMS) : (consGroups todo s).k = s.k := by
  induction todo generalizing s with
  | nil => rfl
  | cons g todo ih => exact (ih (consStep s)).trans (consStep_index s)

theorem consGroups_iterate (todo : List Grp) (s : SMS) :
    consGroups todo s = consStep^[todo.length] s := by
  induction todo generalizing s with
  | nil => rfl
  | cons g todo ih =>
    simpa only [consGroups, List.length_cons, Function.iterate_succ_apply] using ih (consStep s)

/-- The lower-consumption loop concatenates precisely the listed lower ends. -/
theorem consGroups_refines {todo : List Grp} {s : SMS} {C : List Nat}
    (Hry : StackRep s.m s.ryp todo) (HC : Linked s.m.nx s.ch s.ct C)
    (hnd : (C ++ els todo).Nodup) :
    let t := consGroups todo s
    t.ryp = 0 ∧ Linked t.m.nx t.ch t.ct (C ++ els todo) ∧
      t.cons = s.cons ++ todo.map Grp.id ∧ t.G = s.G ∧ t.mode = s.mode ∧
      ∀ post, s.mode = 2 → t = (S.mstep post)^[todo.length] s := by
  induction todo generalizing s C with
  | nil =>
    have hz := Hry.head_zero_iff.mpr rfl
    simp only [consGroups, els, List.flatMap_nil, List.append_nil, List.map_nil]
    exact ⟨hz, HC, trivial, trivial, trivial, by intros; rfl⟩
  | cons g todo ih =>
    obtain ⟨Hr, Hg, Htail, _⟩ := StackRep.cons_iff.mp Hry
    have Hnd : ((C ++ g.els) ++ els todo).Nodup := by
      simpa [els, List.append_assoc] using hnd
    have Hndg := (List.nodup_append.mp Hnd).1
    have Hd := (List.nodup_append.mp Hnd).2.2
    have Hstep := consStep_class Hr Hg HC Hndg
    have Htail' := consStep_stack_frame Hr Hg HC Hndg Htail Hd
    rw [← Hstep.2.1] at Htail'
    have hG : (consStep s).G = s.G := by simp [consStep, Hr]
    have hmode : (consStep s).mode = s.mode := by simp [consStep, Hr]
    obtain ⟨Hzero, Hclass, Hcons, HG, Hmode, Hiterate⟩ := ih Htail' Hstep.1 Hnd
    refine ⟨Hzero, ?_, ?_, HG.trans hG, Hmode.trans hmode, ?_⟩
    · simpa [consGroups, els, List.append_assoc] using Hclass
    · simpa [consGroups, Hstep.2.2.1, List.append_assoc] using Hcons
    · intro post hm
      have hm' : (consStep s).mode = 2 := hmode.trans hm
      have HstepMachine : S.mstep post s = consStep s := by simp [mstep, hm]
      simpa [consGroups, Function.iterate_succ_apply, HstepMachine] using Hiterate post hm'

theorem consGroups_arrays {todo : List Grp} {s : SMS} {C : List Nat}
    (Hry : StackRep s.m s.ryp todo) (HC : Linked s.m.nx s.ch s.ct C)
    (hnd : (C ++ els todo).Nodup) :
    (consGroups todo s).m.ph = s.m.ph ∧ (consGroups todo s).m.pt = s.m.pt ∧
    (consGroups todo s).m.mh = s.m.mh ∧ (consGroups todo s).m.mt = s.m.mt ∧
    (consGroups todo s).m.gn = s.m.gn ∧ (consGroups todo s).rxp = s.rxp ∧
    (consGroups todo s).ah = s.ah ∧ (consGroups todo s).at' = s.at' ∧
    (consGroups todo s).bh = s.bh ∧ (consGroups todo s).bt = s.bt ∧
    (consGroups todo s).G = s.G ∧ (consGroups todo s).v = s.v ∧
    (consGroups todo s).lh = s.lh ∧ (consGroups todo s).lx = s.lx ∧
    (consGroups todo s).mode = s.mode ∧ (consGroups todo s).k = s.k := by
  induction todo generalizing s C with
  | nil => simp [consGroups]
  | cons g todo ih =>
    obtain ⟨Hr, Hg, Htail, _⟩ := StackRep.cons_iff.mp Hry
    have Hnd : ((C ++ g.els) ++ els todo).Nodup := by
      simpa [els, List.append_assoc] using hnd
    have Hndg := (List.nodup_append.mp Hnd).1
    have Hstep := consStep_class Hr Hg HC Hndg
    have Htail' := consStep_stack_frame Hr Hg HC Hndg Htail
      (List.nodup_append.mp Hnd).2.2
    rw [← Hstep.2.1] at Htail'
    have H := ih Htail' Hstep.1 Hnd
    simpa [consGroups, consStep, Hr] using H

/-- All successor writes in a lower loop lie in its accumulated or consumed ends. -/
theorem consGroups_cell_frame {todo : List Grp} {s : SMS} {C : List Nat} {e : Nat}
    (Hry : StackRep s.m s.ryp todo) (HC : Linked s.m.nx s.ch s.ct C)
    (hnd : (C ++ els todo).Nodup) (he : e ∉ C ++ els todo) :
    (consGroups todo s).m.nx e = s.m.nx e := by
  induction todo generalizing s C with
  | nil => rfl
  | cons g todo ih =>
    obtain ⟨Hr, Hg, Htail, _⟩ := StackRep.cons_iff.mp Hry
    have Hnd : ((C ++ g.els) ++ els todo).Nodup := by
      simpa [els, List.append_assoc] using hnd
    have Hndg := (List.nodup_append.mp Hnd).1
    have Hstep := consStep_class Hr Hg HC Hndg
    have Htail' := consStep_stack_frame Hr Hg HC Hndg Htail
      (List.nodup_append.mp Hnd).2.2
    rw [← Hstep.2.1] at Htail'
    have he' : e ∉ (C ++ g.els) ++ els todo := by
      simpa [els, List.append_assoc] using he
    have hegroup : e ∉ C ++ g.els := fun hm => he' (List.mem_append_left _ hm)
    exact (ih Htail' Hstep.1 Hnd he').trans (consStep_cell_frame Hr Hg HC Hndg hegroup)

/-- The lower loop preserves every disjoint represented class. -/
theorem consGroups_linked_frame {todo : List Grp} {s : SMS} {C F : List Nat} {h t : Nat}
    (Hry : StackRep s.m s.ryp todo) (HC : Linked s.m.nx s.ch s.ct C)
    (hnd : (C ++ els todo).Nodup) (HF : Linked s.m.nx h t F)
    (hd : ∀ a ∈ C ++ els todo, ∀ e ∈ F, a ≠ e) :
    Linked (consGroups todo s).m.nx h t F :=
  HF.frame fun e he => consGroups_cell_frame Hry HC hnd (fun hm => hd e hm e he rfl)

/-- The lower loop preserves every disjoint live stack. -/
theorem consGroups_stack_frame {todo foreign : List Grp} {s : SMS} {C : List Nat} {h : Nat}
    (Hry : StackRep s.m s.ryp todo) (HC : Linked s.m.nx s.ch s.ct C)
    (hnd : (C ++ els todo).Nodup) (HF : StackRep s.m h foreign)
    (hd : ∀ a ∈ C ++ els todo, ∀ e ∈ els foreign, a ≠ e) :
    StackRep (consGroups todo s).m h foreign := by
  obtain ⟨hp, ht, hm, hu, hn, _⟩ := consGroups_arrays Hry HC hnd
  apply HF.array_frame
  · intro e he
    exact consGroups_cell_frame Hry HC hnd (fun hm => hd e hm e he rfl)
  · intro g _; rw [hp]
  · intro g _; rw [ht]
  · intro g _; rw [hm]
  · intro g _; rw [hu]
  · intro g _; rw [hn]

end STACS2027.Embed.Sol

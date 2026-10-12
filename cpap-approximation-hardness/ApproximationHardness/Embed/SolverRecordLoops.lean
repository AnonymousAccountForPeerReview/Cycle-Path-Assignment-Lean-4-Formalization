module

public import ApproximationHardness.Embed.SolverBits

/-! # Exact parent and flip writes made by the linked loops -/

@[expose] public section

namespace STACS2027.Embed.Sol

variable (S : Sol)

def writeParents (G : Nat) (rows : List (Nat × Bool)) (a : Nat → Nat) : Nat → Nat :=
  rows.foldl (fun a x => upd a x.1 (G + 1)) a

def writeFlips (rows : List (Nat × Bool)) (a : Nat → Nat) : Nat → Nat :=
  rows.foldl (fun a x => upd a x.1 (if x.2 then 1 else 0)) a

def upperRows (lh : Nat) (groups : List Grp) : List (Nat × Bool) :=
  groups.map fun g => (g.id, !decide (lh < S.kh g.P))

def lowerRows (groups : List Grp) : List (Nat × Bool) :=
  groups.map fun g => (g.id, decide (g.P ≠ []))

theorem popStep_records {s : SMS} {g : Grp}
    (hr : s.rxp = g.id + 1) (hp : s.lh < S.gtop g) (Hg : GroupRep s.m g) :
    (S.popStep s).m.gp = upd s.m.gp g.id (s.G + 1) ∧
      (S.popStep s).m.gf = upd s.m.gf g.id (if s.lh < S.kh g.P then 0 else 1) := by
  simp [popStep, hr, S.gtopM_group Hg, hp, S.khM_linked Hg.positive]

theorem consStep_records {s : SMS} {g : Grp}
    (hr : s.ryp = g.id + 1) (Hg : GroupRep s.m g) :
    (consStep s).m.gp = upd s.m.gp g.id (s.G + 1) ∧
      (consStep s).m.gf = upd s.m.gf g.id (if g.P = [] then 0 else 1) := by
  have hz := Hg.positive.head_zero_iff
  by_cases hp : g.P = []
  · simp [consStep, hr, hz.mpr hp, hp]
  · have hn : s.m.ph g.id ≠ 0 := fun h => hp (hz.mp h)
    simp [consStep, hr, hn, hp]

theorem popGroups_records {todo rest : List Grp} {s : SMS} {A B : List Nat}
    (Hrx : StackRep s.m s.rxp (todo ++ rest))
    (HA : Linked s.m.nx s.ah s.at' A) (HB : Linked s.m.nx s.bh s.bt B)
    (hnd : ((A ++ B) ++ els (todo ++ rest)).Nodup)
    (hpop : ∀ g ∈ todo, s.lh < S.gtop g) :
    (S.popGroups todo s).m.gp = writeParents s.G (S.upperRows s.lh todo) s.m.gp ∧
      (S.popGroups todo s).m.gf = writeFlips (S.upperRows s.lh todo) s.m.gf := by
  induction todo generalizing s A B with
  | nil => exact ⟨rfl, rfl⟩
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
    obtain ⟨Hpar, Hflip⟩ := ih Htail' Hstep.1 Hstep.2.1 Hnd' (by
      intro q hq; rw [hlh]; exact hpop q (List.mem_cons_of_mem _ hq))
    obtain ⟨HparStep, HflipStep⟩ := S.popStep_records Hr hgpop Hg
    constructor
    · simpa [popGroups, upperRows, writeParents, hG, hlh, HparStep] using Hpar
    · by_cases hup : s.lh < S.kh g.P <;>
        simpa [popGroups, upperRows, writeFlips, hlh, HflipStep, hup] using Hflip

theorem consGroups_records {todo : List Grp} {s : SMS} {C : List Nat}
    (Hry : StackRep s.m s.ryp todo) (HC : Linked s.m.nx s.ch s.ct C)
    (hnd : (C ++ els todo).Nodup) :
    (consGroups todo s).m.gp = writeParents s.G (lowerRows todo) s.m.gp ∧
      (consGroups todo s).m.gf = writeFlips (lowerRows todo) s.m.gf := by
  induction todo generalizing s C with
  | nil => exact ⟨rfl, rfl⟩
  | cons g todo ih =>
    obtain ⟨Hr, Hg, Htail, _⟩ := StackRep.cons_iff.mp Hry
    have Hnd : ((C ++ g.els) ++ els todo).Nodup := by simpa [els, List.append_assoc] using hnd
    have Hstep := consStep_class Hr Hg HC (List.nodup_append.mp Hnd).1
    have Htail' := consStep_stack_frame Hr Hg HC (List.nodup_append.mp Hnd).1 Htail
      (List.nodup_append.mp Hnd).2.2
    rw [← Hstep.2.1] at Htail'
    have hG : (consStep s).G = s.G := by simp [consStep, Hr]
    obtain ⟨Hpar, Hflip⟩ := ih Htail' Hstep.1 Hnd
    obtain ⟨HparStep, HflipStep⟩ := consStep_records Hr Hg
    constructor
    · simpa [consGroups, lowerRows, writeParents, hG, HparStep] using Hpar
    · simpa [consGroups, lowerRows, writeFlips, HflipStep] using Hflip

end STACS2027.Embed.Sol

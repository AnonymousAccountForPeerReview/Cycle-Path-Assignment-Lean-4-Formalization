module

public import ApproximationHardness.Embed.DefaultRotationRAM
import Lean.Elab.Tactic.Omega

/-! # Three-slot local cycle interpretation -/

@[expose] public section

namespace STACS2027.Embed.RAMSolver

def slotCycle (n a b e : Nat) : List Nat := [a,b,e].take n

theorem slotCycle_labels (n a b e d : Nat) (hpos : 0<n) (hmax : n≤3)
    (hnd : (slotCycle n a b e).Nodup) (hd : d∈slotCycle n a b e) :
    cnext (slotCycle n a b e) d=nextLabel n d a b e ∧
    cnext (slotCycle n a b e).reverse d=predLabel n d a b e := by
  have hn : n=1 ∨ n=2 ∨ n=3 := by omega
  rcases hn with rfl|rfl|rfl
  · simp only [slotCycle,List.take_succ_cons,List.take_zero,List.mem_cons,List.mem_nil_iff,
      or_false] at hd
    subst d
    simp [slotCycle,cnext,nextLabel,predLabel]
  · simp [slotCycle] at hnd hd
    have hba := Ne.symm hnd
    rcases hd with rfl|rfl
    all_goals simp_all [slotCycle,cnext,nextLabel,predLabel]
  · simp [slotCycle] at hnd hd
    rcases hnd with ⟨⟨hab,hae⟩,hbe⟩
    have hba := Ne.symm hab
    have hea := Ne.symm hae
    have heb := Ne.symm hbe
    rcases hd with rfl|rfl|rfl
    all_goals simp_all [slotCycle,cnext,nextLabel,predLabel]

theorem slotCycle_eq (F : ForestData) (hF : F.Valid) (v : Nat) (hv : F.IsVertex v)
    (hp : (F.parts v).length≤2) :
    slotCycle (F.dartsAt v).length (cycleSlots F v).1 (cycleSlots F v).2.1
      (cycleSlots F v).2.2=ForestData.cycOf hF (fun _=>false) v := by
  have he : (ForestData.cycOf hF (fun _=>false) v).length=(F.dartsAt v).length :=
    (ForestData.cycOf_perm hF hv).length_eq
  cases hparts : F.parts v with
  | nil =>
    by_cases hr : F.IsRoot v
    · by_cases hz : F.zOf v<2*F.E
      · have hdegree := (ForestData.zOf_mem hz).2
        simp [ForestData.cycOf,Plan.ord,ForestData.plan,hparts,hr,hz,hdegree] at he
      · have hn : (F.dartsAt v).length=0 := by
          simpa [ForestData.cycOf,Plan.ord,ForestData.plan,hparts,hr,hz] using he.symm
        simp [slotCycle,cycleSlots,ForestData.cycOf,Plan.ord,ForestData.plan,hparts,hr,hz,hn]
    · have hn : (F.dartsAt v).length=1 := by
        simpa [ForestData.cycOf,Plan.ord,ForestData.plan,hparts,hr] using he.symm
      simp [slotCycle,cycleSlots,ForestData.cycOf,Plan.ord,ForestData.plan,hparts,hr,hn]
  | cons a as =>
    cases as with
    | nil =>
      by_cases hr : F.IsRoot v
      · by_cases hz : F.zOf v<2*F.E
        · have hdegree := (ForestData.zOf_mem hz).2
          simp [ForestData.cycOf,Plan.ord,ForestData.plan,hparts,hr,hz,hdegree] at he
        · have hn : (F.dartsAt v).length=1 := by
            simpa [ForestData.cycOf,Plan.ord,ForestData.plan,hparts,hr,hz] using he.symm
          simp [slotCycle,cycleSlots,ForestData.cycOf,Plan.ord,ForestData.plan,hparts,hr,hz,hn]
      · have hn : (F.dartsAt v).length=2 := by
          simpa [ForestData.cycOf,Plan.ord,ForestData.plan,hparts,hr] using he.symm
        simp [slotCycle,cycleSlots,ForestData.cycOf,Plan.ord,ForestData.plan,hparts,hr,hn]
    | cons b bs =>
      have hbs : bs=[] := by simp only [hparts,List.length_cons] at hp; exact List.eq_nil_of_length_eq_zero (by omega)
      subst bs
      by_cases hr : F.IsRoot v
      · by_cases hz : F.zOf v<2*F.E
        · have hn : (F.dartsAt v).length=3 := by
            simpa [ForestData.cycOf,Plan.ord,ForestData.plan,hparts,hr,hz] using he.symm
          simp [slotCycle,cycleSlots,ForestData.cycOf,Plan.ord,ForestData.plan,hparts,hr,hz,hn]
        · have hn : (F.dartsAt v).length=2 := by
            simpa [ForestData.cycOf,Plan.ord,ForestData.plan,hparts,hr,hz] using he.symm
          simp [slotCycle,cycleSlots,ForestData.cycOf,Plan.ord,ForestData.plan,hparts,hr,hz,hn]
      · have hn : (F.dartsAt v).length=3 := by
          simpa [ForestData.cycOf,Plan.ord,ForestData.plan,hparts,hr] using he.symm
        simp [slotCycle,cycleSlots,ForestData.cycOf,Plan.ord,ForestData.plan,hparts,hr,hn]

theorem cycleSlots_labels (F : ForestData) (hF : F.Valid) (d : Nat) (hd : d<2*F.E)
    (hp : (F.parts (F.rep d)).length≤2) :
    nextLabel (F.dartsAt (F.rep d)).length d (cycleSlots F (F.rep d)).1
      (cycleSlots F (F.rep d)).2.1 (cycleSlots F (F.rep d)).2.2 =
      ForestData.rotN hF (fun _=>false) d ∧
    predLabel (F.dartsAt (F.rep d)).length d (cycleSlots F (F.rep d)).1
      (cycleSlots F (F.rep d)).2.1 (cycleSlots F (F.rep d)).2.2 =
      ForestData.rotInvN hF (fun _=>false) d := by
  have hv := ForestData.isVertex_rep hF hd
  have hm : d∈F.dartsAt (F.rep d) := ForestData.mem_dartsAt.mpr ⟨hd,rfl⟩
  have hpos : 0<(F.dartsAt (F.rep d)).length := List.length_pos_iff.mpr (List.ne_nil_of_mem hm)
  have hcycle := slotCycle_eq F hF (F.rep d) hv hp
  have hnd : (slotCycle (F.dartsAt (F.rep d)).length (cycleSlots F (F.rep d)).1
      (cycleSlots F (F.rep d)).2.1 (cycleSlots F (F.rep d)).2.2).Nodup := by
    rw [hcycle];exact ForestData.cycOf_nodup hF hv
  have hmem : d∈slotCycle (F.dartsAt (F.rep d)).length (cycleSlots F (F.rep d)).1
      (cycleSlots F (F.rep d)).2.1 (cycleSlots F (F.rep d)).2.2 := by
    rw [hcycle];exact (ForestData.mem_cycOf hF hv).mpr ⟨hd,rfl⟩
  have h := slotCycle_labels _ _ _ _ d hpos (hF.deg _) hnd hmem
  rw [hcycle] at h
  exact ⟨h.1.symm,h.2.symm⟩

end STACS2027.Embed.RAMSolver

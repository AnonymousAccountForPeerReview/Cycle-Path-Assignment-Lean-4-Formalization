module

public import ApproximationHardness.Embed.Stack
import Lean.Elab.Tactic.Omega

/-!
# Refinement of fork-consumption steps

The linked implementation moves the two classes of one consumed group to
the appropriate accumulators. The successor-array changes preserve both
accumulated classes, and the recorded parent and flip are the abstract merge data.
-/

@[expose] public section

namespace STACS2027.Embed.Sol

variable (S : Sol)

/-- Consuming one upper stack group extends exactly the upper and lower accumulators. -/
theorem popStep_classes {s : SMS} {g : Grp} {A B : List Nat}
    (hr : s.rxp = g.id + 1) (hpop : s.lh < S.gtop g) (Hg : GroupRep s.m g)
    (HA : Linked s.m.nx s.ah s.at' A) (HB : Linked s.m.nx s.bh s.bt B)
    (hnd : ((A ++ B) ++ g.els).Nodup) :
    Linked (S.popStep s).m.nx (S.popStep s).ah (S.popStep s).at'
      (A ++ S.upC s.lh g) ∧
    Linked (S.popStep s).m.nx (S.popStep s).bh (S.popStep s).bt
      (B ++ S.loC s.lh g) ∧
    (S.popStep s).rxp = s.m.gn g.id ∧
    (S.popStep s).cons = s.cons ++ [g.id] ∧
    (S.popStep s).m.gp g.id = s.G + 1 ∧
    (S.popStep s).m.gf g.id = if s.lh < S.kh g.P then 0 else 1 := by
  have hab := (List.nodup_append.mp (List.nodup_append.mp hnd).1).2.2
  have hc := (List.nodup_append.mp hnd).2.2
  have hA : ∀ a ∈ A, ∀ e ∈ g.els, a ≠ e :=
    fun a ha e he => hc a (List.mem_append_left _ ha) e he
  have hB : ∀ b ∈ B, ∀ e ∈ g.els, b ≠ e :=
    fun b hb e he => hc b (List.mem_append_right _ hb) e he
  have hAU : ∀ a ∈ A, ∀ u ∈ S.upC s.lh g, a ≠ u :=
    fun a ha u hu => hA a ha u (upC_sub hu)
  have hAV : ∀ a ∈ A, ∀ v ∈ S.loC s.lh g, a ≠ v :=
    fun a ha v hv => hA a ha v (loC_sub hv)
  have hBU : ∀ b ∈ B, ∀ u ∈ S.upC s.lh g, b ≠ u :=
    fun b hb u hu => hB b hb u (upC_sub hu)
  have hBV : ∀ b ∈ B, ∀ v ∈ S.loC s.lh g, b ≠ v :=
    fun b hb v hv => hB b hb v (loC_sub hv)
  have htop := S.gtopM_group Hg
  have hkey := S.khM_linked Hg.positive
  by_cases hup : s.lh < S.kh g.P
  · have H := Linked.double_append HA HB Hg.positive Hg.negative
      (by simpa [upC, hup] using hAU) hab (by simpa [loC, hup] using hAV)
      (by simpa [loC, hup] using hBV) (by simpa [upC, hup] using hBU)
    obtain ⟨Hp, Hm⟩ := H
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [popStep, hr, htop, hpop, hkey, hup, upC] using Hp
    · simpa [popStep, hr, htop, hpop, hkey, hup, loC] using Hm
    · simp [popStep, hr, htop, hpop, hkey, hup]
    · simp [popStep, hr, htop, hpop, hkey, hup]
    · simp [popStep, hr, htop, hpop, hkey, hup]
    · simp [popStep, hr, htop, hpop, hkey, hup]
  · have H := Linked.double_append HA HB Hg.negative Hg.positive
      (by simpa [upC, hup] using hAU) hab (by simpa [loC, hup] using hAV)
      (by simpa [loC, hup] using hBV) (by simpa [upC, hup] using hBU)
    obtain ⟨Hp, Hm⟩ := H
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [popStep, hr, htop, hpop, hkey, hup, upC] using Hp
    · simpa [popStep, hr, htop, hpop, hkey, hup, loC] using Hm
    · simp [popStep, hr, htop, hpop, hkey, hup]
    · simp [popStep, hr, htop, hpop, hkey, hup]
    · simp [popStep, hr, htop, hpop, hkey, hup]
    · simp [popStep, hr, htop, hpop, hkey, hup]

/-- Consuming one lower stack group extends the lower accumulator by precisely its ends. -/
theorem consStep_class {s : SMS} {g : Grp} {C : List Nat}
    (hr : s.ryp = g.id + 1) (Hg : GroupRep s.m g)
    (HC : Linked s.m.nx s.ch s.ct C) (hnd : (C ++ g.els).Nodup) :
    Linked (consStep s).m.nx (consStep s).ch (consStep s).ct (C ++ g.els) ∧
    (consStep s).ryp = s.m.gn g.id ∧
    (consStep s).cons = s.cons ++ [g.id] ∧
    (consStep s).m.gp g.id = s.G + 1 ∧
    (consStep s).m.gf g.id = if g.P = [] then 0 else 1 := by
  have hCg := (List.nodup_append.mp hnd).2.2
  have hCP : ∀ c ∈ C, ∀ p ∈ g.P, c ≠ p :=
    fun c hc p hp => hCg c hc p (List.mem_append_left _ hp)
  have hCM : ∀ c ∈ C, ∀ p ∈ g.M, c ≠ p :=
    fun c hc p hp => hCg c hc p (List.mem_append_right _ hp)
  have hPM := (List.nodup_append.mp (List.nodup_append.mp hnd).2.1).2.2
  have HCP := Linked.append HC Hg.positive hCP
  have HM := Linked.append_frame (h₂ := s.m.ph g.id) (t₂ := s.m.pt g.id) HC Hg.negative hCM
  have H := Linked.append HCP HM (by
    intro c hc m hm
    rcases List.mem_append.mp hc with hc | hp
    · exact hCM c hc m hm
    · exact hPM c hp m hm)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [consStep, hr, Grp.els, List.append_assoc] using H
  · simp [consStep, hr]
  · simp [consStep, hr]
  · simp [consStep, hr]
  · have hz := Hg.positive.head_zero_iff
    by_cases hp : g.P = []
    · simp [consStep, hr, hz.mpr hp, hp]
    · have hph : s.m.ph g.id ≠ 0 := fun h => hp (hz.mp h)
      simp [consStep, hr, hph, hp]

/-- Finishing a merge installs the newly created group above the remaining upper stack. -/
theorem consStep_finish {s : SMS} {A B C : List Nat} {rest : List Grp}
    (hr : s.ryp = 0)
    (HA : Linked s.m.nx s.ah s.at' A) (HB : Linked s.m.nx s.bh s.bt B)
    (HC : Linked s.m.nx s.ch s.ct C)
    (hCB : ∀ c ∈ C, ∀ b ∈ B, c ≠ b) (hCA : ∀ c ∈ C, ∀ a ∈ A, c ≠ a)
    (Hrest : StackRep s.m s.rxp rest) (hfresh : ∀ g ∈ rest, g.id ≠ s.G)
    (hCr : ∀ c ∈ C, ∀ g ∈ rest, ∀ e ∈ g.els, c ≠ e) :
    StackRep (consStep s).m (s.G + 1) (⟨s.G, A, C ++ B⟩ :: rest) ∧
      (consStep s).m.rs s.v = s.G + 1 ∧ (consStep s).m.rl s.v = s.lx ∧
      (consStep s).mode = 0 := by
  have HM := Linked.append HC HB hCB
  have HP := Linked.append_frame (h₂ := s.bh) (t₂ := s.bt) HC HA hCA
  have Hnew : GroupRep (consStep s).m ⟨s.G, A, C ++ B⟩ := by
    constructor
    · simpa [consStep, hr, SMem.store] using HP
    · simpa [consStep, hr, SMem.store] using HM
  have Hlower : StackRep (consStep s).m s.rxp rest := by
    apply Hrest.frame
    · intro g hg
      have Hg := Hrest.group g hg
      have Hgp := Linked.append_frame (h₂ := s.bh) (t₂ := s.bt) HC Hg.positive
        (fun c hc e he => hCr c hc g hg e (List.mem_append_left _ he))
      have Hgm := Linked.append_frame (h₂ := s.bh) (t₂ := s.bt) HC Hg.negative
        (fun c hc e he => hCr c hc g hg e (List.mem_append_right _ he))
      constructor
      · simpa [consStep, hr, SMem.store, upd_ne _ _ (hfresh g hg)] using Hgp
      · simpa [consStep, hr, SMem.store, upd_ne _ _ (hfresh g hg)] using Hgm
    · intro g hg
      simp [consStep, hr, SMem.store, upd_ne _ _ (hfresh g hg)]
  refine ⟨StackRep.cons ⟨s.G, A, C ++ B⟩ rest Hnew ?_ hfresh, ?_, ?_, ?_⟩
  · simpa [consStep, hr, SMem.store] using Hlower
  · simp [consStep, hr, SMem.store]
  · simp [consStep, hr, SMem.store]
  · simp [consStep, hr]

end STACS2027.Embed.Sol

module

public import ApproximationHardness.Embed.Node
import Lean.Elab.Tactic.Omega

/-!
# Full linked merge refinement

The two actual array loops consume the upper prefix and the lower stack, then
install exactly the abstract merged group. No supplied embedding enters this
algorithm or its linked representation.
-/

@[expose] public section

namespace STACS2027.Embed.Sol

variable (S : Sol)

theorem flatMap_up_sub {lh : Nat} {seg : List Grp} {e : Nat}
    (h : e ∈ seg.flatMap (S.upC lh)) : e ∈ els seg := by
  obtain ⟨g, hg, he⟩ := List.mem_flatMap.mp h
  exact List.mem_flatMap.mpr ⟨g, hg, upC_sub he⟩

theorem flatMap_lo_sub {lh : Nat} {seg : List Grp} {e : Nat}
    (h : e ∈ seg.flatMap (S.loC lh)) : e ∈ els seg := by
  obtain ⟨g, hg, he⟩ := List.mem_flatMap.mp h
  exact List.mem_flatMap.mpr ⟨g, hg, loC_sub he⟩

theorem els_sub {small large : List Grp} (h : small.Sublist large) :
    ∀ e ∈ els small, e ∈ els large := by
  intro e he
  obtain ⟨g, hg, he⟩ := List.mem_flatMap.mp he
  exact List.mem_flatMap.mpr ⟨g, h.subset hg, he⟩

/-- The exact sequence of linked operations completing a nonempty merge. -/
def mergeState (s : SMS) (rx ry : Res) : SMS :=
  let t := S.popGroups (S.popped ry.low rx) s
  consStep (consGroups ry.seg {t with mode := 2})

theorem mergeState_index (s : SMS) (rx ry : Res) : (S.mergeState s rx ry).k = s.k := by
  unfold mergeState
  rw [consStep_index, consGroups_index]
  exact (S.popGroups_arrays (S.popped ry.low rx) s).2.2.2.2.2.2.2.2.2.2.2.2.1

/-- The linked fork loops compute exactly the abstract merge result. -/
theorem mergeState_refines {s : SMS} {v : Nat} {rx ry : Res}
    (Hv : s.v = v) (HG : s.G = S.gid v) (Hlh : s.lh = ry.low) (Hlx : s.lx = rx.low)
    (HA : s.ah = 0) (HB : s.bh = 0) (HC : s.ch = 0)
    (Hrx : StackRep s.m s.rxp rx.seg) (Hry : StackRep s.m s.ryp ry.seg)
    (hne : ry.seg ≠ []) (hnd : (els rx.seg ++ els ry.seg).Nodup)
    (fresh : ∀ g ∈ rx.seg, g.id ≠ S.gid v) :
    Stored (S.mergeState s rx ry).m v (S.mergeRes v rx ry) ∧
      (S.mergeState s rx ry).mode = 0 ∧
      (S.mergeState s rx ry).cons = s.cons ++
        (S.popped ry.low rx).map Grp.id ++ ry.seg.map Grp.id ∧
      ∀ post, s.mode = 1 → (∀ g ∈ S.rest ry.low rx, S.gtop g ≤ ry.low) →
        S.mergeState s rx ry = (S.mstep post)^[
          (S.popped ry.low rx).length + 1 + ry.seg.length + 1] s := by
  let popped := S.popped ry.low rx
  let rest := S.rest ry.low rx
  let t := S.popGroups popped s
  let start := {t with mode := 2}
  let u := consGroups ry.seg start
  have hsplit : popped ++ rest = rx.seg := S.popped_append_rest ry.low rx
  have hpopSub : popped.Sublist rx.seg := by rw [← hsplit]; exact List.sublist_append_left _ _
  have hrestSub : rest.Sublist rx.seg := by rw [← hsplit]; exact List.sublist_append_right _ _
  have hxy := (List.nodup_append.mp hnd).2.2
  have HAnil : Linked s.m.nx s.ah s.at' [] := HA ▸ Linked.nil s.m.nx s.at'
  have HBnil : Linked s.m.nx s.bh s.bt [] := HB ▸ Linked.nil s.m.nx s.bt
  have Hndrx : (([] ++ []) ++ els (popped ++ rest)).Nodup := by
    simpa [hsplit] using (List.nodup_append.mp hnd).1
  have Hpop : ∀ g ∈ popped, s.lh < S.gtop g := by
    intro g hg
    rw [Hlh]
    exact S.lt_gtop_of_popped hg
  have Hrx' : StackRep s.m s.rxp (popped ++ rest) := hsplit.symm ▸ Hrx
  obtain ⟨Hrest, HApop, HBpop, HconsPop, HlowPop, HgroupPop, HndPop, HmodePop, HiterPop⟩ :=
    S.popGroups_refines Hrx' HAnil HBnil Hndrx Hpop
  have HryPop : StackRep t.m s.ryp ry.seg :=
    S.popGroups_stack_frame Hrx' HAnil HBnil Hndrx Hpop Hry (by
      intro a ha e he
      exact hxy a (els_sub hpopSub a (by simpa using ha)) e he)
  obtain ⟨_, _, _, _, _, Hryp, Hch, Hct, HGpop, Hvpop, Hlhpop, Hlxpop, _⟩ :=
    S.popGroups_arrays popped s
  have HryStart : StackRep start.m start.ryp ry.seg := by
    simpa [start, t, Hryp] using HryPop
  have HCnil : Linked start.m.nx start.ch start.ct [] := by
    simpa [start, t, Hch, HC] using Linked.nil t.m.nx t.ct
  have Hndry : ([] ++ els ry.seg).Nodup := by
    simpa using (List.nodup_append.mp hnd).2.1
  obtain ⟨Hryzero, HCry, HconsRy, HgroupRy, HmodeRy, HiterRy⟩ :=
    S.consGroups_refines HryStart HCnil Hndry
  have HupperSub : ∀ e ∈ popped.flatMap (S.upC s.lh), e ∈ els rx.seg :=
    fun e he => els_sub hpopSub e (S.flatMap_up_sub he)
  have HlowerSub : ∀ e ∈ popped.flatMap (S.loC s.lh), e ∈ els rx.seg :=
    fun e he => els_sub hpopSub e (S.flatMap_lo_sub he)
  have HAstart : Linked start.m.nx start.ah start.at' (popped.flatMap (S.upC s.lh)) := by
    simpa [start, t] using HApop
  have HBstart : Linked start.m.nx start.bh start.bt (popped.flatMap (S.loC s.lh)) := by
    simpa [start, t] using HBpop
  have HrestStart : StackRep start.m start.rxp rest := by simpa [start, t] using Hrest
  have HAend := consGroups_linked_frame HryStart HCnil Hndry HAstart (by
    intro a ha e he
    exact Ne.symm (hxy e (HupperSub e he) a (by simpa using ha)))
  have HBend := consGroups_linked_frame HryStart HCnil Hndry HBstart (by
    intro a ha e he
    exact Ne.symm (hxy e (HlowerSub e he) a (by simpa using ha)))
  have HrestEnd := consGroups_stack_frame HryStart HCnil Hndry HrestStart (by
    intro a ha e he
    exact Ne.symm (hxy e (els_sub hrestSub e he) a (by simpa using ha)))
  obtain ⟨_, _, _, _, _, HrxpEnd, HaEnd, HatEnd, HbEnd, HbtEnd,
      HGend, Hvend, Hlhend, Hlxend, _⟩ := consGroups_arrays HryStart HCnil Hndry
  have HAfinal : Linked u.m.nx u.ah u.at' (popped.flatMap (S.upC s.lh)) := by
    simpa [u, HaEnd, HatEnd] using HAend
  have HBfinal : Linked u.m.nx u.bh u.bt (popped.flatMap (S.loC s.lh)) := by
    simpa [u, HbEnd, HbtEnd] using HBend
  have HRfinal : StackRep u.m u.rxp rest := by simpa [u, HrxpEnd] using HrestEnd
  have HCfinal : Linked u.m.nx u.ch u.ct (els ry.seg) := by simpa [u] using HCry
  have HGfinal : u.G = S.gid v := by simpa [u, start, t] using HGend.trans (HGpop.trans HG)
  have Hvfinal : u.v = v := by simpa [u, start, t] using Hvend.trans (Hvpop.trans Hv)
  have Hlxfinal : u.lx = rx.low := by simpa [u, start, t] using Hlxend.trans (Hlxpop.trans Hlx)
  have Hzero : u.ryp = 0 := Hryzero
  obtain ⟨Hnew, Hstore, HstoreLow, Hmode⟩ := consStep_finish Hzero HAfinal HBfinal HCfinal
    (fun c hc b hb => Ne.symm (hxy b (HlowerSub b hb) c hc))
    (fun c hc a ha => Ne.symm (hxy a (HupperSub a ha) c hc)) HRfinal
    (fun g hg => by rw [HGfinal]; exact fresh g (hrestSub.subset hg))
    (fun c hc g hg e he => Ne.symm (hxy e
      (els_sub hrestSub e (List.mem_flatMap.mpr ⟨g, hg, he⟩)) c hc))
  change Stored (consStep u).m v (S.mergeRes v rx ry) ∧ (consStep u).mode = 0 ∧ _ ∧ _
  refine ⟨?_, Hmode, ?_, ?_⟩
  · constructor
    · have Hstore' : (consStep u).m.rs v = u.G + 1 := by simpa [Hvfinal] using Hstore
      rw [Hstore']
      simpa [mergeRes, hne, HGfinal, Hlh, popped, rest] using Hnew
    · have HstoreLow' : (consStep u).m.rl v = u.lx := by simpa [Hvfinal] using HstoreLow
      rw [HstoreLow', Hlxfinal]
      simp [mergeRes, hne]
  · have HconsFinish : (consStep u).cons = u.cons := by simp [consStep, Hzero]
    change (consStep u).cons = _
    rw [HconsFinish]
    change (consGroups ry.seg start).cons = _
    rw [HconsRy]
    change t.cons ++ ry.seg.map Grp.id = _
    rw [show t.cons = s.cons ++ popped.map Grp.id from HconsPop]
  · intro post HmodeStart Hstop
    have HmodeT : t.mode = 1 := HmodePop.trans HmodeStart
    have HpopStop : S.popStep t = start := S.popStep_stop Hrest (by
      intro g hg
      have hle := Hstop g hg
      simpa [t, HlowPop, Hlh] using hle)
    have Hswitch : S.mstep post t = start := by
      simp only [mstep, HmodeT, Nat.one_ne_zero, ite_false, ite_true]
      exact HpopStop
    have HmodeU : u.mode = 2 := HmodeRy
    have Hfinish : S.mstep post u = consStep u := by simp [mstep, HmodeU]
    have HiterPop' : t = (S.mstep post)^[popped.length] s := HiterPop post HmodeStart
    have HiterRy' : u = (S.mstep post)^[ry.seg.length] start := HiterRy post rfl
    change consStep u = _
    calc
      consStep u = S.mstep post u := Hfinish.symm
      _ = (S.mstep post)^[ry.seg.length + 1] start := by
        rw [HiterRy', Function.iterate_succ_apply']
      _ = (S.mstep post)^[ry.seg.length + 1] (S.mstep post t) := by rw [Hswitch]
      _ = (S.mstep post)^[ry.seg.length + 2] t := rfl
      _ = (S.mstep post)^[ry.seg.length + 2] ((S.mstep post)^[popped.length] s) := by
        rw [HiterPop']
      _ = (S.mstep post)^[ry.seg.length + 2 + popped.length] s :=
        (Function.iterate_add_apply (S.mstep post) _ _ _).symm
      _ = (S.mstep post)^[(S.popped ry.low rx).length + 1 + ry.seg.length + 1] s := by
        congr 1
        dsimp [popped]
        omega

end STACS2027.Embed.Sol

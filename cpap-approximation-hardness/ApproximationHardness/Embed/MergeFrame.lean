module

public import ApproximationHardness.Embed.ForkFinish

/-! # Preservation of results outside a linked merge -/

@[expose] public section

namespace STACS2027.Embed.Sol

variable (S : Sol)

theorem popGroups_protected (todo : List Grp) (s : SMS) :
    (S.popGroups todo s).m.rs = s.m.rs ∧ (S.popGroups todo s).m.rl = s.m.rl ∧
      (S.popGroups todo s).m.inf = s.m.inf ∧ (S.popGroups todo s).m.ia = s.m.ia := by
  induction todo generalizing s with
  | nil => simp [popGroups]
  | cons g todo ih =>
    have H := ih (S.popStep s)
    have Hstep : (S.popStep s).m.rs = s.m.rs ∧ (S.popStep s).m.rl = s.m.rl ∧
        (S.popStep s).m.inf = s.m.inf ∧ (S.popStep s).m.ia = s.m.ia := by
      simp only [popStep]
      split <;> exact ⟨rfl, rfl, rfl, rfl⟩
    exact ⟨H.1.trans Hstep.1, H.2.1.trans Hstep.2.1,
      H.2.2.1.trans Hstep.2.2.1, H.2.2.2.trans Hstep.2.2.2⟩

theorem consGroups_instruction_frame (todo : List Grp) (s : SMS) :
    (consGroups todo s).m.inf = s.m.inf ∧ (consGroups todo s).m.ia = s.m.ia := by
  induction todo generalizing s with
  | nil => exact ⟨rfl, rfl⟩
  | cons g todo ih =>
    have H := ih (consStep s)
    have Hstep : (consStep s).m.inf = s.m.inf ∧ (consStep s).m.ia = s.m.ia := by
      simp only [consStep]; split <;> exact ⟨rfl, rfl⟩
    exact ⟨H.1.trans Hstep.1, H.2.trans Hstep.2⟩

theorem mergeState_instruction_frame (s : SMS) (rx ry : Res) :
    (S.mergeState s rx ry).m.inf = s.m.inf ∧
      (S.mergeState s rx ry).m.ia = s.m.ia := by
  have Hp := S.popGroups_protected (S.popped ry.low rx) s
  have Hc := consGroups_instruction_frame ry.seg
    {S.popGroups (S.popped ry.low rx) s with mode := 2}
  have Hstep : ∀ s : SMS, (consStep s).m.inf = s.m.inf ∧ (consStep s).m.ia = s.m.ia := by
    intro s; simp only [consStep]; split <;> exact ⟨rfl, rfl⟩
  unfold mergeState
  exact ⟨(Hstep _).1.trans (Hc.1.trans Hp.2.2.1),
    (Hstep _).2.trans (Hc.2.trans Hp.2.2.2)⟩

theorem forkFinish_instruction {s : SMS} {m : SMem} {v hx hy code : Nat} {rx ry : Res}
    (Hry : StackRep m hy ry.seg) :
    (S.forkFinish s m v hx hy code rx ry).m.inf v = (if ry.seg = [] then 0 else code) ∧
      (∀ z, z ≠ v → (S.forkFinish s m v hx hy code rx ry).m.inf z = m.inf z) ∧
      (S.forkFinish s m v hx hy code rx ry).m.ia = m.ia := by
  by_cases hnil : ry.seg = []
  · have hyzero : hy = 0 := Hry.head_zero_iff.mpr hnil
    exact ⟨by simp [forkFinish, hnil, forkStart, hyzero],
      by intro z hz; simp [forkFinish, hnil, forkStart, hyzero, upd_ne _ _ hz],
      by simp [forkFinish, hnil, forkStart, hyzero, SMem.store]⟩
  · have hyne : hy ≠ 0 := fun hz => hnil (Hry.head_zero_iff.mp hz)
    have H := S.mergeState_instruction_frame
      (S.forkStart s m v hx rx.low hy ry.low code) rx ry
    refine ⟨?_, ?_, ?_⟩
    · simpa [forkFinish, hnil, forkStart, hyne] using congrFun H.1 v
    · intro z hz
      simpa [forkFinish, hnil, forkStart, hyne, upd_ne _ _ hz] using congrFun H.1 z
    · simpa [forkFinish, hnil, forkStart, hyne] using H.2

theorem consGroups_protected {todo : List Grp} {s : SMS} {C : List Nat}
    (Hry : StackRep s.m s.ryp todo) (HC : Linked s.m.nx s.ch s.ct C)
    (hnd : (C ++ els todo).Nodup) :
    (consGroups todo s).m.rs = s.m.rs ∧ (consGroups todo s).m.rl = s.m.rl ∧
      (consGroups todo s).m.inf = s.m.inf ∧ (consGroups todo s).m.ia = s.m.ia := by
  induction todo generalizing s C with
  | nil => simp [consGroups]
  | cons g todo ih =>
    obtain ⟨Hr, Hg, Htail, _⟩ := StackRep.cons_iff.mp Hry
    have Hnd : ((C ++ g.els) ++ els todo).Nodup := by
      simpa [els, List.append_assoc] using hnd
    have Hstep := consStep_class Hr Hg HC (List.nodup_append.mp Hnd).1
    have Htail' := consStep_stack_frame Hr Hg HC (List.nodup_append.mp Hnd).1 Htail
      (List.nodup_append.mp Hnd).2.2
    rw [← Hstep.2.1] at Htail'
    have H := ih Htail' Hstep.1 Hnd
    simpa [consGroups, consStep, Hr] using H

theorem consStep_finish_foreign {s : SMS} {C : List Nat} {h : Nat} {foreign : List Grp}
    (hr : s.ryp = 0) (HC : Linked s.m.nx s.ch s.ct C)
    (HF : StackRep s.m h foreign)
    (hd : ∀ c ∈ C, ∀ e ∈ els foreign, c ≠ e)
    (fresh : ∀ g ∈ foreign, g.id ≠ s.G) :
    StackRep (consStep s).m h foreign := by
  apply HF.array_frame
  · intro e he
    simpa [consStep, hr, SMem.store] using
      Linked.append_cell_frame (h₂ := s.bh) (t₂ := s.bt) HC
        (fun hc => hd e hc e he rfl)
  all_goals intro g hg; simp [consStep, hr, SMem.store, upd_ne _ _ (fresh g hg)]

theorem mergeState_foreign {s : SMS} {rx ry : Res} {w : Nat} {foreign : Res}
    (Hlh : s.lh = ry.low) (HA : s.ah = 0) (HB : s.bh = 0) (HC : s.ch = 0)
    (Hrx : StackRep s.m s.rxp rx.seg) (Hry : StackRep s.m s.ryp ry.seg)
    (Hnd : (els rx.seg ++ els ry.seg).Nodup) (HF : Stored s.m w foreign)
    (Hw : w ≠ s.v) (fresh : ∀ g ∈ foreign.seg, g.id ≠ s.G)
    (hd : ∀ a ∈ els rx.seg ++ els ry.seg, ∀ e ∈ els foreign.seg, a ≠ e) :
    Stored (S.mergeState s rx ry).m w foreign ∧
      (S.mergeState s rx ry).m.inf = s.m.inf ∧
      (S.mergeState s rx ry).m.ia = s.m.ia := by
  let popped := S.popped ry.low rx
  let rest := S.rest ry.low rx
  let t := S.popGroups popped s
  let start := {t with mode := 2}
  let u := consGroups ry.seg start
  have hsplit : popped ++ rest = rx.seg := S.popped_append_rest ry.low rx
  have hpopSub : popped.Sublist rx.seg := by rw [← hsplit]; exact List.sublist_append_left _ _
  have Hrx' : StackRep s.m s.rxp (popped ++ rest) := hsplit.symm ▸ Hrx
  have HAnil : Linked s.m.nx s.ah s.at' [] := HA ▸ Linked.nil _ _
  have HBnil : Linked s.m.nx s.bh s.bt [] := HB ▸ Linked.nil _ _
  have Hndrx : (([] ++ []) ++ els (popped ++ rest)).Nodup := by
    simpa [hsplit] using (List.nodup_append.mp Hnd).1
  have Hpop : ∀ g ∈ popped, s.lh < S.gtop g := by
    intro g hg; rw [Hlh]; exact S.lt_gtop_of_popped hg
  have HFpop : StackRep t.m (s.m.rs w) foreign.seg :=
    S.popGroups_stack_frame Hrx' HAnil HBnil Hndrx Hpop HF.stack (by
      intro a ha e he
      apply hd a (List.mem_append_left _ ?_) e he
      exact els_sub hpopSub a (by simpa using ha))
  have Hrypop : StackRep t.m s.ryp ry.seg :=
    S.popGroups_stack_frame Hrx' HAnil HBnil Hndrx Hpop Hry (by
      intro a ha e he
      exact (List.nodup_append.mp Hnd).2.2 a
        (els_sub hpopSub a (by simpa using ha)) e he)
  obtain ⟨_, _, _, _, _, Hryp, Hch, Hct, HGpop, Hvpop, _, _, _⟩ :=
    S.popGroups_arrays popped s
  have HryStart : StackRep start.m start.ryp ry.seg := by
    simpa [start, t, Hryp] using Hrypop
  have HCnil : Linked start.m.nx start.ch start.ct [] := by
    simpa [start, t, Hch, HC] using Linked.nil t.m.nx t.ct
  have Hndry : ([] ++ els ry.seg).Nodup := by
    simpa using (List.nodup_append.mp Hnd).2.1
  obtain ⟨Hryzero, HCry, _, _, _, _⟩ := S.consGroups_refines HryStart HCnil Hndry
  change u.ryp = 0 at Hryzero
  have HFend : StackRep u.m (s.m.rs w) foreign.seg :=
    consGroups_stack_frame HryStart HCnil Hndry HFpop (by
      intro a ha e he
      exact hd a (List.mem_append_right _ (by simpa using ha)) e he)
  obtain ⟨_, _, _, _, _, _, _, _, _, _, HGend, Hvend, _, _, _, _⟩ :=
    consGroups_arrays HryStart HCnil Hndry
  have HGfinal : u.G = s.G := HGend.trans HGpop
  have Hvfinal : u.v = s.v := Hvend.trans Hvpop
  have HCfinal : Linked u.m.nx u.ch u.ct (els ry.seg) := by simpa [u] using HCry
  have HFfinish := consStep_finish_foreign Hryzero HCfinal HFend
    (fun c hc e he => hd c (List.mem_append_right _ hc) e he)
    (fun g hg => HGfinal.symm ▸ fresh g hg)
  have HprotPop := S.popGroups_protected popped s
  have HprotRy := consGroups_protected HryStart HCnil Hndry
  have Hrs : u.m.rs = s.m.rs := HprotRy.1.trans HprotPop.1
  have Hrl : u.m.rl = s.m.rl := HprotRy.2.1.trans HprotPop.2.1
  change Stored (consStep u).m w foreign ∧ _ ∧ _
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · have hh : (consStep u).m.rs w = s.m.rs w := by
      simp [consStep, Hryzero, SMem.store, upd_ne _ _ (Hvfinal.symm ▸ Hw), Hrs]
    rw [hh]; exact HFfinish
  · simpa [consStep, Hryzero, SMem.store, upd_ne _ _ (Hvfinal.symm ▸ Hw), Hrl] using HF.low
  · change (consStep u).m.inf = _
    simpa [consStep, Hryzero, SMem.store] using HprotRy.2.2.1.trans HprotPop.2.2.1
  · change (consStep u).m.ia = _
    simpa [consStep, Hryzero, SMem.store] using HprotRy.2.2.2.trans HprotPop.2.2.2

theorem forkFinish_foreign {s : SMS} {m : SMem} {v hx hy code w : Nat} {rx ry foreign : Res}
    (Hrx : StackRep m hx rx.seg) (Hry : StackRep m hy ry.seg)
    (Hnd : (els rx.seg ++ els ry.seg).Nodup) (HF : Stored m w foreign)
    (Hw : w ≠ v) (fresh : ∀ g ∈ foreign.seg, g.id ≠ S.gid v)
    (hd : ∀ a ∈ els rx.seg ++ els ry.seg, ∀ e ∈ els foreign.seg, a ≠ e) :
    Stored (S.forkFinish s m v hx hy code rx ry).m w foreign ∧
      (∀ z, z ≠ v → (S.forkFinish s m v hx hy code rx ry).m.inf z = m.inf z) ∧
      (S.forkFinish s m v hx hy code rx ry).m.ia = m.ia := by
  by_cases hnil : ry.seg = []
  · have hyzero : hy = 0 := Hry.head_zero_iff.mpr hnil
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · have hh : (S.forkFinish s m v hx hy code rx ry).m.rs w = m.rs w := by
        simp [forkFinish, hnil, forkStart, hyzero, SMem.store, upd_ne _ _ Hw]
      rw [hh]
      simpa [forkFinish, hnil, forkStart, hyzero, SMem.store] using
        (HF.stack.store_frame v hx rx.low).inf_frame v 0
    · simpa [forkFinish, hnil, forkStart, hyzero, SMem.store, upd_ne _ _ Hw] using HF.low
    · intro z hz
      simp [forkFinish, hnil, forkStart, hyzero, SMem.store, upd_ne _ _ hz]
    · simp [forkFinish, hnil, forkStart, hyzero, SMem.store]
  · have hyne : hy ≠ 0 := fun hz => hnil (Hry.head_zero_iff.mp hz)
    let start := S.forkStart s m v hx rx.low hy ry.low code
    have Hrx' : StackRep start.m start.rxp rx.seg := by
      simpa [start, forkStart, hyne] using Hrx.inf_frame v code
    have Hry' : StackRep start.m start.ryp ry.seg := by
      simpa [start, forkStart, hyne] using Hry.inf_frame v code
    have HF' : Stored start.m w foreign := by
      exact ⟨by simpa [start, forkStart, hyne] using HF.stack.inf_frame v code,
        by simpa [start, forkStart, hyne] using HF.low⟩
    obtain ⟨Hforeign, Hinf, Hia⟩ := S.mergeState_foreign (s := start) (rx := rx) (ry := ry)
      (by simp [start, forkStart, hyne]) (by simp [start, forkStart, hyne])
      (by simp [start, forkStart, hyne]) (by simp [start, forkStart, hyne])
      Hrx' Hry' Hnd HF' (by simpa [start, forkStart, hyne] using Hw)
      (by simpa [start, forkStart, hyne] using fresh) hd
    refine ⟨by simpa [forkFinish, hnil, start] using Hforeign, ?_, ?_⟩
    · intro z hz
      simpa [forkFinish, hnil, start, forkStart, hyne, upd_ne _ _ hz] using congrFun Hinf z
    · simpa [forkFinish, hnil, start, forkStart, hyne] using Hia

end STACS2027.Embed.Sol

module

public import ApproximationHardness.Embed.SolverRecordLoops

/-! # Exact records of a completed linked merge -/

@[expose] public section

namespace STACS2027.Embed.Sol

variable (S : Sol)

def mergeRows (rx ry : Res) : List (Nat × Bool) :=
  S.upperRows ry.low (S.popped ry.low rx) ++ lowerRows ry.seg

theorem mergeState_records {s : SMS} {rx ry : Res}
    (Hlh : s.lh = ry.low) (HA : s.ah = 0) (HB : s.bh = 0) (HC : s.ch = 0)
    (Hrx : StackRep s.m s.rxp rx.seg) (Hry : StackRep s.m s.ryp ry.seg)
    (Hnd : (els rx.seg ++ els ry.seg).Nodup) :
    (S.mergeState s rx ry).m.gp = writeParents s.G (S.mergeRows rx ry) s.m.gp ∧
      (S.mergeState s rx ry).m.gf = writeFlips (S.mergeRows rx ry) s.m.gf := by
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
  have Hrypop : StackRep t.m s.ryp ry.seg :=
    S.popGroups_stack_frame Hrx' HAnil HBnil Hndrx Hpop Hry (by
      intro a ha e he
      exact (List.nodup_append.mp Hnd).2.2 a
        (els_sub hpopSub a (by simpa using ha)) e he)
  obtain ⟨_, _, _, _, _, Hryp, Hch, _, HGpop, _, _, _, _⟩ :=
    S.popGroups_arrays popped s
  have HryStart : StackRep start.m start.ryp ry.seg := by
    simpa [start, t, Hryp] using Hrypop
  have HCnil : Linked start.m.nx start.ch start.ct [] := by
    simpa [start, t, Hch, HC] using Linked.nil t.m.nx t.ct
  have Hndry : ([] ++ els ry.seg).Nodup := by
    simpa using (List.nodup_append.mp Hnd).2.1
  have Hzero : u.ryp = 0 := (S.consGroups_refines HryStart HCnil Hndry).1
  obtain ⟨Hp, Hf⟩ := S.popGroups_records Hrx' HAnil HBnil Hndrx Hpop
  obtain ⟨Hcp, Hcf⟩ := consGroups_records HryStart HCnil Hndry
  have Hp' : t.m.gp = writeParents s.G (S.upperRows ry.low popped) s.m.gp := by simpa [t, Hlh] using Hp
  have Hf' : t.m.gf = writeFlips (S.upperRows ry.low popped) s.m.gf := by simpa [t, Hlh] using Hf
  have Hcp' : u.m.gp = writeParents s.G (lowerRows ry.seg) t.m.gp := by
    simpa [u, start, t, HGpop] using Hcp
  have Hcf' : u.m.gf = writeFlips (lowerRows ry.seg) t.m.gf := Hcf
  change (consStep u).m.gp = _ ∧ (consStep u).m.gf = _
  constructor
  · simp only [consStep, Hzero, ne_eq, not_true_eq_false, ↓reduceIte, SMem.store]
    rw [Hcp', Hp']
    simp [mergeRows, writeParents, List.foldl_append, popped]
  · simp only [consStep, Hzero, ne_eq, not_true_eq_false, ↓reduceIte, SMem.store]
    rw [Hcf', Hf']
    simp [mergeRows, writeFlips, List.foldl_append, popped]

theorem mergeRows_perm {rx ry : Res} (hy : ry.seg ≠ []) :
    (S.mergeRows rx ry).Perm (S.mergeCons rx ry) := by
  simp only [mergeRows, mergeCons, hy, ↓reduceIte, lowerRows, upperRows]
  exact List.perm_append_comm

theorem writeParents_other (G : Nat) (rows : List (Nat × Bool)) (a : Nat → Nat) (g : Nat)
    (hg : g ∉ rows.map Prod.fst) : writeParents G rows a g = a g := by
  induction rows generalizing a with
  | nil => rfl
  | cons x rows ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at hg
    rw [writeParents, List.foldl_cons]
    exact (ih (upd a x.1 (G + 1)) hg.2).trans (upd_ne _ _ hg.1)

theorem writeFlips_other (rows : List (Nat × Bool)) (a : Nat → Nat) (g : Nat)
    (hg : g ∉ rows.map Prod.fst) : writeFlips rows a g = a g := by
  induction rows generalizing a with
  | nil => rfl
  | cons x rows ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at hg
    rw [writeFlips, List.foldl_cons]
    exact (ih (upd a x.1 (if x.2 then 1 else 0)) hg.2).trans (upd_ne _ _ hg.1)

theorem writeParents_mem (G : Nat) (rows : List (Nat × Bool)) (a : Nat → Nat)
    (hnd : (rows.map Prod.fst).Nodup) (x : Nat × Bool) (hx : x ∈ rows) :
    writeParents G rows a x.1 = G + 1 := by
  induction rows generalizing a with
  | nil => simp at hx
  | cons y rows ih =>
    obtain ⟨hy, hnd'⟩ := List.nodup_cons.mp hnd
    rw [writeParents, List.foldl_cons]
    rcases List.mem_cons.mp hx with rfl | hx
    · exact (writeParents_other G rows (upd a x.1 (G + 1)) x.1 hy).trans (upd_same ..)
    · exact ih _ hnd' hx

theorem writeFlips_mem (rows : List (Nat × Bool)) (a : Nat → Nat)
    (hnd : (rows.map Prod.fst).Nodup) (x : Nat × Bool) (hx : x ∈ rows) :
    writeFlips rows a x.1 = if x.2 then 1 else 0 := by
  induction rows generalizing a with
  | nil => simp at hx
  | cons y rows ih =>
    obtain ⟨hy, hnd'⟩ := List.nodup_cons.mp hnd
    rw [writeFlips, List.foldl_cons]
    rcases List.mem_cons.mp hx with rfl | hx
    · exact (writeFlips_other rows (upd a x.1 (if x.2 then 1 else 0)) x.1 hy).trans (upd_same ..)
    · exact ih _ hnd' hx

def finishRows (rx ry : Res) : List (Nat × Bool) := if ry.seg = [] then [] else S.mergeRows rx ry

theorem finishRows_perm (rx ry : Res) : (S.finishRows rx ry).Perm (S.mergeCons rx ry) := by
  by_cases hy : ry.seg = []
  · simp [finishRows, mergeCons, hy]
  · simp only [finishRows, hy, ↓reduceIte]
    exact S.mergeRows_perm hy

theorem forkFinish_records {s : SMS} {m : SMem} {v hx hy code : Nat} {rx ry : Res}
    (Hrx : StackRep m hx rx.seg) (Hry : StackRep m hy ry.seg)
    (Hnd : (els rx.seg ++ els ry.seg).Nodup) :
    (S.forkFinish s m v hx hy code rx ry).m.gp = writeParents (S.gid v) (S.finishRows rx ry) m.gp ∧
      (S.forkFinish s m v hx hy code rx ry).m.gf = writeFlips (S.finishRows rx ry) m.gf := by
  by_cases hnil : ry.seg = []
  · have hyzero : hy = 0 := Hry.head_zero_iff.mpr hnil
    simp [forkFinish, finishRows, hnil, Sol.forkStart, hyzero, SMem.store, writeParents, writeFlips]
  · have hyne : hy ≠ 0 := fun hz => hnil (Hry.head_zero_iff.mp hz)
    let start := S.forkStart s m v hx rx.low hy ry.low code
    have Hrx' : StackRep start.m start.rxp rx.seg := by
      simpa [start, forkStart, hyne] using Hrx.inf_frame v code
    have Hry' : StackRep start.m start.ryp ry.seg := by
      simpa [start, forkStart, hyne] using Hry.inf_frame v code
    have H := S.mergeState_records (s := start) (rx := rx) (ry := ry)
      (by simp [start, forkStart, hyne]) (by simp [start, forkStart, hyne])
      (by simp [start, forkStart, hyne]) (by simp [start, forkStart, hyne]) Hrx' Hry' Hnd
    simpa [forkFinish, finishRows, hnil, start, forkStart, hyne] using H

end STACS2027.Embed.Sol

module

public import ApproximationHardness.Embed.OrientationSequence
public import ApproximationHardness.RAM.FrameB
import Lean.Elab.Tactic.Omega

/-! # The actual orientation loop preserves every cell outside its orientation block -/

@[expose] public section

namespace STACS2027.Embed.RAMSolver

open RAM

attribute [local simp] ORam.base ORam.group

theorem orientationBody_mem_frame {D : OrientationLayout} {parA flpA : Nat→Nat}
    {o : Nat→Bool} {c : Config} {g : Nat} {todo : List Nat}
    (h : OrientationState D parA flpA o c (g::todo)) (hg : g<D.width)
    (a : Nat) (ha : a<D.orientation ∨ D.orientation+D.width≤a) :
    (run orientationBody c).mem a=c.mem a := by
  have hk := h.keys 0 (by simp)
  have he : (run sequenceRead c).reg ORam.group=g := by
    simpa [sequenceRead_group,h.keyBase] using hk
  have hb : (run sequenceRead c).reg ORam.base=D.orientation := by
    rw [sequenceRead_reg _ _ (by decide)]
    exact h.orientationBase
  simp only [orientationBody,run,sequenceAdvance_mem]
  rw [(orientGroup_frame _).2.2.2.2 a (by rw [he,hb];omega)]
  rw [sequenceRead_mem]

theorem orientationLoop_framed_spec {D : OrientationLayout} {parA flpA : Nat→Nat}
    (hp : ∀ g,parA g≠0 → parA g-1<D.width) :
    ∀ (todo : List Nat) (o : Nat→Bool) (c : Config),
      OrientationState D parA flpA o c todo → (∀ g∈todo,g<D.width) →
      ∃ t c',ExecB D.space orientationLoop c t c' ∧
        OrientationState D parA flpA
          (todo.foldl (fun o g=>upd o g (groupOrientation parA flpA o g)) o) c' [] ∧
        ∀ a,a<D.orientation ∨ D.orientation+D.width≤a → c'.mem a=c.mem a := by
  intro todo
  induction todo with
  | nil =>
    intro o c hc _
    exact ⟨1,c,.loopDone (by simpa using hc.count),hc,fun _ _=>rfl⟩
  | cons g todo ih =>
    intro o c hc hg
    have hgb := hg g (by simp)
    have hA := orientationBody_addrOK hc hgb hp
    have he := execB_run orientationBody orientationBody_loopFree c hA
    obtain ⟨t,c',he',hfinal,hframe⟩ := ih _ _ (orientationBody_state hc hgb hp)
      (fun a ha=>hg a (List.mem_cons_of_mem g ha))
    refine ⟨RAM.cost orientationBody c+t+1,c',
      .loopNext (by have := hc.count;simp at this;omega) he he',hfinal,?_⟩
    intro a ha
    exact (hframe a ha).trans (orientationBody_mem_frame hc hgb a ha)

/-- An arbitrary actual execution has the same outside-block frame. -/
theorem orientationLoop_mem_frame {D : OrientationLayout} {parA flpA : Nat→Nat}
    {todo : List Nat} {o : Nat→Bool} {c c' : Config} {t : Nat}
    (he : ExecB D.space orientationLoop c t c')
    (hp : ∀ g,parA g≠0 → parA g-1<D.width)
    (hc : OrientationState D parA flpA o c todo) (hg : ∀ g∈todo,g<D.width) :
    ∀ a,a<D.orientation ∨ D.orientation+D.width≤a → c'.mem a=c.mem a := by
  obtain ⟨_,c'',he',_,hf⟩ := orientationLoop_framed_spec hp todo o c hc hg
  rw [(he.det he').2]
  exact hf

end STACS2027.Embed.RAMSolver

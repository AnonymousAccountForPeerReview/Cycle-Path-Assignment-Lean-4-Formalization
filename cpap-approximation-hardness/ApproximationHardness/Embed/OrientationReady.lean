module

public import ApproximationHardness.Embed.OrientationKeyMaterialization
import Lean.Elab.Tactic.Omega

/-! # The materialized visit stream supplies the orientation loop invariant -/

@[expose] public section

namespace STACS2027.Embed.RAMSolver

open RAM

theorem keyProgram_orientationState {D : OrientationLayout} {F : ForestData}
    {post : List Nat} {parA flpA : Nat → Nat} {c : Config}
    (hzero : c.reg 0=0) (hone : c.reg 1=1) (hpost : c.reg 4=post.length)
    (hdarts : c.reg 140=2*F.E) (hsource : c.reg 71+post.length≤D.keys)
    (hcells : ∀ i,i<post.length → c.mem (c.reg 71+i)=post.getD i 0)
    (hparent : c.reg 58=D.parents) (hflip : c.reg 59=D.flips)
    (horient : c.reg 100=D.orientation) (hkeys : c.reg 113=D.keys)
    (hcap : (orientationKeys F post).length≤D.capacity)
    (hparents : ∀ g,g<D.width → c.mem (D.parents+g)=parA g)
    (hflips : ∀ g,g<D.width → c.mem (D.flips+g)=flpA g)
    (horientation : ∀ g,g<D.width → c.mem (D.orientation+g)=0) :
    ∃ t c',ExecB D.space keyProgram c t c' ∧ t≤9*post.length+14*F.E+12 ∧
      OrientationState D parA flpA (fun _=>false) c' (orientationKeys F post) ∧ c'.out=c.out := by
  have hlen : (orientationKeys F post).length=post.length+2*F.E := by
    simp [orientationKeys_explicit]
  have hspace : c.reg 113+post.length+2*F.E≤D.space := by
    rw [hkeys]
    have := D.keysBelow;omega
  obtain ⟨t,c',he,ht,hout,hcount,hposition,hvalues,hframe⟩ :=
    keyProgram_spec F post c hzero hone hpost hdarts (by rw [hkeys];exact hsource) hspace hcells
  have hreg r (hr : r<270) (ha : r≠109) (hb : r≠110) := keyProgram_regs he r hr ha hb
  refine ⟨t,c',he,ht,⟨?_,?_,?_,?_,?_,hcount,?_,?_,?_,?_,?_⟩,hout⟩
  · rw [hreg 1 (by decide) (by decide) (by decide)];exact hone
  · rw [hreg 58 (by decide) (by decide) (by decide)];exact hparent
  · rw [hreg 59 (by decide) (by decide) (by decide)];exact hflip
  · rw [hreg 100 (by decide) (by decide) (by decide)];exact horient
  · rw [hreg 113 (by decide) (by decide) (by decide)];exact hkeys
  · rw [hposition];simpa using hcap
  · intro g hg
    rw [hframe _ (Or.inl (by
      rw [hkeys];have := D.parentsBelow;have := D.keysAbove;omega))]
    exact hparents g hg
  · intro g hg
    rw [hframe _ (Or.inl (by
      rw [hkeys];have := D.flipsBelow;have := D.keysAbove;omega))]
    exact hflips g hg
  · intro g hg
    rw [hframe _ (Or.inl (by rw [hkeys];have := D.keysAbove;omega)),horientation g hg]
    rfl
  · intro j hj
    simpa only [hkeys,hposition,Nat.add_zero] using hvalues j hj

end STACS2027.Embed.RAMSolver

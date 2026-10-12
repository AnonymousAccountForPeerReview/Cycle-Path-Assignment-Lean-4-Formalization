module

public import ApproximationHardness.Embed.DefaultRotationStep
import Lean.Elab.Tactic.Omega

/-! # Read-only tables needed by the actual default-rotation scan -/

@[expose] public section

namespace STACS2027.Embed.RAMSolver

open RAM

def defaultSourceRegisters : List Nat := [66,67,68,69,70,160,161,162,166,280]
def defaultFixedRegisters : List Nat := [0,1,140,261,262]++defaultSourceRegisters

structure DefaultReady (F : ForestData) (S : Nat) (c : Config) : Prop where
  zero : c.reg 0=0
  one : c.reg 1=1
  darts : c.reg 140=2*F.E
  separated : c.reg 261+2*F.E≤c.reg 262
  capacity : c.reg 262+2*F.E≤S
  sourceBound : ∀ r∈defaultSourceRegisters,∀ i,i<2*F.E → c.reg r+i<c.reg 261
  rep : ∀ d,d<2*F.E → c.mem (c.reg 160+d)=F.rep d
  parent : ∀ v,v<2*F.E → c.mem (c.reg 166+v)=F.par v
  partner : ∀ d,d<2*F.E → c.mem (c.reg 161+d)=STACS2027.Embed.pair d
  degree : ∀ v,v<2*F.E → c.mem (c.reg 162+v)=(F.dartsAt v).length
  count : ∀ v,v<2*F.E → c.mem (c.reg 66+v)=(F.parts v).length
  leftType : ∀ v,v<2*F.E → c.mem (c.reg 67+v)=itemType ((F.parts v).getD 0 (.node 0))
  leftValue : ∀ v,v<2*F.E → c.mem (c.reg 68+v)=itemValue ((F.parts v).getD 0 (.node 0))
  rightType : ∀ v,v<2*F.E → c.mem (c.reg 69+v)=itemType ((F.parts v).getD 1 (.node 0))
  rightValue : ∀ v,v<2*F.E → c.mem (c.reg 70+v)=itemValue ((F.parts v).getD 1 (.node 0))
  distinguished : ∀ v,v<2*F.E → c.mem (c.reg 280+v)=F.zOf v
  partsBound : ∀ v,v<2*F.E → (F.parts v).length≤2
  childBound : ∀ v,v<2*F.E → ∀ w,Item.node w∈F.parts v → w<2*F.E ∧ F.par w<2*F.E

structure DefaultFrame (F : ForestData) (start c : Config) : Prop where
  reg : ∀ r∈defaultFixedRegisters,c.reg r=start.reg r
  mem : ∀ a,a<start.reg 261 ∨ start.reg 262+2*F.E≤a → c.mem a=start.mem a

theorem DefaultFrame.refl (F : ForestData) (c : Config) : DefaultFrame F c c :=
  ⟨fun _ _=>rfl,fun _ _=>rfl⟩

theorem DefaultFrame.read {F : ForestData} {S : Nat} {start c : Config}
    (h : DefaultFrame F start c) (hs : DefaultReady F S start) (r : Nat)
    (hr : r∈defaultSourceRegisters) (i : Nat) (hi : i<2*F.E) :
    c.mem (c.reg r+i)=start.mem (start.reg r+i) := by
  rw [h.reg r (by simp [defaultFixedRegisters,hr])]
  exact h.mem _ (Or.inl (hs.sourceBound r hr i hi))

theorem DefaultReady.frame {F : ForestData} {S : Nat} {start c : Config}
    (h : DefaultReady F S start) (hf : DefaultFrame F start c) : DefaultReady F S c := by
  have hreg r (hr : r∈defaultFixedRegisters) := hf.reg r hr
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,h.partsBound,h.childBound⟩
  · rw [hreg 0 (by simp [defaultFixedRegisters])];exact h.zero
  · rw [hreg 1 (by simp [defaultFixedRegisters])];exact h.one
  · rw [hreg 140 (by simp [defaultFixedRegisters])];exact h.darts
  · rw [hreg 261 (by simp [defaultFixedRegisters]),hreg 262 (by simp [defaultFixedRegisters])];exact h.separated
  · rw [hreg 262 (by simp [defaultFixedRegisters])];exact h.capacity
  · intro r hr i hi
    rw [hreg r (by simp [defaultFixedRegisters,hr]),hreg 261 (by simp [defaultFixedRegisters])]
    exact h.sourceBound r hr i hi
  · intro d hd;rw [hf.read h 160 (by simp [defaultSourceRegisters]) d hd];exact h.rep d hd
  · intro v hv;rw [hf.read h 166 (by simp [defaultSourceRegisters]) v hv];exact h.parent v hv
  · intro d hd;rw [hf.read h 161 (by simp [defaultSourceRegisters]) d hd];exact h.partner d hd
  · intro v hv;rw [hf.read h 162 (by simp [defaultSourceRegisters]) v hv];exact h.degree v hv
  · intro v hv;rw [hf.read h 66 (by simp [defaultSourceRegisters]) v hv];exact h.count v hv
  · intro v hv;rw [hf.read h 67 (by simp [defaultSourceRegisters]) v hv];exact h.leftType v hv
  · intro v hv;rw [hf.read h 68 (by simp [defaultSourceRegisters]) v hv];exact h.leftValue v hv
  · intro v hv;rw [hf.read h 69 (by simp [defaultSourceRegisters]) v hv];exact h.rightType v hv
  · intro v hv;rw [hf.read h 70 (by simp [defaultSourceRegisters]) v hv];exact h.rightValue v hv
  · intro v hv;rw [hf.read h 280 (by simp [defaultSourceRegisters]) v hv];exact h.distinguished v hv

/-- The literal machine read and selector produce exactly the default rotations. -/
theorem defaultRotationStep_correct {F : ForestData} (hF : F.Valid) {S : Nat} {c : Config}
    (h : DefaultReady F S c) (hd : c.reg 240<2*F.E) :
    AddrOK S defaultRotationStep c ∧
    ∀ a,(run defaultRotationStep c).mem a=
      if a=c.reg 262+c.reg 240 then ForestData.rotInvN hF (fun _=>false) (c.reg 240)
      else if a=c.reg 261+c.reg 240 then ForestData.rotN hF (fun _=>false) (c.reg 240)
      else c.mem a := by
  have hv : F.rep (c.reg 240)<2*F.E := hF.rep_lt _ hd
  have hchild w (hw : Item.node w∈F.parts (F.rep (c.reg 240))) := h.childBound _ hv w hw
  have hchildMem : ∀ w,Item.node w∈F.parts (F.rep (c.reg 240)) →
      c.mem (c.reg 166+w)=F.par w ∧ c.mem (c.reg 161+F.par w)=STACS2027.Embed.pair (F.par w) := by
    intro w hw;exact ⟨h.parent w (hchild w hw).1,h.partner _ (hchild w hw).2⟩
  have hval := rotationRead_values F _ c h.zero h.one h.darts (h.rep _ hd) (h.parent _ hv)
    (h.degree _ hv) (h.count _ hv) (h.leftType _ hv) (h.leftValue _ hv)
    (h.rightType _ hv) (h.rightValue _ hv) (h.distinguished _ hv) (h.partsBound _ hv) hchildMem
  have hselect := nextPredCode_values (run rotationRead c)
    (by rw [rotationRead_reg _ 0 (by omega)];exact h.zero)
    (by rw [rotationRead_reg _ 1 (by omega)];exact h.one) hval.2.2.2.2.2
  rw [rotationRead_reg _ 240 (by omega),hval.2.1,hval.2.2.1,hval.2.2.2.1,hval.2.2.2.2.1] at hselect
  have hpure := cycleSlots_labels F hF (c.reg 240) hd (h.partsBound _ hv)
  rw [hpure.1,hpure.2] at hselect
  have haddr r (hr : r∈defaultSourceRegisters) i (hi : i<2*F.E) : c.reg r+i<S := by
    have := h.sourceBound r hr i hi
    have := h.separated
    have := h.capacity
    omega
  have hread : AddrOK S rotationRead c := by
    apply rotationRead_addrOK F _ S c h.zero h.one (h.rep _ hd) (h.parent _ hv)
      (h.count _ hv) (h.leftType _ hv) (h.leftValue _ hv) (h.rightType _ hv)
      (h.rightValue _ hv) (h.partsBound _ hv)
    · exact haddr 160 (by simp [defaultSourceRegisters]) _ hd
    · exact haddr 166 (by simp [defaultSourceRegisters]) _ hv
    · exact haddr 162 (by simp [defaultSourceRegisters]) _ hv
    · exact haddr 66 (by simp [defaultSourceRegisters]) _ hv
    · exact haddr 67 (by simp [defaultSourceRegisters]) _ hv
    · exact haddr 68 (by simp [defaultSourceRegisters]) _ hv
    · exact haddr 69 (by simp [defaultSourceRegisters]) _ hv
    · exact haddr 70 (by simp [defaultSourceRegisters]) _ hv
    · exact haddr 280 (by simp [defaultSourceRegisters]) _ hv
    · intro w hw
      exact ⟨(hchildMem w hw).1,haddr 166 (by simp [defaultSourceRegisters]) _ (hchild w hw).1,
        haddr 161 (by simp [defaultSourceRegisters]) _ (hchild w hw).2⟩
  refine ⟨defaultRotationStep_addrOK c hread (by have := h.separated;have := h.capacity;omega)
    (by have := h.capacity;omega),?_⟩
  intro a;rw [defaultRotationStep_mem,hselect.1,hselect.2]

end STACS2027.Embed.RAMSolver

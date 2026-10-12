module

public import ApproximationHardness.Embed.SolverExecution
import Lean.Elab.Tactic.Omega

/-! # Certified lower bounds on the addresses written by the solver -/

@[expose] public section

namespace STACS2027.Embed.RAMSolver

open RAM

def FloorReady (bound : Nat) (known : List Nat) (c : Config) : Prop :=
  ∀ r,r∈known → bound≤c.reg r

def floorPlan : Stmt → List Nat → Option (List Nat)
  | .skip,k => some k
  | .const d _,k => some (k.filter (·≠d))
  | .add d a b,k => some (if a∈k ∨ b∈k then d::k.filter (·≠d) else k.filter (·≠d))
  | .sub d _ _,k => some (k.filter (·≠d))
  | .load d _,k => some (k.filter (·≠d))
  | .store a _,k => if a∈k then some k else none
  | .write _,k => some k
  | .seq p q,k => (floorPlan p k).bind (floorPlan q)
  | .ifz _ p q,k => do
      let kp ← floorPlan p k
      let kq ← floorPlan q k
      pure (kp.filter (·∈kq))
  | .loop _ p,k => do
      let kp ← floorPlan p k
      if k.all (·∈kp) then pure k else none

theorem floorReady_setReg {bound value : Nat} {known : List Nat} {c : Config}
    (hr : FloorReady bound known c) (d : Nat) :
    FloorReady bound (known.filter (·≠d)) (c.setReg d value) := by
  intro r hh
  have hm := List.mem_filter.mp hh
  have hn : r≠d := of_decide_eq_true hm.2
  simpa [Config.setReg,hn] using hr r hm.1

theorem floorReady_add {bound : Nat} {known : List Nat} {c : Config}
    (hr : FloorReady bound known c) (d a b : Nat) :
    FloorReady bound (if a∈known ∨ b∈known then d::known.filter (·≠d)
      else known.filter (·≠d)) (c.setReg d (c.reg a+c.reg b)) := by
  split
  · rename_i h
    intro r hm
    rcases List.mem_cons.mp hm with rfl | hm
    · simp only [Config.setReg,↓reduceIte]
      rcases h with ha | hb
      · exact (hr a ha).trans (Nat.le_add_right _ _)
      · exact (hr b hb).trans (Nat.le_add_left _ _)
    · exact floorReady_setReg hr d r hm
  · exact floorReady_setReg hr d

/-- The syntax certificate proves both the register lower bounds and the exact
memory frame for every bounded execution, including nested loops. -/
theorem floorPlan_exec {space bound : Nat} {p : Stmt} {c d : Config} {t : Nat}
    (he : ExecB space p c t d) : ∀ {known result : List Nat},
    floorPlan p known=some result → FloorReady bound known c →
    FloorReady bound result d ∧ ∀ a,a<bound → d.mem a=c.mem a := by
  induction he with
  | skip c => intro k result hp hr;cases hp;exact ⟨hr,fun _ _=>rfl⟩
  | const r v c =>
    intro k result hp hr;cases hp
    exact ⟨floorReady_setReg hr r,fun _ _=>rfl⟩
  | add r a b c =>
    intro k result hp hr;cases hp
    exact ⟨floorReady_add hr r a b,fun _ _=>rfl⟩
  | sub r a b c =>
    intro k result hp hr;cases hp
    exact ⟨floorReady_setReg hr r,fun _ _=>rfl⟩
  | load r a c ha =>
    intro k result hp hr;cases hp
    exact ⟨floorReady_setReg hr r,fun _ _=>rfl⟩
  | store a r c ha =>
    intro k result hp hr
    simp only [floorPlan] at hp
    split at hp
    · rename_i hknown;cases hp
      refine ⟨hr,?_⟩
      intro i hi
      have haddr := hr a hknown
      simp [Config.setMem,show i≠c.reg a by omega]
    · contradiction
  | write r c => intro k result hp hr;cases hp;exact ⟨hr,fun _ _=>rfl⟩
  | @seq p q c₀ c₁ c₂ t₀ t₁ h₁ h₂ ih₁ ih₂ =>
    intro k result hp hr
    simp only [floorPlan] at hp
    cases hx : floorPlan p k with
    | none => simp [hx] at hp
    | some mid =>
      simp only [hx,Option.bind_some] at hp
      obtain ⟨hr₁,hm₁⟩ := ih₁ hx hr
      obtain ⟨hr₂,hm₂⟩ := ih₂ hp hr₁
      exact ⟨hr₂,fun a ha=>(hm₂ a ha).trans (hm₁ a ha)⟩
  | @ifzTrue a p q c₀ c₁ t₀ hz h ih =>
    intro k result hp hr
    simp only [floorPlan] at hp
    cases hx : floorPlan p k with
    | none => simp [hx] at hp
    | some left =>
      cases hy : floorPlan q k with
      | none => simp [hx,hy] at hp
      | some right =>
        simp [hx,hy] at hp
        subst result
        obtain ⟨hl,hm⟩ := ih hx hr
        exact ⟨fun r hh=>hl r (List.mem_filter.mp hh).1,hm⟩
  | @ifzFalse a p q c₀ c₁ t₀ hz h ih =>
    intro k result hp hr
    simp only [floorPlan] at hp
    cases hx : floorPlan p k with
    | none => simp [hx] at hp
    | some left =>
      cases hy : floorPlan q k with
      | none => simp [hx,hy] at hp
      | some right =>
        simp [hx,hy] at hp
        subst result
        obtain ⟨hr',hm⟩ := ih hy hr
        exact ⟨fun r hh=>hr' r (of_decide_eq_true (List.mem_filter.mp hh).2),hm⟩
  | @loopDone a body c₀ hz =>
    intro k result hp hr
    simp only [floorPlan] at hp
    cases hx : floorPlan body k with
    | none => simp [hx] at hp
    | some mid =>
      simp only [hx] at hp
      change (if k.all (·∈mid) then some k else none)=some result at hp
      split at hp
      · cases hp;exact ⟨hr,fun _ _=>rfl⟩
      · contradiction
  | @loopNext a body c₀ c₁ c₂ t₀ t₁ hn hbody hloop ihbody ihloop =>
    intro k result hp hr
    have hp' := hp
    simp only [floorPlan] at hp'
    cases hx : floorPlan body k with
    | none => simp [hx] at hp'
    | some mid =>
      simp only [hx] at hp'
      change (if k.all (·∈mid) then some k else none)=some result at hp'
      split at hp'
      · rename_i hsub;cases hp'
        obtain ⟨hr₁,hm₁⟩ := ihbody hx hr
        have hr₂ : FloorReady bound k c₁ := by
          intro r hh
          exact hr₁ r (of_decide_eq_true ((List.all_eq_true.mp hsub) r hh))
        obtain ⟨hr₃,hm₃⟩ := ihloop hp hr₂
        exact ⟨hr₃,fun a ha=>(hm₃ a ha).trans (hm₁ a ha)⟩
      · contradiction

def solverFloorRegisters : List Nat := (List.range 22).map (50+·)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem solverProgram_floor_certificate :
    floorPlan solverProgram solverFloorRegisters=some solverFloorRegisters := by
  decide

theorem solverFloorReady {L : Layout} {c : Config} (hb : Bases L c) :
    FloorReady L.base solverFloorRegisters c := by
  intro r hr
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hr
  rw [hb.2.2.2.2 j (List.mem_range.mp hj)]
  exact Nat.le_add_right _ _

/-- The entire solver preserves the original input and every cached DFS cell
below its allocated mutable and plan tables. -/
theorem solverProgram_memBelow {L : Layout} {c d : Config} {t : Nat}
    (hb : Bases L c) (he : ExecB L.limit solverProgram c t d) :
    ∀ a,a<L.base → d.mem a=c.mem a := by
  exact (floorPlan_exec he solverProgram_floor_certificate (solverFloorReady hb)).2

end STACS2027.Embed.RAMSolver

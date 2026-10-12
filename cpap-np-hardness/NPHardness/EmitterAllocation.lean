module

public import Complexity.EmitterTools
public import Complexity.StackTableauFits

/-! Polynomial rectangular allocation for clause emitters. A static emitter
can reserve fresh slots even in branches that do not execute. The allocation
uses arithmetic expressions from the already verified compiler. -/

@[expose] public section
namespace STACS2027
open Complexity Complexity.SAT Complexity.StackTableauEmitter
open Complexity.StackTableauEmitterCompile

def emitterSlots {n : Nat} : ClauseProgram n → Nat → Nat
  | .clause _, _ => 1
  | .seq p q, C => emitterSlots p C + emitterSlots q C
  | .forDown _ p, C => C * emitterSlots p C
  | .ifLe _ _ p q, C => emitterSlots p C + emitterSlots q C
  | .ifInput _ p q r, C => emitterSlots p C + emitterSlots q C + emitterSlots r C

def emitterSlotsExpr {n m : Nat} : ClauseProgram n → NumExpr m → NumExpr m
  | .clause _, _ => .const 1
  | .seq p q, C => .add (emitterSlotsExpr p C) (emitterSlotsExpr q C)
  | .forDown _ p, C => .mul C (emitterSlotsExpr p C)
  | .ifLe _ _ p q, C => .add (emitterSlotsExpr p C) (emitterSlotsExpr q C)
  | .ifInput _ p q r, C => .add (.add (emitterSlotsExpr p C) (emitterSlotsExpr q C)) (emitterSlotsExpr r C)

theorem emitterSlotsExpr_eval {n m : Nat} (p : ClauseProgram n) (C : NumExpr m) (env : Env m) :
    (emitterSlotsExpr p C).eval env = emitterSlots p (C.eval env) := by
  induction p <;> simp [emitterSlotsExpr,emitterSlots,NumExpr.eval, *]

def allocatedEmit {n : Nat} : ClauseProgram n → SAT.Word → Env n → Nat → Nat → List (Nat × Clause)
  | .clause ls, _, env, _, base => [(base,ls.map (fun l => l.eval env))]
  | .seq p q, input, env, C, base =>
      allocatedEmit p input env C (base + emitterSlots q C) ++ allocatedEmit q input env C base
  | .forDown bound p, input, env, C, base =>
      (List.range (bound.eval env)).reverse.flatMap fun i =>
        allocatedEmit p input (extend i env) C (base + i * emitterSlots p C)
  | .ifLe l r p q, input, env, C, base =>
      if l.eval env ≤ r.eval env then allocatedEmit p input env C base else allocatedEmit q input env C base
  | .ifInput i p q r, input, env, C, base =>
      match input[i.eval env]? with
      | none => allocatedEmit p input env C base
      | some false => allocatedEmit q input env C base
      | some true => allocatedEmit r input env C base

theorem allocatedEmit_forget {n : Nat} (p : ClauseProgram n) (input : SAT.Word) (env : Env n) (C base : Nat) :
    (allocatedEmit p input env C base).map Prod.snd = p.emit input env := by
  induction p generalizing base with
  | clause ls => rfl
  | seq p q ihp ihq => simp [allocatedEmit,ClauseProgram.emit,ihp,ihq]
  | forDown b p ih =>
    simp only [allocatedEmit,ClauseProgram.emit,List.map_flatMap]
    apply congrArg (List.flatMap · (List.range (b.eval env)).reverse)
    funext i
    exact ih (extend i env) _
  | ifLe l r p q ihp ihq =>
    simp only [allocatedEmit,ClauseProgram.emit]
    split <;> simp [ihp,ihq]
  | ifInput i p q r ihp ihq ihr =>
    simp only [allocatedEmit,ClauseProgram.emit]
    split
    · next h => simp only [h,ihp]
    · next h => simp only [h,ihq]
    · next h => simp only [h,ihr]

theorem allocatedEmit_bounds {n : Nat} (p : ClauseProgram n) (input : SAT.Word) (env : Env n) (C base : Nat)
    (hfit : p.Fits input env C) :
    ∀ x ∈ allocatedEmit p input env C base, base ≤ x.1 ∧ x.1 < base + emitterSlots p C := by
  induction p generalizing base with
  | clause ls =>
    intro x hx
    have he : x = (base,ls.map (fun l => l.eval env)) := by simpa [allocatedEmit] using hx
    subst x
    simp [emitterSlots]
  | seq p q ihp ihq =>
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · have h := ihp env _ hfit.1 x hx
      simp only [emitterSlots]
      omega
    · have h := ihq env _ hfit.2 x hx
      simp only [emitterSlots]
      omega
  | forDown b p ih =>
    intro x hx
    obtain ⟨i,hi,hx⟩ := List.mem_flatMap.mp hx
    have hi' : i < b.eval env := by simpa using hi
    have h := ih (extend i env) _ (hfit.2 i hi') x hx
    have hcap := NumFits.value hfit.1
    have hm : (i+1)*emitterSlots p C ≤ C*emitterSlots p C := Nat.mul_le_mul_right _ (by omega)
    rw [Nat.add_mul,Nat.one_mul] at hm
    simp only [emitterSlots]
    omega
  | ifLe l r p q ihp ihq =>
    simp only [allocatedEmit]
    split
    · intro x hx
      have h := ihp env _ hfit.2.2.1 x hx
      simp only [emitterSlots]
      omega
    · intro x hx
      have h := ihq env _ hfit.2.2.2 x hx
      simp only [emitterSlots]
      omega
  | ifInput i p q r ihp ihq ihr =>
    simp only [allocatedEmit]
    split
    · intro x hx
      have h := ihp env _ hfit.2.1 x hx
      simp only [emitterSlots]
      omega
    · intro x hx
      have h := ihq env _ hfit.2.2.1 x hx
      simp only [emitterSlots]
      omega
    · intro x hx
      have h := ihr env _ hfit.2.2.2 x hx
      simp only [emitterSlots]
      omega

theorem allocatedEmit_descending {n : Nat} (p : ClauseProgram n) (input : SAT.Word) (env : Env n) (C base : Nat)
    (hfit : p.Fits input env C) :
    (allocatedEmit p input env C base).Pairwise (fun x y => y.1 < x.1) := by
  induction p generalizing base with
  | clause ls => simp [allocatedEmit]
  | seq p q ihp ihq =>
    apply List.pairwise_append.mpr
    refine ⟨ihp env _ hfit.1,ihq env _ hfit.2,?_⟩
    intro x hx y hy
    have h1 := allocatedEmit_bounds p input env C _ hfit.1 x hx
    have h2 := allocatedEmit_bounds q input env C _ hfit.2 y hy
    omega
  | forDown bound p ih =>
    apply List.pairwise_flatMap.mpr
    constructor
    · intro i hi
      have hi' : i < bound.eval env := by simpa using hi
      exact ih (extend i env) _ (hfit.2 i hi')
    · have hr : (List.range (bound.eval env)).reverse.Pairwise (fun i j => j < i) := by
        simpa only [List.pairwise_reverse] using
          (List.pairwise_lt_range (n := bound.eval env))
      apply hr.imp_of_mem
      intro i j hi hj hji x hx y hy
      have hi' : i < bound.eval env := by simpa using hi
      have hj' : j < bound.eval env := by simpa using hj
      have h1 := allocatedEmit_bounds p input (extend i env) C _ (hfit.2 i hi') x hx
      have h2 := allocatedEmit_bounds p input (extend j env) C _ (hfit.2 j hj') y hy
      have hm := Nat.mul_le_mul_right (emitterSlots p C) (show j+1 ≤ i by omega)
      rw [Nat.add_mul,Nat.one_mul] at hm
      omega
  | ifLe l r p q ihp ihq =>
    simp only [allocatedEmit]
    split
    · exact ihp env _ hfit.2.2.1
    · exact ihq env _ hfit.2.2.2
  | ifInput i p q r ihp ihq ihr =>
    simp only [allocatedEmit]
    split
    · exact ihp env _ hfit.2.1
    · exact ihq env _ hfit.2.2.1
    · exact ihr env _ hfit.2.2.2

theorem allocatedEmit_literals {n : Nat} (p : ClauseProgram n) (input : SAT.Word) (env : Env n) (C base : Nat)
    (hfit : p.Fits input env C) :
    ∀ x ∈ allocatedEmit p input env C base, x.2.length ≤ C ∧ ∀ l ∈ x.2, l.var ≤ C := by
  induction p generalizing base with
  | clause ls =>
    intro x hx
    have he : x = (base,ls.map (fun l => l.eval env)) := by simpa [allocatedEmit] using hx
    subst x
    refine ⟨by simpa using hfit.1,?_⟩
    intro l hl
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hl
    exact NumFits.value (hfit.2 q hq)
  | seq p q ihp ihq =>
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact ihp env _ hfit.1 x hx
    · exact ihq env _ hfit.2 x hx
  | forDown bound p ih =>
    intro x hx
    obtain ⟨i,hi,hx⟩ := List.mem_flatMap.mp hx
    have hi' : i < bound.eval env := by simpa using hi
    exact ih (extend i env) _ (hfit.2 i hi') x hx
  | ifLe l r p q ihp ihq =>
    simp only [allocatedEmit]
    split
    · exact ihp env _ hfit.2.2.1
    · exact ihq env _ hfit.2.2.2
  | ifInput i p q r ihp ihq ihr =>
    simp only [allocatedEmit]
    split
    · exact ihp env _ hfit.2.1
    · exact ihq env _ hfit.2.2.1
    · exact ihr env _ hfit.2.2.2

end STACS2027

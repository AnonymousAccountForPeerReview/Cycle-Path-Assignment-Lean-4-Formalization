module

public import Runtimes.BoundedCost.OuterRepresentation
public import Runtimes.BoundedCost.InnerCompilerBridge
import Mathlib.Tactic

/-! The outer semantic state is independent of its odometer and power
controls, and of the temporary used to test the seed's deletion budget. -/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 STACS2027.RAM STACS2027.RAM.P3 Complexity.SAT

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

def outerControlWrites : List ℕ :=
  (callerRegister wordIndex :: rT :: wregs (renameRegisters callerRegister odo)) ++
    wregs (renameRegisters callerRegister (powTo wordCount rOL))

def outerReadRegisters : List ℕ := Compiler.globalRegisters ++
  [rOB, rOL, rK, seedSpecialCount, Compiler.processed, Compiler.alive, nodeSuccess]

theorem outerControlWrites_mod {r : ℕ} (hr : r ∈ outerControlWrites) : r % 4 = 3 := by
  simp only [outerControlWrites, List.mem_append, List.mem_cons, renameRegisters_wregs] at hr
  rcases hr with (h | h | h) | h
  · subst r; simp [callerRegister, Nat.add_mod]
  · subst r; decide
  all_goals
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp h
    simp [callerRegister, Nat.add_mod]

theorem outerRep_indep_of_protected (F : Stmt) (layout : CompilerLayout) (nodes : ℕ)
    (original : CNF) (τ : Assignment) (rows : List (Bool × Clause)) (special : CNF)
    (budget depth processed : ℕ) (oldOutput : List ℕ) (answer : Option Assignment)
    (digits : List ℕ) (W : List ℕ)
    (hreads : ∀ r ∈ outerReadRegisters, callerRegister r ∉ W)
    (hmod : ∀ r ∈ W, r % 4 ≠ 0) :
    Indep W (OuterRep F layout nodes original τ rows special budget depth processed
      oldOutput answer digits) := by
  intro c c' hframe h
  rcases h with ⟨⟨hg, hc, hr, hz, ho, hbase, hspecial, hob, hol, hk, hdigits,
    hlen, hcount, hp, halive⟩, hans⟩
  have hg' := Compiler.globals_reg_frame hg (fun r hr => hframe.reg _
    (hreads r (List.mem_append_left _ hr)))
  have hz' := (Compiler.stageZero_reg_indep (Flow.hornSeparator F) W hmod).indep c c' hframe hz
  refine ⟨⟨hg', by simpa only [hframe.mem] using hc,
    by simpa only [hframe.mem] using hr, hz', hframe.out.trans ho,
    by simpa only [hframe.mem] using hbase, by simpa only [hframe.mem] using hspecial,
    (hframe.reg _ (hreads _ (by simp [outerReadRegisters]))).trans hob,
    (hframe.reg _ (hreads _ (by simp [outerReadRegisters]))).trans hol,
    (hframe.reg _ (hreads _ (by simp [outerReadRegisters]))).trans hk,
    by simpa only [hframe.mem] using hdigits, hlen,
    (hframe.reg _ (hreads _ (by simp [outerReadRegisters]))).trans hcount,
    (hframe.reg _ (hreads _ (by simp [outerReadRegisters]))).trans hp,
    (hframe.reg _ (hreads _ (by simp [outerReadRegisters]))).trans halive⟩, ?_⟩
  cases answer with
  | none => exact (hframe.reg _ (hreads _ (by simp [outerReadRegisters]))).trans hans
  | some σ => exact ⟨(hframe.reg _ (hreads _ (by simp [outerReadRegisters]))).trans hans.1,
      by simpa only [hframe.mem] using hans.2⟩

theorem outerRep_indep (F : Stmt) (layout : CompilerLayout) (nodes : ℕ) (original : CNF)
    (τ : Assignment) (rows : List (Bool × Clause)) (special : CNF)
    (budget depth processed : ℕ) (oldOutput : List ℕ) (answer : Option Assignment)
    (digits : List ℕ) :
    Indep outerControlWrites (OuterRep F layout nodes original τ rows special budget depth
      processed oldOutput answer digits) := by
  apply outerRep_indep_of_protected
  · intro r hr
    have hs : r = 200 ∨ r = 201 ∨ r = 202 ∨ r = 203 ∨ r = 204 ∨ r = 220 ∨
      r = 222 ∨ r = 223 ∨ r = 225 ∨ r = 226 ∨ r = 300 ∨ r = 344 ∨ r = 345 ∨
      r = 350 ∨ r = 400 ∨ r = 406 ∨ r = 430 ∨ r = 433 ∨ r = 434 ∨ r = 435 ∨
      r = rOB ∨ r = rOL ∨ r = rK ∨ r = seedSpecialCount ∨ r = Compiler.processed ∨
      r = Compiler.alive ∨ r = nodeSuccess := by
        simpa [outerReadRegisters, Compiler.globalRegisters] using hr
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
    all_goals decide
  · intro r hr
    have hm := outerControlWrites_mod hr
    omega

theorem outerRep_excess_indep (F : Stmt) (layout : CompilerLayout) (nodes : ℕ) (original : CNF)
    (τ : Assignment) (rows : List (Bool × Clause)) (special : CNF)
    (budget depth processed : ℕ) (oldOutput : List ℕ) (answer : Option Assignment)
    (digits : List ℕ) :
    Indep [callerRegister Compiler.branchExcess]
      (OuterRep F layout nodes original τ rows special budget depth processed oldOutput answer digits) := by
  apply outerRep_indep_of_protected
  · intro r hr
    simp only [List.mem_singleton]
    intro he
    have he' := callerRegister_injective he
    subst r
    simp +decide [outerReadRegisters, Compiler.globalRegisters, Compiler.branchExcess] at hr
  · intro r hr
    have he := List.mem_singleton.mp hr
    subst r
    decide

theorem outerGeometry_compilerLayout (constant clauses budget S special : ℕ)
    (hspace : (compilerLayout constant clauses budget).space ≤ S)
    (hspecial : special ≤ min budget clauses + 1) :
    OuterGeometry S (compilerLayout constant clauses budget) (2 * clauses + 1) clauses
      (min budget clauses + 1) special := by
  constructor
  · exact innerGeometry_compilerLayout constant clauses budget S hspace
  all_goals dsimp [compilerLayout]; omega

end STACS2027.Runtimes.BoundedCost
